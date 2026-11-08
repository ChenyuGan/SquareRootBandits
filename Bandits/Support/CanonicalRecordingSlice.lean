/-
Copyright (c) 2026 Bandits Lean preparation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ContinuousControlSlice
public import Bandits.Support.PublicDiscreteDraws
public import Bandits.Support.SparseCalendarReplay
public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.CanonicalRecordingRates

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Concrete recording gates on one accepted public control slice

This module proves the one-slice mask and thinning probabilities from the
actual product measure and draw maps. Its source is
`05_binary_transport.tex:352-431`,
`appendix_b_communication.tex:25-44`, and
`04_slow_fast_learner.tex:96-155`, including canonical rates and
feasibility. It does not assert the conditional
physical recording law or adaptive freshness.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.CanonicalRecordingSlice

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

abbrev Slice (m K : ℕ) := _root_.Bandits.Support.ContinuousControlSlice.Slice m K
abbrev Scalar := _root_.Bandits.Support.ContinuousControlSlice.Scalar

open _root_.Bandits.Support.ContinuousControlSlice
open PublicDiscreteDraws

/-- The zero-based player enumeration of the players other than a fixed owner.
This is the same omitted-coordinate construction used by `Fin.succAbove`. -/
def otherPlayerAt {m : ℕ} (hm : 2 ≤ m) (i : Fin m)
    (r : Fin (followerCount m)) : Fin m :=
  Fin.cast (followerCount_add_one hm)
    ((Fin.cast (followerCount_add_one hm).symm i).succAbove r)

theorem otherPlayerAt_ne {m : ℕ} (hm : 2 ≤ m) (i : Fin m)
    (r : Fin (followerCount m)) : otherPlayerAt hm i r ≠ i := by
  let owner : Fin (followerCount m + 1) :=
    Fin.cast (followerCount_add_one hm).symm i
  intro h
  have h' : Fin.cast (followerCount_add_one hm) (owner.succAbove r) =
      Fin.cast (followerCount_add_one hm) owner := by
    simpa [otherPlayerAt, owner] using h
  exact Fin.succAbove_ne owner r ((Fin.cast_injective (followerCount_add_one hm)) h')

theorem otherPlayerAt_injective {m : ℕ} (hm : 2 ≤ m) (i : Fin m) :
    Function.Injective (otherPlayerAt hm i) := by
  intro r s h
  have h' := (Fin.cast_injective (followerCount_add_one hm)) h
  exact Fin.succAbove_right_injective h'

theorem otherPlayerAt_surjective {m : ℕ} (hm : 2 ≤ m) (i : Fin m)
    (ell : {ell : Fin m // ell ≠ i}) :
    ∃ r : Fin (followerCount m), otherPlayerAt hm i r = ell.val := by
  let owner : Fin (followerCount m + 1) := Fin.cast
    (followerCount_add_one hm).symm i
  let target : Fin (followerCount m + 1) := Fin.cast
    (followerCount_add_one hm).symm ell.val
  have hne : target ≠ owner := by
    intro h
    have h' : Fin.cast (followerCount_add_one hm) target =
        Fin.cast (followerCount_add_one hm) owner := by
      simpa [target, owner] using h
    have hv := (Fin.cast_injective (followerCount_add_one hm)) h'
    exact ell.property (by simpa [target, owner] using hv)
  obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq hne
  refine ⟨r, ?_⟩
  simpa [otherPlayerAt, owner, target] using
    congrArg (Fin.cast (followerCount_add_one hm)) hr

/-- The literal source mask on a continuous control slice. -/
def recordingMask {m K : ℕ} (hK : 0 < K) (i : Fin m) (j : Fin K)
    (x : Slice m K) : Prop :=
  ∀ ell : Fin m, ell ≠ i → pilotDraw hK ell x ≠ j

/-- The source probability factor `zeta = (1 - 1/K)^(m-1)`. -/
def recordingZeta (m K : ℕ) : ℝ :=
  (1 - (1 : ℝ) / (K : ℝ)) ^ (m - 1)

theorem recordingZeta_nonneg_source {m K : ℕ} (hm : 2 ≤ m)
    (hmk : m < K) : 0 ≤ recordingZeta m K := by
  have hKone : (1 : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast (show 1 ≤ K by omega)
  have hbase : 0 ≤ 1 - (1 : ℝ) / (K : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_one (by positivity)).2 hKone
  unfold recordingZeta
  exact pow_nonneg hbase _

theorem recordingZeta_eq_sparseMaskProbability (m K : ℕ) :
    recordingZeta m K = SparseCalendarReplay.sparseMaskProbability K (m - 1) := rfl

/-- The four raw gate scalars, in source order: slot, recorder source, own
pilot, and thin. -/
def gateScalarLabel {m K : ℕ} (i : Fin m) : Fin 4 → Label m K
  | 0 => Label.slot
  | 1 => Label.rec
  | 2 => Label.pilot i
  | 3 => Label.thin

/-- The combined label vector of the nonowner pilot inputs and the four gate
inputs. Its two summands have disjoint labels in the actual slice. -/
def recordingScalarLabel {m K : ℕ} (hm : 2 ≤ m) (i : Fin m) :
    Fin (followerCount m) ⊕ Fin 4 → Label m K
  | .inl r => Label.pilot (otherPlayerAt hm i r)
  | .inr r => gateScalarLabel i r

theorem pilotLabel_injective {m K : ℕ} {r s : Fin m}
    (h : Label.pilot (m := m) (K := K) r = Label.pilot (m := m) (K := K) s) : r = s :=
  Sum.inl_injective (Sum.inr_injective (Sum.inr_injective h))

theorem gateScalarLabel_injective {m K : ℕ} (i : Fin m) :
    Function.Injective (gateScalarLabel (m := m) (K := K) i) := by
  intro r s h
  fin_cases r <;> fin_cases s <;>
    simp [gateScalarLabel, Label.slot, Label.rec, Label.pilot, Label.thin] at h ⊢

theorem recordingScalarLabel_injective {m K : ℕ} (hm : 2 ≤ m) (i : Fin m) :
    Function.Injective (recordingScalarLabel (K := K) hm i) := by
  intro a b h
  cases a with
  | inl r =>
    cases b with
    | inl s =>
      exact congrArg Sum.inl
        (otherPlayerAt_injective hm i (pilotLabel_injective h))
    | inr s =>
      fin_cases s
      · simp [recordingScalarLabel, gateScalarLabel, Label.slot,
          Label.rec, Label.pilot, Label.thin] at h
      · simp [recordingScalarLabel, gateScalarLabel, Label.slot,
          Label.rec, Label.pilot, Label.thin] at h
      · have hp : otherPlayerAt hm i r = i :=
          pilotLabel_injective (by simpa [recordingScalarLabel, gateScalarLabel] using h)
        exact False.elim ((otherPlayerAt_ne hm i r) hp)
      · simp [recordingScalarLabel, gateScalarLabel, Label.slot,
          Label.rec, Label.pilot, Label.thin] at h
  | inr r =>
    cases b with
    | inl s =>
      fin_cases r
      · simp [recordingScalarLabel, gateScalarLabel, Label.slot,
          Label.rec, Label.pilot, Label.thin] at h
      · simp [recordingScalarLabel, gateScalarLabel, Label.slot,
          Label.rec, Label.pilot, Label.thin] at h
      · have hp : i = otherPlayerAt hm i s :=
          pilotLabel_injective (by simpa [recordingScalarLabel, gateScalarLabel] using h)
        exact False.elim ((otherPlayerAt_ne hm i s) hp.symm)
      · simp [recordingScalarLabel, gateScalarLabel, Label.slot,
          Label.rec, Label.pilot, Label.thin] at h
    | inr s =>
      exact congrArg Sum.inr (gateScalarLabel_injective i (by
        simpa [recordingScalarLabel] using h))

/-- The vector of the selected nonowner pilot scalar coordinates. -/
def nonownerPilotScalars {m K : ℕ} (hm : 2 ≤ m) (i : Fin m)
    (x : Slice m K) : Fin (followerCount m) → Scalar :=
  fun r => coordinate (Label.pilot (otherPlayerAt hm i r)) x

/-- The actual four gate scalar coordinates in the continuous slice. -/
def gateScalars {m K : ℕ} (i : Fin m) (x : Slice m K) : Fin 4 → Scalar :=
  fun r => coordinate (gateScalarLabel i r) x

/-- Joint independence of the nonowner pilot scalar vector and the grouped
slot/source/own-pilot/thin vector, obtained by grouping disjoint coordinates
of the accepted slice product law. -/
theorem indepFun_nonownerPilotScalars_gateScalars {m K : ℕ}
    (hm : 2 ≤ m) (hmk : m < K) (i : Fin m) :
    IndepFun (nonownerPilotScalars hm i) (gateScalars i)
      (sliceLaw m K) := by
  let leftSet : Set (Fin (followerCount m) ⊕ Fin 4) := Set.range Sum.inl
  let rightSet : Set (Fin (followerCount m) ⊕ Fin 4) := Set.range Sum.inr
  let leftBlockOf : ((q : leftSet) → Scalar) → Fin (followerCount m) → Scalar :=
    fun z r => z ⟨Sum.inl r, ⟨r, rfl⟩⟩
  let rightBlockOf : ((q : rightSet) → Scalar) → Fin 4 → Scalar :=
    fun z r => z ⟨Sum.inr r, ⟨r, rfl⟩⟩
  have hcoords := (iIndepFun_coordinate m K).precomp
    (recordingScalarLabel_injective hm i)
  have hblocks := hcoords.indepFun_set leftSet rightSet (by
    rw [Set.disjoint_left]
    intro q hq hr
    rcases hq with ⟨r, rfl⟩
    rcases hr with ⟨s, hs⟩
    cases hs)
    (fun q => measurable_coordinate (recordingScalarLabel hm i q))
  have hleft : Measurable leftBlockOf := by
    apply measurable_pi_iff.mpr
    intro r
    let q : leftSet := ⟨Sum.inl r, ⟨r, rfl⟩⟩
    exact measurable_pi_apply q
  have hright : Measurable rightBlockOf := by
    apply measurable_pi_iff.mpr
    intro r
    let q : rightSet := ⟨Sum.inr r, ⟨r, rfl⟩⟩
    exact measurable_pi_apply q
  have hcomp := hblocks.comp hleft hright
  have hleftEq :
      (fun x : Slice m K =>
        leftBlockOf (fun q => coordinate (recordingScalarLabel hm i q.val) x)) =
        nonownerPilotScalars (K := K) hm i := by
    funext x r
    rfl
  have hrightEq :
      (fun x : Slice m K =>
        rightBlockOf (fun q => coordinate (recordingScalarLabel hm i q.val) x)) =
        gateScalars (K := K) i := by
    funext x r
    rfl
  change IndepFun
    (fun x : Slice m K =>
      leftBlockOf (fun q => coordinate (recordingScalarLabel hm i q.val) x))
    (fun x : Slice m K =>
      rightBlockOf (fun q => coordinate (recordingScalarLabel hm i q.val) x))
    (sliceLaw m K) at hcomp
  rw [hleftEq, hrightEq] at hcomp
  exact hcomp

theorem iIndepFun_nonownerPilotScalars {m K : ℕ} (hm : 2 ≤ m)
    (i : Fin m) :
    iIndepFun (fun r x => nonownerPilotScalars hm i x r) (sliceLaw m K) := by
  have h := (iIndepFun_coordinate m K).precomp
    (g := fun r : Fin (followerCount m) => Label.pilot (otherPlayerAt hm i r)) (by
      intro r s hrs
      exact otherPlayerAt_injective hm i (pilotLabel_injective hrs))
  simpa [nonownerPilotScalars] using h

theorem iIndepFun_gateScalars {m K : ℕ} (i : Fin m) :
    iIndepFun (fun r x => gateScalars i x r) (sliceLaw m K) := by
  have h := (iIndepFun_coordinate m K).precomp
    (g := gateScalarLabel i) (gateScalarLabel_injective i)
  simpa [gateScalars] using h

theorem measurable_gateScalars {m K : ℕ} (i : Fin m) :
    Measurable (gateScalars i : Slice m K → Fin 4 → Scalar) := by
  apply measurable_pi_iff.mpr
  intro r
  exact measurable_coordinate (gateScalarLabel i r)

/-- The pilot-mask condition as a measurable subset of the nonowner scalar
vector. -/
def nonownerMaskSet {m K : ℕ} (hK : 0 < K) (j : Fin K) :
    Set (Fin (followerCount m) → Scalar) :=
  Set.univ.pi (fun _ => {v | pilotFromScalar K hK v ≠ j})

/-- Scalar-level slot draw using the accepted inverse-cumulative map. -/
def slotFromScalar (v : Scalar) : Slot :=
  ContinuousCategorical.sample (by decide) slotMass slotMass_sum v

/-- Scalar-level recorder-source draw using the accepted inverse-cumulative
map. -/
def recorderSourceFromScalar {m : ℕ} (hm : 2 ≤ m) (v : Scalar) : Fin m :=
  ContinuousCategorical.sample (by omega) (recorderMass m)
    (recorderMass_sum hm) v

theorem measurable_pilotFromScalar {K : ℕ} (hK : 0 < K) :
    Measurable (pilotFromScalar K hK : Scalar → Fin K) := by
  have heq : pilotFromScalar K hK = equalArmSample K hK := by
    funext v
    exact pilot_eq_equalArmSample hK v
  rw [heq]
  exact ContinuousCategorical.measurable_sample hK
    (equalMass_nonneg K) (equalMass_sum K hK)

@[simp] theorem slotFromScalar_coordinate {m K : ℕ} (x : Slice m K) :
    slotFromScalar (coordinate Label.slot x) = slotDraw x := rfl

@[simp] theorem recorderSourceFromScalar_coordinate {m K : ℕ}
    (hm : 2 ≤ m) (hmk : m < K) (x : Slice m K) :
    recorderSourceFromScalar hm (coordinate Label.rec x) =
      recorderSourceDraw hm hmk x := rfl

theorem pilotFromScalar_coordinate {m K : ℕ} (hK : 0 < K)
    (i : Fin m) (x : Slice m K) :
    pilotFromScalar K hK (coordinate (Label.pilot i) x) = pilotDraw hK i x := rfl

theorem measurableSet_nonownerMaskSet {m K : ℕ} (hK : 0 < K) (j : Fin K) :
    MeasurableSet (nonownerMaskSet (m := m) hK j) := by
  apply MeasurableSet.univ_pi
  intro r
  exact (measurableSet_singleton j).compl.preimage
    (measurable_pilotFromScalar hK)

/-- The literal pilot recording gate on the accepted slice. -/
def pilotRecordingGate {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K)
    (hK : 0 < K) (i : Fin m) (j : Fin K) (a : ℝ) (x : Slice m K) : Prop :=
  slotDraw x = dataSlot ∧ recorderSourceDraw hm hmk x = i ∧
    pilotDraw hK i x = j ∧ recordingMask hK i j x ∧
    (coordinate Label.thin x).val ≤ a

/-- The deterministic-owned-action gate omits the owner's own-pilot test. -/
def deterministicOwnedRecordingGate {m K : ℕ} (hm : 2 ≤ m)
    (hmk : m < K) (hK : 0 < K) (i : Fin m) (j : Fin K) (a : ℝ)
    (x : Slice m K) : Prop :=
  slotDraw x = dataSlot ∧ recorderSourceDraw hm hmk x = i ∧
    recordingMask hK i j x ∧ (coordinate Label.thin x).val ≤ a

theorem measurableSet_thinScalarLe (a : ℝ) :
    MeasurableSet {v : Scalar | v.val ≤ a} :=
  measurableSet_Iic.preimage measurable_subtype_coe

/-- The inclusive threshold has probability `a`, including at both endpoints
of the source range. -/
theorem scalarLaw_measure_thinLe {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    scalarLaw {v : Scalar | v.val ≤ a} = ENNReal.ofReal a := by
  rw [scalarLaw_apply]
  rcases eq_or_lt_of_le ha1 with rfl | ha_lt
  · have hs : Subtype.val '' {v : Scalar | v.val ≤ 1} = Set.Ico 0 1 := by
      ext y
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_Ico]
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact v.property
      · intro hy
        exact ⟨⟨y, hy⟩, by simp [hy.2.le], rfl⟩
    rw [hs, Real.volume_Ico]
    simp
  · have hs : Subtype.val '' {v : Scalar | v.val ≤ a} = Set.Icc 0 a := by
      ext y
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v.property.1, hv⟩
      · rintro ⟨hy0, hya⟩
        refine ⟨⟨y, hy0, lt_of_le_of_lt hya ha_lt⟩, hya, rfl⟩
    rw [hs, Real.volume_Icc]
    simp [ha0]

theorem gateThinMeasure {m K : ℕ} {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (sliceLaw m K) {x | (coordinate Label.thin x).val ≤ a} = ENNReal.ofReal a := by
  have hset : {x : Slice m K | (coordinate (Label.thin (m := m) (K := K)) x).val ≤ a} =
      (coordinate (Label.thin (m := m) (K := K))) ⁻¹' {v : Scalar | v.val ≤ a} := rfl
  rw [hset, ← Measure.map_apply
    (measurable_coordinate (Label.thin (m := m) (K := K)))
    (measurableSet_thinScalarLe a), map_coordinate]
  exact scalarLaw_measure_thinLe ha0 ha1

/-- Each nonowner pilot avoids a fixed arm with probability `1 - 1/K` on the
actual continuous scalar law. -/
theorem scalarLaw_pilotAvoid {K : ℕ} (hK : 0 < K) (j : Fin K) :
    ContinuousCategorical.uniform
      {v | pilotFromScalar K hK v ≠ j} =
        ENNReal.ofReal (1 - (1 : ℝ) / (K : ℝ)) := by
  have hsample := ContinuousCategorical.uniform_sample_singleton hK
    (equalMass_nonneg K) (equalMass_sum K hK) j
  have hsample' : ContinuousCategorical.uniform
      (pilotFromScalar K hK ⁻¹' {j}) =
        ENNReal.ofReal (equalMass K j) := by
    have heq : pilotFromScalar K hK = equalArmSample K hK := by
      funext v
      exact pilot_eq_equalArmSample hK v
    rw [heq]
    change ContinuousCategorical.uniform
      (ContinuousCategorical.sample hK (equalMass K)
        (equalMass_sum K hK) ⁻¹' {j}) = _
    exact hsample
  have hpreimage : pilotFromScalar K hK ⁻¹' ({j}ᶜ) =
      (pilotFromScalar K hK ⁻¹' {j})ᶜ := Set.preimage_compl
  have hset : {v : Scalar | pilotFromScalar K hK v ≠ j} =
      pilotFromScalar K hK ⁻¹' ({j}ᶜ) := by
    ext v
    simp
  rw [hset, hpreimage,
    measure_compl ((measurableSet_singleton j).preimage (measurable_pilotFromScalar hK))
      (measure_ne_top _ _),
    ContinuousCategorical.uniform_univ, hsample']
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_sub]
  · simp [equalMass]
  · exact div_nonneg (by norm_num) (Nat.cast_nonneg K)

theorem map_nonownerPilotScalars {m K : ℕ} (hm : 2 ≤ m)
    (i : Fin m) :
    (sliceLaw m K).map (nonownerPilotScalars hm i) =
      Measure.pi (fun _ : Fin (followerCount m) => scalarLaw) := by
  have h := iIndepFun.map_fun_eq_pi_map
    (f := fun r x => coordinate (Label.pilot (otherPlayerAt hm i r)) x)
    (μ := sliceLaw m K)
    (fun r => (measurable_coordinate
      (Label.pilot (otherPlayerAt hm i r))).aemeasurable)
    (iIndepFun_nonownerPilotScalars hm i)
  change (sliceLaw m K).map (nonownerPilotScalars (K := K) hm i) =
    Measure.pi (fun r : Fin (followerCount m) =>
      (sliceLaw m K).map (fun x => coordinate
        (Label.pilot (otherPlayerAt hm i r)) x)) at h
  simpa only [map_coordinate, scalarLaw] using h

theorem recordingMask_iff_nonownerScalars {m K : ℕ} (hm : 2 ≤ m)
    (hK : 0 < K) (i : Fin m) (j : Fin K) (x : Slice m K) :
    recordingMask hK i j x ↔
      ∀ r : Fin (followerCount m),
        pilotFromScalar K hK (nonownerPilotScalars hm i x r) ≠ j := by
  constructor
  · intro h r
    simpa [nonownerPilotScalars, pilotDraw] using
      h (otherPlayerAt hm i r) (otherPlayerAt_ne hm i r)
  · intro h ell hne
    obtain ⟨r, hr⟩ := otherPlayerAt_surjective hm i ⟨ell, hne⟩
    have := h r
    simpa [nonownerPilotScalars, pilotDraw, hr] using this

theorem recordingMask_event_eq {m K : ℕ} (hm : 2 ≤ m) (hK : 0 < K)
    (i : Fin m) (j : Fin K) :
    {x : Slice m K | recordingMask hK i j x} =
      (nonownerPilotScalars (K := K) hm i) ⁻¹' nonownerMaskSet hK j := by
  ext x
  simp [nonownerMaskSet,
    recordingMask_iff_nonownerScalars hm hK i j x]

theorem measurable_nonownerPilotScalars {m K : ℕ} (hm : 2 ≤ m)
    (i : Fin m) : Measurable (nonownerPilotScalars (K := K) hm i) := by
  apply measurable_pi_iff.mpr
  intro r
  exact measurable_coordinate (Label.pilot (otherPlayerAt hm i r))

theorem measurableSet_recordingMask {m K : ℕ} (hm : 2 ≤ m)
    (hK : 0 < K) (i : Fin m) (j : Fin K) :
    MeasurableSet {x : Slice m K | recordingMask hK i j x} := by
  rw [recordingMask_event_eq hm hK i j]
  exact (measurableSet_nonownerMaskSet hK j).preimage
    (measurable_nonownerPilotScalars hm i)

theorem recordingMask_probability {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K)
    (hK : 0 < K) (i : Fin m) (j : Fin K) :
    (sliceLaw m K) {x | recordingMask hK i j x} =
      ENNReal.ofReal (recordingZeta m K) := by
  let M := nonownerMaskSet (m := m) hK j
  have hmeas := measurableSet_nonownerMaskSet (m := m) hK j
  have hmap := map_nonownerPilotScalars (K := K) hm i
  have hmeasMap : Measurable (nonownerPilotScalars (K := K) hm i :
      Slice m K → Fin (followerCount m) → Scalar) := by
    apply measurable_pi_iff.mpr
    intro r
    exact measurable_coordinate _
  have hprob :
      (sliceLaw m K) ((nonownerPilotScalars (K := K) hm i) ⁻¹' M) =
        (Measure.pi (fun _ : Fin (followerCount m) => scalarLaw)) M := by
    calc
      (sliceLaw m K) ((nonownerPilotScalars (K := K) hm i) ⁻¹' M) =
          (sliceLaw m K).map (nonownerPilotScalars (K := K) hm i) M :=
        (Measure.map_apply hmeasMap hmeas).symm
      _ = _ := by rw [hmap]
  have hset :
      M = Set.univ.pi (fun _ : Fin (followerCount m) =>
        {v : Scalar | pilotFromScalar K hK v ≠ j}) := rfl
  have hevent : {x | recordingMask hK i j x} =
      (nonownerPilotScalars (K := K) hm i) ⁻¹' M := by
    simpa [M] using recordingMask_event_eq hm hK i j
  rw [hevent, hprob, hset, Measure.pi_pi]
  have hAvoid : scalarLaw {v : Scalar | pilotFromScalar K hK v ≠ j} =
      ENNReal.ofReal (1 - (1 : ℝ) / (K : ℝ)) := by
    simpa only [_root_.Bandits.Support.PublicDiscreteDraws.ContinuousControlSlice.scalarLaw_eq_categorical_uniform]
      using scalarLaw_pilotAvoid hK j
  have hbase : 0 ≤ 1 - (1 : ℝ) / (K : ℝ) := by
    have hKone : (1 : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast (show 1 ≤ K by omega)
    exact sub_nonneg.mpr ((div_le_one (by positivity)).2 hKone)
  calc
    (∏ r : Fin (followerCount m),
        scalarLaw {v : Scalar | pilotFromScalar K hK v ≠ j}) =
        ENNReal.ofReal (1 - (1 : ℝ) / (K : ℝ)) ^ followerCount m := by
      simp [hAvoid]
    _ = ENNReal.ofReal ((1 - (1 : ℝ) / (K : ℝ)) ^ (m - 1)) := by
      rw [← ENNReal.ofReal_pow hbase]
      simp [followerCount]
    _ = ENNReal.ofReal (recordingZeta m K) := by
      simp [recordingZeta]

/-- The gate-coordinate marginal laws, obtained from the inverse-cumulative
draws and the inclusive scalar interval. -/
def pilotGateScalarFactorSet {m K : ℕ} (hm : 2 ≤ m) (hK : 0 < K)
    (i : Fin m) (j : Fin K) (a : ℝ) : Fin 4 → Set Scalar
  | 0 => slotFromScalar ⁻¹' {dataSlot}
  | 1 => recorderSourceFromScalar hm ⁻¹' {i}
  | 2 => pilotFromScalar K hK ⁻¹' {j}
  | 3 => {v | v.val ≤ a}

def deterministicGateScalarFactorSet {m : ℕ} (hm : 2 ≤ m)
    (i : Fin m) (a : ℝ) : Fin 4 → Set Scalar
  | 0 => slotFromScalar ⁻¹' {dataSlot}
  | 1 => recorderSourceFromScalar hm ⁻¹' {i}
  | 2 => Set.univ
  | 3 => {v | v.val ≤ a}

theorem gateScalarFactors_probability {m K : ℕ} (hm : 2 ≤ m)
    (hK : 0 < K) (i : Fin m) (j : Fin K) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∏ r : Fin 4, scalarLaw (pilotGateScalarFactorSet hm hK i j a r)) =
        ENNReal.ofReal ((1 / 2) * recorderMass m i *
          (1 / (K : ℝ)) * a) := by
  have hslot : scalarLaw (slotFromScalar ⁻¹' {dataSlot}) =
      ENNReal.ofReal (1 / 2) := by
    change ContinuousCategorical.uniform
      (ContinuousCategorical.sample (by decide) slotMass slotMass_sum ⁻¹'
        {dataSlot}) = _
    rw [ContinuousCategorical.uniform_sample_singleton (by decide)
      slotMass_nonneg slotMass_sum dataSlot, slotMass_data]
  have hsource : scalarLaw (recorderSourceFromScalar hm ⁻¹' {i}) =
      ENNReal.ofReal (recorderMass m i) := by
    change ContinuousCategorical.uniform
      (ContinuousCategorical.sample (by omega) (recorderMass m)
        (recorderMass_sum hm) ⁻¹' {i}) = _
    exact ContinuousCategorical.uniform_sample_singleton (by omega)
      recorderMass_nonneg (recorderMass_sum hm) i
  have hpilot : scalarLaw (pilotFromScalar K hK ⁻¹' {j}) =
      ENNReal.ofReal (1 / (K : ℝ)) := by
    change ContinuousCategorical.uniform (pilotFromScalar K hK ⁻¹' {j}) = _
    have heq : pilotFromScalar K hK = equalArmSample K hK := by
      funext v
      exact pilot_eq_equalArmSample hK v
    rw [heq]
    change ContinuousCategorical.uniform
      (ContinuousCategorical.sample hK (equalMass K)
        (equalMass_sum K hK) ⁻¹' {j}) = _
    rw [ContinuousCategorical.uniform_sample_singleton hK
      (equalMass_nonneg K) (equalMass_sum K hK) j]
    simp [equalMass]
  have hthin := scalarLaw_measure_thinLe ha0 ha1
  rw [Fin.prod_univ_four]
  simp only [pilotGateScalarFactorSet, hslot, hsource, hpilot, hthin]
  have hmass0 : 0 ≤ recorderMass m i := recorderMass_nonneg i
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hmass0),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) hmass0)
      (by positivity))]

theorem deterministicGateScalarFactors_probability {m K : ℕ}
    (hm : 2 ≤ m) (i : Fin m) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∏ r : Fin 4, scalarLaw (deterministicGateScalarFactorSet hm i a r)) =
        ENNReal.ofReal ((1 / 2) * recorderMass m i * a) := by
  have hslot : scalarLaw (slotFromScalar ⁻¹' {dataSlot}) =
      ENNReal.ofReal (1 / 2) := by
    change ContinuousCategorical.uniform
      (ContinuousCategorical.sample (by decide) slotMass slotMass_sum ⁻¹'
        {dataSlot}) = _
    rw [ContinuousCategorical.uniform_sample_singleton (by decide)
      slotMass_nonneg slotMass_sum dataSlot, slotMass_data]
  have hsource : scalarLaw (recorderSourceFromScalar hm ⁻¹' {i}) =
      ENNReal.ofReal (recorderMass m i) := by
    change ContinuousCategorical.uniform
      (ContinuousCategorical.sample (by omega) (recorderMass m)
        (recorderMass_sum hm) ⁻¹' {i}) = _
    exact ContinuousCategorical.uniform_sample_singleton (by omega)
      recorderMass_nonneg (recorderMass_sum hm) i
  have hthin := scalarLaw_measure_thinLe ha0 ha1
  rw [Fin.prod_univ_four]
  simp only [deterministicGateScalarFactorSet, hslot, hsource, hthin,
    MeasureTheory.measure_univ]
  have hmass0 : 0 ≤ recorderMass m i := recorderMass_nonneg i
  simp only [mul_one]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hmass0)]

theorem gateScalarFactorMeasure {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K)
    (hK : 0 < K) (i : Fin m) (j : Fin K) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∏ r : Fin 4, scalarLaw (pilotGateScalarFactorSet hm hK i j a r)) =
        ENNReal.ofReal ((1 / 2) * recorderMass m i *
          (1 / (K : ℝ)) * a) := by
  exact gateScalarFactors_probability hm hK i j a ha0 ha1

theorem deterministicGateScalarFactorMeasure {m K : ℕ} (hm : 2 ≤ m)
    (hmk : m < K) (hK : 0 < K) (i : Fin m) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∏ r : Fin 4, scalarLaw (deterministicGateScalarFactorSet hm i a r)) =
        ENNReal.ofReal ((1 / 2) * recorderMass m i * a) := by
  exact deterministicGateScalarFactors_probability (K := K) hm i a ha0 ha1

theorem measurableSet_pilotGateScalarFactors {m K : ℕ} (hm : 2 ≤ m)
    (hK : 0 < K) (i : Fin m) (j : Fin K) (a : ℝ) :
    ∀ r : Fin 4, MeasurableSet (pilotGateScalarFactorSet hm hK i j a r) := by
  intro r
  fin_cases r
  · exact (measurableSet_singleton dataSlot).preimage
      (ContinuousCategorical.measurable_sample (by decide)
        slotMass_nonneg slotMass_sum)
  · exact (measurableSet_singleton i).preimage
      (ContinuousCategorical.measurable_sample (by omega)
        recorderMass_nonneg (recorderMass_sum hm))
  · exact (measurableSet_singleton j).preimage
      (measurable_pilotFromScalar hK)
  · exact measurableSet_thinScalarLe a

theorem measurableSet_deterministicGateScalarFactors {m : ℕ}
    (hm : 2 ≤ m) (i : Fin m) (a : ℝ) :
    ∀ r : Fin 4, MeasurableSet (deterministicGateScalarFactorSet hm i a r) := by
  intro r
  fin_cases r
  · exact (measurableSet_singleton dataSlot).preimage
      (ContinuousCategorical.measurable_sample (by decide)
        slotMass_nonneg slotMass_sum)
  · exact (measurableSet_singleton i).preimage
      (ContinuousCategorical.measurable_sample (by omega)
        recorderMass_nonneg (recorderMass_sum hm))
  · exact MeasurableSet.univ
  · exact measurableSet_thinScalarLe a

theorem measurableSet_nonownerMaskFactors {m K : ℕ} (hK : 0 < K)
    (j : Fin K) :
    ∀ r : Fin m, MeasurableSet {v : Scalar | pilotFromScalar K hK v ≠ j} := by
  intro r
  exact (measurableSet_singleton j).compl.preimage
    (measurable_pilotFromScalar hK)

theorem map_gateScalars {m K : ℕ} (i : Fin m) :
    (sliceLaw m K).map (gateScalars (K := K) i) =
      Measure.pi (fun _ : Fin 4 => scalarLaw) := by
  have h := iIndepFun.map_fun_eq_pi_map
    (f := fun r x => coordinate (gateScalarLabel (K := K) i r) x)
    (μ := sliceLaw m K)
    (fun r => (measurable_coordinate (gateScalarLabel (K := K) i r)).aemeasurable)
    (iIndepFun_gateScalars i)
  change (sliceLaw m K).map (gateScalars (K := K) i) =
    Measure.pi (fun r : Fin 4 =>
      (sliceLaw m K).map (fun x => coordinate (gateScalarLabel (K := K) i r) x)) at h
  simpa only [map_coordinate, scalarLaw] using h

theorem measurableSet_gateScalarFactors {m K : ℕ} (hm : 2 ≤ m)
    (hK : 0 < K) (i : Fin m) (j : Fin K) (a : ℝ) :
    MeasurableSet (Set.univ.pi (pilotGateScalarFactorSet hm hK i j a)) :=
  MeasurableSet.univ_pi (measurableSet_pilotGateScalarFactors hm hK i j a)

theorem measurableSet_deterministicGateScalarFactorsPi {m : ℕ}
    (hm : 2 ≤ m) (i : Fin m) (a : ℝ) :
    MeasurableSet (Set.univ.pi (deterministicGateScalarFactorSet hm i a)) :=
  MeasurableSet.univ_pi (measurableSet_deterministicGateScalarFactors hm i a)

theorem gateScalars_pilotFactors_probability {m K : ℕ} (hm : 2 ≤ m)
    (hmk : m < K) (hK : 0 < K) (i : Fin m) (j : Fin K) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (sliceLaw m K) (gateScalars i ⁻¹'
      Set.univ.pi (pilotGateScalarFactorSet hm hK i j a)) =
        ENNReal.ofReal ((1 / 2) * recorderMass m i *
          (1 / (K : ℝ)) * a) := by
  rw [← Measure.map_apply (measurable_gateScalars i)
    (measurableSet_gateScalarFactors hm hK i j a), map_gateScalars]
  rw [Measure.pi_pi]
  exact gateScalarFactorMeasure hm hmk hK i j a ha0 ha1

theorem gateScalars_deterministicFactors_probability {m K : ℕ}
    (hm : 2 ≤ m) (hmk : m < K) (hK : 0 < K) (i : Fin m) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (sliceLaw m K) (gateScalars i ⁻¹'
      Set.univ.pi (deterministicGateScalarFactorSet hm i a)) =
        ENNReal.ofReal ((1 / 2) * recorderMass m i * a) := by
  rw [← Measure.map_apply (measurable_gateScalars i)
    (measurableSet_deterministicGateScalarFactorsPi hm i a), map_gateScalars]
  rw [Measure.pi_pi]
  exact deterministicGateScalarFactorMeasure hm hmk hK i a ha0 ha1

/-- The DATA, source, own-pilot and inclusive-thin tests as a measurable set
of the actual four gate scalars. -/
def pilotGateScalarSet {m K : ℕ} (hm : 2 ≤ m) (hK : 0 < K)
    (i : Fin m) (j : Fin K) (a : ℝ) : Set (Fin 4 → Scalar) :=
  Set.univ.pi (pilotGateScalarFactorSet hm hK i j a)

/-- The deterministic-owned-action tests leave the own-pilot coordinate
unconstrained. -/
def deterministicGateScalarSet {m : ℕ} (hm : 2 ≤ m) (i : Fin m)
    (a : ℝ) : Set (Fin 4 → Scalar) :=
  Set.univ.pi (deterministicGateScalarFactorSet hm i a)

theorem pilotGateScalarSet_mem_iff {m K : ℕ} (hm : 2 ≤ m)
    (hmk : m < K) (hK : 0 < K) (i : Fin m) (j : Fin K) (a : ℝ)
    (x : Slice m K) :
    gateScalars i x ∈ pilotGateScalarSet hm hK i j a ↔
      slotDraw x = dataSlot ∧ recorderSourceDraw hm hmk x = i ∧
        pilotDraw hK i x = j ∧ (coordinate Label.thin x).val ≤ a := by
  simp only [pilotGateScalarSet, Set.mem_univ_pi]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [gateScalars, gateScalarLabel, pilotGateScalarFactorSet,
        slotFromScalar_coordinate] using h 0
    · have hs : recorderSourceFromScalar hm (coordinate Label.rec x) = i := by
        simpa [gateScalars, gateScalarLabel, pilotGateScalarFactorSet] using h 1
      rw [← recorderSourceFromScalar_coordinate hm hmk x]
      exact hs
    · simpa [gateScalars, gateScalarLabel, pilotGateScalarFactorSet,
        pilotFromScalar_coordinate] using h 2
    · simpa [gateScalars, gateScalarLabel, pilotGateScalarFactorSet] using h 3
  · rintro ⟨hs, hr, hp, ht⟩ r
    fin_cases r
    · simpa [gateScalars, gateScalarLabel, pilotGateScalarFactorSet,
        slotFromScalar_coordinate] using hs
    · rw [← recorderSourceFromScalar_coordinate hm hmk x] at hr
      simpa [gateScalars, gateScalarLabel, pilotGateScalarFactorSet] using hr
    · simpa [gateScalars, gateScalarLabel, pilotGateScalarFactorSet,
        pilotFromScalar_coordinate] using hp
    · simpa [gateScalars, gateScalarLabel, pilotGateScalarFactorSet] using ht

theorem deterministicGateScalarSet_mem_iff {m K : ℕ} (hm : 2 ≤ m)
    (hmk : m < K) (i : Fin m) (a : ℝ) (x : Slice m K) :
    gateScalars i x ∈ deterministicGateScalarSet hm i a ↔
      slotDraw x = dataSlot ∧ recorderSourceDraw hm hmk x = i ∧
        (coordinate Label.thin x).val ≤ a := by
  simp only [deterministicGateScalarSet, Set.mem_univ_pi]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa [gateScalars, gateScalarLabel, deterministicGateScalarFactorSet,
        slotFromScalar_coordinate] using h 0
    · have hs : recorderSourceFromScalar hm (coordinate Label.rec x) = i := by
        simpa [gateScalars, gateScalarLabel, deterministicGateScalarFactorSet] using h 1
      rw [← recorderSourceFromScalar_coordinate hm hmk x]
      exact hs
    · simpa [gateScalars, gateScalarLabel, deterministicGateScalarFactorSet] using h 3
  · rintro ⟨hs, hr, ht⟩ r
    fin_cases r
    · simpa [gateScalars, gateScalarLabel, deterministicGateScalarFactorSet,
        slotFromScalar_coordinate] using hs
    · rw [← recorderSourceFromScalar_coordinate hm hmk x] at hr
      simpa [gateScalars, gateScalarLabel, deterministicGateScalarFactorSet] using hr
    · simp [gateScalars, gateScalarLabel, deterministicGateScalarFactorSet]
    · simpa [gateScalars, gateScalarLabel, deterministicGateScalarFactorSet] using ht

theorem pilotRecordingGate_event_eq {m K : ℕ} (hm : 2 ≤ m)
    (hmk : m < K) (hK : 0 < K) (i : Fin m) (j : Fin K) (a : ℝ) :
    {x | pilotRecordingGate hm hmk hK i j a x} =
      ((nonownerPilotScalars (K := K) hm i) ⁻¹' nonownerMaskSet hK j) ∩
        ((gateScalars (K := K) i) ⁻¹' pilotGateScalarSet hm hK i j a) := by
  ext x
  change (slotDraw x = dataSlot ∧ recorderSourceDraw hm hmk x = i ∧
      pilotDraw hK i x = j ∧ recordingMask hK i j x ∧
        (coordinate Label.thin x).val ≤ a) ↔
    ((nonownerPilotScalars (K := K) hm i x ∈ nonownerMaskSet hK j) ∧
      gateScalars i x ∈ pilotGateScalarSet hm hK i j a)
  rw [recordingMask_iff_nonownerScalars hm hK i j x,
    pilotGateScalarSet_mem_iff hm hmk hK i j a x]
  simp [nonownerMaskSet, and_assoc, and_left_comm, and_comm]

theorem deterministicOwnedRecordingGate_event_eq {m K : ℕ}
    (hm : 2 ≤ m) (hmk : m < K) (hK : 0 < K) (i : Fin m)
    (j : Fin K) (a : ℝ) :
    {x | deterministicOwnedRecordingGate hm hmk hK i j a x} =
      ((nonownerPilotScalars (K := K) hm i) ⁻¹' nonownerMaskSet hK j) ∩
        ((gateScalars (K := K) i) ⁻¹' deterministicGateScalarSet hm i a) := by
  ext x
  change (slotDraw x = dataSlot ∧ recorderSourceDraw hm hmk x = i ∧
      recordingMask hK i j x ∧ (coordinate Label.thin x).val ≤ a) ↔
    ((nonownerPilotScalars (K := K) hm i x ∈ nonownerMaskSet hK j) ∧
      gateScalars i x ∈ deterministicGateScalarSet hm i a)
  rw [recordingMask_iff_nonownerScalars hm hK i j x,
    deterministicGateScalarSet_mem_iff hm hmk i a x]
  simp [nonownerMaskSet, and_assoc, and_left_comm, and_comm]

theorem measurableSet_pilotRecordingGate {m K : ℕ} (hm : 2 ≤ m)
    (hmk : m < K) (hK : 0 < K) (i : Fin m) (j : Fin K) (a : ℝ) :
    MeasurableSet {x : Slice m K | pilotRecordingGate hm hmk hK i j a x} := by
  rw [pilotRecordingGate_event_eq hm hmk hK i j a]
  exact ((measurableSet_nonownerMaskSet hK j).preimage
      (measurable_nonownerPilotScalars hm i)).inter
    ((measurableSet_gateScalarFactors hm hK i j a).preimage
      (measurable_gateScalars i))

theorem measurableSet_deterministicOwnedRecordingGate {m K : ℕ}
    (hm : 2 ≤ m) (hmk : m < K) (hK : 0 < K) (i : Fin m)
    (j : Fin K) (a : ℝ) :
    MeasurableSet {x : Slice m K | deterministicOwnedRecordingGate hm hmk hK i j a x} := by
  rw [deterministicOwnedRecordingGate_event_eq hm hmk hK i j a]
  exact ((measurableSet_nonownerMaskSet hK j).preimage
      (measurable_nonownerPilotScalars hm i)).inter
    ((measurableSet_deterministicGateScalarFactorsPi hm i a).preimage
      (measurable_gateScalars i))

/-- The exact source pilot-gate probability, including the boundary tests
`a = 0` and `a = 1`. -/
theorem pilotRecordingGate_probability {m K : ℕ} (hm : 2 ≤ m)
    (hmk : m < K) (hK : 0 < K) (i : Fin m) (j : Fin K) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (sliceLaw m K) {x | pilotRecordingGate hm hmk hK i j a x} =
      ENNReal.ofReal ((1 / 2) * recorderMass m i *
        (1 / (K : ℝ)) * recordingZeta m K * a) := by
  rw [pilotRecordingGate_event_eq hm hmk hK i j a]
  rw [(indepFun_nonownerPilotScalars_gateScalars hm hmk i).measure_inter_preimage_eq_mul
    (nonownerMaskSet hK j) (pilotGateScalarSet hm hK i j a)
    (measurableSet_nonownerMaskSet hK j)
    (measurableSet_gateScalarFactors hm hK i j a)]
  rw [← recordingMask_event_eq hm hK i j,
    recordingMask_probability hm hmk hK i j,
    show pilotGateScalarSet hm hK i j a =
      Set.univ.pi (pilotGateScalarFactorSet hm hK i j a) from rfl,
    gateScalars_pilotFactors_probability hm hmk hK i j a ha0 ha1]
  rw [← ENNReal.ofReal_mul (recordingZeta_nonneg_source hm hmk)]
  congr 1
  ring

/-- The exact deterministic-owned-action gate probability; the owner's pilot
does not occur among its tests. -/
theorem deterministicOwnedRecordingGate_probability {m K : ℕ}
    (hm : 2 ≤ m) (hmk : m < K) (hK : 0 < K) (i : Fin m)
    (j : Fin K) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (sliceLaw m K) {x | deterministicOwnedRecordingGate hm hmk hK i j a x} =
      ENNReal.ofReal ((1 / 2) * recorderMass m i * recordingZeta m K * a) := by
  rw [deterministicOwnedRecordingGate_event_eq hm hmk hK i j a]
  rw [(indepFun_nonownerPilotScalars_gateScalars hm hmk i).measure_inter_preimage_eq_mul
    (nonownerMaskSet hK j) (deterministicGateScalarSet hm i a)
    (measurableSet_nonownerMaskSet hK j)
    (measurableSet_deterministicGateScalarFactorsPi hm i a)]
  rw [← recordingMask_event_eq hm hK i j,
    recordingMask_probability hm hmk hK i j,
    show deterministicGateScalarSet hm i a =
      Set.univ.pi (deterministicGateScalarFactorSet hm i a) from rfl,
    gateScalars_deterministicFactors_probability hm hmk hK i a ha0 ha1]
  rw [← ENNReal.ofReal_mul (recordingZeta_nonneg_source hm hmk)]
  congr 1
  ring

/-- On the source domain `2 ≤ m < K`, the literal mask factor is strictly
larger than one quarter. -/
theorem recordingZeta_gt_quarter {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K) :
    1 / 4 < recordingZeta m K := by
  have hK1 : 1 < K := by omega
  have hKreal : (1 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hmk)
  have hKden : (0 : ℝ) < (K : ℝ) - 1 := by linarith
  have hdK : followerCount m + 1 ≤ K := by
    rw [followerCount_add_one hm]
    exact Nat.le_of_lt hmk
  have hdKreal : (followerCount m : ℝ) + 1 ≤ (K : ℝ) := by
    exact_mod_cast hdK
  have hdpos : (0 : ℝ) < (followerCount m : ℝ) := by
    exact_mod_cast followerCount_pos hm
  let u : ℝ := 1 - 1 / (K : ℝ)
  have hu : 0 < u := by
    dsimp [u]
    have hfrac : (1 : ℝ) / (K : ℝ) < 1 := (div_lt_one hKpos).2 hKreal
    linarith
  have huInvSub : u⁻¹ - 1 = 1 / ((K : ℝ) - 1) := by
    dsimp [u]
    field_simp [ne_of_gt hKpos, ne_of_gt hKden]
    <;> ring
  have hlogInv := Real.log_le_sub_one_of_pos (inv_pos.mpr hu)
  rw [Real.log_inv, huInvSub] at hlogInv
  have hlog : -(1 / ((K : ℝ) - 1)) ≤ Real.log u := by linarith
  have hratio : (followerCount m : ℝ) / ((K : ℝ) - 1) ≤ 1 :=
    (div_le_one hKden).2 (by linarith)
  have hlogmul : -1 ≤ (followerCount m : ℝ) * Real.log u := by
    calc
      -1 ≤ -((followerCount m : ℝ) / ((K : ℝ) - 1)) := by linarith
      _ = (followerCount m : ℝ) * (-(1 / ((K : ℝ) - 1))) := by ring
      _ ≤ (followerCount m : ℝ) * Real.log u :=
        mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
  have hexp : Real.exp (-1) ≤ Real.exp
      ((followerCount m : ℝ) * Real.log u) := Real.exp_le_exp.mpr hlogmul
  have hexpPow : Real.exp ((followerCount m : ℝ) * Real.log u) =
      u ^ followerCount m := by
    rw [Real.exp_nat_mul, Real.exp_log hu]
  have hpow : Real.exp (-1) ≤ u ^ followerCount m := by
    rw [← hexpPow]
    exact hexp
  have hexpLower : (1 / 4 : ℝ) < Real.exp (-1) := by
    calc
      (1 / 4 : ℝ) < 1 / 3 := by norm_num
      _ < 1 / Real.exp 1 :=
        (one_div_lt_one_div (by norm_num) (Real.exp_pos 1)).2 Real.exp_one_lt_three
      _ = Real.exp (-1) := by rw [Real.exp_neg]; simp [one_div]
  have hbase : u ^ followerCount m = recordingZeta m K := by
    simp [u, recordingZeta, followerCount]
  rw [← hbase]
  exact lt_of_lt_of_le hexpLower hpow

/-- Every recorder source has positive mass in the source domain. -/
theorem recorderMass_pos {m : ℕ} (hm : 2 ≤ m) (i : Fin m) :
    0 < recorderMass m i := by
  by_cases hi : i.val = 0
  · simp [recorderMass, hi]
  · have hd : 0 < followerCount m := followerCount_pos hm
    simp only [recorderMass, if_neg hi]
    positivity

/-- Uniform lower bound on the coordinator and follower recorder masses. -/
theorem recorderMass_lower {m : ℕ} (hm : 2 ≤ m) (i : Fin m) :
    1 / (2 * (m : ℝ)) ≤ recorderMass m i := by
  by_cases hi : i.val = 0
  · rw [recorderMass, if_pos hi]
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  · rw [recorderMass, if_neg hi]
    have hdpos : (0 : ℝ) < (followerCount m : ℝ) := by
      exact_mod_cast followerCount_pos hm
    have hdle : (followerCount m : ℝ) ≤ (m : ℝ) := by
      have h := followerCount_add_one hm
      have hR : (followerCount m : ℝ) + 1 = (m : ℝ) := by exact_mod_cast h
      linarith
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith

/-- The raw one-slice probability before thinning for the pilot-owner gate. -/
def pilotRecordingGateRawProbability {m K : ℕ} (i : Fin m) : ℝ :=
  (1 / 2) * recorderMass m i * (1 / (K : ℝ)) * recordingZeta m K

/-- The raw one-slice probability before thinning for a deterministic owned
action. -/
def deterministicOwnedGateRawProbability {m K : ℕ} (i : Fin m) : ℝ :=
  (1 / 2) * recorderMass m i * recordingZeta m K

theorem pilotRecordingGateRawProbability_pos {m K : ℕ} (hm : 2 ≤ m)
    (hmk : m < K) (i : Fin m) :
    0 < pilotRecordingGateRawProbability (K := K) i := by
  have hz := recordingZeta_gt_quarter hm hmk
  have hmpos := recorderMass_pos hm i
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hmk)
  simp only [pilotRecordingGateRawProbability]
  positivity

theorem deterministicOwnedGateRawProbability_pos {m K : ℕ}
    (hm : 2 ≤ m) (hmk : m < K) (i : Fin m) :
    0 < deterministicOwnedGateRawProbability (K := K) i := by
  have hz := recordingZeta_gt_quarter hm hmk
  have hmpos := recorderMass_pos hm i
  simp only [deterministicOwnedGateRawProbability]
  positivity

theorem pilotRecordingGateRawProbability_lower {m K : ℕ}
    (hm : 2 ≤ m) (hmk : m < K) (i : Fin m) :
    1 / (16 * (m : ℝ) * (K : ℝ)) ≤
      pilotRecordingGateRawProbability (K := K) i := by
  have hmass := recorderMass_lower hm i
  have hmass0 := recorderMass_nonneg i
  have hzeta := (recordingZeta_gt_quarter hm hmk).le
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hmk)
  have hmassHalf : (1 / 2) * (1 / (2 * (m : ℝ))) ≤
      (1 / 2) * recorderMass m i :=
    mul_le_mul_of_nonneg_left hmass (by norm_num)
  calc
    1 / (16 * (m : ℝ) * (K : ℝ)) =
        ((1 / 2) * (1 / (2 * (m : ℝ)))) *
          ((1 / (K : ℝ)) * (1 / 4)) := by
          field_simp [ne_of_gt hmpos, ne_of_gt hKpos]
          <;> ring
    _ ≤ ((1 / 2) * recorderMass m i) *
          ((1 / (K : ℝ)) * (1 / 4)) :=
          mul_le_mul_of_nonneg_right hmassHalf (by positivity)
    _ = ((1 / 2) * recorderMass m i * (1 / (K : ℝ))) * (1 / 4) := by ring
    _ ≤ ((1 / 2) * recorderMass m i * (1 / (K : ℝ))) * recordingZeta m K :=
          mul_le_mul_of_nonneg_left hzeta (by positivity)
    _ = pilotRecordingGateRawProbability (K := K) i := by
          simp [pilotRecordingGateRawProbability]

theorem deterministicOwnedGateRawProbability_lower {m K : ℕ}
    (hm : 2 ≤ m) (hmk : m < K) (i : Fin m) :
    1 / (16 * (m : ℝ) * (K : ℝ)) ≤
      deterministicOwnedGateRawProbability (K := K) i := by
  have hmass := recorderMass_lower hm i
  have hmass0 := recorderMass_nonneg i
  have hzeta := (recordingZeta_gt_quarter hm hmk).le
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hmk)
  have hKone : (1 : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast (show 1 ≤ K by omega)
  have hdenLe : 16 * (m : ℝ) ≤ 16 * (m : ℝ) * (K : ℝ) := by
    calc
      16 * (m : ℝ) = (16 * (m : ℝ)) * 1 := by ring
      _ ≤ (16 * (m : ℝ)) * (K : ℝ) :=
        mul_le_mul_of_nonneg_left hKone (by positivity)
  have hmassHalf : (1 / 2) * (1 / (2 * (m : ℝ))) ≤
      (1 / 2) * recorderMass m i :=
    mul_le_mul_of_nonneg_left hmass (by norm_num)
  calc
    1 / (16 * (m : ℝ) * (K : ℝ)) ≤ 1 / (16 * (m : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) hdenLe
    _ = ((1 / 2) * (1 / (2 * (m : ℝ)))) * (1 / 4) := by
      field_simp [ne_of_gt hmpos]
      <;> ring
    _ ≤ ((1 / 2) * recorderMass m i) * (1 / 4) :=
      mul_le_mul_of_nonneg_right hmassHalf (by norm_num)
    _ ≤ (1 / 2) * recorderMass m i * recordingZeta m K :=
      mul_le_mul_of_nonneg_left hzeta (by positivity)
    _ = deterministicOwnedGateRawProbability (K := K) i := by
          simp [deterministicOwnedGateRawProbability]

/-- Coordinator recorder mass specialization of the pilot-owner raw gate. -/
theorem pilotRecordingGateRawProbability_coordinator {m K : ℕ}
    (hm : 2 ≤ m) (hmk : m < K) :
    pilotRecordingGateRawProbability (K := K)
      (⟨0, by omega⟩ : Fin m) =
        (1 / 2) * (1 / 2) * (1 / (K : ℝ)) * recordingZeta m K := by
  simp [pilotRecordingGateRawProbability, recorderMass_coordinator hm]

/-- Follower recorder mass specialization of the pilot-owner raw gate. -/
theorem pilotRecordingGateRawProbability_follower {m K : ℕ}
    (hm : 2 ≤ m) (hmk : m < K) (r : Fin (followerCount m)) :
    pilotRecordingGateRawProbability (K := K) (followerPlayer hm r) =
      (1 / 2) * (1 / (2 * (followerCount m : ℝ))) *
        (1 / (K : ℝ)) * recordingZeta m K := by
  simp [pilotRecordingGateRawProbability, recorderMass_follower hm r]

/-- Coordinator recorder mass specialization of the deterministic-owned gate. -/
theorem deterministicOwnedGateRawProbability_coordinator {m K : ℕ}
    (hm : 2 ≤ m) (hmk : m < K) :
    deterministicOwnedGateRawProbability (K := K)
      (⟨0, by omega⟩ : Fin m) =
        (1 / 2) * (1 / 2) * recordingZeta m K := by
  simp [deterministicOwnedGateRawProbability, recorderMass_coordinator hm]

/-- Follower recorder mass specialization of the deterministic-owned gate. -/
theorem deterministicOwnedGateRawProbability_follower {m K : ℕ}
    (hm : 2 ≤ m) (hmk : m < K) (r : Fin (followerCount m)) :
    deterministicOwnedGateRawProbability (K := K) (followerPlayer hm r) =
      (1 / 2) * (1 / (2 * (followerCount m : ℝ))) * recordingZeta m K := by
  simp [deterministicOwnedGateRawProbability, recorderMass_follower hm r]

/-- Feasible thinning threshold for a pilot-owner raw gate. -/
theorem pilotRecordingGateThreshold_mem_Icc {m K : ℕ} (hm : 2 ≤ m)
    (hmk : m < K) (i : Fin m) {xi : ℝ}
    (hxi0 : 0 ≤ xi)
    (hxi : xi ≤ pilotRecordingGateRawProbability (K := K) i) :
    xi / pilotRecordingGateRawProbability (K := K) i ∈ Set.Icc 0 1 := by
  have hraw := pilotRecordingGateRawProbability_pos hm hmk i
  constructor
  · exact div_nonneg hxi0 hraw.le
  · apply (div_le_iff₀ hraw).2
    simpa using hxi

/-- Feasible thinning threshold for a deterministic-owned raw gate. -/
theorem deterministicOwnedGateThreshold_mem_Icc {m K : ℕ} (hm : 2 ≤ m)
    (hmk : m < K) (i : Fin m) {xi : ℝ}
    (hxi0 : 0 ≤ xi)
    (hxi : xi ≤ deterministicOwnedGateRawProbability (K := K) i) :
    xi / deterministicOwnedGateRawProbability (K := K) i ∈ Set.Icc 0 1 := by
  have hraw := deterministicOwnedGateRawProbability_pos hm hmk i
  constructor
  · exact div_nonneg hxi0 hraw.le
  · apply (div_le_iff₀ hraw).2
    simpa using hxi

/-- Concrete threshold cancellation on the pilot-owner gate. -/
theorem pilotRecordingGate_threshold_probability {m K : ℕ}
    (hm : 2 ≤ m) (hmk : m < K) (hK : 0 < K) (i : Fin m) (j : Fin K)
    {xi : ℝ} (hxi0 : 0 ≤ xi)
    (hxi : xi ≤ pilotRecordingGateRawProbability (K := K) i) :
    (sliceLaw m K) {x | pilotRecordingGate hm hmk hK i j
      (xi / pilotRecordingGateRawProbability (K := K) i) x} =
        ENNReal.ofReal xi := by
  have hthreshold := pilotRecordingGateThreshold_mem_Icc hm hmk i hxi0 hxi
  have hraw := pilotRecordingGateRawProbability_pos hm hmk i
  have hcoeff : ((1 / 2) * recorderMass m i *
      (1 / (K : ℝ)) * recordingZeta m K) ≠ 0 := by
    have h := ne_of_gt hraw
    simpa [pilotRecordingGateRawProbability] using h
  have hKne : (K : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (show 0 < K by omega))
  have hmassne : recorderMass m i ≠ 0 := ne_of_gt (recorderMass_pos hm i)
  have hzetapos : 0 < recordingZeta m K :=
    lt_trans (by norm_num) (recordingZeta_gt_quarter hm hmk)
  have hzetane : recordingZeta m K ≠ 0 := ne_of_gt hzetapos
  rw [pilotRecordingGate_probability hm hmk hK i j _ hthreshold.1 hthreshold.2]
  congr 1
  change (1 / 2) * recorderMass m i * (1 / (K : ℝ)) *
    recordingZeta m K *
      (xi / pilotRecordingGateRawProbability (K := K) i) = xi
  simp only [pilotRecordingGateRawProbability]
  field_simp [hcoeff, hKne, hmassne, hzetane]
  <;> ring

/-- Concrete threshold cancellation on the deterministic-owned gate. -/
theorem deterministicOwnedRecordingGate_threshold_probability {m K : ℕ}
    (hm : 2 ≤ m) (hmk : m < K) (hK : 0 < K) (i : Fin m) (j : Fin K)
    {xi : ℝ} (hxi0 : 0 ≤ xi)
    (hxi : xi ≤ deterministicOwnedGateRawProbability (K := K) i) :
    (sliceLaw m K) {x | deterministicOwnedRecordingGate hm hmk hK i j
      (xi / deterministicOwnedGateRawProbability (K := K) i) x} =
        ENNReal.ofReal xi := by
  have hthreshold := deterministicOwnedGateThreshold_mem_Icc hm hmk i hxi0 hxi
  have hraw := deterministicOwnedGateRawProbability_pos hm hmk i
  have hcoeff : ((1 / 2) * recorderMass m i * recordingZeta m K) ≠ 0 := by
    have h := ne_of_gt hraw
    simpa [deterministicOwnedGateRawProbability] using h
  have hmassne : recorderMass m i ≠ 0 := ne_of_gt (recorderMass_pos hm i)
  have hzetapos : 0 < recordingZeta m K :=
    lt_trans (by norm_num) (recordingZeta_gt_quarter hm hmk)
  have hzetane : recordingZeta m K ≠ 0 := ne_of_gt hzetapos
  rw [deterministicOwnedRecordingGate_probability hm hmk hK i j _
    hthreshold.1 hthreshold.2]
  congr 1
  change (1 / 2) * recorderMass m i * recordingZeta m K *
    (xi / deterministicOwnedGateRawProbability (K := K) i) = xi
  simp only [deterministicOwnedGateRawProbability]
  field_simp [hcoeff, hmassne, hzetane]
  <;> ring

/-- Projection of one accepted public slice into the sparse replay snapshot's
pilot fields. The flags are inert fields required by that snapshot structure;
this is not a protocol sampler. -/
def sparseSliceSnapshot {m K : ℕ} (hm : 2 ≤ m) (hK : 0 < K)
    (i : Fin m) (x : Slice m K) :
    SparseCalendarReplay.SparseCalendarRound K (followerCount m) :=
  { data := false
    selectedSource := false
    unoccupied := false
    active := false
    pilot := pilotDraw hK i x
    otherPlayersPilots := fun r => pilotDraw hK (otherPlayerAt hm i r) x
    observation := ⟨0, by norm_num⟩
    thinScalar := ⟨(coordinate Label.thin x).val,
      (coordinate Label.thin x).property⟩ }

/-- The existing sparse replay mask is exactly the concrete public-slice mask
at the owner's pilot arm. -/
theorem sparseSourceMaskPasses_iff_recordingMask {m K : ℕ}
    (hm : 2 ≤ m) (hK : 0 < K) (i : Fin m) (x : Slice m K) :
    SparseCalendarReplay.sourceMaskPasses (sparseSliceSnapshot hm hK i x) ↔
      recordingMask hK i (pilotDraw hK i x) x := by
  constructor
  · intro h ell hne
    obtain ⟨r, hr⟩ := otherPlayerAt_surjective hm i ⟨ell, hne⟩
    have hr' := h r
    simpa [sparseSliceSnapshot, hr] using hr'
  · intro h r
    exact h (otherPlayerAt hm i r) (otherPlayerAt_ne hm i r)

theorem sparseSourceMaskPasses_pilotGate_iff {m K : ℕ}
    (hm : 2 ≤ m) (hmk : m < K) (hK : 0 < K) (i : Fin m)
    (j : Fin K) (x : Slice m K) (hown : pilotDraw hK i x = j) :
    SparseCalendarReplay.sourceMaskPasses (sparseSliceSnapshot hm hK i x) ↔
      recordingMask hK i j x := by
  rw [sparseSourceMaskPasses_iff_recordingMask hm hK i x, hown]



/-- Canonical recording rates fit below both concrete raw DATA gate masses.
The only inputs are the source learning-rate restriction and positive anchor
weights; rate positivity and the upper bound are obtained from the accepted
canonical rate producer. -/
theorem canonical_recording_rate_raw_gate_bounds
    (p : ConstructorDimensions.Parameters) {eta : ℝ}
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (v : Fin p.K → ℝ) (hvpos : ∀ k, 0 < v k)
    (i : Fin p.m) (j : Fin p.K) :
    0 < CanonicalRecordingRates.xi p eta v j ∧
    CanonicalRecordingRates.xi p eta v j ≤
      1 / (16 * (p.m : ℝ) * (p.K : ℝ)) ∧
    CanonicalRecordingRates.xi p eta v j ≤
      pilotRecordingGateRawProbability (K := p.K) i ∧
    CanonicalRecordingRates.xi p eta v j ≤
      deterministicOwnedGateRawProbability (K := p.K) i := by
  have hxiPos := CanonicalRecordingRates.xi_pos p heta v j
  have hxiBound := CanonicalRecordingRates.xi_le_one_div_16mK
    p heta heta_le v hvpos j
  have hpilotRaw := pilotRecordingGateRawProbability_lower
    p.two_le_m p.m_lt_K i
  have hownedRaw := deterministicOwnedGateRawProbability_lower
    p.two_le_m p.m_lt_K i
  exact ⟨hxiPos, hxiBound, hxiBound.trans hpilotRaw,
    hxiBound.trans hownedRaw⟩

/-- The literal canonical pilot threshold belongs to `[0,1]`; no threshold
feasibility premise is supplied by the caller. -/
theorem canonical_pilotRecordingGateThreshold_mem_Icc
    (p : ConstructorDimensions.Parameters) {eta : ℝ}
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (v : Fin p.K → ℝ) (hvpos : ∀ k, 0 < v k)
    (i : Fin p.m) (j : Fin p.K) :
    CanonicalRecordingRates.xi p eta v j /
      pilotRecordingGateRawProbability (K := p.K) i ∈ Set.Icc 0 1 := by
  rcases canonical_recording_rate_raw_gate_bounds p heta heta_le v hvpos i j with
    ⟨hxiPos, _hxiBound, hraw, _hownedRaw⟩
  exact pilotRecordingGateThreshold_mem_Icc p.two_le_m p.m_lt_K i
    hxiPos.le hraw

/-- The literal canonical deterministic-owner threshold belongs to `[0,1]`;
no threshold feasibility premise is supplied by the caller. -/
theorem canonical_deterministicOwnedGateThreshold_mem_Icc
    (p : ConstructorDimensions.Parameters) {eta : ℝ}
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (v : Fin p.K → ℝ) (hvpos : ∀ k, 0 < v k)
    (i : Fin p.m) (j : Fin p.K) :
    CanonicalRecordingRates.xi p eta v j /
      deterministicOwnedGateRawProbability (K := p.K) i ∈ Set.Icc 0 1 := by
  rcases canonical_recording_rate_raw_gate_bounds p heta heta_le v hvpos i j with
    ⟨hxiPos, _hxiBound, _hpilotRaw, hraw⟩
  exact deterministicOwnedGateThreshold_mem_Icc p.two_le_m p.m_lt_K i
    hxiPos.le hraw

/-- The canonical pilot-owning gate has mass exactly its literal canonical
recording rate under the product law of one public slice. -/
theorem canonical_pilotRecordingGate_mass
    (p : ConstructorDimensions.Parameters) {eta : ℝ}
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (v : Fin p.K → ℝ) (hvpos : ∀ k, 0 < v k)
    (i : Fin p.m) (j : Fin p.K) :
    (sliceLaw p.m p.K)
      {x | pilotRecordingGate p.two_le_m p.m_lt_K
        (ConstructorDimensions.K_pos p) i j
        (CanonicalRecordingRates.xi p eta v j /
          pilotRecordingGateRawProbability (K := p.K) i) x} =
      ENNReal.ofReal (CanonicalRecordingRates.xi p eta v j) := by
  rcases canonical_recording_rate_raw_gate_bounds p heta heta_le v hvpos i j with
    ⟨hxiPos, _hxiBound, hraw, _hownedRaw⟩
  exact pilotRecordingGate_threshold_probability p.two_le_m p.m_lt_K
    (ConstructorDimensions.K_pos p) i j hxiPos.le hraw

/-- The canonical deterministic-owner gate has mass exactly its literal
canonical recording rate under the product law of one public slice. -/
theorem canonical_deterministicOwnedRecordingGate_mass
    (p : ConstructorDimensions.Parameters) {eta : ℝ}
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (v : Fin p.K → ℝ) (hvpos : ∀ k, 0 < v k)
    (i : Fin p.m) (j : Fin p.K) :
    (sliceLaw p.m p.K)
      {x | deterministicOwnedRecordingGate p.two_le_m p.m_lt_K
        (ConstructorDimensions.K_pos p) i j
        (CanonicalRecordingRates.xi p eta v j /
          deterministicOwnedGateRawProbability (K := p.K) i) x} =
      ENNReal.ofReal (CanonicalRecordingRates.xi p eta v j) := by
  rcases canonical_recording_rate_raw_gate_bounds p heta heta_le v hvpos i j with
    ⟨hxiPos, _hxiBound, _hpilotRaw, hraw⟩
  exact deterministicOwnedRecordingGate_threshold_probability
    p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p) i j
    hxiPos.le hraw

/-- For an unoccupied follower, the raw pilot-owning gate is exactly the
saved-record factor `ζ / (4 d K)`, with `d = m - 1`. -/
theorem unoccupiedFollower_rawGate_eq_zeta_div_four_d_K
    {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K)
    (r : Fin (followerCount m)) :
    pilotRecordingGateRawProbability (K := K) (followerPlayer hm r) =
      recordingZeta m K /
        (4 * (followerCount m : ℝ) * (K : ℝ)) := by
  rw [pilotRecordingGateRawProbability_follower hm hmk r]
  have hd : (followerCount m : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (followerCount_pos hm))
  have hK : (K : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.zero_lt_of_lt hmk))
  field_simp [hd, hK]
  ring

/-- The saved-record threshold cancels exactly when written in the manuscript's
`ζ / (4 d K)` form, where `d = m - 1`. -/
theorem canonical_unoccupiedFollower_savedThreshold_literal
    (p : ConstructorDimensions.Parameters) {eta : ℝ}
    (v : Fin p.K → ℝ)
    (j : Fin p.K) :
    CanonicalRecordingRates.xi p eta v j /
        (recordingZeta p.m p.K /
          (4 * (followerCount p.m : ℝ) * (p.K : ℝ))) =
      4 * (followerCount p.m : ℝ) * (p.K : ℝ) *
        CanonicalRecordingRates.xi p eta v j /
          recordingZeta p.m p.K := by
  have hzeta : 0 < recordingZeta p.m p.K :=
    lt_trans (by norm_num) (recordingZeta_gt_quarter p.two_le_m p.m_lt_K)
  have hd : 0 < (followerCount p.m : ℝ) :=
    Nat.cast_pos.mpr (followerCount_pos p.two_le_m)
  have hK : 0 < (p.K : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  field_simp [ne_of_gt hzeta, ne_of_gt hd, ne_of_gt hK]

/-- Exact cancellation for the unoccupied follower's saved threshold. Here
`d = followerCount m = m - 1`, matching the manuscript's notation. -/
theorem unoccupiedFollower_savedThreshold_eq
    (p : ConstructorDimensions.Parameters) {eta : ℝ}
    (v : Fin p.K → ℝ)
    (r : Fin (followerCount p.m)) (j : Fin p.K) :
    CanonicalRecordingRates.xi p eta v j /
        pilotRecordingGateRawProbability (K := p.K)
          (followerPlayer p.two_le_m r) =
      4 * (followerCount p.m : ℝ) * (p.K : ℝ) *
        CanonicalRecordingRates.xi p eta v j /
          recordingZeta p.m p.K := by
  have hgate := unoccupiedFollower_rawGate_eq_zeta_div_four_d_K
    p.two_le_m p.m_lt_K r
  have hzeta : 0 < recordingZeta p.m p.K :=
    lt_trans (by norm_num) (recordingZeta_gt_quarter p.two_le_m p.m_lt_K)
  have hd : 0 < (followerCount p.m : ℝ) :=
    Nat.cast_pos.mpr (followerCount_pos p.two_le_m)
  have hK : 0 < (p.K : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  rw [hgate]
  field_simp [ne_of_gt hzeta, ne_of_gt hd, ne_of_gt hK]

/-- Source-exponent connection by explicit substitution only: the equality
`ξ = 2^-h` is an input, not a separately produced dyadic exponent. -/
theorem unoccupiedFollower_savedThreshold_eq_dyadic
    (p : ConstructorDimensions.Parameters) {eta : ℝ}
    (v : Fin p.K → ℝ)
    (r : Fin (followerCount p.m)) (j : Fin p.K) (h : ℤ)
    (hxi : CanonicalRecordingRates.xi p eta v j =
      (2 : ℝ) ^ (-h)) :
    CanonicalRecordingRates.xi p eta v j /
        pilotRecordingGateRawProbability (K := p.K)
          (followerPlayer p.two_le_m r) =
      4 * (followerCount p.m : ℝ) * (p.K : ℝ) * (2 : ℝ) ^ (-h) /
        recordingZeta p.m p.K := by
  calc
    CanonicalRecordingRates.xi p eta v j /
        pilotRecordingGateRawProbability (K := p.K)
          (followerPlayer p.two_le_m r) =
        4 * (followerCount p.m : ℝ) * (p.K : ℝ) *
          CanonicalRecordingRates.xi p eta v j /
            recordingZeta p.m p.K :=
      unoccupiedFollower_savedThreshold_eq p v r j
    _ = 4 * (followerCount p.m : ℝ) * (p.K : ℝ) * (2 : ℝ) ^ (-h) /
        recordingZeta p.m p.K := by rw [hxi]

end Bandits.Support.CanonicalRecordingSlice

end
