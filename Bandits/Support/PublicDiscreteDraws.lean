/-
Copyright (c) 2026 Bandits Lean preparation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ContinuousControlSlice
public import Bandits.Support.ContinuousCategorical

/-!
# Concrete public draws from one accepted control slice

This module realizes the `slot`, `sel`, `rec`, and player-pilot maps from
`sources/zip4/manuscript/appendix_b_communication.tex:25-44`, and the DATA
recording mask pilots from `sources/zip4/manuscript/05_binary_transport.tex:352-393`.
All maps consume the actual labels of `ContinuousControlSlice.sliceLaw`.
This module does not define a second slice, tuple algorithm, adaptive history,
or physical recording process.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.PublicDiscreteDraws

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace ContinuousControlSlice

/-- The two accepted support modules use the same genuine `[0,1)` subtype. -/
theorem scalarCarrier_eq_categorical :
    ContinuousControlSlice.Scalar = ContinuousCategorical.Scalar := rfl

/-- The slice scalar law is exactly the generic categorical uniform law. -/
theorem scalarLaw_eq_categorical_uniform :
    ContinuousControlSlice.scalarLaw = ContinuousCategorical.uniform := rfl

end ContinuousControlSlice

/-- The ordered slot indices are `0 = DATA`, `1 = DOWN`, and `2 = UP`. -/
abbrev Slot := Fin 3

/-- The DATA slot in the source order. -/
def dataSlot : Slot := 0

/-- The DOWN slot in the source order. -/
def downSlot : Slot := 1

/-- The UP slot in the source order. -/
def upSlot : Slot := 2

/-- The source population of followers, `d = m - 1`. -/
def followerCount (m : ℕ) : ℕ := m - 1

theorem followerCount_pos {m : ℕ} (hm : 2 ≤ m) : 0 < followerCount m := by
  simp only [followerCount]
  omega

theorem followerCount_add_one {m : ℕ} (hm : 2 ≤ m) : followerCount m + 1 = m := by
  simp only [followerCount]
  omega

/-- A follower index `r` denotes source player label `r.val + 1`. -/
def followerPlayer {m : ℕ} (hm : 2 ≤ m) (r : Fin (followerCount m)) : Fin m :=
  ⟨r.val + 1, by have := r.isLt; simp only [followerCount] at this; omega⟩

theorem followerPlayer_val {m : ℕ} (hm : 2 ≤ m) (r : Fin (followerCount m)) :
    (followerPlayer hm r).val = r.val + 1 := rfl

/-- Source slot masses in the fixed order DATA, DOWN, UP. -/
def slotMass (i : Slot) : ℝ :=
  if i.val = 0 then 1 / 2 else 1 / 4

theorem slotMass_data : slotMass dataSlot = 1 / 2 := by
  norm_num [slotMass, dataSlot]

theorem slotMass_down : slotMass downSlot = 1 / 4 := by
  norm_num [slotMass, downSlot]

theorem slotMass_up : slotMass upSlot = 1 / 4 := by
  norm_num [slotMass, upSlot]

theorem slotMass_nonneg (i : Slot) : 0 ≤ slotMass i := by
  simp only [slotMass]
  split <;> positivity

theorem slotMass_sum : ∑ i : Slot, slotMass i = 1 := by
  norm_num [slotMass, Fin.sum_univ_succ]

/-- Equal categorical mass on a nonempty finite arm or follower index. -/
def equalMass (n : ℕ) : Fin n → ℝ := fun _ => 1 / (n : ℝ)

theorem equalMass_nonneg (n : ℕ) (i : Fin n) : 0 ≤ equalMass n i := by
  simp only [equalMass]
  positivity

theorem sum_const_fin_real (n : ℕ) (c : ℝ) :
    (∑ _i : Fin n, c) = (n : ℝ) * c := by
  simp [Finset.sum_const]

theorem equalMass_sum (n : ℕ) (hn : 0 < n) :
    ∑ i : Fin n, equalMass n i = 1 := by
  rw [show (∑ i : Fin n, equalMass n i) = (n : ℝ) * (1 / (n : ℝ)) by
    simp [equalMass]]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  field_simp

/-- Recorder masses on players: coordinator `0` has mass `1/2` and each
follower has mass `1/(2d)`, with `d = m - 1`. -/
def recorderMass (m : ℕ) (i : Fin m) : ℝ :=
  if i.val = 0 then 1 / 2 else 1 / (2 * (followerCount m : ℝ))

theorem recorderMass_nonneg {m : ℕ} (i : Fin m) :
    0 ≤ recorderMass m i := by
  simp only [recorderMass]
  split <;> positivity

theorem recorderMass_coordinator {m : ℕ} (hm : 2 ≤ m) :
    recorderMass m (⟨0, by omega⟩ : Fin m) = 1 / 2 := by
  simp [recorderMass]

theorem recorderMass_follower {m : ℕ} (hm : 2 ≤ m)
    (r : Fin (followerCount m)) :
    recorderMass m (followerPlayer hm r) = 1 / (2 * (followerCount m : ℝ)) := by
  simp [recorderMass, followerPlayer]

theorem recorderMass_sum {m : ℕ} (hm : 2 ≤ m) :
    ∑ i : Fin m, recorderMass m i = 1 := by
  have hdpos := followerCount_pos hm
  have hmd := followerCount_add_one hm
  have hdcast :
      (followerCount (followerCount m + 1) : ℝ) = (followerCount m : ℝ) := by
    simp [followerCount]
  rw [← hmd, Fin.sum_univ_succ]
  simp only [recorderMass, Fin.val_zero, ↓reduceIte, Fin.val_succ, Nat.succ_ne_zero]
  simp_rw [hdcast]
  rw [sum_const_fin_real]
  have hdR : (followerCount m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hdpos)
  field_simp
  ring

/-- The literal inverse-cumulative slot draw from the reserved `slot` label. -/
def slotDraw {m K : ℕ} (x : ContinuousControlSlice.Slice m K) : Slot :=
  ContinuousCategorical.sample (by decide) slotMass slotMass_sum
    (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.slot x)

/-- The literal inverse-cumulative uniform follower draw from `sel`. Its
result index `r` denotes player `r.val + 1`. -/
def selectedFollowerDraw {m K : ℕ} (hm : 2 ≤ m) (_hmk : m < K)
    (x : ContinuousControlSlice.Slice m K) : Fin (followerCount m) :=
  ContinuousCategorical.sample (followerCount_pos hm)
    (equalMass (followerCount m)) (equalMass_sum _ (followerCount_pos hm))
    (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.sel x)

/-- The literal inverse-cumulative DATA recorder-source draw from `rec`. -/
def recorderSourceDraw {m K : ℕ} (hm : 2 ≤ m) (_hmk : m < K)
    (x : ContinuousControlSlice.Slice m K) : Fin m :=
  ContinuousCategorical.sample (by omega) (recorderMass m)
    (recorderMass_sum hm)
    (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec x)

/-- The source arm number `1 + floor(K v)` for a DATA pilot. -/
def pilotArmLabel (K : ℕ) (v : ContinuousCategorical.Scalar) : ℕ :=
  1 + Nat.floor ((K : ℝ) * v.val)

theorem pilot_floor_lt {K : ℕ} (hK : 0 < K) (v : ContinuousCategorical.Scalar) :
    Nat.floor ((K : ℝ) * v.val) < K := by
  apply (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg K) v.property.1)).2
  calc
    (K : ℝ) * v.val < (K : ℝ) * 1 :=
      mul_lt_mul_of_pos_left v.property.2 (by exact_mod_cast hK)
    _ = (K : ℝ) := by ring

theorem pilotArmLabel_le {K : ℕ} (hK : 0 < K) (v : ContinuousCategorical.Scalar) :
    pilotArmLabel K v ≤ K := by
  simp only [pilotArmLabel]
  have h := pilot_floor_lt hK v
  omega

/-- A DATA pilot indexed by its zero-based `Fin K` arm. The corresponding
source arm label is `pilotArmLabel K v = pilot.val + 1`. -/
def pilotFromScalar (K : ℕ) (hK : 0 < K) (v : ContinuousCategorical.Scalar) : Fin K :=
  ⟨Nat.floor ((K : ℝ) * v.val), pilot_floor_lt hK v⟩

def pilotDraw {m K : ℕ} (hK : 0 < K) (r : Fin m)
    (x : ContinuousControlSlice.Slice m K) : Fin K :=
  pilotFromScalar K hK
    (ContinuousControlSlice.coordinate (ContinuousControlSlice.Label.pilot r) x)

theorem pilotArmLabel_eq_val_add_one {m K : ℕ} (hK : 0 < K) (r : Fin m)
    (x : ContinuousControlSlice.Slice m K) :
    pilotArmLabel K (ContinuousControlSlice.coordinate
      (ContinuousControlSlice.Label.pilot r) x) = (pilotDraw hK r x).val + 1 := by
  simp only [pilotArmLabel, pilotDraw, pilotFromScalar, Fin.val_mk]
  omega

theorem pilot_arm_label_positive {K : ℕ} (v : ContinuousCategorical.Scalar) :
    1 ≤ pilotArmLabel K v := by
  simp only [pilotArmLabel]
  omega

/-- Every pilot lands in the source arm range `1,...,K`. -/
theorem pilotArmLabel_mem {K : ℕ} (hK : 0 < K) (v : ContinuousCategorical.Scalar) :
    1 ≤ pilotArmLabel K v ∧ pilotArmLabel K v ≤ K :=
  ⟨pilot_arm_label_positive v, pilotArmLabel_le hK v⟩

/-- The generic equal-mass inverse-cumulative categorical rule on `Fin K`. -/
def equalArmSample (K : ℕ) (hK : 0 < K) (v : ContinuousCategorical.Scalar) : Fin K :=
  ContinuousCategorical.sample hK (equalMass K) (equalMass_sum K hK) v

/-- The floor DATA pilot is exactly the generic equal-mass categorical draw. -/
theorem pilot_eq_equalArmSample {K : ℕ} (hK : 0 < K) (v : ContinuousCategorical.Scalar) :
    pilotFromScalar K hK v = equalArmSample K hK v := by
  apply Fin.ext
  let i : Fin K := ⟨Nat.floor ((K : ℝ) * v.val), pilot_floor_lt hK v⟩
  have hnonneg : 0 ≤ (K : ℝ) * v.val :=
    mul_nonneg (Nat.cast_nonneg K) v.property.1
  have hfloorLo : (Nat.floor ((K : ℝ) * v.val) : ℝ) ≤ (K : ℝ) * v.val :=
    Nat.floor_le hnonneg
  have hfloorHi : (K : ℝ) * v.val < (Nat.floor ((K : ℝ) * v.val) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos
  have hlow : ContinuousCategorical.lower (equalMass K) i =
      (i.val : ℝ) / (K : ℝ) := by
    simp [ContinuousCategorical.lower, equalMass, Finset.sum_const]
    field_simp [hKne]
  have hupp : ContinuousCategorical.upper (equalMass K) i =
      ((i.val + 1 : ℕ) : ℝ) / (K : ℝ) := by
    simp [ContinuousCategorical.upper, equalMass, Finset.sum_const, Nat.cast_add]
    field_simp [hKne]
  have hinterval :
      ContinuousCategorical.lower (equalMass K) i ≤ v.val ∧
        v.val < ContinuousCategorical.upper (equalMass K) i := by
    rw [hlow, hupp]
    constructor
    · apply (div_le_iff₀ hKpos).2
      simpa [i, mul_comm] using hfloorLo
    · apply (lt_div_iff₀ hKpos).2
      simpa [i, mul_comm] using hfloorHi
  have hs := (ContinuousCategorical.sample_eq_iff hK
    (fun i => equalMass_nonneg K i)
    (equalMass_sum K hK) v i).2 hinterval
  exact congrArg Fin.val hs.symm

/-- Push the actual reserved coordinate through the accepted generic
inverse-cumulative sampler. -/
theorem measurePreserving_sampleCoordinate {m K n : ℕ} (c : ContinuousControlSlice.Label m K)
    (hn : 0 < n) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) :
    MeasurePreserving
      (fun x => ContinuousCategorical.sample hn p hsum
        (ContinuousControlSlice.coordinate c x))
      (ContinuousControlSlice.sliceLaw m K)
      (ContinuousCategorical.massPMF p hp hsum).toMeasure := by
  have hcoord : MeasurePreserving (ContinuousControlSlice.coordinate c)
      (ContinuousControlSlice.sliceLaw m K) ContinuousCategorical.uniform := by
    refine ⟨ContinuousControlSlice.measurable_coordinate c, ?_⟩
    calc
      (ContinuousControlSlice.sliceLaw m K).map
          (ContinuousControlSlice.coordinate c) = ContinuousControlSlice.scalarLaw :=
        ContinuousControlSlice.map_coordinate c
      _ = ContinuousCategorical.uniform :=
        ContinuousControlSlice.scalarLaw_eq_categorical_uniform
  have hsample : MeasurePreserving (ContinuousCategorical.sample hn p hsum)
      ContinuousCategorical.uniform
      (ContinuousCategorical.massPMF p hp hsum).toMeasure :=
    ⟨ContinuousCategorical.measurable_sample hn hp hsum,
      ContinuousCategorical.uniform_map_sample hn hp hsum⟩
  exact hsample.comp hcoord

/-- The exact finite PMF of the ordered DATA, DOWN, UP slot. -/
def slotPMF : PMF Slot :=
  ContinuousCategorical.massPMF slotMass slotMass_nonneg slotMass_sum

/-- The exact finite PMF of the uniformly selected follower index. -/
def selectedFollowerPMF {m : ℕ} (hm : 2 ≤ m) : PMF (Fin (followerCount m)) :=
  ContinuousCategorical.massPMF (equalMass (followerCount m))
    (equalMass_nonneg (followerCount m))
    (equalMass_sum (followerCount m) (followerCount_pos hm))

/-- The exact finite PMF of the DATA recorder source. -/
def recorderSourcePMF {m : ℕ} (hm : 2 ≤ m) : PMF (Fin m) :=
  ContinuousCategorical.massPMF (recorderMass m) (recorderMass_nonneg)
    (recorderMass_sum hm)

/-- The exact finite PMF of one uniform DATA pilot arm. -/
def pilotPMF (K : ℕ) (hK : 0 < K) : PMF (Fin K) :=
  ContinuousCategorical.massPMF (equalMass K) (equalMass_nonneg K)
    (equalMass_sum K hK)

theorem measurable_slotDraw {m K : ℕ} :
    Measurable (slotDraw : ContinuousControlSlice.Slice m K → Slot) :=
  ContinuousCategorical.measurable_sample (by decide) slotMass_nonneg slotMass_sum |>.comp
    (ContinuousControlSlice.measurable_coordinate ContinuousControlSlice.Label.slot)

theorem measurePreserving_slotDraw {m K : ℕ} :
    MeasurePreserving slotDraw (ContinuousControlSlice.sliceLaw m K) slotPMF.toMeasure := by
  change MeasurePreserving
    (fun x => ContinuousCategorical.sample (by decide) slotMass slotMass_sum
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.slot x))
    (ContinuousControlSlice.sliceLaw m K)
    (ContinuousCategorical.massPMF slotMass slotMass_nonneg slotMass_sum).toMeasure
  exact measurePreserving_sampleCoordinate (m := m) (K := K)
    ContinuousControlSlice.Label.slot (by decide) slotMass slotMass_nonneg slotMass_sum

theorem map_slotDraw {m K : ℕ} :
    (ContinuousControlSlice.sliceLaw m K).map slotDraw = slotPMF.toMeasure :=
  measurePreserving_slotDraw.map_eq

theorem measurePreserving_selectedFollowerDraw {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K) :
    MeasurePreserving (selectedFollowerDraw hm hmk)
      (ContinuousControlSlice.sliceLaw m K) (selectedFollowerPMF hm).toMeasure := by
  change MeasurePreserving
    (fun x => ContinuousCategorical.sample (followerCount_pos hm)
      (equalMass (followerCount m)) (equalMass_sum _ (followerCount_pos hm))
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.sel x))
    (ContinuousControlSlice.sliceLaw m K)
    (ContinuousCategorical.massPMF (equalMass (followerCount m))
      (equalMass_nonneg (followerCount m))
      (equalMass_sum (followerCount m) (followerCount_pos hm))).toMeasure
  exact measurePreserving_sampleCoordinate (m := m) (K := K)
    ContinuousControlSlice.Label.sel (followerCount_pos hm) (equalMass (followerCount m))
    (equalMass_nonneg (followerCount m)) (equalMass_sum _ (followerCount_pos hm))

theorem measurable_selectedFollowerDraw {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K) :
    Measurable (selectedFollowerDraw hm hmk) :=
  (measurePreserving_selectedFollowerDraw hm hmk).measurable

theorem map_selectedFollowerDraw {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K) :
    (ContinuousControlSlice.sliceLaw m K).map (selectedFollowerDraw hm hmk) =
      (selectedFollowerPMF hm).toMeasure :=
  (measurePreserving_selectedFollowerDraw hm hmk).map_eq

theorem measurePreserving_recorderSourceDraw {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K) :
    MeasurePreserving (recorderSourceDraw hm hmk)
      (ContinuousControlSlice.sliceLaw m K) (recorderSourcePMF hm).toMeasure := by
  change MeasurePreserving
    (fun x => ContinuousCategorical.sample (by omega) (recorderMass m)
      (recorderMass_sum hm) (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec x))
    (ContinuousControlSlice.sliceLaw m K)
    (ContinuousCategorical.massPMF (recorderMass m) recorderMass_nonneg
      (recorderMass_sum hm)).toMeasure
  exact measurePreserving_sampleCoordinate (m := m) (K := K)
    ContinuousControlSlice.Label.rec (by omega) (recorderMass m)
    recorderMass_nonneg (recorderMass_sum hm)

theorem measurable_recorderSourceDraw {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K) :
    Measurable (recorderSourceDraw hm hmk) :=
  (measurePreserving_recorderSourceDraw hm hmk).measurable

theorem map_recorderSourceDraw {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K) :
    (ContinuousControlSlice.sliceLaw m K).map (recorderSourceDraw hm hmk) =
      (recorderSourcePMF hm).toMeasure :=
  (measurePreserving_recorderSourceDraw hm hmk).map_eq

theorem measurePreserving_pilotDraw {m K : ℕ} (hK : 0 < K) (r : Fin m) :
    MeasurePreserving (pilotDraw hK r) (ContinuousControlSlice.sliceLaw m K)
      (pilotPMF K hK).toMeasure := by
  have hsample := measurePreserving_sampleCoordinate (m := m) (K := K)
    (ContinuousControlSlice.Label.pilot r) hK (equalMass K) (equalMass_nonneg K)
    (equalMass_sum K hK)
  have hfun : pilotDraw hK r = fun x => equalArmSample K hK
      (ContinuousControlSlice.coordinate (ContinuousControlSlice.Label.pilot r) x) := by
    funext x
    exact pilot_eq_equalArmSample hK
      (ContinuousControlSlice.coordinate (ContinuousControlSlice.Label.pilot r) x)
  rw [hfun]
  simpa only [pilotPMF, equalArmSample] using hsample

theorem measurable_pilotDraw {m K : ℕ} (hK : 0 < K) (r : Fin m) :
    Measurable (pilotDraw hK r) := (measurePreserving_pilotDraw hK r).measurable

theorem map_pilotDraw {m K : ℕ} (hK : 0 < K) (r : Fin m) :
    (ContinuousControlSlice.sliceLaw m K).map (pilotDraw hK r) = (pilotPMF K hK).toMeasure :=
  (measurePreserving_pilotDraw hK r).map_eq

theorem slotDraw_atom {m K : ℕ} (i : Slot) :
    (ContinuousControlSlice.sliceLaw m K) (slotDraw ⁻¹' {i}) =
      ENNReal.ofReal (slotMass i) := by
  calc
    _ = ((ContinuousControlSlice.sliceLaw m K).map slotDraw) {i} :=
      (Measure.map_apply measurable_slotDraw (measurableSet_singleton i)).symm
    _ = slotPMF.toMeasure {i} := by rw [measurePreserving_slotDraw.map_eq]
    _ = ENNReal.ofReal (slotMass i) := by
      rw [PMF.toMeasure_apply_singleton _ i (measurableSet_singleton i),
        slotPMF, ContinuousCategorical.massPMF_apply]

theorem selectedFollowerDraw_atom {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K)
    (i : Fin (followerCount m)) :
    (ContinuousControlSlice.sliceLaw m K)
      (selectedFollowerDraw hm hmk ⁻¹' {i}) =
        ENNReal.ofReal (equalMass (followerCount m) i) := by
  calc
    _ = ((ContinuousControlSlice.sliceLaw m K).map (selectedFollowerDraw hm hmk)) {i} :=
      (Measure.map_apply (measurePreserving_selectedFollowerDraw hm hmk).measurable
        (measurableSet_singleton i)).symm
    _ = (selectedFollowerPMF hm).toMeasure {i} := by
      rw [(measurePreserving_selectedFollowerDraw hm hmk).map_eq]
    _ = ENNReal.ofReal (equalMass (followerCount m) i) := by
      rw [PMF.toMeasure_apply_singleton _ i (measurableSet_singleton i),
        selectedFollowerPMF, ContinuousCategorical.massPMF_apply]

theorem recorderSourceDraw_atom {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K)
    (i : Fin m) :
    (ContinuousControlSlice.sliceLaw m K) (recorderSourceDraw hm hmk ⁻¹' {i}) =
      ENNReal.ofReal (recorderMass m i) := by
  calc
    _ = ((ContinuousControlSlice.sliceLaw m K).map (recorderSourceDraw hm hmk)) {i} :=
      (Measure.map_apply (measurePreserving_recorderSourceDraw hm hmk).measurable
        (measurableSet_singleton i)).symm
    _ = (recorderSourcePMF hm).toMeasure {i} := by
      rw [(measurePreserving_recorderSourceDraw hm hmk).map_eq]
    _ = ENNReal.ofReal (recorderMass m i) := by
      rw [PMF.toMeasure_apply_singleton _ i (measurableSet_singleton i),
        recorderSourcePMF, ContinuousCategorical.massPMF_apply]

theorem pilotDraw_atom {m K : ℕ} (hK : 0 < K) (r : Fin m) (i : Fin K) :
    (ContinuousControlSlice.sliceLaw m K) (pilotDraw hK r ⁻¹' {i}) =
      ENNReal.ofReal (equalMass K i) := by
  calc
    _ = ((ContinuousControlSlice.sliceLaw m K).map (pilotDraw hK r)) {i} :=
      (Measure.map_apply (measurePreserving_pilotDraw hK r).measurable
        (measurableSet_singleton i)).symm
    _ = (pilotPMF K hK).toMeasure {i} := by
      rw [(measurePreserving_pilotDraw hK r).map_eq]
    _ = ENNReal.ofReal (equalMass K i) := by
      rw [PMF.toMeasure_apply_singleton _ i (measurableSet_singleton i),
        pilotPMF, ContinuousCategorical.massPMF_apply]

/-- The actual one-slice draw-family indices, including one pilot per player. -/
inductive DrawIndex (m K : ℕ) where
  | slot
  | selectedFollower
  | recorderSource
  | pilot (r : Fin m)
  deriving DecidableEq, Fintype

/-- Output carrier for each member of the heterogeneous public draw family. -/
def DrawOutput {m K : ℕ} : DrawIndex m K → Type
  | .slot => Slot
  | .selectedFollower => Fin (followerCount m)
  | .recorderSource => Fin m
  | .pilot _ => Fin K

instance {m K : ℕ} : ∀ i : DrawIndex m K, MeasurableSpace (DrawOutput i)
  | .slot => ⊤
  | .selectedFollower => ⊤
  | .recorderSource => ⊤
  | .pilot _ => ⊤

/-- The reserved scalar label used by each member of the source draw family. -/
def drawLabel {m K : ℕ} : DrawIndex m K → ContinuousControlSlice.Label m K
  | .slot => ContinuousControlSlice.Label.slot
  | .selectedFollower => ContinuousControlSlice.Label.sel
  | .recorderSource => ContinuousControlSlice.Label.rec
  | .pilot r => ContinuousControlSlice.Label.pilot r

theorem drawLabel_injective {m K : ℕ} :
    Function.Injective (drawLabel : DrawIndex m K → ContinuousControlSlice.Label m K) := by
  intro a b h
  cases a with
  | slot =>
    cases b <;> simp [drawLabel, ContinuousControlSlice.Label.slot,
      ContinuousControlSlice.Label.sel, ContinuousControlSlice.Label.rec,
      ContinuousControlSlice.Label.pilot] at h ⊢
  | selectedFollower =>
    cases b <;> simp [drawLabel, ContinuousControlSlice.Label.slot,
      ContinuousControlSlice.Label.sel, ContinuousControlSlice.Label.rec,
      ContinuousControlSlice.Label.pilot] at h ⊢
  | recorderSource =>
    cases b <;> simp [drawLabel, ContinuousControlSlice.Label.slot,
      ContinuousControlSlice.Label.sel, ContinuousControlSlice.Label.rec,
      ContinuousControlSlice.Label.pilot] at h ⊢
  | pilot r =>
    cases b with
    | slot => simp [drawLabel, ContinuousControlSlice.Label.slot,
        ContinuousControlSlice.Label.pilot] at h
    | selectedFollower => simp [drawLabel, ContinuousControlSlice.Label.sel,
        ContinuousControlSlice.Label.pilot] at h
    | recorderSource => simp [drawLabel, ContinuousControlSlice.Label.rec,
        ContinuousControlSlice.Label.pilot] at h
    | pilot s =>
      apply congrArg DrawIndex.pilot
      exact Sum.inl_injective (Sum.inr_injective (Sum.inr_injective h))

/-- Every public draw as a function of its reserved scalar coordinate. -/
def drawFromScalar {m K : ℕ} (hm : 2 ≤ m) (_hmk : m < K) (hK : 0 < K) :
    (i : DrawIndex m K) → ContinuousCategorical.Scalar → DrawOutput i
  | .slot, v => ContinuousCategorical.sample (by decide) slotMass slotMass_sum v
  | .selectedFollower, v => ContinuousCategorical.sample (followerCount_pos hm)
      (equalMass (followerCount m)) (equalMass_sum _ (followerCount_pos hm)) v
  | .recorderSource, v => ContinuousCategorical.sample (by omega)
      (recorderMass m) (recorderMass_sum hm) v
  | .pilot _, v => pilotFromScalar K hK v

/-- The concrete slot, selected-follower, recorder-source, and pilot maps
consuming the corresponding coordinates of the accepted continuous slice. -/
def drawFamily {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K) (hK : 0 < K) :
    (i : DrawIndex m K) → ContinuousControlSlice.Slice m K → DrawOutput i :=
  fun i x => drawFromScalar hm hmk hK i
    (ContinuousControlSlice.coordinate (drawLabel i) x)

@[simp] theorem drawFamily_slot {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K)
    (hK : 0 < K) : drawFamily hm hmk hK .slot = slotDraw := rfl

@[simp] theorem drawFamily_selectedFollower {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K)
    (hK : 0 < K) :
    drawFamily hm hmk hK .selectedFollower = selectedFollowerDraw hm hmk := rfl

@[simp] theorem drawFamily_recorderSource {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K)
    (hK : 0 < K) :
    drawFamily hm hmk hK .recorderSource = recorderSourceDraw hm hmk := rfl

@[simp] theorem drawFamily_pilot {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K)
    (hK : 0 < K) (r : Fin m) :
    drawFamily hm hmk hK (.pilot r) = pilotDraw hK r := rfl

theorem measurable_drawFromScalar {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K)
    (hK : 0 < K) (i : DrawIndex m K) :
    Measurable (drawFromScalar hm hmk hK i) := by
  cases i with
  | slot =>
      exact ContinuousCategorical.measurable_sample (by decide)
        slotMass_nonneg slotMass_sum
  | selectedFollower =>
      exact ContinuousCategorical.measurable_sample (followerCount_pos hm)
        (equalMass_nonneg _) (equalMass_sum _ (followerCount_pos hm))
  | recorderSource =>
      exact ContinuousCategorical.measurable_sample (by omega)
        recorderMass_nonneg (recorderMass_sum hm)
  | pilot _ =>
      have hp : pilotFromScalar K hK = equalArmSample K hK := by
        funext v
        exact pilot_eq_equalArmSample hK v
      change Measurable (pilotFromScalar K hK)
      rw [hp]
      exact ContinuousCategorical.measurable_sample hK
        (equalMass_nonneg K) (equalMass_sum K hK)

theorem measurable_drawFamily {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K)
    (hK : 0 < K) (i : DrawIndex m K) :
    Measurable (drawFamily hm hmk hK i) := by
  exact (measurable_drawFromScalar hm hmk hK i).comp
    (ContinuousControlSlice.measurable_coordinate (drawLabel i))

/-- Joint independence of all source draw outputs, proved from disjoint
coordinates in the actual slice product measure. -/
theorem iIndepFun_drawFamily {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K)
    (hK : 0 < K) :
    iIndepFun (drawFamily hm hmk hK) (ContinuousControlSlice.sliceLaw m K) := by
  have hcoords := (ContinuousControlSlice.iIndepFun_coordinate m K).precomp
    (g := drawLabel) drawLabel_injective
  exact hcoords.comp (drawFromScalar hm hmk hK)
    (measurable_drawFromScalar hm hmk hK)

/-- The full raw vector of tuple scalar inputs. The independent ordered-tuple
sampler owns their algorithm and resulting law. -/
def tupleInputs {m K : ℕ} (x : ContinuousControlSlice.Slice m K) :
    Fin m → ContinuousControlSlice.Scalar :=
  fun r => ContinuousControlSlice.coordinate (ContinuousControlSlice.Label.tuple r) x

theorem measurable_tupleInputs {m K : ℕ} :
    Measurable (tupleInputs : ContinuousControlSlice.Slice m K → Fin m →
      ContinuousControlSlice.Scalar) :=
  measurable_pi_iff.mpr (fun r =>
    ContinuousControlSlice.measurable_coordinate (ContinuousControlSlice.Label.tuple r))

theorem tupleLabel_injective {m K : ℕ} :
    Function.Injective
      (ContinuousControlSlice.Label.tuple : Fin m → ContinuousControlSlice.Label m K) := by
  intro r s h
  exact Sum.inl_injective (Sum.inr_injective h)

/-- The raw tuple scalar inputs are jointly independent and have their true
product `[0,1)` law under the accepted slice sampler. -/
theorem iIndepFun_tupleInputs {m K : ℕ} :
    iIndepFun (fun r x => tupleInputs x r) (ContinuousControlSlice.sliceLaw m K) :=
  (ContinuousControlSlice.iIndepFun_coordinate m K).precomp tupleLabel_injective

def tupleScalarLaw (m : ℕ) : Measure (Fin m → ContinuousControlSlice.Scalar) :=
  Measure.pi (fun _ : Fin m => ContinuousControlSlice.scalarLaw)

theorem map_tupleInputs {m K : ℕ} :
    (ContinuousControlSlice.sliceLaw m K).map tupleInputs = tupleScalarLaw m := by
  change (ContinuousControlSlice.sliceLaw m K).map
    (fun x r => ContinuousControlSlice.coordinate (ContinuousControlSlice.Label.tuple r) x) = _
  have h := (iIndepFun_tupleInputs (m := m) (K := K)).map_fun_eq_pi_map
    (fun r => (ContinuousControlSlice.measurable_coordinate
      (ContinuousControlSlice.Label.tuple r)).aemeasurable)
  simpa only [ContinuousControlSlice.map_coordinate, tupleScalarLaw] using h

/-- Combined index type for the draw family and every raw tuple input. -/
abbrev DrawOrTupleIndex (m K : ℕ) := DrawIndex m K ⊕ Fin m

def DrawOrTupleOutput {m K : ℕ} : DrawOrTupleIndex m K → Type
  | .inl i => DrawOutput i
  | .inr _ => ContinuousControlSlice.Scalar

instance {m K : ℕ} : ∀ i : DrawOrTupleIndex m K, MeasurableSpace (DrawOrTupleOutput i)
  | .inl i => inferInstanceAs (MeasurableSpace (DrawOutput i))
  | .inr _ => inferInstanceAs (MeasurableSpace ContinuousControlSlice.Scalar)

def DrawOrTupleLabel {m K : ℕ} : DrawOrTupleIndex m K →
    ContinuousControlSlice.Label m K
  | .inl i => drawLabel i
  | .inr r => ContinuousControlSlice.Label.tuple r

theorem drawOrTupleLabel_injective {m K : ℕ} :
    Function.Injective
      (DrawOrTupleLabel : DrawOrTupleIndex m K → ContinuousControlSlice.Label m K) := by
  intro a b h
  cases a with
  | inl i =>
    cases b with
    | inl j => exact congrArg Sum.inl (drawLabel_injective h)
    | inr r =>
      cases i <;> simp [DrawOrTupleLabel, drawLabel,
        ContinuousControlSlice.Label.slot, ContinuousControlSlice.Label.sel,
        ContinuousControlSlice.Label.rec, ContinuousControlSlice.Label.pilot,
        ContinuousControlSlice.Label.tuple] at h
  | inr r =>
    cases b with
    | inl i =>
      cases i <;> simp [DrawOrTupleLabel, drawLabel,
        ContinuousControlSlice.Label.slot, ContinuousControlSlice.Label.sel,
        ContinuousControlSlice.Label.rec, ContinuousControlSlice.Label.pilot,
        ContinuousControlSlice.Label.tuple] at h
    | inr s => exact congrArg Sum.inr (tupleLabel_injective h)

def drawOrTupleFamily {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K) (hK : 0 < K) :
    (i : DrawOrTupleIndex m K) → ContinuousControlSlice.Slice m K → DrawOrTupleOutput i
  | .inl i, x => drawFamily hm hmk hK i x
  | .inr r, x => tupleInputs x r

def drawOrTupleFromScalar {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K) (hK : 0 < K) :
    (i : DrawOrTupleIndex m K) → ContinuousCategorical.Scalar → DrawOrTupleOutput i
  | .inl i, v => drawFromScalar hm hmk hK i v
  | .inr _, v => v

theorem measurable_drawOrTupleFromScalar {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K)
    (hK : 0 < K) (i : DrawOrTupleIndex m K) :
    Measurable (drawOrTupleFromScalar hm hmk hK i) := by
  cases i with
  | inl j =>
      change Measurable (drawFromScalar hm hmk hK j)
      exact measurable_drawFromScalar hm hmk hK j
  | inr _ =>
      change Measurable (id : ContinuousCategorical.Scalar → ContinuousCategorical.Scalar)
      exact measurable_id

theorem measurable_drawOrTupleFamily {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K)
    (hK : 0 < K) (i : DrawOrTupleIndex m K) :
    Measurable (drawOrTupleFamily hm hmk hK i) := by
  cases i with
  | inl j =>
      change Measurable (drawFamily hm hmk hK j)
      exact measurable_drawFamily hm hmk hK j
  | inr r =>
      change Measurable (ContinuousControlSlice.coordinate
        (ContinuousControlSlice.Label.tuple r))
      exact ContinuousControlSlice.measurable_coordinate _

/-- The complete draw family and the full tuple-input vector are jointly
independent, by grouping disjoint-label coordinates in the accepted product
slice law. This is stronger than pairwise independence. -/
theorem iIndepFun_drawOrTupleFamily {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K)
    (hK : 0 < K) :
    iIndepFun (drawOrTupleFamily hm hmk hK) (ContinuousControlSlice.sliceLaw m K) := by
  have hcoords := (ContinuousControlSlice.iIndepFun_coordinate m K).precomp
    (g := DrawOrTupleLabel) drawOrTupleLabel_injective
  have h := hcoords.comp (drawOrTupleFromScalar hm hmk hK)
    (measurable_drawOrTupleFromScalar hm hmk hK)
  change iIndepFun (fun i x => drawOrTupleFromScalar hm hmk hK i
    (ContinuousControlSlice.coordinate (DrawOrTupleLabel i) x))
      (ContinuousControlSlice.sliceLaw m K) at h
  have heq : drawOrTupleFamily hm hmk hK =
      (fun i x => drawOrTupleFromScalar hm hmk hK i
        (ContinuousControlSlice.coordinate (DrawOrTupleLabel i) x)) := by
    funext i x
    cases i <;> rfl
  rw [heq]
  exact h

def drawIndexSet {m K : ℕ} : Set (DrawOrTupleIndex m K) := Set.range Sum.inl

def tupleIndexSet {m K : ℕ} : Set (DrawOrTupleIndex m K) := Set.range Sum.inr

def drawVector {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K) (hK : 0 < K)
    (x : ContinuousControlSlice.Slice m K) : (i : DrawIndex m K) → DrawOutput i :=
  fun i => drawFamily hm hmk hK i x

def drawBlockOf {m K : ℕ}
    (z : (i : drawIndexSet (m := m) (K := K)) → DrawOrTupleOutput i.val) :
    (i : DrawIndex m K) → DrawOutput i :=
  fun i =>
    let j : drawIndexSet (m := m) (K := K) := ⟨Sum.inl i, ⟨i, rfl⟩⟩
    z j

def tupleBlockOf {m K : ℕ}
    (z : (i : tupleIndexSet (m := m) (K := K)) → DrawOrTupleOutput i.val) :
    Fin m → ContinuousControlSlice.Scalar :=
  fun r =>
    let j : tupleIndexSet (m := m) (K := K) := ⟨Sum.inr r, ⟨r, rfl⟩⟩
    z j

theorem measurable_drawBlockOf {m K : ℕ} :
    Measurable (drawBlockOf :
      ((i : drawIndexSet (m := m) (K := K)) → DrawOrTupleOutput i.val) →
        (i : DrawIndex m K) → DrawOutput i) := by
  apply measurable_pi_iff.mpr
  intro i
  let si : drawIndexSet (m := m) (K := K) := ⟨Sum.inl i, ⟨i, rfl⟩⟩
  exact measurable_pi_apply si

theorem measurable_tupleBlockOf {m K : ℕ} :
    Measurable (tupleBlockOf :
      ((i : tupleIndexSet (m := m) (K := K)) → DrawOrTupleOutput i.val) →
        Fin m → ContinuousControlSlice.Scalar) := by
  apply measurable_pi_iff.mpr
  intro r
  let si : tupleIndexSet (m := m) (K := K) := ⟨Sum.inr r, ⟨r, rfl⟩⟩
  exact measurable_pi_apply si

theorem indepFun_drawFamily_tupleInputs {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K)
    (hK : 0 < K) :
    IndepFun (drawVector hm hmk hK) (tupleInputs (m := m) (K := K))
      (ContinuousControlSlice.sliceLaw m K) := by
  have hgroups := (iIndepFun_drawOrTupleFamily hm hmk hK).indepFun_set
    (drawIndexSet (m := m) (K := K)) (tupleIndexSet (m := m) (K := K)) (by
      rw [Set.disjoint_left]
      intro i hi hj
      rcases hi with ⟨a, rfl⟩
      rcases hj with ⟨b, hb⟩
      cases hb) (measurable_drawOrTupleFamily hm hmk hK)
  have hcomp := hgroups.comp measurable_drawBlockOf measurable_tupleBlockOf
  change IndepFun (drawVector hm hmk hK) tupleInputs
    (ContinuousControlSlice.sliceLaw m K)
  have hleft :
      (fun x => drawBlockOf (fun i => drawOrTupleFamily hm hmk hK i.val x)) =
        drawVector hm hmk hK := by
    funext x i
    simp [drawBlockOf, drawOrTupleFamily, drawVector]
  have hright :
      (fun x => tupleBlockOf (fun i => drawOrTupleFamily hm hmk hK i.val x)) =
        tupleInputs := by
    funext x r
    simp [tupleBlockOf, drawOrTupleFamily, tupleInputs]
  change IndepFun
    (fun x => drawBlockOf (fun i => drawOrTupleFamily hm hmk hK i.val x))
    (fun x => tupleBlockOf (fun i => drawOrTupleFamily hm hmk hK i.val x))
    (ContinuousControlSlice.sliceLaw m K) at hcomp
  rw [hleft, hright] at hcomp
  exact hcomp

end Bandits.Support.PublicDiscreteDraws

end
