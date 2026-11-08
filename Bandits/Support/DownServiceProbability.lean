/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActiveRoundActions
public import Bandits.Support.ActiveObservationBridge
public import Bandits.Support.PublicDiscreteDraws
public import Bandits.Support.OrderedTupleSampler
public import Bandits.Support.ContinuousLearningRows
public import Bandits.Support.AffineChannelLaw
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Exact one-round DOWN service probability

The fixed-snapshot collision identities are from
`sources/zip4/manuscript/05_binary_transport.tex:155-175`; the two definitions
of a positive DOWN service observation and its one-round mass are from
`05_binary_transport.tex:253-275`. The continuous scalar labels and genuine
affine channel samples are from
`sources/zip4/manuscript/appendix_b_communication.tex:25-44`.

This module fixes one assignment, one snapshot, one reward row, one current
DOWN word, and one fast arm outside the assignment image. A round is then
constructed from the accepted continuous slice maps and the accepted affine
channel sample. No actual history, stale-word exclusion, freshness after
conditioning on history, quota, stopping rule, or conditional expectation is
asserted here. In particular, the no-released snapshot invariant is an explicit
application input.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.DownServiceProbability

open MeasureTheory
open ProbabilityTheory
open Bandits.Support.AffineChannelLaw
open Bandits.Support.ActiveRoundActions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.FiniteBanditModel
open Bandits.Support.OrderedTupleSampler
open Bandits.Support.PublicDiscreteDraws
open scoped ENNReal

variable (p : Parameters)

/-- Arms with strictly positive reward in the fixed bounded row. -/
def positiveArms {K : ℕ} (row : RewardRow K) : Finset (Arm K) :=
  Finset.univ.filter fun a => 0 < row.val a

/-- Source arm number of the selected follower's tuple coordinate. -/
def receiverArm {m K : ℕ} (hm : 2 ≤ m) (i : Follower m)
    (tuple : OrderedTupleSampler.Tuple m K) : Arm K :=
  tuple.val (followerPlayer hm i)

/-- DOWN channel index for the fixed missing follower. -/
def downChannel (p : Parameters) (i : Fin (d p)) : Channel p := (0, i)

/-- UP channel index, retained in the constructed physical input even though a
DOWN observation does not inspect it. -/
def upChannel (p : Parameters) (i : Fin (d p)) : Channel p := (1, i)

/-- Construct the literal action input from one accepted public control draw.
The slot, selected follower, tuple, every pilot, and both affine samples are
read from their reserved coordinates. Only the fast arm and current DOWN word
and the otherwise unused UP word are fixed application data. -/
def roundInput (p : Parameters) {a : Assignment p.m p.K}
    (i : Follower p.m) (word : Word (B p)) (upWord : Word (B p)) (fast : Arm p.K)
    (hfast : ∀ j, fast ≠ a.assigned j) (control : TimeControl p) :
    RoundInput a (B p) :=
  { slot := slotDraw control.1
    selected := selectedFollowerDraw p.two_le_m p.m_lt_K control.1
    tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K control.1
    pilots := fun j => pilotDraw (ConstructorDimensions.K_pos p) j control.1
    down := ⟨control.2 (downChannel p i), word⟩
    up := ⟨control.2 (upChannel p i), upWord⟩
    fast := fast
    fast_outside := hfast }

/-- The same construction at one actual index of the accepted public row law. -/
def roundInputAt (p : Parameters) {a : Assignment p.m p.K}
    (t : Fin p.T) (i : Follower p.m) (word : Word (B p)) (upWord : Word (B p)) (fast : Arm p.K)
    (hfast : ∀ j, fast ≠ a.assigned j) (row : LearningRow p) :
    RoundInput a (B p) :=
  roundInput p i word upWord fast hfast (controlAt t row)

/-- The source's positive DOWN service observation for a fixed missing
follower. Both branches use the actual physical feedback of the constructed
round; the pending branch additionally requires a zero hash. -/
def sourceDownService {m K B : ℕ} (hm : 2 ≤ m) {a : Assignment m K}
    (s : Snapshot a) (i : Follower m) (row : RewardRow K)
    (r : RoundInput a B) : Prop :=
  r.slot = downSlot ∧ r.selected = i ∧ i ∈ s.missing ∧
    ((s.status i = .unoccupied ∧
        0 < feedback hm s r row (followerPlayer hm i)) ∨
      (s.status i = .pending ∧ r.down.bit = 0 ∧
        0 < feedback hm s r row (coordinator hm)))

private abbrev TupleFiber {m K : ℕ} (i : Fin m) (arm : Fin K) :=
  {tuple : OrderedTupleSampler.Tuple m K // tuple.val i = arm}

private def tupleArmSwapEquiv {m K : ℕ} (a b : Fin K) :
    OrderedTupleSampler.Tuple m K ≃ OrderedTupleSampler.Tuple m K where
  toFun tuple := ⟨Equiv.swap a b ∘ tuple.val,
    (Equiv.injective (Equiv.swap a b)).comp tuple.property⟩
  invFun tuple := ⟨Equiv.swap a b ∘ tuple.val,
    (Equiv.injective (Equiv.swap a b)).comp tuple.property⟩
  left_inv tuple := by
    apply Subtype.ext
    funext i
    simp [Function.comp_def]
  right_inv tuple := by
    apply Subtype.ext
    funext i
    simp [Function.comp_def]

private def tupleFiberSwapEquiv {m K : ℕ} (i : Fin m) (a b : Fin K) :
    TupleFiber i a ≃ TupleFiber i b where
  toFun tuple :=
    ⟨tupleArmSwapEquiv a b tuple.1, by
      change Equiv.swap a b (tuple.1.val i) = b
      rw [tuple.2, Equiv.swap_apply_left]⟩
  invFun tuple :=
    ⟨tupleArmSwapEquiv a b tuple.1, by
      change Equiv.swap a b (tuple.1.val i) = a
      rw [tuple.2, Equiv.swap_apply_right]⟩
  left_inv tuple := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    simp [tupleArmSwapEquiv, Function.comp_def]
  right_inv tuple := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    simp [tupleArmSwapEquiv, Function.comp_def]

private theorem tupleFiber_card_eq {m K : ℕ} (i : Fin m) (a b : Fin K) :
    Fintype.card (TupleFiber i a) = Fintype.card (TupleFiber i b) :=
  Fintype.card_congr (tupleFiberSwapEquiv i a b)

private theorem tuple_coordinate_card_total {m K : ℕ} (i : Fin m) :
    Fintype.card (OrderedTupleSampler.Tuple m K) =
      ∑ arm : Fin K, Fintype.card (TupleFiber i arm) := by
  let coordinate : OrderedTupleSampler.Tuple m K → Fin K := fun tuple => tuple.val i
  calc
    Fintype.card (OrderedTupleSampler.Tuple m K) =
        Fintype.card (Σ arm : Fin K, {tuple : OrderedTupleSampler.Tuple m K //
          coordinate tuple = arm}) :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv coordinate)).symm
    _ = ∑ arm : Fin K, Fintype.card {tuple : OrderedTupleSampler.Tuple m K //
          coordinate tuple = arm} := Fintype.card_sigma
    _ = ∑ arm : Fin K, Fintype.card (TupleFiber i arm) := by
      apply Finset.sum_congr rfl
      intro arm harm
      rfl

private theorem tuple_coordinate_fiber_card_eq
    {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K) (i : Fin m) (arm : Fin K) :
    Fintype.card (TupleFiber i arm) =
      (K.descFactorial m) / K := by
  classical
  let zeroArm : Fin K := ⟨0, by omega⟩
  let c : ℕ := Fintype.card (TupleFiber i zeroArm)
  have hconstant : ∀ a : Fin K, Fintype.card (TupleFiber i a) = c := by
    intro a
    exact tupleFiber_card_eq i a zeroArm
  have hKpos : 0 < K := lt_trans (by omega : 0 < m) hmk
  have htotal := tuple_coordinate_card_total (m := m) (K := K) i
  have hsum : (∑ a : Fin K, Fintype.card (TupleFiber i a)) = K * c := by
    calc
      (∑ a : Fin K, Fintype.card (TupleFiber i a)) = ∑ a : Fin K, c := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hconstant a
      _ = K * c := by simp [Finset.sum_const]
  have htotal' : Fintype.card (OrderedTupleSampler.Tuple m K) = K * c :=
    htotal.trans hsum
  have hcard : Fintype.card (OrderedTupleSampler.Tuple m K) = K.descFactorial m :=
    OrderedTupleSampler.card_tuple m K
  have hdiv : (K.descFactorial m) / K = c := by
    calc
      (K.descFactorial m) / K = Fintype.card (OrderedTupleSampler.Tuple m K) / K := by
        rw [hcard]
      _ = (K * c) / K := by rw [htotal']
      _ = c := by simpa [Nat.mul_comm] using Nat.mul_div_left c hKpos
  rw [hconstant arm, hdiv]

private theorem tuple_coordinate_filter_card
    {m K : ℕ} (_hm : 2 ≤ m) (_hmk : m < K) (hKpos : 0 < K) (i : Fin m)
    (S : Finset (Fin K)) :
    (Finset.univ.filter fun tuple : OrderedTupleSampler.Tuple m K =>
      tuple.val i ∈ S).card = S.card * Fintype.card (TupleFiber i ⟨0, hKpos⟩) := by
  classical
  let coordinate : OrderedTupleSampler.Tuple m K → Fin K := fun tuple => tuple.val i
  have hfilter := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (OrderedTupleSampler.Tuple m K)) S coordinate
  rw [← hfilter]
  calc
    (∑ arm ∈ S, (Finset.univ.filter fun tuple : OrderedTupleSampler.Tuple m K =>
        coordinate tuple = arm).card) =
      ∑ arm ∈ S, Fintype.card (TupleFiber i arm) := by
        apply Finset.sum_congr rfl
        intro arm harm
        symm
        simpa [TupleFiber, coordinate] using
          (Fintype.card_subtype (fun tuple : OrderedTupleSampler.Tuple m K =>
            coordinate tuple = arm))
    _ = S.card * Fintype.card (TupleFiber i ⟨0, hKpos⟩) := by
      calc
        (∑ arm ∈ S, Fintype.card (TupleFiber i arm)) =
            ∑ arm ∈ S, Fintype.card (TupleFiber i ⟨0, hKpos⟩) := by
          apply Finset.sum_congr rfl
          intro arm harm
          exact tupleFiber_card_eq i arm ⟨0, hKpos⟩
        _ = S.card * Fintype.card (TupleFiber i ⟨0, hKpos⟩) := by
          simp [Finset.sum_const]

private theorem tuple_total_factorization
    {m K : ℕ} (_hm : 2 ≤ m) (hmk : m < K) (i : Fin m) :
    Fintype.card (OrderedTupleSampler.Tuple m K) =
      K * Fintype.card (TupleFiber i ⟨0, Nat.lt_trans (by omega : 0 < m) hmk⟩) := by
  let zeroArm : Fin K := ⟨0, Nat.lt_trans (by omega : 0 < m) hmk⟩
  calc
    Fintype.card (OrderedTupleSampler.Tuple m K) =
        ∑ arm : Fin K, Fintype.card (TupleFiber i arm) :=
      tuple_coordinate_card_total (m := m) (K := K) i
    _ = ∑ arm : Fin K, Fintype.card (TupleFiber i zeroArm) := by
      apply Finset.sum_congr rfl
      intro arm harm
      exact tupleFiber_card_eq i arm zeroArm
    _ = K * Fintype.card (TupleFiber i zeroArm) := by simp [Finset.sum_const]

/-- The receiver coordinate is uniform on all `K` arms. This is derived from
the accepted ordered-tuple pushforward and arm-permutation symmetry. -/
theorem orderedTupleReceiver_uniform
    {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K) (i : Fin m)
    (S : Finset (Fin K)) :
    (ContinuousControlSlice.sliceLaw m K)
      {x | (OrderedTupleSampler.sample hm hmk x).val i ∈ S} =
        ENNReal.ofReal ((S.card : ℝ) / K) := by
  classical
  let μ := ContinuousControlSlice.sliceLaw m K
  let event : Set (OrderedTupleSampler.Tuple m K) := {tuple | tuple.val i ∈ S}
  have hmap := OrderedTupleSampler.map_sample hm hmk
  have hmeas : MeasurableSet event := MeasurableSet.of_discrete
  change μ ((OrderedTupleSampler.sample hm hmk) ⁻¹' event) = _
  rw [← Measure.map_apply (OrderedTupleSampler.measurable_sample hm hmk) hmeas,
    hmap, PMF.toMeasure_apply_fintype]
  simp only [Set.indicator, OrderedTupleSampler.uniformTuplePMF_apply]
  let decPred : DecidablePred (fun x : OrderedTupleSampler.Tuple m K => x ∈ event) :=
    Classical.decPred _
  have hsumCondition :
      (∑ x : OrderedTupleSampler.Tuple m K,
        if x ∈ event then (K.descFactorial m : ℝ≥0∞)⁻¹ else 0) =
      ∑ x : OrderedTupleSampler.Tuple m K,
        if x.val i ∈ S then (K.descFactorial m : ℝ≥0∞)⁻¹ else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hmem : x.val i ∈ S <;> simp [event, hmem]
  calc
    (∑ x : OrderedTupleSampler.Tuple m K,
        if x ∈ event then (K.descFactorial m : ℝ≥0∞)⁻¹ else 0) =
      ∑ x : OrderedTupleSampler.Tuple m K,
        if x.val i ∈ S then (K.descFactorial m : ℝ≥0∞)⁻¹ else 0 := hsumCondition
    _ = ENNReal.ofReal ((S.card : ℝ) / K) := by
      change (∑ tuple ∈ (Finset.univ : Finset (OrderedTupleSampler.Tuple m K)),
        if tuple.val i ∈ S then (K.descFactorial m : ℝ≥0∞)⁻¹ else 0) = _
      rw [← Finset.sum_filter]
      rw [Finset.sum_const, nsmul_eq_mul]
      have hKpos : 0 < K := lt_trans (by omega : 0 < m) hmk
      rw [tuple_coordinate_filter_card hm hmk hKpos i S]
      let c := Fintype.card (TupleFiber i ⟨0, hKpos⟩)
      have hdesc : K.descFactorial m = K * c := by
        simpa [c] using
          (OrderedTupleSampler.card_tuple m K).symm.trans
            (tuple_total_factorization hm hmk i)
      have hc : 0 < c := by
        let tuple : OrderedTupleSampler.Tuple m K :=
          ⟨fun j => ⟨j.val, by omega⟩, by
            intro j k hjk
            have hvalue : (⟨j.val, by omega⟩ : Fin K) = ⟨k.val, by omega⟩ := hjk
            exact Fin.ext (congrArg (fun z : Fin K => z.val) hvalue)⟩
        let swapped : OrderedTupleSampler.Tuple m K :=
          tupleArmSwapEquiv (tuple.val i) ⟨0, hKpos⟩ tuple
        have hfiber : swapped.1 i = (⟨0, hKpos⟩ : Fin K) := by
          change Equiv.swap (tuple.val i) ⟨0, hKpos⟩ (tuple.val i) = _
          exact Equiv.swap_apply_left _ _
        have hnonempty : Nonempty (TupleFiber i ⟨0, hKpos⟩) :=
          ⟨⟨swapped, hfiber⟩⟩
        exact Fintype.card_pos_iff.mpr hnonempty
      have hcancel :
          (S.card : ℝ≥0∞) * (c : ℝ≥0∞) /
              ((K : ℝ≥0∞) * (c : ℝ≥0∞)) =
            (S.card : ℝ≥0∞) / (K : ℝ≥0∞) := by
        exact ENNReal.mul_div_mul_right _ _
          (by exact_mod_cast (Nat.ne_of_gt hc)) (ENNReal.natCast_ne_top _)
      rw [hdesc, Nat.cast_mul, Nat.cast_mul]
      change ((S.card : ℝ≥0∞) * (c : ℝ≥0∞)) *
        ((K : ℝ≥0∞) * (c : ℝ≥0∞))⁻¹ = _
      rw [← div_eq_mul_inv, hcancel]
      rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_div_of_pos (by positivity)]
      simp only [ENNReal.ofReal_natCast]

private abbrev SliceOutput (p : Parameters) :=
  (Slot × Follower p.m) × OrderedTupleSampler.Tuple p.m p.K

private def sliceOutput (p : Parameters) (x : Slice p) : SliceOutput p :=
  ((slotDraw x, selectedFollowerDraw p.two_le_m p.m_lt_K x),
    OrderedTupleSampler.sample p.two_le_m p.m_lt_K x)

private def selectedDrawPair {m K : ℕ}
    (draws : (i : PublicDiscreteDraws.DrawIndex m K) →
      PublicDiscreteDraws.DrawOutput i) :
    Slot × Fin (followerCount m) :=
  (draws .slot, draws .selectedFollower)

private theorem measurable_selectedDrawPair {m K : ℕ} :
    Measurable (selectedDrawPair (m := m) (K := K)) := by
  exact (measurable_pi_apply PublicDiscreteDraws.DrawIndex.slot).prodMk
    (measurable_pi_apply PublicDiscreteDraws.DrawIndex.selectedFollower)

private theorem measurable_sliceOutput (p : Parameters) :
    Measurable (sliceOutput p : Slice p → SliceOutput p) := by
  exact (PublicDiscreteDraws.measurable_slotDraw.prodMk
      (PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K)).prodMk
    (OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K)

private def sliceServiceSet (p : Parameters) (i : Follower p.m)
    (row : RewardRow p.K) : Set (SliceOutput p) :=
  {z | z.1.1 = downSlot ∧ z.1.2 = i ∧
    0 < row.val (receiverArm p.two_le_m i z.2)}

private theorem sliceServiceSet_measurable (p : Parameters) (i : Follower p.m)
    (row : RewardRow p.K) : MeasurableSet (sliceServiceSet p i row) :=
  MeasurableSet.of_discrete

private theorem sliceServiceProbability (p : Parameters) (i : Follower p.m)
    (row : RewardRow p.K) :
    (ContinuousControlSlice.sliceLaw p.m p.K)
      ((sliceOutput p) ⁻¹' sliceServiceSet p i row) =
        ENNReal.ofReal
          (((positiveArms row).card : ℝ) /
            (4 * (d p : ℝ) * p.K)) := by
  classical
  let μ := ContinuousControlSlice.sliceLaw p.m p.K
  let pairDraw : ContinuousControlSlice.Slice p.m p.K → Slot × Follower p.m :=
    fun x => (slotDraw x, selectedFollowerDraw p.two_le_m p.m_lt_K x)
  let tupleDraw : ContinuousControlSlice.Slice p.m p.K → OrderedTupleSampler.Tuple p.m p.K :=
    fun x => OrderedTupleSampler.sampleCube p.m_lt_K
      (PublicDiscreteDraws.tupleInputs x)
  let tupleSet : Set (OrderedTupleSampler.Tuple p.m p.K) :=
    {f | receiverArm p.two_le_m i f ∈ positiveArms row}
  have hgroup := PublicDiscreteDraws.indepFun_drawFamily_tupleInputs
    p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p)
  have hgroup' := hgroup.comp
    (measurable_selectedDrawPair (m := p.m) (K := p.K))
    (OrderedTupleSampler.measurable_sampleCube p.m_lt_K)
  have hpairMap :
      (fun x => selectedDrawPair (PublicDiscreteDraws.drawVector p.two_le_m p.m_lt_K
        (ConstructorDimensions.K_pos p) x)) = pairDraw := by
    funext x
    apply Prod.ext <;> rfl
  have htupleMap :
      OrderedTupleSampler.sampleCube p.m_lt_K ∘ PublicDiscreteDraws.tupleInputs = tupleDraw := by
    funext x
    rfl
  have hdrawTuple : IndepFun pairDraw tupleDraw μ := by
    rw [← hpairMap, ← htupleMap]
    exact hgroup'
  have hpair : μ (pairDraw ⁻¹' {(downSlot, i)}) =
      ENNReal.ofReal (1 / 4) * ENNReal.ofReal (1 / (d p : ℝ)) := by
    have hij : (PublicDiscreteDraws.DrawIndex.slot : PublicDiscreteDraws.DrawIndex p.m p.K) ≠
        PublicDiscreteDraws.DrawIndex.selectedFollower := by
      intro h
      cases h
    have h := (PublicDiscreteDraws.iIndepFun_drawFamily
      p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p)).indepFun hij
    have hmass := h.measure_inter_preimage_eq_mul
      ({downSlot} : Set Slot) ({i} : Set (Fin (d p)))
      (measurableSet_singleton _) (measurableSet_singleton _)
    have hslotEq : PublicDiscreteDraws.drawFamily p.two_le_m p.m_lt_K
        (ConstructorDimensions.K_pos p) .slot = slotDraw := by rfl
    have hselectedEq : PublicDiscreteDraws.drawFamily p.two_le_m p.m_lt_K
        (ConstructorDimensions.K_pos p) .selectedFollower =
          selectedFollowerDraw p.two_le_m p.m_lt_K := by rfl
    rw [hslotEq, hselectedEq] at hmass
    change μ (slotDraw ⁻¹' {downSlot} ∩
      selectedFollowerDraw p.two_le_m p.m_lt_K ⁻¹' {i}) = _ at hmass
    have hevent : pairDraw ⁻¹' {(downSlot, i)} =
        slotDraw ⁻¹' {downSlot} ∩
          selectedFollowerDraw p.two_le_m p.m_lt_K ⁻¹' {i} := by
      ext x
      simp [pairDraw]
    have hslotMass := PublicDiscreteDraws.slotDraw_atom (m := p.m) (K := p.K) downSlot
    have hselectedMass := PublicDiscreteDraws.selectedFollowerDraw_atom p.two_le_m
      p.m_lt_K i
    calc
      μ (pairDraw ⁻¹' {(downSlot, i)}) =
          μ (slotDraw ⁻¹' {downSlot} ∩
            selectedFollowerDraw p.two_le_m p.m_lt_K ⁻¹' {i}) := by rw [hevent]
      _ = μ (slotDraw ⁻¹' {downSlot}) *
          μ (selectedFollowerDraw p.two_le_m p.m_lt_K ⁻¹' {i}) := hmass
      _ = ENNReal.ofReal (1 / 4) * ENNReal.ofReal (1 / (d p : ℝ)) := by
        rw [hslotMass, hselectedMass, slotMass_down, equalMass]
        norm_num [d, PublicDiscreteDraws.followerCount]
  have hinputs : OrderedTupleSampler.tupleInputs (m := p.m) (K := p.K) =
      PublicDiscreteDraws.tupleInputs (m := p.m) (K := p.K) := by
    funext x r
    rfl
  have hsampleEq : OrderedTupleSampler.sample p.two_le_m p.m_lt_K = tupleDraw := by
    funext x
    change OrderedTupleSampler.sampleCube p.m_lt_K
        (OrderedTupleSampler.tupleInputs x) =
      OrderedTupleSampler.sampleCube p.m_lt_K (PublicDiscreteDraws.tupleInputs x)
    rw [hinputs]
  have htuple : μ (tupleDraw ⁻¹' tupleSet) =
      ENNReal.ofReal (((positiveArms row).card : ℝ) / (p.K : ℝ)) := by
    have h := orderedTupleReceiver_uniform p.two_le_m p.m_lt_K
      (followerPlayer p.two_le_m i) (positiveArms row)
    rw [hsampleEq] at h
    simpa [μ, tupleSet, receiverArm] using h
  have hmeasure := hdrawTuple.measure_inter_preimage_eq_mul
    ({(downSlot, i)} : Set (Slot × Follower p.m)) tupleSet
    (MeasurableSet.of_discrete) (MeasurableSet.of_discrete)
  have hevent : (sliceOutput p) ⁻¹' sliceServiceSet p i row =
      pairDraw ⁻¹' {(downSlot, i)} ∩ tupleDraw ⁻¹' tupleSet := by
    ext x
    simp [sliceOutput, sliceServiceSet, pairDraw, tupleDraw, tupleSet,
      positiveArms, and_assoc, hsampleEq]
  rw [hevent, hmeasure, hpair, htuple]
  have hdpos : 0 < (d p : ℝ) := by
    dsimp [d]
    exact_mod_cast Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) p.two_le_m)
  have hKpos : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hnnonneg : 0 ≤ ((positiveArms row).card : ℝ) / p.K := by positivity
  have hpairnonneg : 0 ≤ (1 / 4 : ℝ) * (1 / (d p : ℝ)) := by positivity
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / 4)]
  rw [← ENNReal.ofReal_mul hpairnonneg]
  congr 1
  field_simp

private theorem affineBitProbability {p : Parameters}
    (word : Word (B p)) (bit : Bit) :
    (AffineChannelLaw.jointLaw (B p)).toMeasure
      {sample | affineHash sample word = bit} = (1 : ℝ≥0∞) / 2 := by
  rw [← AffineChannelLaw.eventProbability_eq_measure,
    AffineChannelLaw.affineHash_probability]

private theorem source_unoccupied_iff
    {m K B : ℕ} {a : Assignment m K} (hm : 2 ≤ m) (s : Snapshot a)
    (i : Follower m) (hinv : no_released_while_missing s)
    (row : RewardRow K) (r : RoundInput a B) (hstatus : s.status i = .unoccupied) :
    sourceDownService hm s i row r ↔
      r.slot = downSlot ∧ r.selected = i ∧ i ∈ s.missing ∧
        r.down.bit = 1 ∧ 0 < row.val (r.tuple.val (followerPlayer hm i)) := by
  have hfeedback := ActiveRoundActions.unoccupied_down_feedback hm s r row
  rw [sourceDownService]
  constructor
  · rintro ⟨hslot, hselected, hmember, hbranch⟩
    rcases hbranch with ⟨_, hpositive⟩ | ⟨hwrong, _, _⟩
    · have hselectedMissing : r.selected ∈ s.missing := by simpa [hselected] using hmember
      have hselectedStatus : s.status r.selected = .unoccupied := by
        simpa [hselected] using hstatus
      have hfb := hfeedback hslot hselectedMissing hinv hselectedStatus
      rw [hselected] at hfb
      rw [hfb] at hpositive
      by_cases hbit : r.down.bit = 1
      · exact ⟨hslot, hselected, hmember, hbit, by simpa [hbit] using hpositive⟩
      · have hzero : r.down.bit = 0 := by
          rcases ActiveRoundActions.bit_eq_zero_or_one r.down.bit with hz | ho
          · exact hz
          · exact False.elim (hbit ho)
        rw [hzero] at hpositive
        simp at hpositive
    · simp [hstatus] at hwrong
  · rintro ⟨hslot, hselected, hmember, hbit, hreward⟩
    have hselectedMissing : r.selected ∈ s.missing := by simpa [hselected] using hmember
    have hselectedStatus : s.status r.selected = .unoccupied := by
      simpa [hselected] using hstatus
    have hfb := hfeedback hslot hselectedMissing hinv hselectedStatus
    rw [hselected] at hfb
    have hpositive : 0 < feedback hm s r row (followerPlayer hm i) := by
      rw [hfb]
      simpa [hbit] using hreward
    exact ⟨hslot, hselected, hmember, Or.inl ⟨hstatus, hpositive⟩⟩

private theorem source_pending_iff
    {m K B : ℕ} {a : Assignment m K} (hm : 2 ≤ m) (s : Snapshot a)
    (i : Follower m) (hinv : no_released_while_missing s)
    (row : RewardRow K) (r : RoundInput a B) (hstatus : s.status i = .pending) :
    sourceDownService hm s i row r ↔
      r.slot = downSlot ∧ r.selected = i ∧ i ∈ s.missing ∧
        r.down.bit = 0 ∧ 0 < row.val (r.tuple.val (followerPlayer hm i)) := by
  have hfeedback := ActiveRoundActions.pending_down_coordinator_feedback hm s r row
  rw [sourceDownService]
  constructor
  · rintro ⟨hslot, hselected, hmember, hbranch⟩
    rcases hbranch with ⟨hwrong, _⟩ | ⟨_, hbit, hpositive⟩
    · simp [hstatus] at hwrong
    · have hselectedMissing : r.selected ∈ s.missing := by simpa [hselected] using hmember
      have hselectedStatus : s.status r.selected = .pending := by
        simpa [hselected] using hstatus
      have hfb := hfeedback hslot hselectedMissing hinv hselectedStatus hbit
      rw [hselected] at hfb
      rw [hfb] at hpositive
      exact ⟨hslot, hselected, hmember, hbit, hpositive⟩
  · rintro ⟨hslot, hselected, hmember, hbit, hreward⟩
    have hselectedMissing : r.selected ∈ s.missing := by simpa [hselected] using hmember
    have hselectedStatus : s.status r.selected = .pending := by
      simpa [hselected] using hstatus
    have hfb := hfeedback hslot hselectedMissing hinv hselectedStatus hbit
    rw [hselected] at hfb
    have hpositive : 0 < feedback hm s r row (coordinator hm) := by
      rw [hfb]
      exact hreward
    exact ⟨hslot, hselected, hmember, Or.inr ⟨hstatus, hbit, hpositive⟩⟩

private theorem sourceDownService_iff_output
    (p : Parameters) {a : Assignment p.m p.K} (s : Snapshot a)
    (i : Follower p.m) (hi : i ∈ s.missing)
    (hinv : no_released_while_missing s) (row : RewardRow p.K)
    (word : Word (B p)) (upWord : Word (B p)) (fast : Arm p.K)
    (hfast : ∀ j, fast ≠ a.assigned j)
    (control : TimeControl p) :
    sourceDownService p.two_le_m s i row (roundInput p i word upWord fast hfast control) ↔
      (sliceOutput p control.1).1.1 = downSlot ∧
        (sliceOutput p control.1).1.2 = i ∧
        0 < row.val (receiverArm p.two_le_m i (sliceOutput p control.1).2) ∧
        ((s.status i = .unoccupied ∧
            affineHash (control.2 (downChannel p i)) word = 1) ∨
          (s.status i = .pending ∧
            affineHash (control.2 (downChannel p i)) word = 0)) := by
  have hmissing : s.missing ≠ ∅ := ActiveRoundActions.missing_ne_empty_of_mem s i hi
  have hnotreleased : s.status i ≠ .released := hinv hmissing i
  cases hstatus : s.status i with
  | unoccupied =>
      have h := source_unoccupied_iff p.two_le_m s i hinv row
        (roundInput p i word upWord fast hfast control) hstatus
      constructor
      · intro hsource
        have hfields := h.mp hsource
        rcases hfields with ⟨hslot, hselected, hmember, hbit, hreward⟩
        refine ⟨?_, ?_, ?_, Or.inl ⟨rfl, ?_⟩⟩
        · simpa [roundInput, sliceOutput] using hslot
        · simpa [roundInput, sliceOutput, ContinuousLearningRows.d,
            PublicDiscreteDraws.followerCount] using hselected
        · simpa [roundInput, sliceOutput, receiverArm] using hreward
        · simpa [roundInput, downChannel, ActiveRoundActions.HashedWord.bit] using hbit
      · rintro ⟨hslot, hselected, hreward, hbranch⟩
        rcases hbranch with ⟨hstat, hbit⟩ | ⟨hstat, hbit⟩
        · have hslot' : (roundInput p i word upWord fast hfast control).slot = downSlot := by
            simpa [roundInput, sliceOutput] using hslot
          have hselected' : (roundInput p i word upWord fast hfast control).selected = i := by
            simpa [roundInput, sliceOutput, ContinuousLearningRows.d,
              PublicDiscreteDraws.followerCount] using hselected
          have hbit' : (roundInput p i word upWord fast hfast control).down.bit = 1 := by
            simpa [roundInput, downChannel, ActiveRoundActions.HashedWord.bit] using hbit
          have hreward' : 0 < row.val ((roundInput p i word upWord fast hfast control).tuple.val
              (followerPlayer p.two_le_m i)) := by
            simpa [roundInput, sliceOutput, receiverArm] using hreward
          exact h.mpr ⟨hslot', hselected', hi, hbit', hreward'⟩
        · simp at hstat
  | pending =>
      have h := source_pending_iff p.two_le_m s i hinv row
        (roundInput p i word upWord fast hfast control) hstatus
      constructor
      · intro hsource
        have hfields := h.mp hsource
        rcases hfields with ⟨hslot, hselected, hmember, hbit, hreward⟩
        refine ⟨?_, ?_, ?_, Or.inr ⟨rfl, ?_⟩⟩
        · simpa [roundInput, sliceOutput] using hslot
        · simpa [roundInput, sliceOutput, ContinuousLearningRows.d,
            PublicDiscreteDraws.followerCount] using hselected
        · simpa [roundInput, sliceOutput, receiverArm] using hreward
        · simpa [roundInput, downChannel, ActiveRoundActions.HashedWord.bit] using hbit
      · rintro ⟨hslot, hselected, hreward, hbranch⟩
        rcases hbranch with ⟨hstat, hbit⟩ | ⟨hstat, hbit⟩
        · simp at hstat
        · have hslot' : (roundInput p i word upWord fast hfast control).slot = downSlot := by
            simpa [roundInput, sliceOutput] using hslot
          have hselected' : (roundInput p i word upWord fast hfast control).selected = i := by
            simpa [roundInput, sliceOutput, ContinuousLearningRows.d,
              PublicDiscreteDraws.followerCount] using hselected
          have hbit' : (roundInput p i word upWord fast hfast control).down.bit = 0 := by
            simpa [roundInput, downChannel, ActiveRoundActions.HashedWord.bit] using hbit
          have hreward' : 0 < row.val ((roundInput p i word upWord fast hfast control).tuple.val
              (followerPlayer p.two_le_m i)) := by
            simpa [roundInput, sliceOutput, receiverArm] using hreward
          exact h.mpr ⟨hslot', hselected', hi, hbit', hreward'⟩
  | released =>
      exact False.elim (hnotreleased hstatus)

/-- If an explicitly supplied finite live trace has this fixed constructed round
and snapshot at time `t`, the unoccupied positive-service branch yields the
accepted decoder equation. The two equalities are application inputs: this
lemma does not identify an arbitrary trace with the random process. -/
theorem live_unoccupied_sourceDownService_equation {p : Parameters}
    {a : Assignment p.m p.K}
    (rounds : Fin p.T → LiveRoundData a (B p)) (t : Fin p.T)
    (s : Snapshot a) (i : Follower p.m) (row : RewardRow p.K)
    (word : Word (B p)) (upWord : Word (B p)) (fast : Arm p.K)
    (hfast : ∀ j, fast ≠ a.assigned j) (control : TimeControl p)
    (hsnapshot : s = liveSegment p.two_le_m (List.ofFn rounds |>.take t.val))
    (hinput : (rounds t).input = roundInput p i word upWord fast hfast control)
    (hrewards : (rounds t).rewards = row)
    (hstatus : s.status i = .unoccupied)
    (hservice : sourceDownService p.two_le_m s i row
      (roundInput p i word upWord fast hfast control)) :
    AffineBatchDecoder.equation (control.2 (downChannel p i)) word := by
  rcases hservice with ⟨hslot, hselected, hmissing, hbranch⟩
  have hpositive : 0 < feedback p.two_le_m s
      (roundInput p i word upWord fast hfast control) row (followerPlayer p.two_le_m i) := by
    rcases hbranch with ⟨hbranchStatus, hpos⟩ | ⟨hbranchStatus, _, _⟩
    · simpa [hstatus] using hpos
    · rw [hstatus] at hbranchStatus
      cases hbranchStatus
  have hslot' : (rounds t).input.slot = downSlot := by
    rw [hinput]
    exact hslot
  have hselected' : (rounds t).input.selected = i := by
    rw [hinput]
    exact hselected
  have hmissing' : i ∈
      (liveSegment p.two_le_m (List.ofFn rounds |>.take t.val)).missing := by
    rw [← hsnapshot]
    exact hmissing
  have hstatus' :
      (liveSegment p.two_le_m (List.ofFn rounds |>.take t.val)).status i = .unoccupied := by
    rw [← hsnapshot]
    exact hstatus
  have hpositive' : 0 < feedback p.two_le_m
      (liveSegment p.two_le_m (List.ofFn rounds |>.take t.val))
      (rounds t).input (rounds t).rewards (followerPlayer p.two_le_m i) := by
    rw [← hsnapshot, hinput, hrewards]
    exact hpositive
  have hequation := ActiveObservationBridge.live_unoccupied_down_positive_equation
    p a rounds t i hslot' hselected' hmissing' hstatus' hpositive'
  simpa [hinput, roundInput, downChannel] using hequation

private theorem timeControl_sourceEvent_measurable
    (p : Parameters) {a : Assignment p.m p.K} (s : Snapshot a)
    (i : Follower p.m) (hi : i ∈ s.missing)
    (hinv : no_released_while_missing s) (row : RewardRow p.K)
    (word : Word (B p)) (upWord : Word (B p)) (fast : Arm p.K)
    (hfast : ∀ j, fast ≠ a.assigned j) :
    MeasurableSet {control : TimeControl p |
      sourceDownService p.two_le_m s i row (roundInput p i word upWord fast hfast control)} := by
  have houtput : Measurable (fun control : TimeControl p =>
      (sliceOutput p control.1, control.2 (downChannel p i))) := by
    exact ((measurable_sliceOutput p).comp measurable_fst).prodMk
      ((measurable_pi_apply (downChannel p i)).comp measurable_snd)
  have hs : MeasurableSet
      {z : SliceOutput p × Sample (B p) |
        z.1.1.1 = downSlot ∧ z.1.1.2 = i ∧
          0 < row.val (receiverArm p.two_le_m i z.1.2) ∧
          ((s.status i = .unoccupied ∧ affineHash z.2 word = 1) ∨
            (s.status i = .pending ∧ affineHash z.2 word = 0))} :=
    MeasurableSet.of_discrete
  have hiff := sourceDownService_iff_output p s i hi hinv row word upWord fast hfast
  have heq : {control : TimeControl p |
      sourceDownService p.two_le_m s i row (roundInput p i word upWord fast hfast control)} =
      (fun control : TimeControl p =>
        (sliceOutput p control.1, control.2 (downChannel p i))) ⁻¹'
          {z : SliceOutput p × Sample (B p) |
            z.1.1.1 = downSlot ∧ z.1.1.2 = i ∧
              0 < row.val (receiverArm p.two_le_m i z.1.2) ∧
              ((s.status i = .unoccupied ∧ affineHash z.2 word = 1) ∨
                (s.status i = .pending ∧ affineHash z.2 word = 0))} := by
    ext control
    exact hiff control
  rw [heq]
  exact houtput hs

/-- Exact source event mass under one genuine accepted public-row round.
The fixed DOWN word is used both in the affine hash and in the physical action;
its hash bit is not an assumed Bernoulli marginal. -/
theorem sourceDownService_probability {p : Parameters}
    {a : Assignment p.m p.K} (s : Snapshot a) (i : Follower p.m)
    (hi : i ∈ s.missing) (hinv : no_released_while_missing s)
    (row : RewardRow p.K) (word : Word (B p)) (upWord : Word (B p))
    (fast : Arm p.K)
    (hfast : ∀ j, fast ≠ a.assigned j) :
    (timeControlLaw p)
      {control | sourceDownService p.two_le_m s i row (roundInput p i word upWord fast hfast control)} =
        ENNReal.ofReal
          (((positiveArms row).card : ℝ) /
            (8 * (d p : ℝ) * p.K)) := by
  classical
  let μ := timeControlLaw p
  let output : TimeControl p → SliceOutput p × Sample (B p) :=
    fun control => (sliceOutput p control.1, control.2 (downChannel p i))
  have houtput : Measurable output := by
    exact ((measurable_sliceOutput p).comp measurable_fst).prodMk
      ((measurable_pi_apply (downChannel p i)).comp measurable_snd)
  have houtputLaw : μ.map output =
      ((ContinuousControlSlice.sliceLaw p.m p.K).map (sliceOutput p)).prod
        ((AffineChannelLaw.jointLaw (B p)).toMeasure) := by
    have hind := (ContinuousLearningRows.indepFun_slice_affineSamples p).comp
      (measurable_sliceOutput p) (measurable_pi_apply (downChannel p i))
    have hprod := hind.map_prod_eq_prod_map_map
      ((measurable_sliceOutput p).comp measurable_fst).aemeasurable
      ((measurable_pi_apply (downChannel p i)).comp measurable_snd).aemeasurable
    have hmapChoices : μ.map (fun control => sliceOutput p control.1) =
        (ContinuousControlSlice.sliceLaw p.m p.K).map (sliceOutput p) := by
      calc
        μ.map (fun control => sliceOutput p control.1) =
            (μ.map Prod.fst).map (sliceOutput p) := by
              exact (Measure.map_map (measurable_sliceOutput p) measurable_fst).symm
        _ = _ := by rw [ContinuousLearningRows.map_slice p]
    have hmapSample : μ.map (fun control => control.2 (downChannel p i)) =
        (AffineChannelLaw.jointLaw (B p)).toMeasure :=
      ContinuousLearningRows.map_affineSample p (downChannel p i)
    change μ.map (fun control => (sliceOutput p control.1,
      control.2 (downChannel p i))) = _
    calc
      _ = (μ.map (fun control => sliceOutput p control.1)).prod
          (μ.map (fun control => control.2 (downChannel p i))) := hprod
      _ = _ := by rw [hmapChoices, hmapSample]
  have hiff := sourceDownService_iff_output p s i hi hinv row word upWord fast hfast
  have hset : MeasurableSet
      {z : SliceOutput p × Sample (B p) |
        z.1.1.1 = downSlot ∧ z.1.1.2 = i ∧
          0 < row.val (receiverArm p.two_le_m i z.1.2) ∧
          ((s.status i = .unoccupied ∧ affineHash z.2 word = 1) ∨
            (s.status i = .pending ∧ affineHash z.2 word = 0))} :=
    MeasurableSet.of_discrete
  have heq : {control : TimeControl p |
      sourceDownService p.two_le_m s i row (roundInput p i word upWord fast hfast control)} =
      output ⁻¹'
        {z : SliceOutput p × Sample (B p) |
          z.1.1.1 = downSlot ∧ z.1.1.2 = i ∧
            0 < row.val (receiverArm p.two_le_m i z.1.2) ∧
            ((s.status i = .unoccupied ∧ affineHash z.2 word = 1) ∨
              (s.status i = .pending ∧ affineHash z.2 word = 0))} := by
    ext control
    exact hiff control
  rw [heq, ← Measure.map_apply houtput hset, houtputLaw]
  cases hstatus : s.status i with
  | unoccupied =>
      have hslice : ((ContinuousControlSlice.sliceLaw p.m p.K).map (sliceOutput p))
          (sliceServiceSet p i row) =
            ENNReal.ofReal (((positiveArms row).card : ℝ) /
              (4 * (d p : ℝ) * p.K)) := by
        rw [Measure.map_apply (measurable_sliceOutput p)
          (sliceServiceSet_measurable p i row)]
        exact sliceServiceProbability p i row
      have hbit : (AffineChannelLaw.jointLaw (B p)).toMeasure
          {sample | affineHash sample word = 1} = (1 : ℝ≥0∞) / 2 :=
        affineBitProbability (p := p) word 1
      have hevent :
          {z : SliceOutput p × Sample (B p) |
            z.1.1.1 = downSlot ∧ z.1.1.2 = i ∧
              0 < row.val (receiverArm p.two_le_m i z.1.2) ∧
              affineHash z.2 word = 1} =
          sliceServiceSet p i row ×ˢ {sample | affineHash sample word = 1} := by
        ext z
        simp [sliceServiceSet, and_assoc]
      simp
      rw [hevent, Measure.prod_prod, hslice, hbit]
      have hq : 0 ≤ ((positiveArms row).card : ℝ) / (4 * (d p : ℝ) * p.K) := by
        positivity
      have hhalf : (1 : ℝ≥0∞) / 2 = ENNReal.ofReal (1 / 2 : ℝ) := by
        norm_num [ENNReal.ofReal_div_of_pos]
      rw [hhalf, ← ENNReal.ofReal_mul hq]
      congr 1
      field_simp
      ring
  | pending =>
      have hslice : ((ContinuousControlSlice.sliceLaw p.m p.K).map (sliceOutput p))
          (sliceServiceSet p i row) =
            ENNReal.ofReal (((positiveArms row).card : ℝ) /
              (4 * (d p : ℝ) * p.K)) := by
        rw [Measure.map_apply (measurable_sliceOutput p)
          (sliceServiceSet_measurable p i row)]
        exact sliceServiceProbability p i row
      have hbit : (AffineChannelLaw.jointLaw (B p)).toMeasure
          {sample | affineHash sample word = 0} = (1 : ℝ≥0∞) / 2 :=
        affineBitProbability (p := p) word 0
      have hevent :
          {z : SliceOutput p × Sample (B p) |
            z.1.1.1 = downSlot ∧ z.1.1.2 = i ∧
              0 < row.val (receiverArm p.two_le_m i z.1.2) ∧
              affineHash z.2 word = 0} =
          sliceServiceSet p i row ×ˢ {sample | affineHash sample word = 0} := by
        ext z
        simp [sliceServiceSet, and_assoc]
      simp
      rw [hevent, Measure.prod_prod, hslice, hbit]
      have hq : 0 ≤ ((positiveArms row).card : ℝ) / (4 * (d p : ℝ) * p.K) := by
        positivity
      have hhalf : (1 : ℝ≥0∞) / 2 = ENNReal.ofReal (1 / 2 : ℝ) := by
        norm_num [ENNReal.ofReal_div_of_pos]
      rw [hhalf, ← ENNReal.ofReal_mul hq]
      congr 1
      field_simp
      ring
  | released =>
      have hmissing : s.missing ≠ ∅ := ActiveRoundActions.missing_ne_empty_of_mem s i hi
      exact False.elim (hinv hmissing i hstatus)

/-- The exact service law also holds at each fixed calendar coordinate of an
accepted `LearningRow`. This remains an unconditional one-round marginal. -/
theorem sourceDownService_probability_at {p : Parameters}
    {a : Assignment p.m p.K} (t : Fin p.T) (s : Snapshot a)
    (i : Follower p.m) (hi : i ∈ s.missing)
    (hinv : no_released_while_missing s) (row : RewardRow p.K)
    (word : Word (B p)) (upWord : Word (B p)) (fast : Arm p.K)
    (hfast : ∀ j, fast ≠ a.assigned j) :
    (learningRowLaw p)
      {publicRow | sourceDownService p.two_le_m s i row
        (roundInputAt p t i word upWord fast hfast publicRow)} =
        ENNReal.ofReal
          (((positiveArms row).card : ℝ) /
            (8 * (d p : ℝ) * p.K)) := by
  have hmeas := timeControl_sourceEvent_measurable p s i hi hinv row word upWord fast hfast
  have hmap := ContinuousLearningRows.map_controlAt (p := p) t
  rw [show {publicRow | sourceDownService p.two_le_m s i row
      (roundInputAt p t i word upWord fast hfast publicRow)} =
      controlAt t ⁻¹' {control | sourceDownService p.two_le_m s i row
        (roundInput p i word upWord fast hfast control)} by
        ext publicRow
        rfl]
  rw [← Measure.map_apply (ContinuousLearningRows.measurable_controlAt t) hmeas,
    hmap]
  exact sourceDownService_probability s i hi hinv row word upWord fast hfast

end Bandits.Support.DownServiceProbability

end
