/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapPhysicalInput
public import Bandits.Support.BootstrapPrivateRoundStreams
public import Bandits.Support.BootstrapBlockIsolation
public import Bandits.Support.PrivateRoundFreshness
public import Bandits.Support.BootstrapModeService
public import Bandits.Support.OrderedTupleSampler
public import Bandits.Support.PublicDiscreteDraws
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Actual coordinator DOWN count means

For fixed incoming block data, this file studies the actual
`BootstrapPhysicalBlock.run` on the complete-row/private-coordinate product.
It proves the current DOWN-positive indicator bounds, their calendar-block
sum, and the pointwise block-size bound.

The lower bound uses the actual fresh block activity coins supplied by
`BootstrapPhysicalInput.blockInput`. Its joint event is factored through the
accepted scalar products: all incoming followers are inactive, the current
row slot and coordinator tuple arm have their stated values, and every current
uniform arm used by an incoming follower avoids that tuple arm. The estimate
is for this fixed incoming-state product law; it is not a chronological
conditional expectation.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:638-656`,
`sources/zip4/manuscript/07_public_setup.tex:61-110`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-58`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.BootstrapDownCountMean

open MeasureTheory
open ProbabilityTheory
open ActiveRoundActions
open ConstructorDimensions BootstrapDimensions FiniteBanditModel
open BootstrapPrivateRoundStreams PrivateRoundFreshness
open BootstrapPhysicalBlock BootstrapPhysicalInput
open ContinuousControlSlice PublicDiscreteDraws OrderedTupleSampler
open BootstrapBlockIsolation BootstrapModeService BootstrapBlockConstruction PrivateSourceStreams
open scoped BigOperators ENNReal

abbrev Experiment (p : ConstructorDimensions.Parameters) :=
  CompletePublicTable.CompleteRow p × ExtendedPrivateCoordinates p

variable {p : ConstructorDimensions.Parameters} {s : Fin (n_boot p)}

/-- The actual physical block input, with its row sampled from the fixed
complete-row coordinate and its fresh private draws from the extended law. -/
def physicalInput (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀ j a, (1 : ℝ) ≤
  BootstrapWeightPotential.weight (b_N p) (numerators j) a) (ids : CompletePublicTable.IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (e : Experiment p) :
  BootstrapPhysicalBlock.Input p s :=
  BootstrapPhysicalInput.blockInput p s incoming numerators hpos ids e.1 rewards e.2

/-- The literal DOWN-positive event on the existing run's pre-choice state,
actions, and own physical feedback. -/
def downPositiveEvent (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀ j a, (1 : ℝ) ≤
  BootstrapWeightPotential.weight (b_N p) (numerators j) a) (ids : CompletePublicTable.IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (t : Fin p.T) (a : Fin p.K) (e : Experiment p)
  : Prop :=
  BootstrapPhysicalBlock.slot (physicalInput p s incoming numerators hpos ids rewards e) t =
      downSlot ∧
    BootstrapPhysicalBlock.actions (physicalInput p s incoming numerators hpos ids rewards e)
      (BootstrapPhysicalBlock.run (physicalInput p s incoming numerators hpos ids rewards e)
        t.val) t (coordinator p.two_le_m) = a ∧
    0 < BootstrapPhysicalBlock.feedback
      (physicalInput p s incoming numerators hpos ids rewards e)
      (BootstrapPhysicalBlock.run (physicalInput p s incoming numerators hpos ids rewards e)
        t.val) t (coordinator p.two_le_m)

/-- The literal current indicator `Z_t(a)` on the fixed incoming-state
complete-row/private product law. -/
def downPositiveIndicator (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀ j a, (1 : ℝ) ≤
  BootstrapWeightPotential.weight (b_N p) (numerators j) a) (ids : CompletePublicTable.IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (t : Fin p.T) (a : Fin p.K) (e : Experiment p)
  : ℝ := by
  classical
  exact if downPositiveEvent p s incoming numerators hpos ids rewards t a e then 1 else 0

/-- The rounded-reward support indicator `chi_t(a)`. -/
def rewardSupport (p : ConstructorDimensions.Parameters) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (t : Fin p.T) (a : Fin p.K) : ℝ :=
  if 0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t a)
  then 1 else 0

/-- The actual coordinator count on the calendar block, obtained by summing
the current indicators over precisely that block. -/
def downBlockCount (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀ j a, (1 : ℝ) ≤
  BootstrapWeightPotential.weight (b_N p) (numerators j) a) (ids : CompletePublicTable.IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K) (e : Experiment p) : ℝ :=
  ∑ t ∈ calendarBlock p s,
    downPositiveIndicator p s incoming numerators hpos ids rewards t a e

/-- The rounded-reward support count on the same calendar block. -/
def rewardSupportCount (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K) : ℝ :=
  ∑ t ∈ calendarBlock p s, rewardSupport p rewards t a

/-- The three accepted factor coordinates used to compute the joint lower
event. Activity is sampled from the same block triple that `physicalInput`
installs; current arms use their actual labelled round scalars. -/
def downExperimentFactors (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀ j a, (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N
  p) (numerators j) a) (t : Fin p.T) (e : Experiment p) : ContinuousControlSlice.Slice p.m p.K × ((Fin (p.m - 1) → Bool × Fin p.K × Fin (A_id p)) × (Player p.m → Fin p.K)) :=
  ((e.1.2 t).1,
    (PrivateSourceStreams.blockDrawProfileMap p numerators hpos (e.2.1.1 s),
      fun i => BootstrapPrivateRoundStreams.fullArmScalarDraw p (e.2.2.1 (i, t))))
private def inactiveProfileSet (p : ConstructorDimensions.Parameters) (incoming : Finset (Follower p.m)) : Set (Fin (p.m - 1) → Bool × Fin p.K × Fin (A_id p)) :=
  {profile | ∀ j ∈ incoming, (profile j).1 = false}
private def downTupleSet (p : ConstructorDimensions.Parameters) (a : Fin p.K) : Set (ContinuousControlSlice.Slice p.m p.K) :=
  {u | PublicDiscreteDraws.slotDraw u = downSlot ∧
    (OrderedTupleSampler.sample p.two_le_m p.m_lt_K u).val (coordinator p.two_le_m) = a}
private def tupleFirstScalar (p : ConstructorDimensions.Parameters) (u : ContinuousControlSlice.Scalar) : Fin p.K :=
  PublicDiscreteDraws.equalArmSample p.K (K_pos p) u
private theorem univ_orderEmbOfFin_eq_id (K : ℕ) : (Finset.univ : Finset (Fin K)).orderEmbOfFin (by simp) = OrderEmbedding.id (Fin K) := by
  have h := Finset.orderEmbOfFin_unique'
    (s := (Finset.univ : Finset (Fin K))) (h := by simp)
    (f := OrderEmbedding.id (Fin K)) (fun _ => Finset.mem_univ _)
  exact h.symm
private theorem tuple_coordinator_eq_firstScalar (p : ConstructorDimensions.Parameters) (u : ContinuousControlSlice.Slice p.m p.K) : (OrderedTupleSampler.sample p.two_le_m p.m_lt_K u).val
  (coordinator p.two_le_m) = tupleFirstScalar p (ContinuousControlSlice.coordinate (ContinuousControlSlice.Label.tuple (coordinator p.two_le_m)) u) := by
  have hsource := OrderedTupleSampler.sample_source_equation p.two_le_m
    p.m_lt_K u (coordinator p.two_le_m)
  have hrem : OrderedTupleSampler.remainder
      (OrderedTupleSampler.restrict
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K u) 0 (Nat.zero_le p.m)) =
      (Finset.univ : Finset (Fin p.K)) := by
    simp [OrderedTupleSampler.remainder, OrderedTupleSampler.restrict]
  have hfirst : OrderedTupleSampler.rank p.K (K_pos p)
      (ContinuousControlSlice.coordinate
        (ContinuousControlSlice.Label.tuple (coordinator p.two_le_m)) u) =
      tupleFirstScalar p
        (ContinuousControlSlice.coordinate
          (ContinuousControlSlice.Label.tuple (coordinator p.two_le_m)) u) := by
    have hrank : OrderedTupleSampler.rank p.K (K_pos p)
        (ContinuousControlSlice.coordinate
          (ContinuousControlSlice.Label.tuple (coordinator p.two_le_m)) u) =
        PublicDiscreteDraws.pilotFromScalar p.K (K_pos p)
          (ContinuousControlSlice.coordinate
            (ContinuousControlSlice.Label.tuple (coordinator p.two_le_m)) u) := by
      apply Fin.ext
      rfl
    exact hrank.trans (PublicDiscreteDraws.pilot_eq_equalArmSample (K_pos p) _)
  calc
    (OrderedTupleSampler.sample p.two_le_m p.m_lt_K u).val (coordinator p.two_le_m) =
      (OrderedTupleSampler.remainder
        (OrderedTupleSampler.restrict
          (OrderedTupleSampler.sample p.two_le_m p.m_lt_K u) 0 (Nat.zero_le p.m))).orderEmbOfFin
        (OrderedTupleSampler.card_remainder _)
        (OrderedTupleSampler.rank p.K (K_pos p)
          (u (ContinuousControlSlice.Label.tuple (coordinator p.two_le_m)))) := hsource
    _ = tupleFirstScalar p
        (ContinuousControlSlice.coordinate
          (ContinuousControlSlice.Label.tuple (coordinator p.two_le_m)) u) := by
      simpa [hrem, univ_orderEmbOfFin_eq_id, ContinuousControlSlice.coordinate] using hfirst
private theorem downTupleSet_measurable (p : ConstructorDimensions.Parameters) (a : Fin p.K) : MeasurableSet (downTupleSet p a) := by
  apply (measurableSet_eq_fun
    (PublicDiscreteDraws.measurable_slotDraw (m := p.m) (K := p.K))
    measurable_const).inter
  exact measurableSet_eq_fun
    (measurable_pi_apply (coordinator p.two_le_m) |>.comp
      (measurable_subtype_coe.comp
        (OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K)))
    measurable_const
private theorem slice_downTuple_mass (p : ConstructorDimensions.Parameters) (a : Fin p.K) : (ContinuousControlSlice.sliceLaw p.m p.K).real (downTupleSet p a) = (1 / 4 : ℝ) * (1 / (p.K : ℝ)) := by
  classical
  let labels : Fin 2 → ContinuousControlSlice.Label p.m p.K := fun i =>
    if i.val = 0 then ContinuousControlSlice.Label.slot
    else ContinuousControlSlice.Label.tuple (coordinator p.two_le_m)
  have hlabels : Function.Injective labels := by
    intro i j hij
    fin_cases i
    · fin_cases j
      · rfl
      · cases hij
    · fin_cases j
      · cases hij
      · rfl
  have hcoords := (ContinuousControlSlice.iIndepFun_coordinate p.m p.K).precomp
    (g := labels) hlabels
  have hscalarIndep : IndepFun
      (ContinuousControlSlice.coordinate (labels 0))
      (ContinuousControlSlice.coordinate (labels 1))
      (ContinuousControlSlice.sliceLaw p.m p.K) := by
    exact hcoords.indepFun (by decide)
  have hslotMap : Measurable (ContinuousCategorical.sample (by decide)
      PublicDiscreteDraws.slotMass PublicDiscreteDraws.slotMass_sum) :=
    ContinuousCategorical.measurable_sample (by decide)
      PublicDiscreteDraws.slotMass_nonneg PublicDiscreteDraws.slotMass_sum
  have htupleMap : Measurable (tupleFirstScalar p) := by
    change Measurable (PublicDiscreteDraws.equalArmSample p.K (K_pos p))
    exact ContinuousCategorical.measurable_sample (K_pos p)
      (PublicDiscreteDraws.equalMass_nonneg p.K)
      (PublicDiscreteDraws.equalMass_sum p.K (K_pos p))
  have hdrawIndep := hscalarIndep.comp hslotMap htupleMap
  have hslotMarg :
      (ContinuousControlSlice.sliceLaw p.m p.K)
        ((fun u => ContinuousCategorical.sample (by decide)
          PublicDiscreteDraws.slotMass PublicDiscreteDraws.slotMass_sum
          (ContinuousControlSlice.coordinate (labels 0) u)) ⁻¹' {downSlot}) =
        ENNReal.ofReal (1 / 4 : ℝ) := by
    have hfun : (fun u : ContinuousControlSlice.Slice p.m p.K =>
        ContinuousCategorical.sample (by decide) PublicDiscreteDraws.slotMass
          PublicDiscreteDraws.slotMass_sum (ContinuousControlSlice.coordinate (labels 0) u)) =
        PublicDiscreteDraws.slotDraw := by
      funext u
      simp [labels, PublicDiscreteDraws.slotDraw,
        ContinuousControlSlice.coordinate]
    rw [hfun, PublicDiscreteDraws.slotDraw_atom]
    norm_num [PublicDiscreteDraws.slotPMF, PublicDiscreteDraws.slotMass_down,
      ContinuousCategorical.massPMF_apply]
  have htupleMarg :
      (ContinuousControlSlice.sliceLaw p.m p.K)
        ((tupleFirstScalar p ∘ ContinuousControlSlice.coordinate (labels 1)) ⁻¹' {a}) =
        ENNReal.ofReal (1 / (p.K : ℝ)) := by
    have hpre : (tupleFirstScalar p ∘ ContinuousControlSlice.coordinate (labels 1)) ⁻¹' {a} =
        ContinuousControlSlice.coordinate (labels 1) ⁻¹' (tupleFirstScalar p ⁻¹' {a}) := rfl
    rw [hpre, ← Measure.map_apply
      (ContinuousControlSlice.measurable_coordinate (labels 1))
      ((measurableSet_singleton a).preimage htupleMap),
      ContinuousControlSlice.map_coordinate]
    change ContinuousControlSlice.scalarLaw (tupleFirstScalar p ⁻¹' {a}) = _
    rw [ContinuousControlSlice.scalarLaw_eq_categorical_uniform]
    change ContinuousCategorical.uniform
      ((PublicDiscreteDraws.equalArmSample p.K (K_pos p)) ⁻¹' {a}) = _
    exact ContinuousCategorical.uniform_sample_singleton (K_pos p)
      (PublicDiscreteDraws.equalMass_nonneg p.K)
      (PublicDiscreteDraws.equalMass_sum p.K (K_pos p)) a
  have hsets : downTupleSet p a =
      (fun u => ContinuousCategorical.sample (by decide)
        PublicDiscreteDraws.slotMass PublicDiscreteDraws.slotMass_sum
        (ContinuousControlSlice.coordinate (labels 0) u)) ⁻¹' {downSlot} ∩
      (tupleFirstScalar p ∘ ContinuousControlSlice.coordinate (labels 1)) ⁻¹' {a} := by
    ext u
    simp only [downTupleSet, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff]
    rw [show labels 0 = ContinuousControlSlice.Label.slot by rfl,
      show labels 1 = ContinuousControlSlice.Label.tuple (coordinator p.two_le_m) by
        simp [labels]]
    rw [tuple_coordinator_eq_firstScalar]
    simp [PublicDiscreteDraws.slotDraw]
  rw [hsets, Measure.real]
  have hind := hdrawIndep.measure_inter_preimage_eq_mul
    {downSlot} {a} (measurableSet_singleton downSlot) (measurableSet_singleton a)
  have hslotId : (fun u : ContinuousControlSlice.Slice p.m p.K =>
      ContinuousCategorical.sample (by decide) PublicDiscreteDraws.slotMass
        PublicDiscreteDraws.slotMass_sum (ContinuousControlSlice.coordinate (labels 0) u)) =
      fun u => ContinuousCategorical.sample (by decide) PublicDiscreteDraws.slotMass
        PublicDiscreteDraws.slotMass_sum
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.slot u) := by
    funext u
    simp [labels]
  have htupleId : (tupleFirstScalar p ∘ ContinuousControlSlice.coordinate (labels 1)) =
      fun u => tupleFirstScalar p
        (ContinuousControlSlice.coordinate
          (ContinuousControlSlice.Label.tuple (coordinator p.two_le_m)) u) := by
    funext u
    simp [labels]
  change ((ContinuousControlSlice.sliceLaw p.m p.K)
      ((ContinuousCategorical.sample (by decide) PublicDiscreteDraws.slotMass
        PublicDiscreteDraws.slotMass_sum ∘ ContinuousControlSlice.coordinate (labels 0)) ⁻¹'
        {downSlot} ∩
        (tupleFirstScalar p ∘ ContinuousControlSlice.coordinate (labels 1)) ⁻¹' {a})).toReal = _
  have hslotMarg' :
      (ContinuousControlSlice.sliceLaw p.m p.K)
        ((ContinuousCategorical.sample (by decide) PublicDiscreteDraws.slotMass
          PublicDiscreteDraws.slotMass_sum ∘ ContinuousControlSlice.coordinate (labels 0)) ⁻¹'
          {downSlot}) = ENNReal.ofReal (1 / 4 : ℝ) := by
    have hset :
        (ContinuousCategorical.sample (by decide) PublicDiscreteDraws.slotMass
          PublicDiscreteDraws.slotMass_sum ∘ ContinuousControlSlice.coordinate (labels 0)) ⁻¹'
            {downSlot} =
          (fun u => ContinuousCategorical.sample (by decide) PublicDiscreteDraws.slotMass
            PublicDiscreteDraws.slotMass_sum
            (ContinuousControlSlice.coordinate (labels 0) u)) ⁻¹' {downSlot} := by
      ext u
      rfl
    rw [hset]
    exact hslotMarg
  rw [hind, hslotMarg', htupleMarg]
  rw [ENNReal.toReal_mul]
  norm_num
private def uniformAvoidSet (p : ConstructorDimensions.Parameters) (incoming : Finset (Follower p.m)) (a : Fin p.K) : Set (Player p.m → Fin p.K) :=
  {arms | ∀ j ∈ incoming, arms (PublicDiscreteDraws.followerPlayer p.two_le_m j) ≠ a}
private theorem incoming_card_le_followerCount (p : ConstructorDimensions.Parameters) (incoming : Finset (Follower p.m)) : incoming.card ≤ p.m - 1 := by
  have hcard := Finset.card_le_univ incoming
  change incoming.card ≤ Fintype.card (Fin (p.m - 1)) at hcard
  rw [Fintype.card_fin] at hcard
  exact hcard

/-- Exact mass of the fresh activity-coin event on the incoming set, obtained
from the accepted fixed-state sampler pushforward. -/
theorem privateBlockProfile_all_inactive_probability (p : ConstructorDimensions.Parameters) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀ j a, (1 :
  ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a) : privateBlockProfileEventProbability p numerators hpos (fun profile => ∀ j ∈ incoming, (profile j).1 = false) = (1 - 1 /
  (p.m : ℝ)) ^ incoming.card := by
  classical
  let U : Finset (Fin (p.m - 1)) := incoming
  change privateBlockProfileEventProbability p numerators hpos
    (fun profile => ∀ j ∈ U, (profile j).1 = false) = _
  rw [privateBlockProfileEventProbability_forall p numerators hpos
    (fun j outcome => j ∈ U → (outcome.1 = false))]
  have hmass (j : Fin (p.m - 1)) :
      privateBlockDrawEventMass p (numerators j) (hpos j)
        (fun outcome => j ∈ U → outcome.1 = false) =
      if j ∈ U then activityProbability p false else 1 := by
    by_cases hj : j ∈ U
    · have hcondition : (fun outcome : Bool × Fin p.K × Fin (A_id p) =>
          j ∈ U → outcome.1 = false) = fun outcome => outcome.1 = false := by
        funext outcome
        simp [hj]
      rw [hcondition]
      unfold privateBlockDrawEventMass
      rw [if_pos hj]
      have hconvert :
          (∑ outcome : Bool × Fin p.K × Fin (A_id p),
            @ite ℝ (outcome.1 = false) (Classical.propDecidable (outcome.1 = false))
              (privateBlockDrawLaw p (numerators j) (hpos j) outcome).toReal 0) =
          ∑ outcome : Bool × Fin p.K × Fin (A_id p),
            @ite ℝ (outcome.1 = false) (instDecidableEqBool outcome.1 false)
              (privateBlockDrawLaw p (numerators j) (hpos j) outcome).toReal 0 := by
        apply Finset.sum_congr rfl
        intro outcome houtcome
        by_cases h : outcome.1 = false <;> simp [h]
      exact hconvert.trans
        (privateBlockDrawLaw_inactive_event_mass p (numerators j) (hpos j))
    · rw [if_neg hj]
      have hcondition : (fun outcome : Bool × Fin p.K × Fin (A_id p) =>
          j ∈ U → outcome.1 = false) = fun _ => True := by
        funext outcome
        simp [hj]
      rw [hcondition]
      unfold privateBlockDrawEventMass
      simp [privateBlockDrawLaw_real_mass_sum_eq_one]
  simp_rw [hmass]
  rw [Finset.prod_ite_mem_eq]
  simp only [activityProbability, Bool.false_eq_true, ↓reduceIte]
  rw [Finset.prod_const (s := U)]
  rfl

/-- The actual fresh block activity coins jointly leave every incoming
follower inactive with mass at least one quarter, including empty `incoming`.
-/
theorem privateBlockProfile_all_inactive_ge_quarter (p : ConstructorDimensions.Parameters) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀ j a, (1 :
  ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a) : (1 / 4 : ℝ) ≤ privateBlockProfileEventProbability p numerators hpos (fun profile => ∀ j ∈ incoming, (profile j).1 = false) := by
  rw [privateBlockProfile_all_inactive_probability]
  have hcard := incoming_card_le_followerCount p incoming
  have hmpos : (0 : ℝ) < (p.m : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
  have hmoneNat : 1 ≤ p.m := le_trans (by decide) p.two_le_m
  have hmone : (1 : ℝ) ≤ (p.m : ℝ) := by exact_mod_cast hmoneNat
  have hqnonneg : 0 ≤ 1 - 1 / (p.m : ℝ) := by
    have hi : 1 / (p.m : ℝ) ≤ 1 := by
      rw [div_le_one hmpos]
      exact hmone
    linarith
  have hqle : 1 - 1 / (p.m : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (p.m : ℝ) := by positivity
    linarith
  let q : ℝ := 1 + ((p.m - 1 : ℕ) : ℝ)⁻¹
  have hq : 1 - 1 / (p.m : ℝ) = q⁻¹ := by
    dsimp [q]
    have hmoneNat : 1 ≤ p.m := le_trans (by decide) p.two_le_m
    have hsub : ((p.m - 1 : ℕ) : ℝ) = (p.m : ℝ) - 1 := by
      rw [Nat.cast_sub hmoneNat]
      norm_num
    have hsubpos : (0 : ℝ) < (p.m : ℝ) - 1 := by
      have hp : 1 < p.m := lt_of_lt_of_le (by decide) p.two_le_m
      exact sub_pos.mpr (by exact_mod_cast hp)
    rw [hsub]
    field_simp [hmpos.ne', hsubpos.ne']
    ring
  have hqbase : 1 ≤ q := by
    dsimp [q]
    exact le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hqpow : q ^ (p.m - 1) < 3 := by
    have hpow : q ^ (p.m - 1) ≤ Real.exp 1 := by
      dsimp [q]
      exact Real.one_add_inv_pow_le_exp
    exact hpow.trans_lt Real.exp_one_lt_three
  have hinv : (1 / 3 : ℝ) < (q ^ (p.m - 1))⁻¹ := by
    simpa [one_div] using one_div_lt_one_div_of_lt
      (pow_pos (by linarith [hqbase]) _) hqpow
  have hfull : (1 / 4 : ℝ) ≤ (1 - 1 / (p.m : ℝ)) ^ (p.m - 1) := by
    have hEq : (1 - 1 / (p.m : ℝ)) ^ (p.m - 1) = (q ^ (p.m - 1))⁻¹ := by
      rw [hq, inv_pow]
    rw [hEq]
    exact (by norm_num : (1 / 4 : ℝ) ≤ 1 / 3).trans hinv.le
  calc
    (1 / 4 : ℝ) ≤ (1 - 1 / (p.m : ℝ)) ^ (p.m - 1) := hfull
    _ ≤ (1 - 1 / (p.m : ℝ)) ^ incoming.card :=
      pow_le_pow_of_le_one hqnonneg hqle hcard
private theorem fullArmScalarDraw_law (p : ConstructorDimensions.Parameters) : ContinuousCategorical.uniform.map (BootstrapPrivateRoundStreams.fullArmScalarDraw p) =
  BootstrapModeService.privateArmMeasure p := by
  apply Measure.ext_of_singleton
  intro a
  rw [BootstrapPrivateRoundStreams.fullArmScalarDraw_map_atom,
    BootstrapModeService.privateArmMeasure,
    PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a)]
  simp [PublicDiscreteDraws.pilotPMF, ContinuousCategorical.massPMF_apply,
    PublicDiscreteDraws.equalMass]
private theorem measurePreserving_currentUniformArms (p : ConstructorDimensions.Parameters) : MeasurePreserving (fun x : PrivateRoundFreshness.CurrentRoundScalars p => fun i =>
  BootstrapPrivateRoundStreams.fullArmScalarDraw p (x i)) (PrivateRoundFreshness.currentRoundScalarLaw p) (BootstrapModeService.privateArmVectorMeasure p) := by
  have hmap :
      (Measure.pi (fun _ : Fin p.m => ContinuousCategorical.uniform)).map
        (fun x i => BootstrapPrivateRoundStreams.fullArmScalarDraw p (x i)) =
      Measure.pi (fun _ : Fin p.m =>
        ContinuousCategorical.uniform.map (BootstrapPrivateRoundStreams.fullArmScalarDraw p)) := by
    exact Measure.pi_map_pi (fun _ =>
      (BootstrapPrivateRoundStreams.measurable_fullArmScalarDraw p).aemeasurable)
  refine ⟨?_, ?_⟩
  · exact measurable_pi_iff.mpr fun i =>
      (BootstrapPrivateRoundStreams.measurable_fullArmScalarDraw p).comp
        (measurable_pi_apply i)
  · change (Measure.pi (fun _ : Fin p.m => ContinuousCategorical.uniform)).map
      (fun x i => BootstrapPrivateRoundStreams.fullArmScalarDraw p (x i)) = _
    rw [hmap]
    congr 1
    funext i
    exact fullArmScalarDraw_law p

private theorem measurePreserving_privateDownFactors (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀ j a, (1 : ℝ) ≤
  BootstrapWeightPotential.weight (b_N p) (numerators j) a) (t : Fin p.T) : MeasurePreserving (fun coordinates : ExtendedPrivateCoordinates p => (PrivateSourceStreams.blockDrawProfileMap p
  numerators hpos (coordinates.1.1 s), fun i => BootstrapPrivateRoundStreams.fullArmScalarDraw p (coordinates.2.1 (i, t)))) (BootstrapPrivateRoundStreams.extendedPrivateLaw p)
  ((BootstrapBlockIsolation.privateBlockProfileLaw p numerators hpos).toMeasure.prod (BootstrapModeService.privateArmVectorMeasure p)) := by
  let hsplit := PrivateRoundFreshness.extendedPrivateRoundSplit_measurePreserving p t
  let hprofile : MeasurePreserving
      (fun view : PrivateRoundFreshness.PastView p t =>
        PrivateSourceStreams.blockDrawProfileMap p numerators hpos (view.1.1 s))
      (PrivateRoundFreshness.pastViewLaw p t)
      (BootstrapBlockIsolation.privateBlockProfileLaw p numerators hpos).toMeasure := by
    let hBase : MeasurePreserving
        (fun z : PrivateSourceStreams.PrivateCoordinates p =>
          PrivateSourceStreams.blockDrawProfileMap p numerators hpos (z.1 s))
        (PrivateSourceStreams.privateCoordinatesLaw p)
        (BootstrapBlockIsolation.privateBlockProfileLaw p numerators hpos).toMeasure := by
      have hEval : MeasurePreserving
          (fun z : PrivateSourceStreams.FollowerBlockInputs p => z s)
          (PrivateSourceStreams.followerBlockInputsLaw p)
          (PrivateSourceStreams.blockScalarProfileLaw p) := by
        change MeasurePreserving (Function.eval s)
          (Measure.pi (fun _ : Fin (n_boot p) => PrivateSourceStreams.blockScalarProfileLaw p))
          (PrivateSourceStreams.blockScalarProfileLaw p)
        exact measurePreserving_eval _ s
      have hDraw : MeasurePreserving
          (PrivateSourceStreams.blockDrawProfileMap p numerators hpos)
          (PrivateSourceStreams.blockScalarProfileLaw p)
          (BootstrapBlockIsolation.privateBlockProfileLaw p numerators hpos).toMeasure :=
        ⟨PrivateSourceStreams.measurable_blockDrawProfileMap p numerators hpos,
          PrivateSourceStreams.blockDrawProfileMap_law p numerators hpos⟩
      exact (hDraw.comp hEval).comp measurePreserving_fst
    exact hBase.comp measurePreserving_fst
  let hCurrent : MeasurePreserving
      (fun x : PrivateRoundFreshness.CurrentRoundScalars p =>
        fun i => BootstrapPrivateRoundStreams.fullArmScalarDraw p (x i))
      (PrivateRoundFreshness.currentRoundScalarLaw p)
      (BootstrapModeService.privateArmVectorMeasure p) :=
    measurePreserving_currentUniformArms p
  have hCurrentFuture : MeasurePreserving
      (fun z : PrivateRoundFreshness.CurrentRoundScalars p ×
        PrivateRoundFreshness.FutureRoundScalars p t =>
          fun i => BootstrapPrivateRoundStreams.fullArmScalarDraw p (z.1 i))
      ((PrivateRoundFreshness.currentRoundScalarLaw p).prod
        (PrivateRoundFreshness.futureRoundScalarLaw p t))
      (BootstrapModeService.privateArmVectorMeasure p) :=
    hCurrent.comp measurePreserving_fst
  have hPair : MeasurePreserving
      (fun z : PrivateRoundFreshness.PastView p t ×
        (PrivateRoundFreshness.CurrentRoundScalars p ×
          PrivateRoundFreshness.FutureRoundScalars p t) =>
        (PrivateSourceStreams.blockDrawProfileMap p numerators hpos (z.1.1.1 s),
          fun i => BootstrapPrivateRoundStreams.fullArmScalarDraw p (z.2.1 i)))
      ((PrivateRoundFreshness.pastViewLaw p t).prod
        ((PrivateRoundFreshness.currentRoundScalarLaw p).prod
          (PrivateRoundFreshness.futureRoundScalarLaw p t)))
      ((BootstrapBlockIsolation.privateBlockProfileLaw p numerators hpos).toMeasure.prod
        (BootstrapModeService.privateArmVectorMeasure p)) :=
    hprofile.prod hCurrentFuture
  have hFinal := hPair.comp hsplit
  have hfun :
      (fun coordinates : ExtendedPrivateCoordinates p =>
        (PrivateSourceStreams.blockDrawProfileMap p numerators hpos
          (coordinates.1.1 s),
          fun i => BootstrapPrivateRoundStreams.fullArmScalarDraw p
            (coordinates.2.1 (i, t)))) =
      (fun z => (PrivateSourceStreams.blockDrawProfileMap p numerators hpos
        (z.1.1.1 s), fun i => BootstrapPrivateRoundStreams.fullArmScalarDraw p (z.2.1 i))) ∘
        PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p t := by
    funext coordinates
    rfl
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hFinal.measurable
  · rw [hfun]
    exact hFinal.map_eq

/-- The exact joint pushforward of the fixed incoming-state experiment onto
the current row slice, actual block draw profile, and current uniform arms. -/
theorem measurePreserving_downExperimentFactors (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀ j a, (1 : ℝ) ≤
  BootstrapWeightPotential.weight (b_N p) (numerators j) a) (t : Fin p.T) : MeasurePreserving (downExperimentFactors p s numerators hpos t) ((CompletePublicTable.completeRowMeasure p).prod
  (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) ((ContinuousControlSlice.sliceLaw p.m p.K).prod ((BootstrapBlockIsolation.privateBlockProfileLaw p numerators hpos).toMeasure.prod
  (BootstrapModeService.privateArmVectorMeasure p))) := by
  have hrow : MeasurePreserving
      (fun row : CompletePublicTable.CompleteRow p => (row.2 t).1)
      (CompletePublicTable.completeRowMeasure p)
      (ContinuousControlSlice.sliceLaw p.m p.K) := by
    have hComplete : MeasurePreserving Prod.snd
        (CompletePublicTable.completeRowMeasure p)
        (ContinuousLearningRows.learningRowLaw p) := by
      change MeasurePreserving Prod.snd
        ((CompletePublicTable.forwardRowMeasure p).prod
          (ContinuousLearningRows.learningRowLaw p)) _
      exact measurePreserving_snd
    change MeasurePreserving
      (fun row : CompletePublicTable.CompleteRow p => ContinuousLearningRows.sliceAt t row.2)
      (CompletePublicTable.completeRowMeasure p) _
    exact (ContinuousLearningRows.measurePreserving_sliceAt t).comp hComplete
  have hprivate := measurePreserving_privateDownFactors p s numerators hpos t
  change MeasurePreserving
    (Prod.map (fun row : CompletePublicTable.CompleteRow p => (row.2 t).1)
      (fun coordinates : ExtendedPrivateCoordinates p =>
        (PrivateSourceStreams.blockDrawProfileMap p numerators hpos
          (coordinates.1.1 s),
          fun i => BootstrapPrivateRoundStreams.fullArmScalarDraw p
            (coordinates.2.1 (i, t)))))
    _ _
  exact hrow.prod hprivate

private def downActionProfile (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀ j a, (1 : ℝ)
  ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a) (ids : CompletePublicTable.IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (t : Fin p.T) (e : Experiment p) :
  FiniteBanditModel.ActionProfile p.m p.K :=
  fun i => if hi : i = coordinator p.two_le_m then
      (BootstrapPhysicalBlock.tuple
        (physicalInput p s incoming numerators hpos ids rewards e) t).val i
    else if hj : followerIndex p.two_le_m i hi ∈ incoming then
      BootstrapPhysicalBlock.uninformedAction
        (physicalInput p s incoming numerators hpos ids rewards e) t
        ⟨followerIndex p.two_le_m i hi, hj⟩
    else (BootstrapPhysicalBlock.tuple
      (physicalInput p s incoming numerators hpos ids rewards e) t).val i

private theorem measurable_downActionProfile (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos :
  ∀ j a, (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a) (ids : CompletePublicTable.IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (t : Fin p.T) : Measurable
  (downActionProfile p s incoming numerators hpos ids rewards t) := by
  classical
  apply measurable_pi_iff.mpr
  intro i
  rcases ActiveRoundActions.player_cases p.two_le_m i with hcoord | ⟨j, hj⟩
  · subst i
    have hslice : Measurable (fun e : Experiment p => (e.1.2 t).1) := by
      exact measurable_fst.comp <| (measurable_pi_apply t).comp <|
        measurable_snd.comp measurable_fst
    have htuple : Measurable (fun e : Experiment p =>
        BootstrapPhysicalBlock.tuple
          (physicalInput p s incoming numerators hpos ids rewards e) t) := by
      change Measurable (fun e : Experiment p =>
        OrderedTupleSampler.sample p.two_le_m p.m_lt_K ((e.1.2 t).1))
      exact (OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K).comp hslice
    change Measurable (fun e : Experiment p =>
      (BootstrapPhysicalBlock.tuple
        (physicalInput p s incoming numerators hpos ids rewards e) t).val
        (coordinator p.two_le_m))
    exact (measurable_pi_apply (coordinator p.two_le_m)).comp
      (measurable_subtype_coe.comp htuple)
  · subst i
    by_cases hjin : j ∈ incoming
    · let j' : {j // j ∈ incoming} := ⟨j, hjin⟩
      have hprofile : Measurable (fun e : Experiment p =>
          PrivateSourceStreams.blockDrawProfileMap p numerators hpos (e.2.1.1 s)) := by
        exact (PrivateSourceStreams.measurable_blockDrawProfileMap p numerators hpos).comp
          ((measurable_pi_apply s).comp
            (measurable_fst.comp (measurable_fst.comp measurable_snd)))
      have hentry : Measurable (fun e : Experiment p =>
          PrivateSourceStreams.blockDrawProfileMap p numerators hpos
            (e.2.1.1 s) (sourceFollowerIndex p j)) :=
        (measurable_pi_apply (sourceFollowerIndex p j)).comp hprofile
      have hactive : Measurable (fun e : Experiment p =>
          (PrivateSourceStreams.blockDrawProfileMap p numerators hpos
            (e.2.1.1 s) (sourceFollowerIndex p j)).1) := measurable_fst.comp hentry
      have hheld : Measurable (fun e : Experiment p =>
          ((PrivateSourceStreams.blockDrawProfileMap p numerators hpos
            (e.2.1.1 s) (sourceFollowerIndex p j)).2).1) :=
        measurable_fst.comp (measurable_snd.comp hentry)
      have hid : Measurable (fun e : Experiment p =>
          (ids ((PrivateSourceStreams.blockDrawProfileMap p numerators hpos
            (e.2.1.1 s) (sourceFollowerIndex p j)).2).2 t)) := by
        have hprivateID : Measurable (fun e : Experiment p =>
            ((PrivateSourceStreams.blockDrawProfileMap p numerators hpos
              (e.2.1.1 s) (sourceFollowerIndex p j)).2).2) :=
          measurable_snd.comp (measurable_snd.comp hentry)
        exact (Measurable.of_discrete (f := fun u : Fin (A_id p) => ids u t)).comp
          hprivateID
      have huniform : Measurable (fun e : Experiment p =>
          BootstrapPrivateRoundStreams.fullArmScalarDraw p (e.2.2.1
            (PublicDiscreteDraws.followerPlayer p.two_le_m j, t))) := by
        exact (BootstrapPrivateRoundStreams.measurable_fullArmScalarDraw p).comp
          ((measurable_pi_apply (PublicDiscreteDraws.followerPlayer p.two_le_m j, t)).comp
            (measurable_fst.comp (measurable_snd.comp measurable_snd)))
      have havoid : Measurable (fun e : Experiment p =>
          (BootstrapPhysicalInput.followerAvoidArmValueMap p s incoming numerators hpos
            e.2 j' t)) := by
        exact (BootstrapPhysicalInput.measurable_followerAvoidArmValueMap_at
          p s incoming numerators hpos j' t).comp measurable_snd
      have hactiveSet : MeasurableSet {e : Experiment p |
          (PrivateSourceStreams.blockDrawProfileMap p numerators hpos
            (e.2.1.1 s) (sourceFollowerIndex p j)).1 = true} :=
        measurableSet_eq_fun hactive measurable_const
      have hidSet : MeasurableSet {e : Experiment p |
          ids ((PrivateSourceStreams.blockDrawProfileMap p numerators hpos
            (e.2.1.1 s) (sourceFollowerIndex p j)).2).2 t = true} :=
        measurableSet_eq_fun hid measurable_const
      have hinner : Measurable (fun e : Experiment p =>
          if ids ((PrivateSourceStreams.blockDrawProfileMap p numerators hpos
              (e.2.1.1 s) (sourceFollowerIndex p j)).2).2 t then
            BootstrapPhysicalInput.followerAvoidArmValueMap p s incoming numerators hpos
              e.2 j' t
          else ((PrivateSourceStreams.blockDrawProfileMap p numerators hpos
              (e.2.1.1 s) (sourceFollowerIndex p j)).2).1) :=
        Measurable.ite hidSet havoid hheld
      have houter : Measurable (fun e : Experiment p =>
          if (PrivateSourceStreams.blockDrawProfileMap p numerators hpos
              (e.2.1.1 s) (sourceFollowerIndex p j)).1 then
            if ids ((PrivateSourceStreams.blockDrawProfileMap p numerators hpos
                (e.2.1.1 s) (sourceFollowerIndex p j)).2).2 t then
              BootstrapPhysicalInput.followerAvoidArmValueMap p s incoming numerators hpos
                e.2 j' t
            else ((PrivateSourceStreams.blockDrawProfileMap p numerators hpos
                (e.2.1.1 s) (sourceFollowerIndex p j)).2).1
          else BootstrapPrivateRoundStreams.fullArmScalarDraw p (e.2.2.1
            (PublicDiscreteDraws.followerPlayer p.two_le_m j, t))) :=
        Measurable.ite hactiveSet hinner huniform
      have hnotcoord : PublicDiscreteDraws.followerPlayer (m := p.m) p.two_le_m j ≠
          ActiveRoundActions.coordinator p.two_le_m :=
        ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m j
      have hindex : ActiveRoundActions.followerIndex p.two_le_m
          (PublicDiscreteDraws.followerPlayer (m := p.m) p.two_le_m j) hnotcoord = j :=
        ActiveRoundActions.followerIndex_followerPlayer p.two_le_m j hnotcoord
      let jIndex : {j // j ∈ incoming} :=
        ⟨ActiveRoundActions.followerIndex p.two_le_m
          (PublicDiscreteDraws.followerPlayer (m := p.m) p.two_le_m j) hnotcoord,
          by simpa [hindex] using hjin⟩
      have havoidIndex : Measurable (fun e : Experiment p =>
          BootstrapPhysicalInput.followerAvoidArmValueMap p s incoming numerators hpos
            e.2 jIndex t) := by
        exact (BootstrapPhysicalInput.measurable_followerAvoidArmValueMap_at
          p s incoming numerators hpos jIndex t).comp measurable_snd
      have hinnerIndex : Measurable (fun e : Experiment p =>
          if ids ((PrivateSourceStreams.blockDrawProfileMap p numerators hpos
              (e.2.1.1 s) (sourceFollowerIndex p j)).2).2 t then
            BootstrapPhysicalInput.followerAvoidArmValueMap p s incoming numerators hpos
              e.2 jIndex t
          else ((PrivateSourceStreams.blockDrawProfileMap p numerators hpos
              (e.2.1.1 s) (sourceFollowerIndex p j)).2).1) :=
        Measurable.ite hidSet havoidIndex hheld
      have houterIndex : Measurable (fun e : Experiment p =>
          if (PrivateSourceStreams.blockDrawProfileMap p numerators hpos
              (e.2.1.1 s) (sourceFollowerIndex p j)).1 then
            if ids ((PrivateSourceStreams.blockDrawProfileMap p numerators hpos
                (e.2.1.1 s) (sourceFollowerIndex p j)).2).2 t then
              BootstrapPhysicalInput.followerAvoidArmValueMap p s incoming numerators hpos
                e.2 jIndex t
            else ((PrivateSourceStreams.blockDrawProfileMap p numerators hpos
                (e.2.1.1 s) (sourceFollowerIndex p j)).2).1
          else BootstrapPrivateRoundStreams.fullArmScalarDraw p (e.2.2.1
            (PublicDiscreteDraws.followerPlayer (m := p.m) p.two_le_m j, t))) :=
        Measurable.ite hactiveSet hinnerIndex huniform
      simpa [downActionProfile, BootstrapPhysicalBlock.followerAction,
        BootstrapPhysicalBlock.uninformedAction, physicalInput,
        BootstrapPhysicalInput.blockInput, j', hjin,
        ActiveRoundActions.followerPlayer_ne_coordinator,
        hindex, jIndex,
        BootstrapPhysicalInput.sourceFollowerIndex,
        BootstrapPhysicalInput.currentBlockDrawProfile,
        BootstrapPhysicalInput.currentBlockDrawProfileMap,
        BootstrapPhysicalInput.activityMap, BootstrapPhysicalInput.heldMap,
        BootstrapPhysicalInput.privateIDMap, BootstrapPhysicalInput.uniformArmMap,
        BootstrapPhysicalInput.followerAvoidArmValueMap,
        BootstrapPhysicalInput.playerRoundScalarAt] using houterIndex
    · have hslice : Measurable (fun e : Experiment p => (e.1.2 t).1) := by
        exact measurable_fst.comp <| (measurable_pi_apply t).comp <|
          measurable_snd.comp measurable_fst
      have htuple : Measurable (fun e : Experiment p =>
          BootstrapPhysicalBlock.tuple
            (physicalInput p s incoming numerators hpos ids rewards e) t) := by
        change Measurable (fun e : Experiment p =>
          OrderedTupleSampler.sample p.two_le_m p.m_lt_K ((e.1.2 t).1))
        exact (OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K).comp hslice
      have hprofileEq :
          (fun e : Experiment p =>
            downActionProfile p s incoming numerators hpos ids rewards t e
              (PublicDiscreteDraws.followerPlayer p.two_le_m j)) =
          (fun e : Experiment p =>
            (BootstrapPhysicalBlock.tuple
              (physicalInput p s incoming numerators hpos ids rewards e) t).val
              (PublicDiscreteDraws.followerPlayer p.two_le_m j)) := by
        funext e
        simp [downActionProfile, ActiveRoundActions.followerPlayer_ne_coordinator,
          ActiveRoundActions.followerIndex_followerPlayer, hjin]
      rw [hprofileEq]
      exact (measurable_pi_apply (PublicDiscreteDraws.followerPlayer p.two_le_m j)).comp
        (measurable_subtype_coe.comp htuple)

private theorem actualActions_eq_downActionProfile (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ)
  (hpos : ∀ j a, (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a) (ids : CompletePublicTable.IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (t : Fin p.T) (e :
  Experiment p) (hslot : BootstrapPhysicalBlock.slot (physicalInput p s incoming numerators hpos ids rewards e) t = downSlot) : BootstrapPhysicalBlock.actions (physicalInput p s incoming
  numerators hpos ids rewards e) (BootstrapPhysicalBlock.run (physicalInput p s incoming numerators hpos ids rewards e) t.val) t = downActionProfile p s incoming numerators hpos ids rewards
  t e := by
  funext i
  rcases ActiveRoundActions.player_cases p.two_le_m i with hcoord | ⟨j, hj⟩
  · subst i
    rw [BootstrapPhysicalBlock.actions_coordinator,
      BootstrapPhysicalBlock.coordinatorAction_down _ _ _ hslot]
    simp [downActionProfile]
  · subst i
    rw [BootstrapPhysicalBlock.actions_follower]
    have hinput : (physicalInput p s incoming numerators hpos ids rewards e).uninformed = incoming := by
      simp [physicalInput, BootstrapPhysicalInput.blockInput]
    have hnotcoord := ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m j
    have hindex := ActiveRoundActions.followerIndex_followerPlayer p.two_le_m j hnotcoord
    by_cases hji : j ∈ incoming
    · have hnotcoord := ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m j
      have hprofile : downActionProfile p s incoming numerators hpos ids rewards t e
          (PublicDiscreteDraws.followerPlayer (m := p.m) p.two_le_m j) =
          BootstrapPhysicalBlock.uninformedAction
            (physicalInput p s incoming numerators hpos ids rewards e) t ⟨j, hji⟩ := by
        unfold downActionProfile
        rw [dif_neg hnotcoord, hindex, dif_pos hji]
      have hactual : BootstrapPhysicalBlock.followerAction
          (physicalInput p s incoming numerators hpos ids rewards e) t j =
          BootstrapPhysicalBlock.uninformedAction
            (physicalInput p s incoming numerators hpos ids rewards e) t ⟨j, hji⟩ := by
        rw [BootstrapPhysicalBlock.followerAction, dif_pos (by simpa [hinput] using hji)]
      rw [hprofile, hactual]
    · have hnotcoord := ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m j
      have hprofile : downActionProfile p s incoming numerators hpos ids rewards t e
          (PublicDiscreteDraws.followerPlayer (m := p.m) p.two_le_m j) =
          (BootstrapPhysicalBlock.tuple
            (physicalInput p s incoming numerators hpos ids rewards e) t).val
            (PublicDiscreteDraws.followerPlayer (m := p.m) p.two_le_m j) := by
        unfold downActionProfile
        rw [dif_neg hnotcoord, hindex, dif_neg hji]
      have hactual : BootstrapPhysicalBlock.followerAction
          (physicalInput p s incoming numerators hpos ids rewards e) t j =
          (BootstrapPhysicalBlock.tuple
            (physicalInput p s incoming numerators hpos ids rewards e) t).val
            (PublicDiscreteDraws.followerPlayer (m := p.m) p.two_le_m j) := by
        rw [BootstrapPhysicalBlock.followerAction, dif_neg (by simpa [hinput] using hji)]
        unfold BootstrapPhysicalBlock.unoccupiedAction
        rw [hslot]
        simp [downSlot, dataSlot, upSlot]
      rw [hprofile, hactual]

private theorem measurable_downSlotMap (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀ j
  a, (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a) (ids : CompletePublicTable.IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (t : Fin p.T) : Measurable (fun e
  : Experiment p => BootstrapPhysicalBlock.slot (physicalInput p s incoming numerators hpos ids rewards e) t) := by
  change Measurable (fun e : Experiment p => PublicDiscreteDraws.slotDraw ((e.1.2 t).1))
  exact (PublicDiscreteDraws.measurable_slotDraw (m := p.m) (K := p.K)).comp <|
    measurable_fst.comp <| (measurable_pi_apply t).comp <|
      measurable_snd.comp measurable_fst

/-- The literal DOWN-positive event has a measurable set on the exact product
law. The run state is eliminated only after proving the DOWN action equation. -/
theorem measurable_downPositiveEvent (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀ j a,
  (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a) (ids : CompletePublicTable.IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (t : Fin p.T) (a : Fin p.K) :
  MeasurableSet {e : Experiment p | downPositiveEvent p s incoming numerators hpos ids rewards t a e} := by
  classical
  let slotMap := fun e : Experiment p => BootstrapPhysicalBlock.slot
    (physicalInput p s incoming numerators hpos ids rewards e) t
  let actMap := downActionProfile p s incoming numerators hpos ids rewards t
  have hslot : Measurable slotMap := measurable_downSlotMap p s incoming numerators
    hpos ids rewards t
  have hact : Measurable actMap := measurable_downActionProfile p s incoming numerators
    hpos ids rewards t
  have hcoord : Measurable (fun e : Experiment p => actMap e (coordinator p.two_le_m)) := by
    change Measurable (fun e : Experiment p =>
      (BootstrapPhysicalBlock.tuple
        (physicalInput p s incoming numerators hpos ids rewards e) t).val
        (coordinator p.two_le_m))
    have hslice : Measurable (fun e : Experiment p => (e.1.2 t).1) := by
      exact measurable_fst.comp <| (measurable_pi_apply t).comp <|
        measurable_snd.comp measurable_fst
    have htuple : Measurable (fun e : Experiment p =>
        BootstrapPhysicalBlock.tuple
          (physicalInput p s incoming numerators hpos ids rewards e) t) := by
      change Measurable (fun e : Experiment p =>
        OrderedTupleSampler.sample p.two_le_m p.m_lt_K ((e.1.2 t).1))
      exact (OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K).comp hslice
    exact (measurable_pi_apply (coordinator p.two_le_m)).comp
      (measurable_subtype_coe.comp htuple)
  have hcollision : MeasurableSet {e : Experiment p |
      FiniteBanditModel.collisionFreeFor (actMap e) (coordinator p.two_le_m)} := by
    have hcond (j : Player p.m) : MeasurableSet {e : Experiment p |
        j = coordinator p.two_le_m ∨ actMap e j ≠ actMap e (coordinator p.two_le_m)} := by
      by_cases hj : j = coordinator p.two_le_m
      · simp [hj]
      · have hneq : MeasurableSet {e : Experiment p |
            actMap e j ≠ actMap e (coordinator p.two_le_m)} :=
          (measurableSet_eq_fun ((measurable_pi_apply j).comp hact) hcoord).compl
        simpa [hj] using hneq
    have hset : {e : Experiment p |
        FiniteBanditModel.collisionFreeFor (actMap e) (coordinator p.two_le_m)} =
      Set.iInter (fun j : Player p.m => {e : Experiment p |
        j = coordinator p.two_le_m ∨ actMap e j ≠ actMap e (coordinator p.two_le_m)}) := by
      ext e
      simp only [Set.mem_ofPred_eq, Set.mem_iInter,
        FiniteBanditModel.collisionFreeFor]
      constructor
      · intro h j
        by_cases hj : j = coordinator p.two_le_m
        · exact Or.inl hj
        · exact Or.inr (h j hj)
      · intro h j hj
        rcases h j with hji | hne
        · exact (hj hji).elim
        · exact hne
    rw [hset]
    exact MeasurableSet.iInter hcond
  have hreward : MeasurableSet {e : Experiment p | rewardSupport p rewards t a = 1} := by
    by_cases h : rewardSupport p rewards t a = 1 <;> simp [h]
  have hslotSet : MeasurableSet {e : Experiment p | slotMap e = downSlot} :=
    measurableSet_eq_fun hslot measurable_const
  have hcoordSet : MeasurableSet {e : Experiment p | actMap e (coordinator p.two_le_m) = a} :=
    measurableSet_eq_fun hcoord measurable_const
  have hformula : {e : Experiment p | downPositiveEvent p s incoming numerators hpos
      ids rewards t a e} =
      (({e | slotMap e = downSlot} ∩ {e | actMap e (coordinator p.two_le_m) = a}) ∩
        {e | FiniteBanditModel.collisionFreeFor (actMap e) (coordinator p.two_le_m)}) ∩
        {e | rewardSupport p rewards t a = 1} := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hs, ha, hf⟩
      have hrun := actualActions_eq_downActionProfile p s incoming numerators hpos
        ids rewards t e hs
      have hcoordActual := congrFun hrun (coordinator p.two_le_m)
      have hprofileCoord := hcoordActual.symm.trans ha
      have hfreeProfile : FiniteBanditModel.collisionFreeFor
          (downActionProfile p s incoming numerators hpos ids rewards t e)
          (coordinator p.two_le_m) := by
        have hfreeActual := FiniteBanditModel.collisionFreeFor_of_playerFeedback_pos
          (BootstrapPhysicalBlock.actions
            (physicalInput p s incoming numerators hpos ids rewards e)
            (BootstrapPhysicalBlock.run
              (physicalInput p s incoming numerators hpos ids rewards e) t.val) t)
          (fun arm => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (rewards t arm)) (coordinator p.two_le_m) hf
        simpa [hrun] using hfreeActual
      have hfeedbackProfile : 0 < FiniteBanditModel.playerFeedback
          (downActionProfile p s incoming numerators hpos ids rewards t e)
          (fun arm => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (rewards t arm)) (coordinator p.two_le_m) := by
        have htemp := hf
        rw [BootstrapPhysicalBlock.feedback, hrun] at htemp
        simpa [physicalInput, BootstrapPhysicalInput.blockInput] using htemp
      have hfeedback' : 0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (rewards t a) := by
        simpa [FiniteBanditModel.playerFeedback, hfreeProfile, hprofileCoord]
          using hfeedbackProfile
      have hchi : rewardSupport p rewards t a = 1 := by
        simp [rewardSupport, hfeedback']
      exact ⟨⟨⟨hs, hprofileCoord⟩, hfreeProfile⟩, hchi⟩
    · rintro ⟨⟨⟨hs, ha⟩, hfree⟩, hchi⟩
      have hrun := actualActions_eq_downActionProfile p s incoming numerators hpos
        ids rewards t e hs
      have hcoordActual := congrFun hrun (coordinator p.two_le_m)
      change downActionProfile p s incoming numerators hpos ids rewards t e
        (coordinator p.two_le_m) = a at ha
      have hprofileCoord := ha
      change FiniteBanditModel.collisionFreeFor
        (downActionProfile p s incoming numerators hpos ids rewards t e)
        (coordinator p.two_le_m) at hfree
      have hposReward : 0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (rewards t a) := by
        simp [rewardSupport] at hchi
        exact hchi
      have hfeedbackProfile : 0 < FiniteBanditModel.playerFeedback
          (downActionProfile p s incoming numerators hpos ids rewards t e)
          (fun arm => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (rewards t arm)) (coordinator p.two_le_m) := by
        rw [FiniteBanditModel.playerFeedback, if_pos hfree, hprofileCoord]
        exact hposReward
      have hfeed : 0 < BootstrapPhysicalBlock.feedback
          (physicalInput p s incoming numerators hpos ids rewards e)
          (BootstrapPhysicalBlock.run
            (physicalInput p s incoming numerators hpos ids rewards e) t.val)
          t (coordinator p.two_le_m) := by
        rw [BootstrapPhysicalBlock.feedback, hrun]
        simpa [physicalInput, BootstrapPhysicalInput.blockInput] using hfeedbackProfile
      exact ⟨hs, hcoordActual.trans ha, hfeed⟩
  rw [hformula]
  exact ((hslotSet.inter hcoordSet).inter hcollision).inter hreward

/-- The literal indicator is measurable and integrable on the exact fixed
complete-row/private product law. -/
theorem downPositiveIndicator_integrable (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀ j
  a, (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a) (ids : CompletePublicTable.IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (t : Fin p.T) (a : Fin p.K) :
  Integrable (downPositiveIndicator p s incoming numerators hpos ids rewards t a) ((CompletePublicTable.completeRowMeasure p).prod (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) := by
  classical
  let μ := (CompletePublicTable.completeRowMeasure p).prod
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p)
  have hset := measurable_downPositiveEvent p s incoming numerators hpos ids rewards t a
  have hmeas : Measurable (downPositiveIndicator p s incoming numerators hpos ids rewards t a) := by
    change Measurable (fun e => if downPositiveEvent p s incoming numerators hpos ids rewards t a e
      then (1 : ℝ) else 0)
    exact Measurable.ite hset measurable_const measurable_const
  apply Integrable.of_bound hmeas.aestronglyMeasurable 1
  filter_upwards [] with e
  rw [Real.norm_eq_abs, downPositiveIndicator]
  split_ifs <;> norm_num

private theorem inactiveProfileSet_measure (p : ConstructorDimensions.Parameters) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀ j a, (1 : ℝ) ≤
  BootstrapWeightPotential.weight (b_N p) (numerators j) a) : ((BootstrapBlockIsolation.privateBlockProfileLaw p numerators hpos).toMeasure).real (inactiveProfileSet p incoming) =
  privateBlockProfileEventProbability p numerators hpos (fun profile => ∀ j ∈ incoming, (profile j).1 = false) := by
  classical
  rw [Measure.real, PMF.toMeasure_apply_fintype]
  rw [ENNReal.toReal_sum (fun profile _ => by
    by_cases h : profile ∈ inactiveProfileSet p incoming
    · simp [Set.indicator, h,
        (BootstrapBlockIsolation.privateBlockProfileLaw p numerators hpos).apply_ne_top]
    · simp [Set.indicator, h])]
  unfold privateBlockProfileEventProbability
  apply Finset.sum_congr rfl
  intro profile hprofile
  by_cases h : ∀ j ∈ incoming, (profile j).1 = false
  · simp only [inactiveProfileSet, Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs <;> rfl
  · simp only [inactiveProfileSet, Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs <;> rfl

private theorem uniformAvoidSet_measure (p : ConstructorDimensions.Parameters) (incoming : Finset (Follower p.m)) (a : Fin p.K) : (BootstrapModeService.privateArmVectorMeasure p).real
  (uniformAvoidSet p incoming a) = (1 - 1 / (p.K : ℝ)) ^ incoming.card := by
  classical
  have hset : uniformAvoidSet p incoming a =
      BootstrapModeService.privateArmAvoidanceSet p
        (incoming.image (PublicDiscreteDraws.followerPlayer p.two_le_m)) a := by
    ext arms
    simp [uniformAvoidSet, BootstrapModeService.privateArmAvoidanceSet]
  rw [hset, BootstrapModeService.privateArmVectorAvoidance_mass]
  rw [Finset.card_image_of_injective _ (followerPlayer_injective p.two_le_m)]

private theorem inactiveProfileSet_exact_mass (p : ConstructorDimensions.Parameters) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀ j a, (1 : ℝ) ≤
  BootstrapWeightPotential.weight (b_N p) (numerators j) a) : ((BootstrapBlockIsolation.privateBlockProfileLaw p numerators hpos).toMeasure).real (inactiveProfileSet p incoming) = (1 - 1 /
  (p.m : ℝ)) ^ incoming.card := by
  rw [inactiveProfileSet_measure p incoming numerators hpos,
    privateBlockProfile_all_inactive_probability p incoming numerators hpos]

private theorem inactiveProfileSet_ge_quarter (p : ConstructorDimensions.Parameters) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀ j a, (1 : ℝ) ≤
  BootstrapWeightPotential.weight (b_N p) (numerators j) a) : (1 / 4 : ℝ) ≤ ((BootstrapBlockIsolation.privateBlockProfileLaw p numerators hpos).toMeasure).real (inactiveProfileSet p
  incoming) := by
  rw [inactiveProfileSet_measure p incoming numerators hpos]
  exact privateBlockProfile_all_inactive_ge_quarter p incoming numerators hpos

private theorem uniformAvoidSet_ge_quarter (p : ConstructorDimensions.Parameters) (incoming : Finset (Follower p.m)) (a : Fin p.K) : (1 / 4 : ℝ) ≤
  (BootstrapModeService.privateArmVectorMeasure p).real (uniformAvoidSet p incoming a) := by
  rw [uniformAvoidSet_measure]
  have hcard : incoming.card ≤ p.K - 1 := by
    have hinc := incoming_card_le_followerCount p incoming
    have hmk : p.m ≤ p.K := Nat.le_of_lt p.m_lt_K
    omega
  have hKpos : (0 : ℝ) < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hKoneNat : 1 ≤ p.K :=
    le_trans (by decide : 1 ≤ 2) (le_trans p.two_le_m (Nat.le_of_lt p.m_lt_K))
  have hKone : (1 : ℝ) ≤ (p.K : ℝ) := by
    exact_mod_cast hKoneNat
  have hqnonneg : 0 ≤ 1 - 1 / (p.K : ℝ) := by
    have hrecip : 1 / (p.K : ℝ) ≤ 1 := by
      rw [div_le_one hKpos]
      exact hKone
    linarith
  have hqle : 1 - 1 / (p.K : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (p.K : ℝ) := by positivity
    linarith
  let q : ℝ := 1 + ((p.K - 1 : ℕ) : ℝ)⁻¹
  have hq : 1 - 1 / (p.K : ℝ) = q⁻¹ := by
    dsimp [q]
    have hsubcast : ((p.K - 1 : ℕ) : ℝ) = (p.K : ℝ) - 1 := by
      rw [Nat.cast_sub hKoneNat]
      norm_num
    have hsubpos : (0 : ℝ) < (p.K : ℝ) - 1 := by
      have hKgt : 1 < p.K :=
        lt_of_lt_of_le (by decide : 1 < 2)
          (le_trans p.two_le_m (Nat.le_of_lt p.m_lt_K))
      exact sub_pos.mpr (by exact_mod_cast hKgt)
    rw [hsubcast]
    field_simp [hKpos.ne', hsubpos.ne']
    ring
  have hqbase : 1 ≤ q := by
    dsimp [q]
    exact le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hpow : q ^ (p.K - 1) ≤ Real.exp 1 := by
    dsimp [q]
    exact Real.one_add_inv_pow_le_exp
  have hpowlt : q ^ incoming.card < 3 := by
    have hpowle : q ^ incoming.card ≤ q ^ (p.K - 1) :=
      pow_le_pow_right₀ hqbase hcard
    exact (hpowle.trans hpow).trans_lt Real.exp_one_lt_three
  have hinv : (1 / 3 : ℝ) < (q ^ incoming.card)⁻¹ := by
    simpa [one_div] using one_div_lt_one_div_of_lt
      (pow_pos (by linarith [hqbase]) _) hpowlt
  have hpower : (1 / 4 : ℝ) ≤ (1 - 1 / (p.K : ℝ)) ^ incoming.card := by
    rw [hq, inv_pow]
    exact (by norm_num : (1 / 4 : ℝ) ≤ 1 / 3).trans hinv.le
  exact hpower

private def downLowerRectangle (p : ConstructorDimensions.Parameters) (incoming : Finset (Follower p.m)) (a : Fin p.K) : Set (ContinuousControlSlice.Slice p.m p.K × ((Fin (p.m - 1) → Bool ×
  Fin p.K × Fin (A_id p)) × (Player p.m → Fin p.K))) :=
  downTupleSet p a ×ˢ (inactiveProfileSet p incoming ×ˢ uniformAvoidSet p incoming a)

private theorem downLowerRectangle_measurable (p : ConstructorDimensions.Parameters) (incoming : Finset (Follower p.m)) (a : Fin p.K) : MeasurableSet (downLowerRectangle p incoming a) := by
  apply MeasurableSet.prod
  · exact downTupleSet_measurable p a
  · apply MeasurableSet.prod
    · exact MeasurableSet.of_discrete
    · exact MeasurableSet.of_discrete

private theorem real_prod_rectangle {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (A : Set α) (B :
  Set β) : (μ.prod ν).real (A ×ˢ B) = μ.real A * ν.real B := by
  simp [Measure.real, Measure.prod_prod]

private theorem downLowerRectangle_mass (p : ConstructorDimensions.Parameters) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀ j a, (1 : ℝ) ≤
  BootstrapWeightPotential.weight (b_N p) (numerators j) a) (a : Fin p.K) : ((ContinuousControlSlice.sliceLaw p.m p.K).prod ((BootstrapBlockIsolation.privateBlockProfileLaw p numerators
  hpos).toMeasure.prod (BootstrapModeService.privateArmVectorMeasure p))).real (downLowerRectangle p incoming a) = ((1 / 4 : ℝ) * (1 / (p.K : ℝ))) * (((1 - 1 / (p.m : ℝ)) ^ incoming.card) *
  ((1 - 1 / (p.K : ℝ)) ^ incoming.card)) := by
  classical
  change ((ContinuousControlSlice.sliceLaw p.m p.K).prod
      ((BootstrapBlockIsolation.privateBlockProfileLaw p numerators hpos).toMeasure.prod
        (BootstrapModeService.privateArmVectorMeasure p))).real
      (downTupleSet p a ×ˢ
        (inactiveProfileSet p incoming ×ˢ uniformAvoidSet p incoming a)) = _
  rw [real_prod_rectangle, real_prod_rectangle, slice_downTuple_mass,
    inactiveProfileSet_exact_mass p incoming numerators hpos,
    uniformAvoidSet_measure p incoming a]

private theorem downLowerRectangle_subset_downPositiveEvent (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin
  p.K → ℕ) (hpos : ∀ j a, (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a) (ids : CompletePublicTable.IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (t : Fin
  p.T) (a : Fin p.K) (e : Experiment p) (hrect : downExperimentFactors p s numerators hpos t e ∈ downLowerRectangle p incoming a) (hchi : rewardSupport p rewards t a = 1) : downPositiveEvent
  p s incoming numerators hpos ids rewards t a e := by
  classical
  let x := physicalInput p s incoming numerators hpos ids rewards e
  have hrow : (downExperimentFactors p s numerators hpos t e).1 ∈ downTupleSet p a :=
    hrect.1
  have hprofile : (downExperimentFactors p s numerators hpos t e).2.1 ∈
      inactiveProfileSet p incoming := hrect.2.1
  have harms : (downExperimentFactors p s numerators hpos t e).2.2 ∈
      uniformAvoidSet p incoming a := hrect.2.2
  have hslot : BootstrapPhysicalBlock.slot x t = downSlot := by
    simpa [downExperimentFactors, downTupleSet, x, physicalInput, BootstrapPhysicalInput.blockInput,
      BootstrapPhysicalBlock.slot, PublicDiscreteDraws.slotDraw] using hrow.1
  have htuple : (BootstrapPhysicalBlock.tuple x t).val (coordinator p.two_le_m) = a := by
    simpa [downExperimentFactors, downTupleSet, x, physicalInput, BootstrapPhysicalInput.blockInput,
      BootstrapPhysicalBlock.tuple] using hrow.2
  have hrun := actualActions_eq_downActionProfile p s incoming numerators hpos
    ids rewards t e hslot
  have hcoord : BootstrapPhysicalBlock.actions x (BootstrapPhysicalBlock.run x t.val) t
      (coordinator p.two_le_m) = a := by
    rw [hrun]
    simpa [downActionProfile, x] using htuple
  have hcoordProfile : downActionProfile p s incoming numerators hpos ids rewards t e
      (coordinator p.two_le_m) = a := by
    simpa [downActionProfile] using htuple
  have hfreeProfile : FiniteBanditModel.collisionFreeFor
      (downActionProfile p s incoming numerators hpos ids rewards t e)
      (coordinator p.two_le_m) := by
    intro i hne
    rcases ActiveRoundActions.player_cases p.two_le_m i with hcoord | ⟨j, rfl⟩
    · exact (hne hcoord).elim
    · by_cases hj : j ∈ incoming
      · let j' : {j // j ∈ incoming} := ⟨j, hj⟩
        have hactive : x.active j' = false := by
          change (BootstrapPhysicalInput.blockInput p s incoming numerators hpos ids e.1
            rewards e.2).active j' = false
          rw [BootstrapPhysicalInput.blockInput_active]
          exact hprofile (sourceFollowerIndex p j) hj
        have hinput : x.uninformed = incoming := by
          simp [x, physicalInput, BootstrapPhysicalInput.blockInput]
        have hjx : j ∈ x.uninformed := by simpa [hinput] using hj
        have hsub : j' = (⟨j, hjx⟩ : {j // j ∈ x.uninformed}) := by
          apply Subtype.ext
          rfl
        have hactive' : x.active ⟨j, hjx⟩ = false := by
          rw [← hsub]
          exact hactive
        have hactiveMap : BootstrapPhysicalInput.activityMap p s incoming numerators hpos e.2 j' = false := by
          simpa [x, physicalInput, BootstrapPhysicalInput.blockInput] using hactive
        have havoid : (downExperimentFactors p s numerators hpos t e).2.2
            (PublicDiscreteDraws.followerPlayer (m := p.m) p.two_le_m j) ≠ a :=
          harms j hj
        have hprofileAction : downActionProfile p s incoming numerators hpos ids rewards t e
            (PublicDiscreteDraws.followerPlayer (m := p.m) p.two_le_m j) =
              BootstrapPhysicalBlock.followerAction x t j := by
          have hnotcoord := ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m j
          have hindex := ActiveRoundActions.followerIndex_followerPlayer p.two_le_m j hnotcoord
          have hjx : j ∈ x.uninformed := by simpa [hinput] using hj
          unfold downActionProfile
          rw [dif_neg hnotcoord, hindex, dif_pos hj]
          change BootstrapPhysicalBlock.uninformedAction x t ⟨j, hj⟩ =
            BootstrapPhysicalBlock.followerAction x t j
          rw [BootstrapPhysicalBlock.followerAction, dif_pos hjx]
        rw [hprofileAction, hcoordProfile]
        have haction : BootstrapPhysicalBlock.followerAction x t j =
            BootstrapPrivateRoundStreams.fullArmScalarDraw p
              (e.2.2.1 (PublicDiscreteDraws.followerPlayer (m := p.m) p.two_le_m j, t)) := by
          rw [BootstrapPhysicalBlock.followerAction, dif_pos hjx]
          unfold BootstrapPhysicalBlock.uninformedAction
          rw [if_neg (by rw [hactive']; decide)]
          change BootstrapPhysicalInput.uniformArmMap p e.2
            (PublicDiscreteDraws.followerPlayer (m := p.m) p.two_le_m j) t =
            BootstrapPrivateRoundStreams.fullArmScalarDraw p
              (e.2.2.1 (PublicDiscreteDraws.followerPlayer (m := p.m) p.two_le_m j, t))
          rfl
        rw [haction]
        simpa [downExperimentFactors] using havoid
      · have hprofileAction : downActionProfile p s incoming numerators hpos ids rewards t e
            (PublicDiscreteDraws.followerPlayer (m := p.m) p.two_le_m j) =
              (BootstrapPhysicalBlock.tuple x t).val
                (PublicDiscreteDraws.followerPlayer (m := p.m) p.two_le_m j) := by
          have hnotcoord := ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m j
          have hindex := ActiveRoundActions.followerIndex_followerPlayer p.two_le_m j hnotcoord
          unfold downActionProfile
          rw [dif_neg hnotcoord, hindex, dif_neg hj]
        have hactualAction : BootstrapPhysicalBlock.followerAction x t j =
            (BootstrapPhysicalBlock.tuple x t).val
              (PublicDiscreteDraws.followerPlayer (m := p.m) p.two_le_m j) := by
          have hinput : x.uninformed = incoming := by
            simp [x, physicalInput, BootstrapPhysicalInput.blockInput]
          have hnot : j ∉ x.uninformed := by simpa [hinput] using hj
          rw [BootstrapPhysicalBlock.followerAction, dif_neg hnot]
          unfold BootstrapPhysicalBlock.unoccupiedAction
          rw [hslot]
          simp [downSlot, dataSlot, upSlot]
        have hprofileFollower : downActionProfile p s incoming numerators hpos ids rewards t e
            (PublicDiscreteDraws.followerPlayer (m := p.m) p.two_le_m j) =
            BootstrapPhysicalBlock.followerAction x t j := hprofileAction.trans hactualAction.symm
        rw [hprofileFollower, hcoordProfile]
        have htupleAction : BootstrapPhysicalBlock.followerAction x t j =
            (BootstrapPhysicalBlock.tuple x t).val
              (PublicDiscreteDraws.followerPlayer (m := p.m) p.two_le_m j) := hactualAction
        rw [htupleAction]
        intro heq
        have harmEq : (BootstrapPhysicalBlock.tuple x t).val (PublicDiscreteDraws.followerPlayer p.two_le_m j) =
            (BootstrapPhysicalBlock.tuple x t).val (coordinator p.two_le_m) := calc
          (BootstrapPhysicalBlock.tuple x t).val (PublicDiscreteDraws.followerPlayer p.two_le_m j) = a := heq
          _ = (BootstrapPhysicalBlock.tuple x t).val (coordinator p.two_le_m) := htuple.symm
        exact (followerPlayer_ne_coordinator p.two_le_m j)
          ((BootstrapPhysicalBlock.tuple x t).property harmEq)
  have hfree : FiniteBanditModel.collisionFreeFor
      (BootstrapPhysicalBlock.actions x (BootstrapPhysicalBlock.run x t.val) t)
      (coordinator p.two_le_m) := by
    rw [hrun]
    exact hfreeProfile
  have hrewpos : 0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
      (rewards t a) := by
    simp [rewardSupport] at hchi
    simpa [x, physicalInput, BootstrapPhysicalInput.blockInput] using hchi
  have hfeedback : 0 < BootstrapPhysicalBlock.feedback x
      (BootstrapPhysicalBlock.run x t.val) t (coordinator p.two_le_m) := by
    rw [BootstrapPhysicalBlock.feedback]
    unfold FiniteBanditModel.playerFeedback
    rw [if_pos hfree, hcoord]
    simpa [x, physicalInput, BootstrapPhysicalInput.blockInput] using hrewpos
  exact ⟨hslot, hcoord, hfeedback⟩

private theorem downPositiveEvent_implies_downTuple (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ)
  (hpos : ∀ j a, (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a) (ids : CompletePublicTable.IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (t : Fin p.T) (a :
  Fin p.K) (e : Experiment p) (he : downPositiveEvent p s incoming numerators hpos ids rewards t a e) : (downExperimentFactors p s numerators hpos t e).1 ∈ downTupleSet p a := by
  rcases he with ⟨hslot, haction, hfeedback⟩
  let x := physicalInput p s incoming numerators hpos ids rewards e
  have htuple := BootstrapPhysicalInput.actions_coordinator_down p s incoming numerators hpos
    ids e.1 rewards e.2 (BootstrapPhysicalBlock.run x t.val) t hslot
  have hreward : 0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
      (rewards t a) := by
    have hfeedback' : 0 < FiniteBanditModel.playerFeedback
        (BootstrapPhysicalBlock.actions x (BootstrapPhysicalBlock.run x t.val) t)
        (fun arm => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (rewards t arm)) (coordinator p.two_le_m) := by
      simpa [x, physicalInput, BootstrapPhysicalInput.blockInput,
        BootstrapPhysicalBlock.feedback] using hfeedback
    have haction' : BootstrapPhysicalBlock.actions x (BootstrapPhysicalBlock.run x t.val) t
        (coordinator p.two_le_m) = a := by
      simpa [x] using haction
    have hfree := FiniteBanditModel.collisionFreeFor_of_playerFeedback_pos
      (BootstrapPhysicalBlock.actions x (BootstrapPhysicalBlock.run x t.val) t)
      (fun arm => RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t arm))
      (coordinator p.two_le_m) hfeedback'
    simp [FiniteBanditModel.playerFeedback, hfree, haction'] at hfeedback'
    exact hfeedback'
  constructor
  · simpa [downExperimentFactors, x, physicalInput, BootstrapPhysicalInput.blockInput,
      BootstrapPhysicalBlock.slot, PublicDiscreteDraws.slotDraw] using hslot
  · have htupleArm : (BootstrapPhysicalBlock.tuple x t).val (coordinator p.two_le_m) = a := by
      exact htuple.symm.trans haction
    simpa [downTupleSet, downExperimentFactors, x, physicalInput,
      BootstrapPhysicalInput.blockInput, BootstrapPhysicalBlock.tuple] using htupleArm

/-- The current indicator integral is the probability of its literal event. -/
theorem downPositiveIndicator_integral_eq (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀
  j a, (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a) (ids : CompletePublicTable.IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (t : Fin p.T) (a : Fin p.K) :
  (∫ e, downPositiveIndicator p s incoming numerators hpos ids rewards t a e ∂ (CompletePublicTable.completeRowMeasure p).prod (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) =
  ((CompletePublicTable.completeRowMeasure p).prod (BootstrapPrivateRoundStreams.extendedPrivateLaw p)).real {e | downPositiveEvent p s incoming numerators hpos ids rewards t a e} := by
  classical
  have hset := measurable_downPositiveEvent p s incoming numerators hpos ids rewards t a
  have hfun : downPositiveIndicator p s incoming numerators hpos ids rewards t a =
      ({e | downPositiveEvent p s incoming numerators hpos ids rewards t a e}.indicator 1) := by
    funext e
    simp [downPositiveIndicator, Set.indicator]
  rw [hfun]
  change (∫ e, {e | downPositiveEvent p s incoming numerators hpos ids rewards t a e}.indicator
    1 e ∂
      (CompletePublicTable.completeRowMeasure p).prod
        (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) = _
  exact integral_indicator_one hset

private theorem factorPreimage_indicator_integral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β) (f : α → β) (hmp : MeasurePreserving f μ ν) (E : Set
  β) (hE : MeasurableSet E) : (∫ x, (f ⁻¹' E).indicator (fun _ : α => (1 : ℝ)) x ∂μ) = ν.real E := by
  change (∫ x, (f ⁻¹' E).indicator 1 x ∂μ) = _
  rw [integral_indicator_one (hE.preimage hmp.measurable)]
  change (μ (f ⁻¹' E)).toReal = (ν E).toReal
  rw [← hmp.map_eq, Measure.map_apply hmp.measurable hE]

private def downUpperRectangle (p : ConstructorDimensions.Parameters) (a : Fin p.K) : Set (ContinuousControlSlice.Slice p.m p.K × ((Fin (p.m - 1) → Bool × Fin p.K × Fin (A_id p)) × (Player
  p.m → Fin p.K))) :=
  downTupleSet p a ×ˢ Set.univ

private theorem downUpperRectangle_measurable (p : ConstructorDimensions.Parameters) (a : Fin p.K) : MeasurableSet (downUpperRectangle p a) :=
  MeasurableSet.prod (downTupleSet_measurable p a) MeasurableSet.univ

private theorem downUpperRectangle_mass (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀ j a, (1 : ℝ) ≤
  BootstrapWeightPotential.weight (b_N p) (numerators j) a) (t : Fin p.T) (a : Fin p.K) : ((ContinuousControlSlice.sliceLaw p.m p.K).prod ((BootstrapBlockIsolation.privateBlockProfileLaw p
  numerators hpos).toMeasure.prod (BootstrapModeService.privateArmVectorMeasure p))).real (downUpperRectangle p a) = (1 / (4 * (p.K : ℝ)) : ℝ) := by
  classical
  change ((ContinuousControlSlice.sliceLaw p.m p.K).prod
      ((BootstrapBlockIsolation.privateBlockProfileLaw p numerators hpos).toMeasure.prod
        (BootstrapModeService.privateArmVectorMeasure p))).real
      (downTupleSet p a ×ˢ Set.univ) = _
  rw [real_prod_rectangle, slice_downTuple_mass, probReal_univ]
  field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt (K_pos p))]

private theorem downPositiveEvent_implies_rewardSupport (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K →
  ℕ) (hpos : ∀ j a, (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a) (ids : CompletePublicTable.IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (t : Fin p.T) (a :
  Fin p.K) (e : Experiment p) (he : downPositiveEvent p s incoming numerators hpos ids rewards t a e) : rewardSupport p rewards t a = 1 := by
  rcases he with ⟨hslot, haction, hfeedback⟩
  let x := physicalInput p s incoming numerators hpos ids rewards e
  have hfeedback' : 0 < FiniteBanditModel.playerFeedback
      (BootstrapPhysicalBlock.actions x (BootstrapPhysicalBlock.run x t.val) t)
      (fun arm => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        (rewards t arm)) (coordinator p.two_le_m) := by
    simpa [x, physicalInput, BootstrapPhysicalInput.blockInput,
      BootstrapPhysicalBlock.feedback] using hfeedback
  have haction' : BootstrapPhysicalBlock.actions x (BootstrapPhysicalBlock.run x t.val) t
      (coordinator p.two_le_m) = a := by
    simpa [x] using haction
  have hfree := FiniteBanditModel.collisionFreeFor_of_playerFeedback_pos
    (BootstrapPhysicalBlock.actions x (BootstrapPhysicalBlock.run x t.val) t)
    (fun arm => RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t arm))
    (coordinator p.two_le_m) hfeedback'
  have hrewpos : 0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
      (rewards t a) := by
    simp [FiniteBanditModel.playerFeedback, hfree, haction'] at hfeedback'
    exact hfeedback'
  simp [rewardSupport, hrewpos]

/-- Actual fixed-incoming-state product-law mean bounds for the current
coordinator DOWN-positive indicator. The lower event averages the real block
activity coins jointly with the row slot/tuple and labelled current arm draws. -/
theorem downPositiveIndicator_mean_bounds (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀
  j a, (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a) (ids : CompletePublicTable.IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (t : Fin p.T) (a : Fin p.K) :
  rewardSupport p rewards t a / (64 * (p.K : ℝ)) ≤ ∫ e, downPositiveIndicator p s incoming numerators hpos ids rewards t a e ∂ ((CompletePublicTable.completeRowMeasure p).prod
  (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) ∧ (∫ e, downPositiveIndicator p s incoming numerators hpos ids rewards t a e ∂ ((CompletePublicTable.completeRowMeasure p).prod
  (BootstrapPrivateRoundStreams.extendedPrivateLaw p))) ≤ rewardSupport p rewards t a / (p.K : ℝ) := by
  classical
  let μ := (CompletePublicTable.completeRowMeasure p).prod
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p)
  let factors := downExperimentFactors p s numerators hpos t
  let ν := (ContinuousControlSlice.sliceLaw p.m p.K).prod
    ((BootstrapBlockIsolation.privateBlockProfileLaw p numerators hpos).toMeasure.prod
      (BootstrapModeService.privateArmVectorMeasure p))
  let Rlo := downLowerRectangle p incoming a
  let Rhi := downUpperRectangle p a
  have hZ : Integrable (downPositiveIndicator p s incoming numerators hpos ids rewards t a) μ :=
    downPositiveIndicator_integrable p s incoming numerators hpos ids rewards t a
  have hZeq := downPositiveIndicator_integral_eq p s incoming numerators hpos ids rewards t a
  have hchi01 : rewardSupport p rewards t a = 0 ∨ rewardSupport p rewards t a = 1 := by
    unfold rewardSupport
    split_ifs <;> norm_num
  rcases hchi01 with hchi0 | hchi1
  · have hno (e : Experiment p) : ¬ downPositiveEvent p s incoming numerators hpos ids rewards t a e := by
      intro he
      have := downPositiveEvent_implies_rewardSupport p s incoming numerators hpos ids
        rewards t a e he
      rw [hchi0] at this
      norm_num at this
    have hzero : ∀ e, downPositiveIndicator p s incoming numerators hpos ids rewards t a e = 0 := by
      intro e
      simp [downPositiveIndicator, hno e]
    constructor
    · rw [hchi0]
      simp [hzero]
    · rw [hchi0]
      simp [hzero]
  · have hFactors : MeasurePreserving factors μ ν :=
      measurePreserving_downExperimentFactors p s numerators hpos t
    have hRlo : MeasurableSet Rlo := downLowerRectangle_measurable p incoming a
    have hRhi : MeasurableSet Rhi := downUpperRectangle_measurable p a
    have hprelo : MeasurableSet (factors ⁻¹' Rlo) := hRlo.preimage hFactors.measurable
    have hprehi : MeasurableSet (factors ⁻¹' Rhi) := hRhi.preimage hFactors.measurable
    have hIlo : Integrable ((factors ⁻¹' Rlo).indicator (fun _ => (1 : ℝ))) μ := by
      have hm : Measurable ((factors ⁻¹' Rlo).indicator
          (fun _ : Experiment p => (1 : ℝ))) := measurable_const.indicator hprelo
      exact Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun e => by
        rw [Real.norm_eq_abs]
        by_cases he : factors e ∈ Rlo <;> simp [Set.indicator, he])
    have hIhi : Integrable ((factors ⁻¹' Rhi).indicator (fun _ => (1 : ℝ))) μ := by
      have hm : Measurable ((factors ⁻¹' Rhi).indicator
          (fun _ : Experiment p => (1 : ℝ))) := measurable_const.indicator hprehi
      exact Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun e => by
        rw [Real.norm_eq_abs]
        by_cases he : factors e ∈ Rhi <;> simp [Set.indicator, he])
    have hrectlo :
        (∫ e, (factors ⁻¹' Rlo).indicator (fun _ => (1 : ℝ)) e ∂μ) = ν.real Rlo :=
      factorPreimage_indicator_integral μ ν factors hFactors Rlo hRlo
    have hrecthi :
        (∫ e, (factors ⁻¹' Rhi).indicator (fun _ => (1 : ℝ)) e ∂μ) = ν.real Rhi :=
      factorPreimage_indicator_integral μ ν factors hFactors Rhi hRhi
    have hloPoint (e : Experiment p) :
        (factors ⁻¹' Rlo).indicator (fun _ => (1 : ℝ)) e ≤
          downPositiveIndicator p s incoming numerators hpos ids rewards t a e := by
      by_cases he : factors e ∈ Rlo
      · have hactual := downLowerRectangle_subset_downPositiveEvent p s incoming numerators
          hpos ids rewards t a e (by simpa [Rlo, factors] using he) hchi1
        simp [Set.indicator, he, downPositiveIndicator, hactual]
      · have hnonneg : 0 ≤ downPositiveIndicator p s incoming numerators hpos ids rewards t a e := by
          unfold downPositiveIndicator
          split_ifs <;> norm_num
        simpa [Set.indicator, he] using hnonneg
    have hhiPoint (e : Experiment p) :
        downPositiveIndicator p s incoming numerators hpos ids rewards t a e ≤
          (factors ⁻¹' Rhi).indicator (fun _ => (1 : ℝ)) e := by
      by_cases he : downPositiveEvent p s incoming numerators hpos ids rewards t a e
      · have hrow := downPositiveEvent_implies_downTuple p s incoming numerators hpos ids
          rewards t a e he
        have hmem : factors e ∈ Rhi := by
          simpa [Rhi, factors, downUpperRectangle] using hrow
        simp [Set.indicator, hmem, downPositiveIndicator, he]
      · have hnonneg : 0 ≤ (factors ⁻¹' Rhi).indicator
            (fun _ : Experiment p => (1 : ℝ)) e := by
          by_cases hm : factors e ∈ Rhi <;> simp [Set.indicator, hm]
        simpa [downPositiveIndicator, he] using hnonneg
    have hlowIntegral := integral_mono hIlo hZ hloPoint
    have hhighIntegral := integral_mono hZ hIhi hhiPoint
    have hmasslo : ν.real Rlo =
        ((1 / 4 : ℝ) * (1 / (p.K : ℝ))) *
          (((1 - 1 / (p.m : ℝ)) ^ incoming.card) *
            ((1 - 1 / (p.K : ℝ)) ^ incoming.card)) := by
      simpa [ν, Rlo] using downLowerRectangle_mass p incoming numerators hpos a
    have hmasshi : ν.real Rhi = 1 / (4 * (p.K : ℝ)) := by
      simpa [ν, Rhi] using downUpperRectangle_mass p s numerators hpos t a
    have hactMeasure := inactiveProfileSet_ge_quarter p incoming numerators hpos
    have hact : (1 / 4 : ℝ) ≤ (1 - 1 / (p.m : ℝ)) ^ incoming.card := by
      rw [← inactiveProfileSet_exact_mass p incoming numerators hpos]
      exact hactMeasure
    have harmMeasure := uniformAvoidSet_ge_quarter p incoming a
    have harm : (1 / 4 : ℝ) ≤ (1 - 1 / (p.K : ℝ)) ^ incoming.card := by
      rw [← uniformAvoidSet_measure p incoming a]
      exact harmMeasure
    have hfactorNonneg : 0 ≤ (1 / 4 : ℝ) * (1 / (p.K : ℝ)) := by positivity
    have hprobNonneg : 0 ≤ (1 - 1 / (p.m : ℝ)) ^ incoming.card := by positivity
    have hprod : (1 / 4 : ℝ) * (1 / 4 : ℝ) ≤
        ((1 - 1 / (p.m : ℝ)) ^ incoming.card) *
          ((1 - 1 / (p.K : ℝ)) ^ incoming.card) :=
      mul_le_mul hact harm (by positivity) (by positivity)
    have hlowerMass : rewardSupport p rewards t a / (64 * (p.K : ℝ)) ≤ ν.real Rlo := by
      rw [hchi1, hmasslo]
      calc
        (1 : ℝ) / (64 * (p.K : ℝ)) =
            ((1 / 4 : ℝ) * (1 / (p.K : ℝ))) * ((1 / 4 : ℝ) * (1 / 4 : ℝ)) := by
              field_simp
              ring
        _ ≤ ((1 / 4 : ℝ) * (1 / (p.K : ℝ))) *
            (((1 - 1 / (p.m : ℝ)) ^ incoming.card) *
              ((1 - 1 / (p.K : ℝ)) ^ incoming.card)) :=
          mul_le_mul_of_nonneg_left hprod hfactorNonneg
    have hKpos : (0 : ℝ) < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
    have hupperMass : ν.real Rhi ≤ rewardSupport p rewards t a / (p.K : ℝ) := by
      rw [hchi1, hmasshi]
      exact one_div_le_one_div_of_le (by positivity : (0 : ℝ) < p.K)
        (by nlinarith : (p.K : ℝ) ≤ 4 * (p.K : ℝ))
    have hlow : ν.real Rlo ≤
        ∫ e, downPositiveIndicator p s incoming numerators hpos ids rewards t a e ∂μ := by
      rw [← hrectlo]
      exact hlowIntegral
    have hhigh :
        ∫ e, downPositiveIndicator p s incoming numerators hpos ids rewards t a e ∂μ ≤
          ν.real Rhi := by
      rw [← hrecthi]
      exact hhighIntegral
    constructor
    · exact hlowerMass.trans hlow
    · exact hhigh.trans hupperMass

/-- The actual count over a calendar block is integrable as a finite sum of
the literal current indicators. -/
theorem downBlockCount_integrable (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀ j a, (1
  : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a) (ids : CompletePublicTable.IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K) : Integrable
  (downBlockCount p s incoming numerators hpos ids rewards a) ((CompletePublicTable.completeRowMeasure p).prod (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) := by
  classical
  apply integrable_finsetSum
  intro t ht
  exact downPositiveIndicator_integrable p s incoming numerators hpos ids rewards t a

/-- The calendar-block DOWN-count mean is the sum of the actual per-round
fixed-incoming-state means, including when the terminal block is clipped. -/
theorem downBlockCount_mean_bounds (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀ j a, (1
  : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a) (ids : CompletePublicTable.IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K) : rewardSupportCount p s
  rewards a / (64 * (p.K : ℝ)) ≤ ∫ e, downBlockCount p s incoming numerators hpos ids rewards a e ∂ ((CompletePublicTable.completeRowMeasure p).prod
  (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) ∧ (∫ e, downBlockCount p s incoming numerators hpos ids rewards a e ∂ ((CompletePublicTable.completeRowMeasure p).prod
  (BootstrapPrivateRoundStreams.extendedPrivateLaw p))) ≤ rewardSupportCount p s rewards a / (p.K : ℝ) := by
  classical
  let μ := (CompletePublicTable.completeRowMeasure p).prod
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p)
  have hterm (t : Fin p.T) (ht : t ∈ calendarBlock p s) :=
    downPositiveIndicator_mean_bounds p s incoming numerators hpos ids rewards t a
  have hint : ∀ t ∈ calendarBlock p s,
      Integrable (fun e => downPositiveIndicator p s incoming numerators hpos ids rewards t a e) μ := by
    intro t ht
    exact downPositiveIndicator_integrable p s incoming numerators hpos ids rewards t a
  have hsum := integral_finsetSum (calendarBlock p s) hint
  change (rewardSupportCount p s rewards a / (64 * (p.K : ℝ)) ≤
        ∫ e, ∑ t ∈ calendarBlock p s,
          downPositiveIndicator p s incoming numerators hpos ids rewards t a e ∂μ) ∧
      (∫ e, ∑ t ∈ calendarBlock p s,
        downPositiveIndicator p s incoming numerators hpos ids rewards t a e ∂μ ≤
        rewardSupportCount p s rewards a / (p.K : ℝ))
  constructor
  · rw [rewardSupportCount, Finset.sum_div]
    calc
      (∑ t ∈ calendarBlock p s,
          rewardSupport p rewards t a / (64 * (p.K : ℝ))) ≤
          ∑ t ∈ calendarBlock p s,
            ∫ e, downPositiveIndicator p s incoming numerators hpos ids rewards t a e ∂μ :=
        Finset.sum_le_sum fun t ht => (hterm t ht).1
      _ = ∫ e, downBlockCount p s incoming numerators hpos ids rewards a e ∂μ := by
        simpa [downBlockCount, μ] using hsum.symm
  · rw [rewardSupportCount, Finset.sum_div]
    calc
      (∫ e, downBlockCount p s incoming numerators hpos ids rewards a e ∂μ) =
          ∑ t ∈ calendarBlock p s,
            ∫ e, downPositiveIndicator p s incoming numerators hpos ids rewards t a e ∂μ := by
        simpa [downBlockCount, μ] using hsum
      _ ≤ ∑ t ∈ calendarBlock p s, rewardSupport p rewards t a / (p.K : ℝ) :=
        Finset.sum_le_sum fun t ht => (hterm t ht).2

/-- Pointwise actual count, actual clipped calendar cardinality, and source
bootstrap cap. -/
theorem downBlockCount_pointwise_bounds (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ) (hpos : ∀ j
  a, (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a) (ids : CompletePublicTable.IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K) (e : Experiment p)
  : 0 ≤ downBlockCount p s incoming numerators hpos ids rewards a e ∧ downBlockCount p s incoming numerators hpos ids rewards a e ≤ ((calendarBlock p s).card : ℝ) ∧ (calendarBlock p s).card
  ≤ B_boot p := by
  classical
  have hterm_nonneg (t : Fin p.T) :
      0 ≤ downPositiveIndicator p s incoming numerators hpos ids rewards t a e := by
    unfold downPositiveIndicator
    split_ifs <;> norm_num
  have hterm_le (t : Fin p.T) :
      downPositiveIndicator p s incoming numerators hpos ids rewards t a e ≤ 1 := by
    unfold downPositiveIndicator
    split_ifs <;> norm_num
  change 0 ≤ (∑ t ∈ calendarBlock p s,
      downPositiveIndicator p s incoming numerators hpos ids rewards t a e) ∧
    (∑ t ∈ calendarBlock p s,
      downPositiveIndicator p s incoming numerators hpos ids rewards t a e) ≤
        ((calendarBlock p s).card : ℝ) ∧
      (calendarBlock p s).card ≤ B_boot p
  constructor
  · apply Finset.sum_nonneg
    intro t ht
    exact hterm_nonneg t
  · constructor
    · calc
        (∑ t ∈ calendarBlock p s,
            downPositiveIndicator p s incoming numerators hpos ids rewards t a e) ≤
          ∑ _t ∈ calendarBlock p s, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro t ht
            exact hterm_le t
        _ = ((calendarBlock p s).card : ℝ) := by simp
    · exact BootstrapDimensions.calendarBlock_card_le_B_boot p s

end Bandits.Support.BootstrapDownCountMean

end
