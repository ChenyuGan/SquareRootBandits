/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CausalBootstrapBlockProduct
public import Bandits.Support.GeneratedDownBlockBoundaryMean
public import Bandits.Support.GeneratedMonitorCountAdaptedness

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Conditional means for the generated reference DOWN monitor

For the literal generated reference block test, this module proves the two
conditional mean bounds on the causal source-prefix filtration under the
original complete-row/private-coordinate law. The lower bound localizes the
actual all-incoming-inactive round means to an arbitrary prefix cell, then
uses the accepted causal product to average the fresh activity coordinates.
The sufficient fresh event requires all `m - 1` raw activity coins to be
inactive, including unused coins of informed followers; it is proved to lie
inside the actual incoming-inactive guard, with no change to any arm rule.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:638-683` and
`sources/zip4/manuscript/07_public_setup.tex:63-113`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapPhysicalInput
open Bandits.Support.CompletePublicTable
open Bandits.Support.GeneratedBlockDrawLaw
open Bandits.Support.GeneratedBlockGuardLaw
open Bandits.Support.GeneratedBlockStartLaw
open Bandits.Support.GeneratedBootstrapBlockFiltrationRepair
open Bandits.Support.GeneratedBootstrapRoundLaw
open Bandits.Support.GeneratedDownBlockBoundaryMean
open Bandits.Support.GeneratedDownConditionalMean
open Bandits.Support.GeneratedMonitorCountAdaptedness
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferencePrelaunchFollower

namespace Bandits.Support.GeneratedBootstrapMonitorMeans

abbrev Parameters := ConstructorDimensions.Parameters

abbrev Coordinates (p : Parameters) :=
  GeneratedBootstrapBlockFiltrationRepair.Coordinates p

variable {p : Parameters}

/-! ## The literal stopped comparison and normalized processes -/

/-- The actual no-launch event at the incoming boundary of block `s`. -/
def noLaunchEvent (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) : Set (Coordinates p) :=
  {e | (ReferenceInitializationRun.run
    (GeneratedBootstrapBlockFiltrationRepair.referenceInput
      p ids rewards C_star C_h eta e) s.val).crossing = none}

/-- The real zero-one indicator of the existing run's no-launch guard. -/
def noLaunchWeight (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) : Coordinates p → ℝ := by
  classical
  exact fun e => if e ∈ noLaunchEvent p ids rewards C_star C_h eta s then 1 else 0

/-- The normalized literal generated DOWN-positive test for block `s`. -/
def normalizedDownBlockTest (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) (a : Fin p.K) : Coordinates p → ℝ :=
  fun e => downBlockTest p ids rewards C_star C_h eta s a e / (B_boot p : ℝ)

/-- The predictable stopped support process `v_s` from the source monitor
comparison, using the literal rounded-positive count on block `s`. -/
def normalizedDownBlockPredictableValue (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) (a : Fin p.K) : Coordinates p → ℝ :=
  fun e => noLaunchWeight p ids rewards C_star C_h eta s e *
    (roundedPositiveCount p s rewards a /
      ((p.K : ℝ) * (B_boot p : ℝ)))

private def rawInactiveScalars (p : Parameters) : Set PrivateSourceStreams.BlockScalars :=
  {x | activityScalarDraw p x.1 = false}

private def rawInactiveProfile (p : Parameters) :
    Set (Fin (p.m - 1) → PrivateSourceStreams.BlockScalars) :=
  Set.pi Set.univ (fun _ => rawInactiveScalars p)

private def rawInactiveCurrentBlock (p : Parameters) :
    Set (CausalBootstrapBlockProduct.RawCurrentBlock p) :=
  {z | z.1 ∈ rawInactiveProfile p}

private def rawInactiveOriginalEvent (p : Parameters) (s : Fin (n_boot p)) :
    Set (Coordinates p) :=
  {e | (CausalBootstrapBlockProduct.causalProductEquiv p s e).2.1 ∈
    rawInactiveCurrentBlock p}

private theorem measurableSet_rawInactiveScalars (p : Parameters) :
    MeasurableSet (rawInactiveScalars p) := by
  change MeasurableSet {x : PrivateSourceStreams.BlockScalars |
    activityScalarDraw p x.1 = false}
  exact (measurableSet_singleton false).preimage
    ((activityScalarDraw_measurable p).comp measurable_fst)

private theorem measurableSet_rawInactiveProfile (p : Parameters) :
    MeasurableSet (rawInactiveProfile p) := by
  exact MeasurableSet.pi Set.countable_univ (fun _ _ =>
    measurableSet_rawInactiveScalars p)

private theorem measurableSet_rawInactiveCurrentBlock (p : Parameters) :
    MeasurableSet (rawInactiveCurrentBlock p) := by
  have hset : rawInactiveCurrentBlock p =
      rawInactiveProfile p ×ˢ (Set.univ : Set BootstrapPrivateRoundStreams.Scalar) := by
    ext z
    simp [rawInactiveCurrentBlock]
  rw [hset]
  exact (measurableSet_rawInactiveProfile p).prod MeasurableSet.univ

private theorem activityInactiveBlockScalars_mass (p : Parameters) :
    blockScalarsLaw (rawInactiveScalars p) =
      ENNReal.ofReal (BootstrapBlockConstruction.activityProbability p false) := by
  have hset : rawInactiveScalars p =
      (activityScalarDraw p ⁻¹' ({false} : Set Bool)) ×ˢ
        (Set.univ : Set (PrivateSourceStreams.Scalar × PrivateSourceStreams.Scalar)) := by
    ext x
    simp [rawInactiveScalars, Set.mem_preimage]
  rw [hset]
  change (ContinuousCategorical.uniform.prod
      (ContinuousCategorical.uniform.prod ContinuousCategorical.uniform)) _ = _
  rw [Measure.prod_prod, activityScalarDraw_uniform_mass]
  simp

private theorem rawInactiveProfile_mass (p : Parameters) :
    blockScalarProfileLaw p (rawInactiveProfile p) =
      ENNReal.ofReal
        (BootstrapBlockConstruction.activityProbability p false ^ (p.m - 1)) := by
  change Measure.pi (fun _ : Fin (p.m - 1) => blockScalarsLaw) _ = _
  rw [show rawInactiveProfile p =
      Set.pi Set.univ (fun _ : Fin (p.m - 1) => rawInactiveScalars p) by rfl,
    Measure.pi_pi]
  rw [activityInactiveBlockScalars_mass]
  simp only [Finset.prod_const]
  have hq : 0 ≤ BootstrapBlockConstruction.activityProbability p false :=
    BootstrapBlockConstruction.activityProbability_nonneg p false
  rw [← ENNReal.ofReal_pow hq]
  rw [Finset.card_univ, Fintype.card_fin]

private theorem rawInactiveCurrentBlock_mass (p : Parameters) :
    CausalBootstrapBlockProduct.rawCurrentBlockLaw p (rawInactiveCurrentBlock p) =
      ENNReal.ofReal
        (BootstrapBlockConstruction.activityProbability p false ^ (p.m - 1)) := by
  have hset : rawInactiveCurrentBlock p =
      rawInactiveProfile p ×ˢ (Set.univ : Set BootstrapPrivateRoundStreams.Scalar) := by
    ext z
    simp [rawInactiveCurrentBlock]
  rw [CausalBootstrapBlockProduct.rawCurrentBlockLaw, hset, Measure.prod_prod]
  rw [rawInactiveProfile_mass]
  simp

private theorem rawInactiveProbability_ge_quarter (p : Parameters) :
    (1 / 4 : ℝ) ≤ BootstrapBlockConstruction.activityProbability p false ^ (p.m - 1) := by
  have hcard : (sourceIncomingFinset p (ReferenceInitializationRun.initial p)).card =
      p.m - 1 := by
    rw [sourceIncomingFinset_card]
    have hinit : ReferenceInitializationRun.uninformed (ReferenceInitializationRun.initial p) =
        Finset.univ := by
      ext i
      simp [ReferenceInitializationRun.uninformed, ReferenceInitializationRun.initial]
    rw [hinit, Finset.card_univ]
    change Fintype.card (Fin (PublicDiscreteDraws.followerCount p.m)) = p.m - 1
    rw [Fintype.card_fin]
    simp [PublicDiscreteDraws.followerCount]
  have h := allIncomingInactive_probability_ge_quarter p
    (ReferenceInitializationRun.initial p)
  rw [hcard] at h
  simpa [BootstrapBlockConstruction.activityProbability] using h

private theorem rawInactiveProbability_nonneg (p : Parameters) :
    0 ≤ BootstrapBlockConstruction.activityProbability p false ^ (p.m - 1) :=
  pow_nonneg (BootstrapBlockConstruction.activityProbability_nonneg p false) _

/-- A prefix cell, including a null cell, retains the source quarter mass
after intersecting with the fresh event that every original follower activity
coin is inactive. This is the exact product-cylinder consequence on the
original law and literal `sourcePrefix`. -/
private theorem boundaryCell_rawInactive_mass_ge_quarter (p : Parameters)
    (s : Fin (n_boot p)) (A : Set (Coordinates p))
    (hA : MeasurableSet[boundarySigma p s.val] A) :
    (1 / 4 : ℝ) * (GeneratedBootstrapRoundLaw.originalLaw p).real A ≤
      (GeneratedBootstrapRoundLaw.originalLaw p).real
        (A ∩ rawInactiveOriginalEvent p s) := by
  let μ := GeneratedBootstrapRoundLaw.originalLaw p
  obtain ⟨P, hP, hpre⟩ := (MeasurableSpace.measurableSet_comap).mp hA
  have hplain := CausalBootstrapBlockProduct.causalProduct_cylinder p s P
    Set.univ Set.univ Set.univ hP MeasurableSet.univ MeasurableSet.univ
      MeasurableSet.univ
  have hplainSet :
      {e | (CausalBootstrapBlockProduct.causalProductEquiv p s e).1 ∈ P ∧
        (CausalBootstrapBlockProduct.causalProductEquiv p s e).2.1 ∈
          (Set.univ : Set (CausalBootstrapBlockProduct.RawCurrentBlock p)) ∧
        (CausalBootstrapBlockProduct.causalProductEquiv p s e).2.2.1 ∈
          (Set.univ : Set (CausalBootstrapBlockProduct.EntireFutureRow p s)) ∧
        (CausalBootstrapBlockProduct.causalProductEquiv p s e).2.2.2 ∈
          (Set.univ : Set (CausalBootstrapBlockProduct.Remainder p s))} = A := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_univ, and_true]
    rw [CausalBootstrapBlockProduct.causalProductEquiv_sourcePrefix]
    change e ∈ GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p s.val ⁻¹' P ↔ e ∈ A
    rw [hpre]
  rw [hplainSet] at hplain
  have hAENN : μ A = CausalBootstrapBlockProduct.sourcePrefixLaw p s P := by
    simpa [μ] using hplain
  have hjoint := CausalBootstrapBlockProduct.causalProduct_cylinder p s P
    (rawInactiveCurrentBlock p) Set.univ Set.univ hP
    (measurableSet_rawInactiveCurrentBlock p) MeasurableSet.univ MeasurableSet.univ
  have hjointSet :
      {e | (CausalBootstrapBlockProduct.causalProductEquiv p s e).1 ∈ P ∧
        (CausalBootstrapBlockProduct.causalProductEquiv p s e).2.1 ∈
          rawInactiveCurrentBlock p ∧
        (CausalBootstrapBlockProduct.causalProductEquiv p s e).2.2.1 ∈
          (Set.univ : Set (CausalBootstrapBlockProduct.EntireFutureRow p s)) ∧
        (CausalBootstrapBlockProduct.causalProductEquiv p s e).2.2.2 ∈
          (Set.univ : Set (CausalBootstrapBlockProduct.Remainder p s))} =
      A ∩ rawInactiveOriginalEvent p s := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_univ, and_true]
    constructor
    · rintro ⟨hp, hi⟩
      refine ⟨?_, hi⟩
      rw [CausalBootstrapBlockProduct.causalProductEquiv_sourcePrefix] at hp
      have hp' : e ∈ GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p s.val ⁻¹' P := by
        simpa [Set.mem_preimage] using hp
      rw [hpre] at hp'
      exact hp'
    · rintro ⟨ha, hi⟩
      refine ⟨?_, hi⟩
      have ha' : e ∈ GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p s.val ⁻¹' P := by
        rw [hpre]
        exact ha
      have hsrc : GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p s.val e ∈ P := by
        simpa [Set.mem_preimage] using ha'
      rw [← CausalBootstrapBlockProduct.causalProductEquiv_sourcePrefix] at hsrc
      exact hsrc
  rw [hjointSet] at hjoint
  have hmass : μ (A ∩ rawInactiveOriginalEvent p s) =
      μ A * ENNReal.ofReal
        (BootstrapBlockConstruction.activityProbability p false ^ (p.m - 1)) := by
    rw [hjoint, rawInactiveCurrentBlock_mass, hAENN]
    simp only [measure_univ, mul_one]
  have hq := rawInactiveProbability_ge_quarter p
  have hqnonneg := rawInactiveProbability_nonneg p
  have hreal : μ.real (A ∩ rawInactiveOriginalEvent p s) =
      μ.real A * BootstrapBlockConstruction.activityProbability p false ^ (p.m - 1) := by
    change (μ (A ∩ rawInactiveOriginalEvent p s)).toReal =
      (μ A).toReal * BootstrapBlockConstruction.activityProbability p false ^ (p.m - 1)
    rw [hmass, ENNReal.toReal_mul, ENNReal.toReal_ofReal hqnonneg]
  rw [hreal]
  calc
    (1 / 4 : ℝ) * μ.real A = μ.real A * (1 / 4 : ℝ) := by ring
    _ ≤ μ.real A * BootstrapBlockConstruction.activityProbability p false ^ (p.m - 1) :=
      mul_le_mul_of_nonneg_left hq MeasureTheory.measureReal_nonneg

private theorem measurableSet_noLaunchEvent (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) :
    MeasurableSet[boundarySigma p s.val] (noLaunchEvent p ids rewards C_star C_h eta s) := by
  change MeasurableSet[boundarySigma p s.val]
    {e | (ReferenceInitializationRun.run
      (referenceInput p ids rewards C_star C_h eta e) s.val).crossing = none}
  exact measurableSet_noLaunchGuard p s.val ids rewards C_star C_h eta

theorem measurable_noLaunchWeight_at_boundary (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) :
    Measurable[boundarySigma p s.val] (noLaunchWeight p ids rewards C_star C_h eta s) := by
  classical
  have hN := measurableSet_noLaunchEvent p ids rewards C_star C_h eta s
  unfold noLaunchWeight
  exact Measurable.ite hN measurable_const measurable_const

theorem measurable_normalizedDownBlockPredictableValue_at_boundary
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) (a : Fin p.K) :
    Measurable[boundarySigma p s.val]
      (normalizedDownBlockPredictableValue p ids rewards C_star C_h eta s a) := by
  change Measurable[boundarySigma p s.val]
    (fun e => noLaunchWeight p ids rewards C_star C_h eta s e *
      (roundedPositiveCount p s rewards a / ((p.K : ℝ) * (B_boot p : ℝ))))
  exact (measurable_noLaunchWeight_at_boundary p ids rewards C_star C_h eta s).mul_const _

theorem integrable_normalizedDownBlockPredictableValue_originalLaw
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) (a : Fin p.K) :
    Integrable (normalizedDownBlockPredictableValue p ids rewards C_star C_h eta s a)
      (GeneratedBootstrapRoundLaw.originalLaw p) := by
  let c : ℝ := roundedPositiveCount p s rewards a /
    ((p.K : ℝ) * (B_boot p : ℝ))
  have hc : 0 ≤ c := by
    dsimp [c, roundedPositiveCount]
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro t ht
      split_ifs <;> norm_num
    · positivity
  apply Integrable.of_mem_Icc 0 c
  · have hm := (measurable_normalizedDownBlockPredictableValue_at_boundary
      p ids rewards C_star C_h eta s a).mono
        (boundaryFiltration_le_ambient p s.val) (by rfl)
    exact hm.aemeasurable
  · filter_upwards [] with e
    constructor
    · dsimp [normalizedDownBlockPredictableValue, noLaunchWeight, c]
      split <;> positivity
    · dsimp [normalizedDownBlockPredictableValue, noLaunchWeight, c]
      split
      · simp
      · simpa [normalizedDownBlockPredictableValue, noLaunchWeight] using hc

theorem normalizedDownBlockTest_eq_sourceShifted_at_block
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) (a : Fin p.K) (e : Coordinates p) :
    normalizedDownBlockTest p ids rewards C_star C_h eta s a e =
      GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest p ids rewards
        C_star C_h eta (s.val + 1) a e := by
  exact (GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest_at_block
    p ids rewards C_star C_h eta s a e).symm

/-- Preserve the accepted active/stopped counter-increment identity for the
literal block test. Its first-crossing and already-stopped cases remain owned
by `GeneratedMonitorCountAdaptedness`. -/
theorem downBlockTest_eq_referenceCounterIncrement (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) (a : Fin p.K) (e : Coordinates p) :
    downBlockTest p ids rewards C_star C_h eta s a e =
      ((GeneratedMonitorCountAdaptedness.referenceDownBlockCounterIncrementAt
        p ids rewards C_star C_h eta s.val a e : ℕ) : ℝ) :=
  GeneratedMonitorCountAdaptedness.downBlockTest_eq_referenceCounterIncrement
    p ids rewards C_star C_h eta s a e

theorem measurable_normalizedDownBlockTest_at_boundary
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) (a : Fin p.K) :
    @Measurable (Coordinates p) ℝ (boundarySigma p (s.val + 1)) inferInstance
      (normalizedDownBlockTest p ids rewards C_star C_h eta s a) := by
  have hEq : normalizedDownBlockTest p ids rewards C_star C_h eta s a =
      GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest p ids rewards
        C_star C_h eta (s.val + 1) a :=
    funext (normalizedDownBlockTest_eq_sourceShifted_at_block p ids rewards C_star C_h eta s a)
  rw [hEq]
  exact GeneratedMonitorCountAdaptedness.measurable_sourceShiftedDownBlockTest_at_boundary
    p ids rewards C_star C_h eta (s.val + 1) a

theorem integrable_normalizedDownBlockTest_originalLaw
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) (a : Fin p.K) :
    Integrable (normalizedDownBlockTest p ids rewards C_star C_h eta s a)
      (GeneratedBootstrapRoundLaw.originalLaw p) := by
  have hEq : normalizedDownBlockTest p ids rewards C_star C_h eta s a =
      GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest p ids rewards
        C_star C_h eta (s.val + 1) a :=
    funext (normalizedDownBlockTest_eq_sourceShifted_at_block p ids rewards C_star C_h eta s a)
  rw [hEq]
  exact GeneratedMonitorCountAdaptedness.integrable_sourceShiftedDownBlockTest_originalLaw
    p ids rewards C_star C_h eta (s.val + 1) a

/-- The literal normalized test has the accepted unit-interval bound,
including the first crossing block and the clipped final block. -/
theorem normalizedDownBlockTest_mem_unitInterval
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) (a : Fin p.K) (e : Coordinates p) :
    normalizedDownBlockTest p ids rewards C_star C_h eta s a e ∈ Set.Icc 0 1 := by
  rw [normalizedDownBlockTest_eq_sourceShifted_at_block]
  exact GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest_mem_unitInterval
    p ids rewards C_star C_h eta (s.val + 1) a e

/-! ## Conditional mean bounds on arbitrary prefix cells -/

private theorem integrable_downBlockTestOn (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) (a : Fin p.K)
    (A : Set (Coordinates p)) :
    IntegrableOn (downBlockTest p ids rewards C_star C_h eta s a) A
      (GeneratedBootstrapRoundLaw.originalLaw p) :=
  (integrable_downBlockTest ids rewards C_star C_h eta s a).integrableOn

private theorem setIntegral_round_lower_on_inactive (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) (t : Fin p.T)
    (ht : t ∈ calendarBlock p s) (a : Fin p.K) (A : Set (Coordinates p))
    (hA : MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p t.val] A)
    (hguard : ∀ e ∈ A, processedAllInactive
      (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e) = true) :
    (rewardSupport rewards t a / (16 * (p.K : ℝ))) *
        (GeneratedBootstrapRoundLaw.originalLaw p).real A ≤
      ∫ e in A, GeneratedBootstrapFiltration.testValue p ids rewards C_star C_h eta s t
        (downPositiveCurrentTest ids rewards s t a) e
        ∂GeneratedBootstrapRoundLaw.originalLaw p := by
  let f := GeneratedBootstrapFiltration.testValue p ids rewards C_star C_h eta s t
    (downPositiveCurrentTest ids rewards s t a)
  have hf : Integrable f (GeneratedBootstrapRoundLaw.originalLaw p) :=
    GeneratedDownConditionalMean.integrable_downPositiveCurrentTest ids rewards
      C_star C_h eta s t ht a
  have hce := GeneratedDownConditionalMean.actual_downPositive_condExp_lower_on_allInactive
    ids rewards C_star C_h eta s t ht a
  have hAambient : MeasurableSet A :=
    (GeneratedBootstrapFiltration.analysisFiltration_le p t.val) A hA
  have hceRestrict :
      (fun _ : Coordinates p => rewardSupport rewards t a / (16 * (p.K : ℝ))) ≤ᵐ[
        (GeneratedBootstrapRoundLaw.originalLaw p).restrict A]
        condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
          (GeneratedBootstrapRoundLaw.originalLaw p) f := by
    change ∀ᵐ e ∂(GeneratedBootstrapRoundLaw.originalLaw p).restrict A,
      rewardSupport rewards t a / (16 * (p.K : ℝ)) ≤
        condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
          (GeneratedBootstrapRoundLaw.originalLaw p) f e
    apply (ae_restrict_iff' (μ := GeneratedBootstrapRoundLaw.originalLaw p)
      (s := A) hAambient).2
    filter_upwards [hce] with e he hmem
    exact he (hguard e hmem)
  have hcei : Integrable
      (condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
        (GeneratedBootstrapRoundLaw.originalLaw p) f)
      (GeneratedBootstrapRoundLaw.originalLaw p) := integrable_condExp
  have hconstInt : IntegrableOn
      (fun _ : Coordinates p => rewardSupport rewards t a / (16 * (p.K : ℝ))) A
      (GeneratedBootstrapRoundLaw.originalLaw p) := by
    exact (integrable_const _).integrableOn
  have hmono := setIntegral_mono_ae_restrict
    hconstInt hcei.integrableOn hceRestrict
  calc
    (rewardSupport rewards t a / (16 * (p.K : ℝ))) *
        (GeneratedBootstrapRoundLaw.originalLaw p).real A =
      ∫ _e in A, rewardSupport rewards t a / (16 * (p.K : ℝ))
        ∂GeneratedBootstrapRoundLaw.originalLaw p := by
          rw [setIntegral_const]
          simp only [smul_eq_mul, mul_comm]
    _ ≤ ∫ e in A,
        condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
          (GeneratedBootstrapRoundLaw.originalLaw p) f e
        ∂GeneratedBootstrapRoundLaw.originalLaw p := hmono
    _ = ∫ e in A, f e ∂GeneratedBootstrapRoundLaw.originalLaw p :=
      setIntegral_condExp (GeneratedBootstrapFiltration.analysisFiltration_le p t.val) hf hA

private theorem setIntegral_round_upper (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) (t : Fin p.T)
    (ht : t ∈ calendarBlock p s) (a : Fin p.K) (A : Set (Coordinates p))
    (hA : MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p t.val] A) :
    ∫ e in A, GeneratedBootstrapFiltration.testValue p ids rewards C_star C_h eta s t
        (downPositiveCurrentTest ids rewards s t a) e
        ∂GeneratedBootstrapRoundLaw.originalLaw p ≤
      (rewardSupport rewards t a / (p.K : ℝ)) *
        (GeneratedBootstrapRoundLaw.originalLaw p).real A := by
  let f := GeneratedBootstrapFiltration.testValue p ids rewards C_star C_h eta s t
    (downPositiveCurrentTest ids rewards s t a)
  have hf : Integrable f (GeneratedBootstrapRoundLaw.originalLaw p) :=
    GeneratedDownConditionalMean.integrable_downPositiveCurrentTest ids rewards
      C_star C_h eta s t ht a
  have hce := GeneratedDownConditionalMean.actual_downPositive_condExp_upper
    ids rewards C_star C_h eta s t ht a
  have hAambient : MeasurableSet A :=
    (GeneratedBootstrapFiltration.analysisFiltration_le p t.val) A hA
  have hceRestrict :
      condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
        (GeneratedBootstrapRoundLaw.originalLaw p) f ≤ᵐ[
          (GeneratedBootstrapRoundLaw.originalLaw p).restrict A]
        fun _ => rewardSupport rewards t a / (p.K : ℝ) := by
    change ∀ᵐ e ∂(GeneratedBootstrapRoundLaw.originalLaw p).restrict A,
      condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
        (GeneratedBootstrapRoundLaw.originalLaw p) f e ≤ rewardSupport rewards t a / (p.K : ℝ)
    apply (ae_restrict_iff' (μ := GeneratedBootstrapRoundLaw.originalLaw p)
      (s := A) hAambient).2
    filter_upwards [hce] with e he hmem
    exact he
  have hcei : Integrable
      (condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
        (GeneratedBootstrapRoundLaw.originalLaw p) f)
      (GeneratedBootstrapRoundLaw.originalLaw p) := integrable_condExp
  have hconstInt : IntegrableOn
      (fun _ : Coordinates p => rewardSupport rewards t a / (p.K : ℝ)) A
      (GeneratedBootstrapRoundLaw.originalLaw p) := by
    exact (integrable_const _).integrableOn
  have hmono := setIntegral_mono_ae_restrict
    hcei.integrableOn hconstInt hceRestrict
  calc
    _ = ∫ e in A,
        condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
          (GeneratedBootstrapRoundLaw.originalLaw p) f e
        ∂GeneratedBootstrapRoundLaw.originalLaw p :=
      (setIntegral_condExp (GeneratedBootstrapFiltration.analysisFiltration_le p t.val) hf hA).symm
    _ ≤ ∫ _e in A, rewardSupport rewards t a / (p.K : ℝ)
        ∂GeneratedBootstrapRoundLaw.originalLaw p := hmono
    _ = _ := by
      rw [setIntegral_const]
      simp only [smul_eq_mul, mul_comm]

private theorem setIntegral_downBlockTest_eq_sum (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) (a : Fin p.K) (A : Set (Coordinates p)) :
    ∫ e in A, downBlockTest p ids rewards C_star C_h eta s a e
        ∂GeneratedBootstrapRoundLaw.originalLaw p =
      ∑ t ∈ calendarBlock p s,
        ∫ e in A, GeneratedBootstrapFiltration.testValue p ids rewards C_star C_h eta s t
          (downPositiveCurrentTest ids rewards s t a) e
          ∂GeneratedBootstrapRoundLaw.originalLaw p := by
  unfold downBlockTest
  rw [integral_finsetSum]
  intro t ht
  exact (GeneratedDownConditionalMean.integrable_downPositiveCurrentTest ids rewards
    C_star C_h eta s t ht a).integrableOn

private theorem setIntegral_downBlockTest_lower_on_guard (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) (a : Fin p.K) (A : Set (Coordinates p))
    (hA : ∀ t ∈ calendarBlock p s,
      MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p t.val] A)
    (hguard : ∀ e ∈ A, ∀ t ∈ calendarBlock p s,
      processedAllInactive
        (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e) = true) :
    (roundedPositiveCount p s rewards a / (16 * (p.K : ℝ))) *
        (GeneratedBootstrapRoundLaw.originalLaw p).real A ≤
      ∫ e in A, downBlockTest p ids rewards C_star C_h eta s a e
        ∂GeneratedBootstrapRoundLaw.originalLaw p := by
  have hsum := setIntegral_downBlockTest_eq_sum ids rewards C_star C_h eta s a A
  rw [hsum, roundedPositiveCount_eq_rewardSupportCount]
  rw [BootstrapDownCountMean.rewardSupportCount, Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro t ht
  exact setIntegral_round_lower_on_inactive ids rewards C_star C_h eta s t ht a A
    (hA t ht) (fun e he => hguard e he t ht)

private theorem setIntegral_downBlockTest_upper (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) (a : Fin p.K) (A : Set (Coordinates p))
    (hA : ∀ t ∈ calendarBlock p s,
      MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p t.val] A) :
    ∫ e in A, downBlockTest p ids rewards C_star C_h eta s a e
        ∂GeneratedBootstrapRoundLaw.originalLaw p ≤
      (roundedPositiveCount p s rewards a / (p.K : ℝ)) *
        (GeneratedBootstrapRoundLaw.originalLaw p).real A := by
  have hsum := setIntegral_downBlockTest_eq_sum ids rewards C_star C_h eta s a A
  rw [hsum, roundedPositiveCount_eq_rewardSupportCount]
  rw [BootstrapDownCountMean.rewardSupportCount, Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro t ht
  exact setIntegral_round_upper ids rewards C_star C_h eta s t ht a A (hA t ht)

private theorem startGuard_subset_from_rawInactive (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) (e : Coordinates p)
    (hno : e ∈ noLaunchEvent p ids rewards C_star C_h eta s)
    (hraw : e ∈ rawInactiveOriginalEvent p s) :
    processedAllInactive (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s
      (GeneratedDownBlockBoundaryMean.blockStartRound s) e) = true := by
  classical
  let x := GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e
  let b := ReferenceInitializationRun.run x s.val
  have hcross : b.crossing = none := by
    exact hno
  have hprogress := ReferenceInitializationRun.run_progress x s.val (Nat.le_of_lt s.isLt)
  have hnotSome : ¬ b.crossing.isSome = true := by
    simp [hcross]
  have hcompleted : b.completed = s.val := hprogress.resolve_left hnotSome
  have hblock : b.completed < n_boot p := by
    rw [hcompleted]
    exact s.isLt
  have hnext : ReferenceInitializationRun.nextBlock b hblock = s :=
    GeneratedBootstrapRoundLaw.processed_nextBlock ids rewards C_star C_h eta s e hcross hblock
  have hrawAll : ∀ j : Fin (p.m - 1),
      activityScalarDraw p (e.2.1.1 s j).1 = false := by
    have hcurmem : (CausalBootstrapBlockProduct.causalProductEquiv p s e).2.1 ∈
        rawInactiveCurrentBlock p := by
      simpa [rawInactiveOriginalEvent] using hraw
    have hprofile : (CausalBootstrapBlockProduct.causalProductEquiv p s e).2.1.1 ∈
        rawInactiveProfile p := by
      simpa [rawInactiveCurrentBlock] using hcurmem
    have hprofile' : ∀ j : Fin (p.m - 1),
        (CausalBootstrapBlockProduct.causalProductEquiv p s e).2.1.1 j ∈
          rawInactiveScalars p := by
      simpa [rawInactiveProfile] using hprofile
    intro j
    have hj := hprofile' j
    change activityScalarDraw p
      ((CausalBootstrapBlockProduct.causalProductEquiv p s e).2.1.1 j).1 = false at hj
    rw [CausalBootstrapBlockProduct.causalProductEquiv_currentProfile] at hj
    exact hj
  rw [GeneratedBootstrapRoundLaw.descriptor]
  change processedAllInactive
      (GeneratedBootstrapRoundLaw.descriptorAtBoundary p x b
        (GeneratedDownBlockBoundaryMean.blockStartRound s)) = true
  rw [GeneratedBootstrapRoundLaw.descriptorAtBoundary, ite_eq_left hcross, dite_eq_left hblock]
  simp only [GeneratedDownConditionalMean.processedAllInactive]
  rw [decide_eq_true_eq]
  simp only [GeneratedDownConditionalMean.descriptorAllInactive]
  intro j
  rw [hnext]
  simpa [BootstrapPhysicalInput.currentBlockDrawProfile,
    PrivateSourceStreams.blockDrawProfileMap, PrivateSourceStreams.privateBlockDrawMap,
    x, GeneratedBootstrapBlockFiltrationRepair.referenceInput,
    GeneratedBootstrapRoundLaw.input, ReferenceInitializationMeasurability.inputOfCoordinates] using
      hrawAll (BootstrapPhysicalInput.sourceFollowerIndex p j.1)

private theorem roundedPositiveCount_nonneg (s : Fin (n_boot p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K) :
    0 ≤ roundedPositiveCount p s rewards a := by
  unfold roundedPositiveCount
  apply Finset.sum_nonneg
  intro t ht
  split_ifs <;> norm_num

private theorem setIntegral_noLaunchWeight_mul (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) (A : Set (Coordinates p))
    (hA : MeasurableSet[boundarySigma p s.val] A) (c : ℝ) :
    ∫ e in A, noLaunchWeight p ids rewards C_star C_h eta s e * c
      ∂GeneratedBootstrapRoundLaw.originalLaw p =
    c * (GeneratedBootstrapRoundLaw.originalLaw p).real
      (A ∩ noLaunchEvent p ids rewards C_star C_h eta s) := by
  classical
  let N := noLaunchEvent p ids rewards C_star C_h eta s
  let Alive := A ∩ N
  have hN : MeasurableSet[boundarySigma p s.val] N :=
    measurableSet_noLaunchEvent p ids rewards C_star C_h eta s
  have hAambient : MeasurableSet A :=
    (boundaryFiltration_le_ambient p s.val) A hA
  have hNambient : MeasurableSet N :=
    (boundaryFiltration_le_ambient p s.val) N hN
  have hAlive : MeasurableSet Alive := hAambient.inter hNambient
  have hEq : (∫ e in A, noLaunchWeight p ids rewards C_star C_h eta s e * c
      ∂GeneratedBootstrapRoundLaw.originalLaw p) =
      ∫ e in Alive, noLaunchWeight p ids rewards C_star C_h eta s e * c
        ∂GeneratedBootstrapRoundLaw.originalLaw p := by
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      hAambient (Set.inter_subset_left : Alive ⊆ A) (by
        intro e he
        have hnotN : e ∉ N := by
          intro hn
          exact he.2 ⟨he.1, hn⟩
        change (if e ∈ N then (1 : ℝ) else 0) * c = 0
        rw [ite_eq_right hnotN]
        simp)
  calc
    _ = ∫ e in Alive, noLaunchWeight p ids rewards C_star C_h eta s e * c
        ∂GeneratedBootstrapRoundLaw.originalLaw p := hEq
    _ = ∫ _e in Alive, c ∂GeneratedBootstrapRoundLaw.originalLaw p := by
      apply setIntegral_congr_fun hAlive
      intro e he
      change (if e ∈ N then (1 : ℝ) else 0) * c = c
      rw [ite_eq_left he.2]
      ring
    _ = c * (GeneratedBootstrapRoundLaw.originalLaw p).real Alive := by
      rw [setIntegral_const]
      simp only [smul_eq_mul, mul_comm]

private theorem integrable_noLaunchWeight_mul_const (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) (c : ℝ) (hc : 0 ≤ c) :
    Integrable (fun e => noLaunchWeight p ids rewards C_star C_h eta s e * c)
      (GeneratedBootstrapRoundLaw.originalLaw p) := by
  apply Integrable.of_mem_Icc 0 c
  · have hm := (measurable_noLaunchWeight_at_boundary p ids rewards C_star C_h eta s).mul_const c
    have hm' := hm.mono (boundaryFiltration_le_ambient p s.val) (by rfl)
    exact hm'.aemeasurable
  · filter_upwards [] with e
    by_cases he : e ∈ noLaunchEvent p ids rewards C_star C_h eta s
    · simp [noLaunchWeight, he, hc]
    · simp [noLaunchWeight, he, hc]

/-! A conditional-expectation order criterion using only cells in the smaller
sigma algebra. The functions being compared are measurable there, so their
negative sublevel cells belong to this family. -/

private theorem ae_nonneg_of_integrals_on_measurable_cells
    {α : Type*} {F M : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}
    (hFM : F ≤ M) (hf : Integrable f μ)
    (hfF : StronglyMeasurable[F] f)
    (hcell : ∀ A, MeasurableSet[F] A → 0 ≤ ∫ x in A, f x ∂μ) :
    0 ≤ᵐ[μ] f := by
  change ∀ᵐ x ∂μ, (0 : ℝ) ≤ f x
  rw [ae_const_le_iff_forall_lt_measure_zero]
  intro b hb
  let A := {x | f x ≤ b}
  have hA : MeasurableSet[F] A := measurableSet_le hfF.measurable measurable_const
  have hAambient : MeasurableSet A := hFM A hA
  have hmass : μ A < ⊤ := by
    simpa [A] using Integrable.measure_le_lt_top hf hb
  have hIntegralUpper : ∫ x in A, f x ∂μ ≤ b * μ.real A := by
    have hconst : (∫ x in A, f x ∂μ) ≤ ∫ _x in A, b ∂μ := by
      refine setIntegral_mono_ae_restrict hf.integrableOn (integrableOn_const hmass.ne) ?_
      rw [Filter.EventuallyLE, ae_restrict_iff' hAambient]
      exact Filter.Eventually.of_forall (fun x hx => hx)
    rwa [setIntegral_const, smul_eq_mul, mul_comm] at hconst
  have hAzero : μ A = 0 := by
    by_contra hne
    have hpos : 0 < μ.real A := ENNReal.toReal_pos hne hmass.ne
    have hneg : b * μ.real A < 0 := mul_neg_of_neg_of_pos hb hpos
    exact (not_lt_of_ge (hcell A hA) (hIntegralUpper.trans_lt hneg))
  exact hAzero

private theorem ae_le_of_integrals_on_measurable_cells
    {α : Type*} {F M : MeasurableSpace α} {μ : Measure α} {f g : α → ℝ}
    (hFM : F ≤ M) (hf : Integrable f μ) (hg : Integrable g μ)
    (hfF : StronglyMeasurable[F] f) (hgF : StronglyMeasurable[F] g)
    (hcell : ∀ A, MeasurableSet[F] A →
      ∫ x in A, f x ∂μ ≤ ∫ x in A, g x ∂μ) : f ≤ᵐ[μ] g := by
  change ∀ᵐ x ∂μ, f x ≤ g x
  have hdiff : 0 ≤ᵐ[μ] (fun x => g x - f x) := by
    apply ae_nonneg_of_integrals_on_measurable_cells hFM (hg.sub hf) (hgF.sub hfF)
    intro A hA
    rw [integral_sub' hg.integrableOn hf.integrableOn, sub_nonneg]
    exact hcell A hA
  filter_upwards [hdiff] with x hx
  exact sub_nonneg.mp hx

/-- Localized two-sided estimates on every causal boundary cell, without
dividing by its mass. In particular this includes null cells, intersections
with any other boundary event, and both launch-guard cases. -/
theorem boundary_cell_integral_bounds (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) (a : Fin p.K)
    (A : Set (Coordinates p)) (hA : MeasurableSet[boundarySigma p s.val] A) :
    ∫ e in A, noLaunchWeight p ids rewards C_star C_h eta s e *
        (roundedPositiveCount p s rewards a / (64 * (p.K : ℝ)))
        ∂GeneratedBootstrapRoundLaw.originalLaw p ≤
      ∫ e in A, downBlockTest p ids rewards C_star C_h eta s a e
        ∂GeneratedBootstrapRoundLaw.originalLaw p ∧
    ∫ e in A, downBlockTest p ids rewards C_star C_h eta s a e
        ∂GeneratedBootstrapRoundLaw.originalLaw p ≤
      ∫ e in A, noLaunchWeight p ids rewards C_star C_h eta s e *
        (roundedPositiveCount p s rewards a / (p.K : ℝ))
        ∂GeneratedBootstrapRoundLaw.originalLaw p := by
  let μ := GeneratedBootstrapRoundLaw.originalLaw p
  let N := noLaunchEvent p ids rewards C_star C_h eta s
  let Alive := A ∩ N
  let startGuard : Set (Coordinates p) :=
    {e | processedAllInactive (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s
      (GeneratedDownBlockBoundaryMean.blockStartRound s) e) = true}
  let E := Alive ∩ startGuard
  have hN : MeasurableSet[boundarySigma p s.val] N :=
    measurableSet_noLaunchEvent p ids rewards C_star C_h eta s
  have hAlive : MeasurableSet[boundarySigma p s.val] Alive := hA.inter hN
  have hAambient : MeasurableSet A :=
    (boundaryFiltration_le_ambient p s.val) A hA
  have hNambient : MeasurableSet N :=
    (boundaryFiltration_le_ambient p s.val) N hN
  have hAliveAmbient : MeasurableSet Alive := hAambient.inter hNambient
  have hboundaryStart : boundarySigma p s.val ≤
      GeneratedBootstrapFiltration.analysisFiltration p
        (GeneratedDownBlockBoundaryMean.blockStartRound s).val := by
    change boundaryFiltration p s.val ≤ _
    rw [GeneratedDownBlockBoundaryMean.blockStartRound_is_elapsed]
    exact boundaryFiltration_le_analysis_at_elapsed p s.val
  have hstartMeas : MeasurableSet[
      GeneratedBootstrapFiltration.analysisFiltration p
        (GeneratedDownBlockBoundaryMean.blockStartRound s).val] startGuard := by
    change MeasurableSet[
      GeneratedBootstrapFiltration.analysisFiltration p
        (GeneratedDownBlockBoundaryMean.blockStartRound s).val]
      {e | processedAllInactive (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s
        (GeneratedDownBlockBoundaryMean.blockStartRound s) e) = true}
    exact (measurableSet_singleton true).preimage
      (actual_allInactiveGuard_measurable ids rewards C_star C_h eta s
        (GeneratedDownBlockBoundaryMean.blockStartRound s)
        (GeneratedDownBlockBoundaryMean.blockStartRound_mem s))
  have hboundaryAt : ∀ t ∈ calendarBlock p s,
      boundarySigma p s.val ≤ GeneratedBootstrapFiltration.analysisFiltration p t.val := by
    intro t ht
    have htime : (GeneratedDownBlockBoundaryMean.blockStartRound s).val ≤ t.val :=
      ((BootstrapDimensions.mem_calendarBlock_iff p s t).mp ht).1
    exact hboundaryStart.trans ((GeneratedBootstrapFiltration.analysisFiltration p).mono htime)
  have hAliveAt : ∀ t ∈ calendarBlock p s,
      MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p t.val] Alive := by
    intro t ht
    exact (hboundaryAt t ht) Alive hAlive
  have hstartAt : ∀ t ∈ calendarBlock p s,
      MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p t.val] startGuard := by
    intro t ht
    have htime : (GeneratedDownBlockBoundaryMean.blockStartRound s).val ≤ t.val :=
      ((BootstrapDimensions.mem_calendarBlock_iff p s t).mp ht).1
    exact ((GeneratedBootstrapFiltration.analysisFiltration p).mono htime) startGuard hstartMeas
  have hEAt : ∀ t ∈ calendarBlock p s,
      MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p t.val] E := by
    intro t ht
    exact (hAliveAt t ht).inter (hstartAt t ht)
  have hguard : ∀ e ∈ E, ∀ t ∈ calendarBlock p s,
      processedAllInactive (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e) = true := by
    intro e he t ht
    have hno : e ∈ N := he.1.2
    have hstart : e ∈ startGuard := he.2
    let x := GeneratedBootstrapBlockFiltrationRepair.referenceInput
      p ids rewards C_star C_h eta e
    let b := ReferenceInitializationRun.run x s.val
    have hcross : b.crossing = none := hno
    have hprogress := ReferenceInitializationRun.run_progress x s.val
      (Nat.le_of_lt s.isLt)
    have hnotSome : ¬ b.crossing.isSome = true := by
      simp [hcross]
    have hcompleted : b.completed = s.val := hprogress.resolve_left hnotSome
    have hb : GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b := rfl
    exact GeneratedDownBlockBoundaryMean.processedAllInactive_persists_on_block
      ids rewards C_star C_h eta s b hcompleted hcross e hb hstart t ht
  have hglobalMass := boundaryCell_rawInactive_mass_ge_quarter p s Alive hAlive
  have hglobalSubset : Alive ∩ rawInactiveOriginalEvent p s ⊆ E := by
    intro e he
    refine ⟨he.1, ?_⟩
    exact startGuard_subset_from_rawInactive ids rewards C_star C_h eta s e
      he.1.2 he.2
  have hmass : (1 / 4 : ℝ) * μ.real Alive ≤ μ.real E := by
    calc
      _ ≤ μ.real (Alive ∩ rawInactiveOriginalEvent p s) := hglobalMass
      _ ≤ μ.real E := measureReal_mono hglobalSubset
  have hLowerE := setIntegral_downBlockTest_lower_on_guard ids rewards C_star C_h eta s a E
    hEAt hguard
  have hUpperAlive := setIntegral_downBlockTest_upper ids rewards C_star C_h eta s a Alive hAliveAt
  have hEsubset : E ⊆ Alive := Set.inter_subset_left
  have hnonnegRestrict :
      0 ≤ᵐ[μ.restrict Alive] downBlockTest p ids rewards C_star C_h eta s a := by
    apply (ae_restrict_iff' (μ := μ) (s := Alive) hAliveAmbient).2
    filter_upwards [] with e he
    exact (downBlockTest_nonneg_le_boot ids rewards C_star C_h eta s a e).1
  have hEtoAlive :
      ∫ e in E, downBlockTest p ids rewards C_star C_h eta s a e ∂μ ≤
        ∫ e in Alive, downBlockTest p ids rewards C_star C_h eta s a e ∂μ := by
    apply setIntegral_mono_set (integrable_downBlockTestOn ids rewards C_star C_h eta s a Alive)
    · exact hnonnegRestrict
    · exact Filter.Eventually.of_forall (fun e he => hEsubset he)
  have hSnonneg := roundedPositiveCount_nonneg s rewards a
  have hcoef : 0 ≤ roundedPositiveCount p s rewards a / (16 * (p.K : ℝ)) := by
    positivity
  have hK : (p.K : ℝ) ≠ 0 := (Nat.cast_pos.mpr (K_pos p)).ne'
  have hscale :
      (roundedPositiveCount p s rewards a / (64 * (p.K : ℝ))) * μ.real Alive ≤
        (roundedPositiveCount p s rewards a / (16 * (p.K : ℝ))) * μ.real E := by
    calc
      _ = (roundedPositiveCount p s rewards a / (16 * (p.K : ℝ))) *
          ((1 / 4 : ℝ) * μ.real Alive) := by
            field_simp [hK]
            ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass hcoef
  have hLowerAlive :
      (roundedPositiveCount p s rewards a / (64 * (p.K : ℝ))) * μ.real Alive ≤
        ∫ e in Alive, downBlockTest p ids rewards C_star C_h eta s a e ∂μ :=
    hscale.trans (hLowerE.trans hEtoAlive)
  have hfullEq :
      ∫ e in A, downBlockTest p ids rewards C_star C_h eta s a e ∂μ =
        ∫ e in Alive, downBlockTest p ids rewards C_star C_h eta s a e ∂μ := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hAambient
      (Set.inter_subset_left : Alive ⊆ A)
    intro e he
    have hnotN : e ∉ N := by
      intro hn
      exact he.2 ⟨he.1, hn⟩
    have hcross :
        (ReferenceInitializationRun.run
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput
            p ids rewards C_star C_h eta e) s.val).crossing ≠ none := by
      intro hc
      apply hnotN
      exact hc
    exact downBlockTest_eq_zero_when_stopped ids rewards C_star C_h eta s a e (by
      simpa [GeneratedBootstrapRoundLaw.input,
        GeneratedBootstrapBlockFiltrationRepair.referenceInput] using hcross)
  have hNmeanLower := setIntegral_noLaunchWeight_mul ids rewards C_star C_h eta s A hA
    (roundedPositiveCount p s rewards a / (64 * (p.K : ℝ)))
  have hNmeanUpper := setIntegral_noLaunchWeight_mul ids rewards C_star C_h eta s A hA
    (roundedPositiveCount p s rewards a / (p.K : ℝ))
  constructor
  · calc
      ∫ e in A, noLaunchWeight p ids rewards C_star C_h eta s e *
          (roundedPositiveCount p s rewards a / (64 * (p.K : ℝ))) ∂μ =
          (roundedPositiveCount p s rewards a / (64 * (p.K : ℝ))) * μ.real Alive := hNmeanLower
      _ ≤ ∫ e in Alive, downBlockTest p ids rewards C_star C_h eta s a e ∂μ := hLowerAlive
      _ = ∫ e in A, downBlockTest p ids rewards C_star C_h eta s a e ∂μ := hfullEq.symm
  · calc
      ∫ e in A, downBlockTest p ids rewards C_star C_h eta s a e ∂μ =
          ∫ e in Alive, downBlockTest p ids rewards C_star C_h eta s a e ∂μ := hfullEq
      _ ≤ (roundedPositiveCount p s rewards a / (p.K : ℝ)) * μ.real Alive := hUpperAlive
      _ = ∫ e in A, noLaunchWeight p ids rewards C_star C_h eta s e *
          (roundedPositiveCount p s rewards a / (p.K : ℝ)) ∂μ := by
            rw [hNmeanUpper]

/-- Two-sided conditional mean bounds for the literal generated reference
DOWN-block count on the causal boundary filtration and original complete-row
law. The lower estimate uses the actual no-launch guard and every fresh
incoming activity coin; no ID goodness hypothesis is required. -/
theorem downBlockTest_condExp_bounds (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) (a : Fin p.K) :
    (fun e => noLaunchWeight p ids rewards C_star C_h eta s e *
        (roundedPositiveCount p s rewards a / (64 * (p.K : ℝ)))) ≤ᵐ[
      GeneratedBootstrapRoundLaw.originalLaw p]
      condExp (boundarySigma p s.val) (GeneratedBootstrapRoundLaw.originalLaw p)
        (downBlockTest p ids rewards C_star C_h eta s a) ∧
    condExp (boundarySigma p s.val) (GeneratedBootstrapRoundLaw.originalLaw p)
        (downBlockTest p ids rewards C_star C_h eta s a) ≤ᵐ[
      GeneratedBootstrapRoundLaw.originalLaw p]
      (fun e => noLaunchWeight p ids rewards C_star C_h eta s e *
        (roundedPositiveCount p s rewards a / (p.K : ℝ))) := by
  let μ := GeneratedBootstrapRoundLaw.originalLaw p
  let : IsProbabilityMeasure μ := GeneratedBootstrapRoundLaw.originalLaw_probability p
  let : IsFiniteMeasure μ := inferInstance
  let hm : boundarySigma p s.val ≤ (inferInstance : MeasurableSpace (Coordinates p)) :=
    boundaryFiltration_le_ambient p s.val
  have htrimFinite : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  let : IsFiniteMeasure (μ.trim hm) := htrimFinite
  let : SigmaFinite (μ.trim hm) := inferInstance
  let gLower := fun e : Coordinates p => noLaunchWeight p ids rewards C_star C_h eta s e *
    (roundedPositiveCount p s rewards a / (64 * (p.K : ℝ)))
  let gUpper := fun e : Coordinates p => noLaunchWeight p ids rewards C_star C_h eta s e *
    (roundedPositiveCount p s rewards a / (p.K : ℝ))
  have hF : boundarySigma p s.val ≤ (inferInstance : MeasurableSpace (Coordinates p)) := by
    change boundaryFiltration p s.val ≤ _
    exact boundaryFiltration_le_ambient p s.val
  have hf : Integrable (downBlockTest p ids rewards C_star C_h eta s a) μ :=
    integrable_downBlockTest ids rewards C_star C_h eta s a
  have hLowerConst : 0 ≤ roundedPositiveCount p s rewards a /
      (64 * (p.K : ℝ)) := div_nonneg (roundedPositiveCount_nonneg s rewards a) (by positivity)
  have hUpperConst : 0 ≤ roundedPositiveCount p s rewards a / (p.K : ℝ) :=
    div_nonneg (roundedPositiveCount_nonneg s rewards a) (by positivity)
  have hLowerInt := integrable_noLaunchWeight_mul_const ids rewards C_star C_h eta s
    (roundedPositiveCount p s rewards a / (64 * (p.K : ℝ))) hLowerConst
  have hUpperInt := integrable_noLaunchWeight_mul_const ids rewards C_star C_h eta s
    (roundedPositiveCount p s rewards a / (p.K : ℝ)) hUpperConst
  have hLowerSm : StronglyMeasurable[boundarySigma p s.val] gLower := by
    change StronglyMeasurable[boundarySigma p s.val] (fun e =>
      noLaunchWeight p ids rewards C_star C_h eta s e *
        (roundedPositiveCount p s rewards a / (64 * (p.K : ℝ))))
    exact ((measurable_noLaunchWeight_at_boundary p ids rewards C_star C_h eta s).mul_const _).stronglyMeasurable
  have hUpperSm : StronglyMeasurable[boundarySigma p s.val] gUpper := by
    change StronglyMeasurable[boundarySigma p s.val] (fun e =>
      noLaunchWeight p ids rewards C_star C_h eta s e *
        (roundedPositiveCount p s rewards a / (p.K : ℝ)))
    exact ((measurable_noLaunchWeight_at_boundary p ids rewards C_star C_h eta s).mul_const _).stronglyMeasurable
  have hcellBounds := boundary_cell_integral_bounds ids rewards C_star C_h eta s a
  have hLowerCell : ∀ A, MeasurableSet[boundarySigma p s.val] A →
      ∫ e in A, gLower e ∂μ ≤ ∫ e in A, downBlockTest p ids rewards C_star C_h eta s a e ∂μ := by
    intro A hA
    simpa [gLower, μ] using (hcellBounds A hA).1
  have hUpperCell : ∀ A, MeasurableSet[boundarySigma p s.val] A →
      ∫ e in A, downBlockTest p ids rewards C_star C_h eta s a e ∂μ ≤
        ∫ e in A, gUpper e ∂μ := by
    intro A hA
    simpa [gUpper, μ] using (hcellBounds A hA).2
  have hLowerCECell : ∀ A, MeasurableSet[boundarySigma p s.val] A →
      ∫ e in A, gLower e ∂μ ≤
        ∫ e in A, condExp (boundarySigma p s.val) μ
          (downBlockTest p ids rewards C_star C_h eta s a) e ∂μ := by
    intro A hA
    calc
      ∫ e in A, gLower e ∂μ ≤
          ∫ e in A, downBlockTest p ids rewards C_star C_h eta s a e ∂μ := hLowerCell A hA
      _ = ∫ e in A, condExp (boundarySigma p s.val) μ
          (downBlockTest p ids rewards C_star C_h eta s a) e ∂μ := by
            symm
            exact setIntegral_condExp hm hf hA
  have hUpperCECell : ∀ A, MeasurableSet[boundarySigma p s.val] A →
      ∫ e in A, condExp (boundarySigma p s.val) μ
        (downBlockTest p ids rewards C_star C_h eta s a) e ∂μ ≤
        ∫ e in A, gUpper e ∂μ := by
    intro A hA
    calc
      ∫ e in A, condExp (boundarySigma p s.val) μ
          (downBlockTest p ids rewards C_star C_h eta s a) e ∂μ =
          ∫ e in A, downBlockTest p ids rewards C_star C_h eta s a e ∂μ :=
            setIntegral_condExp hm hf hA
      _ ≤ ∫ e in A, gUpper e ∂μ := hUpperCell A hA
  constructor
  · exact ae_le_of_integrals_on_measurable_cells
      (F := boundarySigma p s.val)
      (M := (inferInstance : MeasurableSpace (Coordinates p)))
      (μ := μ) hF hLowerInt integrable_condExp hLowerSm stronglyMeasurable_condExp hLowerCECell
  · exact ae_le_of_integrals_on_measurable_cells
      (F := boundarySigma p s.val)
      (M := (inferInstance : MeasurableSpace (Coordinates p)))
      (μ := μ) hF integrable_condExp hUpperInt stronglyMeasurable_condExp hUpperSm hUpperCECell

/-- Normalized conditional means for the accepted source-shifted process at
time `s.val + 1`, compared with its predictable stopped support value `v_s`. -/
theorem normalizedDownBlockTest_condExp_bounds (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) (a : Fin p.K) :
    (fun e => normalizedDownBlockPredictableValue p ids rewards C_star C_h eta s a e / 64) ≤ᵐ[
      GeneratedBootstrapRoundLaw.originalLaw p]
      condExp (boundarySigma p s.val) (GeneratedBootstrapRoundLaw.originalLaw p)
        (normalizedDownBlockTest p ids rewards C_star C_h eta s a) ∧
    condExp (boundarySigma p s.val) (GeneratedBootstrapRoundLaw.originalLaw p)
        (normalizedDownBlockTest p ids rewards C_star C_h eta s a) ≤ᵐ[
      GeneratedBootstrapRoundLaw.originalLaw p]
      normalizedDownBlockPredictableValue p ids rewards C_star C_h eta s a := by
  let μ := GeneratedBootstrapRoundLaw.originalLaw p
  let : IsProbabilityMeasure μ := GeneratedBootstrapRoundLaw.originalLaw_probability p
  let : IsFiniteMeasure μ := inferInstance
  let B : ℝ := B_boot p
  have hB : 0 < B := by
    change 0 < (B_boot p : ℝ)
    exact_mod_cast B_boot_pos p
  have hK : (p.K : ℝ) ≠ 0 := (Nat.cast_pos.mpr (K_pos p)).ne'
  have hce := downBlockTest_condExp_bounds p ids rewards C_star C_h eta s a
  have hscaled := condExp_smul (μ := μ) (B⁻¹)
    (downBlockTest p ids rewards C_star C_h eta s a) (boundarySigma p s.val)
  have hinput : normalizedDownBlockTest p ids rewards C_star C_h eta s a =
      (B⁻¹) • downBlockTest p ids rewards C_star C_h eta s a := by
    funext e
    simp [normalizedDownBlockTest, B, div_eq_mul_inv, smul_eq_mul]
    ring
  have hceEq : condExp (boundarySigma p s.val) μ
      (normalizedDownBlockTest p ids rewards C_star C_h eta s a) =ᵐ[μ]
      (fun e => condExp (boundarySigma p s.val) μ
        (downBlockTest p ids rewards C_star C_h eta s a) e / B) := by
    filter_upwards [hscaled] with e he
    rw [hinput]
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using he
  have hlow : (fun e =>
      (noLaunchWeight p ids rewards C_star C_h eta s e *
        (roundedPositiveCount p s rewards a / (64 * (p.K : ℝ)))) / B) ≤ᵐ[μ]
      (fun e => condExp (boundarySigma p s.val) μ
        (downBlockTest p ids rewards C_star C_h eta s a) e / B) := by
    filter_upwards [hce.1] with e he
    exact (div_le_div_iff_of_pos_right hB).2 he
  have hupp : (fun e => condExp (boundarySigma p s.val) μ
      (downBlockTest p ids rewards C_star C_h eta s a) e / B) ≤ᵐ[μ]
      (fun e => (noLaunchWeight p ids rewards C_star C_h eta s e *
        (roundedPositiveCount p s rewards a / (p.K : ℝ))) / B) := by
    filter_upwards [hce.2] with e he
    exact (div_le_div_iff_of_pos_right hB).2 he
  have hlowCompare : (fun e => normalizedDownBlockPredictableValue
      p ids rewards C_star C_h eta s a e / 64) =ᵐ[μ]
      (fun e => (noLaunchWeight p ids rewards C_star C_h eta s e *
        (roundedPositiveCount p s rewards a / (64 * (p.K : ℝ)))) / B) := by
    filter_upwards [] with e
    simp only [normalizedDownBlockPredictableValue, B]
    field_simp [hK, hB.ne']
  have huppCompare : (fun e => (noLaunchWeight p ids rewards C_star C_h eta s e *
      (roundedPositiveCount p s rewards a / (p.K : ℝ))) / B) =ᵐ[μ]
      normalizedDownBlockPredictableValue p ids rewards C_star C_h eta s a := by
    filter_upwards [] with e
    simp only [normalizedDownBlockPredictableValue, B]
    field_simp [hK, hB.ne']
  constructor
  · filter_upwards [hlowCompare, hlow, hceEq] with e hcmp hce hce'
    rw [hce']
    exact hcmp.le.trans hce
  · filter_upwards [hceEq, hupp, huppCompare] with e hce' hu hcmp
    rw [hce']
    exact hu.trans hcmp.le

/-- The same normalized comparison stated directly for the accepted
source-shifted observable at time `s.val + 1`, conditional on boundary `s.val`.
No new count process or extension outside the accepted source clock is used. -/
theorem sourceShiftedDownBlockTest_condExp_bounds
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (s : Fin (n_boot p)) (a : Fin p.K) :
    (fun e => normalizedDownBlockPredictableValue p ids rewards C_star C_h eta s a e / 64) ≤ᵐ[
      GeneratedBootstrapRoundLaw.originalLaw p]
      condExp (boundarySigma p s.val) (GeneratedBootstrapRoundLaw.originalLaw p)
        (GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest p ids rewards
          C_star C_h eta (s.val + 1) a) ∧
    condExp (boundarySigma p s.val) (GeneratedBootstrapRoundLaw.originalLaw p)
        (GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest p ids rewards
          C_star C_h eta (s.val + 1) a) ≤ᵐ[
      GeneratedBootstrapRoundLaw.originalLaw p]
      normalizedDownBlockPredictableValue p ids rewards C_star C_h eta s a := by
  have hEq : normalizedDownBlockTest p ids rewards C_star C_h eta s a =
      GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest p ids rewards
        C_star C_h eta (s.val + 1) a :=
    funext (normalizedDownBlockTest_eq_sourceShifted_at_block p ids rewards C_star C_h eta s a)
  rw [← hEq]
  exact normalizedDownBlockTest_condExp_bounds p ids rewards C_star C_h eta s a

/-- The accepted finite-prefix block sum/counter identity specialized to the
literal block tests. Its induction and stopped-history decomposition remain
owned by `GeneratedMonitorCountAdaptedness`. -/
theorem downBlockTest_prefix_sum_eq_counter (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (r : ℕ) (hr : r ≤ n_boot p) (a : Fin p.K)
    (e : Coordinates p) :
    (∑ s : Fin r, downBlockTest p ids rewards C_star C_h eta
      ⟨s.val, Nat.lt_of_lt_of_le s.isLt hr⟩ a e) =
      ((ReferenceInitializationRun.run
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput
          p ids rewards C_star C_h eta e) r).counters a : ℝ) :=
  GeneratedMonitorCountAdaptedness.downBlockTest_sum_eq_counter
    p ids rewards C_star C_h eta r hr a e

end Bandits.Support.GeneratedBootstrapMonitorMeans

end
