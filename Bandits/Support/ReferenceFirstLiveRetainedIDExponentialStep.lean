/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionPrecallOverflowSelectedRowExpectation

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic

/-!
# One first-LIVE calendar step on the retained original identification array

Sources: `04_slow_fast_learner.tex:140-188,245-290`,
`06_interruptions.tex:355-426`, `07_public_setup.tex:123-164`, and
`08_main_theorem.tex:111-130` in the pinned ZIP4 manuscript.

All restrictions below use the original identification projection and the
existing source and branch measures. They require no positive stratum mass.
The whole reward table and unrestricted construction constants remain fixed.
These are internal first-window estimates for the fixed-ID mean consumer.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstLiveRetainedIDExponentialStep

variable {p : ConstructorDimensions.Parameters}

local notation "S" => BootstrapPrivateRoundStreams.SourceInput p
local notation "mu" => BootstrapPrivateRoundStreams.sourceInputLaw p

/-- The literal retained original-ID cylinder in the original source space. -/
def originalIDSet (A : Set (CompletePublicTable.IDArray p)) : Set S :=
  {z | z.1.1 ∈ A}

/-- Erasing current and future selected controls preserves the whole ID array. -/
theorem measurableSet_originalIDSet_prefix
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ)
    (A : Set (CompletePublicTable.IDArray p)) (hA : MeasurableSet A) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (n + 1)] (originalIDSet A) := by
  have hid : Measurable (fun z : S => z.1.1) := measurable_fst.comp measurable_fst
  have hm : Measurable[(inferInstance : MeasurableSpace S).comap
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n)]
      (fun z : S => (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z).1.1) :=
    hid.comp (comap_measurable _)
  change MeasurableSet[(inferInstance : MeasurableSpace S).comap
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (n + 1 - 1))] _
  rw [show n + 1 - 1 = n by omega]
  exact hA.preimage hm

/-- Ambient measurability of the same original-ID cylinder. -/
theorem measurableSet_originalIDSet
    (A : Set (CompletePublicTable.IDArray p)) (hA : MeasurableSet A) :
    MeasurableSet (originalIDSet A) :=
  hA.preimage (measurable_fst.comp measurable_fst)

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p)

local notation "Zplus" => ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
  rate rewards C_star C_h q t s hs control0
local notation "muPlus" => ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
  rate rewards C_star C_h q t s hs control0
local notation "Fplus" => ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField
  rate rewards C_star C_h q t s hs control0
local notation "Ze" => ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
  rate rewards C_star C_h q t s hs control0
local notation "muE" => ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
  rate rewards C_star C_h q t s hs control0
local notation "Fe" => ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty
  rate rewards C_star C_h q t s hs control0
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
variable (a : Fin p.K)

local notation "expAt" => fun (n : ℕ) (z : S) => Real.exp (beta *
  ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt
    rate rewards C_star C_h a n z)

/-- The continuing branch retains the original ID in its actual prefix field. -/
theorem measurableSet_originalIDSet_nonempty
    (A : Set (CompletePublicTable.IDArray p)) (hA : MeasurableSet A) :
    MeasurableSet[Fplus] {z : Zplus | z.val.val.1.1 ∈ A} := by
  have hid : Measurable (fun z : S => z.1.1) := measurable_fst.comp measurable_fst
  have hm : Measurable[Fplus] (fun z : Zplus =>
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val).1.1) :=
    hid.comp (comap_measurable _)
  have heq : (fun z : Zplus =>
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val).1.1) =
      fun z => z.val.val.1.1 := by
    funext z
    rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
    rfl
  rw [heq] at hm
  exact hA.preimage hm

/-- The empty-pending branch uses the same retained original-ID projection. -/
theorem measurableSet_originalIDSet_empty
    (A : Set (CompletePublicTable.IDArray p)) (hA : MeasurableSet A) :
    MeasurableSet[Fe] {z : Ze | z.val.val.1.1 ∈ A} := by
  have hid : Measurable (fun z : S => z.1.1) := measurable_fst.comp measurable_fst
  have hm : Measurable[Fe] (fun z : Ze =>
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val).1.1) :=
    hid.comp (comap_measurable _)
  have heq : (fun z : Ze =>
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val).1.1) =
      fun z => z.val.val.1.1 := by
    funext z
    rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
    rfl
  rw [heq] at hm
  exact hA.preimage hm

/-- Localize the actual continuing conditional step before integrating it. -/
theorem integral_exp_nonempty_originalID_step
    (A : Set (CompletePublicTable.IDArray p)) (hA : MeasurableSet A) :
    (∫ z in {z : Zplus | z.val.val.1.1 ∈ A},
      expAt (t.val + 1) z.val.val - expAt t.val z.val.val ∂muPlus) ≤
      (muPlus).real {z : Zplus | z.val.val.1.1 ∈ A} := by
  let D : Set Zplus := {z | z.val.val.1.1 ∈ A}
  let before := ReferenceFirstLiveConditionalExponentialQueue.expBacklogBefore
    rate rewards C_star C_h q t s hs control0 a
  let after := ReferenceFirstLiveConditionalExponentialQueue.expBacklogAfter
    rate rewards C_star C_h q t s hs control0 a
  have hD : MeasurableSet[Fplus] D :=
    measurableSet_originalIDSet_nonempty rate rewards C_star C_h q t s hs control0 A hA
  have hle := ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
    rate rewards C_star C_h q t s hs control0
  have hb : Integrable before muPlus :=
    ReferenceFirstLiveConditionalExponentialQueue.integrable_expBacklogBefore
      rate rewards C_star C_h q t s hs control0 a
  have ha : Integrable after muPlus :=
    ReferenceFirstLiveConditionalExponentialQueue.integrable_expBacklogAfter
      rate rewards C_star C_h q t s hs control0 a
  have heq : (fun z : Zplus => expAt (t.val + 1) z.val.val - expAt t.val z.val.val) =
      fun z => after z - before z := by
    funext z
    dsimp only
    rw [ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt_after
      rate rewards C_star C_h q t s hs control0 z a,
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt_before
        rate rewards C_star C_h q t s hs control0 z a]
    rfl
  rw [heq, integral_sub ha.integrableOn hb.integrableOn]
  apply (sub_le_iff_le_add').mpr
  calc
    (∫ z in D, after z ∂muPlus) = ∫ z in D, muPlus[after | Fplus] z ∂muPlus :=
      (setIntegral_condExp hle ha hD).symm
    _ ≤ ∫ z in D, 1 + before z ∂muPlus := by
      apply integral_mono_ae integrable_condExp.integrableOn
        ((integrable_const (1 : ℝ)).add hb).integrableOn
      apply ae_restrict_of_ae
      filter_upwards [ReferenceFirstLiveConditionalExponentialQueue.expBacklogAfter_condExp_step
        rate rewards C_star C_h q t s hs control0 a] with z hz
      have hG : (ReferenceFirstLiveAllArmPrefixAdaptation.strictPastOverflowFalseSet
          rate rewards C_star C_h q t s hs control0).indicator (fun _ => (1 : ℝ)) z ≤ 1 := by
        by_cases hmem : z ∈ ReferenceFirstLiveAllArmPrefixAdaptation.strictPastOverflowFalseSet
          rate rewards C_star C_h q t s hs control0
        · simp only [Set.indicator_of_mem hmem, le_refl]
        · simp only [Set.indicator_of_notMem hmem, zero_le_one]
      exact hz.trans (by dsimp only [before, Pi.add_apply]; linarith only [hG])
    _ = (∫ z in D, before z ∂muPlus) + (muPlus).real D := by
      rw [integral_add (integrable_const (1 : ℝ)) hb.integrableOn]
      simp only [integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ]
      exact add_comm _ _

/-- Localize the actual empty-pending conditional step on its prefix field. -/
theorem integral_exp_empty_originalID_step
    (A : Set (CompletePublicTable.IDArray p)) (hA : MeasurableSet A) :
    (∫ z in {z : Ze | z.val.val.1.1 ∈ A},
      expAt (t.val + 1) z.val.val - expAt t.val z.val.val ∂muE) ≤
      (muE).real {z : Ze | z.val.val.1.1 ∈ A} := by
  let D : Set Ze := {z | z.val.val.1.1 ∈ A}
  let before := ReferenceFirstLiveEmptyPendingConditionalExponentialQueue.expBacklogBefore
    rate rewards C_star C_h q t s hs control0 a
  let after := ReferenceFirstLiveEmptyPendingConditionalExponentialQueue.expBacklogAfter
    rate rewards C_star C_h q t s hs control0 a
  have hD : MeasurableSet[Fe] D :=
    measurableSet_originalIDSet_empty rate rewards C_star C_h q t s hs control0 A hA
  have hle := ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
    rate rewards C_star C_h q t s hs control0
  have hb : Integrable before muE :=
    ReferenceFirstLiveEmptyPendingConditionalExponentialQueue.integrable_expBacklogBefore
      rate rewards C_star C_h q t s hs control0 a
  have ha : Integrable after muE :=
    ReferenceFirstLiveEmptyPendingConditionalExponentialQueue.integrable_expBacklogAfter
      rate rewards C_star C_h q t s hs control0 a
  have heq : (fun z : Ze => expAt (t.val + 1) z.val.val - expAt t.val z.val.val) =
      fun z => after z - before z := by
    funext z
    dsimp only
    rw [ReferenceFirstLiveCalendarExponentialBound.firstWindowBacklogAt_empty_after
      rate rewards C_star C_h q t s hs control0 z a,
      ReferenceFirstLiveCalendarExponentialBound.firstWindowBacklogAt_empty_before
        rate rewards C_star C_h q t s hs control0 z a]
    rfl
  rw [heq, integral_sub ha.integrableOn hb.integrableOn]
  apply (sub_le_iff_le_add').mpr
  calc
    (∫ z in D, after z ∂muE) = ∫ z in D, muE[after | Fe] z ∂muE :=
      (setIntegral_condExp hle ha hD).symm
    _ ≤ ∫ z in D, 1 + before z ∂muE := by
      apply integral_mono_ae integrable_condExp.integrableOn
        ((integrable_const (1 : ℝ)).add hb).integrableOn
      exact ae_restrict_of_ae
        (ReferenceFirstLiveEmptyPendingConditionalExponentialQueue.expBacklogAfter_condExp_step
          rate rewards C_star C_h q t s hs control0 a)
    _ = (∫ z in D, before z ∂muE) + (muE).real D := by
      rw [integral_add (integrable_const (1 : ℝ)) hb.integrableOn]
      simp only [integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ]
      exact add_comm _ _

section Birth

local notation "Zbirth" => ReferenceTotalSourceDisintegration.SourceStratum
  rate rewards C_star C_h t (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
local notation "muBirth" => ReferenceTotalSourceDisintegration.sourceStratumMeasure
  rate rewards C_star C_h t (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
local notation "X" => ReferenceFirstLaunchRecordingPhysicalMarker.RetainedStart
  rate rewards C_star C_h q t control0
local notation "muC" => ReferenceRetainedSourceCoupling.retainedRemainderMeasure
  rate rewards C_star C_h q t t.val le_rfl control0
local notation "coords" => ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
  rate rewards C_star C_h q t control0
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "birthY" => ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
  rate rewards C_star C_h q t control0
local notation "firstUpdate" => ReferenceFirstLaunchCommonUpdateSource.firstUpdate
  rate rewards C_star C_h q t control0

open ConstructorDimensions

/-- The birth coordinate selector retains the original ID, without redraws. -/
theorem sourceCoordinates_originalID (z : Zbirth) :
    (coords z).1.val.1.1 = z.val.1.1 := by
  change (ReferenceTotalSourceDisintegration.sourceRetainedInput
    rate rewards C_star C_h t control0
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t) z).val.1.1 = _
  rw [ReferenceTotalSourceDisintegration.sourceRetainedInput_val]
  exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_id p q t z.val

private theorem birth_originalID_mass
    (A : Set (CompletePublicTable.IDArray p)) (hA : MeasurableSet A) :
    muBirth {z : Zbirth | z.val.1.1 ∈ A} = muC {x : X | x.val.1.1 ∈ A} := by
  let B : Set X := {x | x.val.1.1 ∈ A}
  have hB : MeasurableSet B := hA.preimage
    ((measurable_fst.comp measurable_fst).comp measurable_subtype_coe)
  have hm := congrArg (fun ν => ν (B ×ˢ Set.univ))
    (ReferenceFirstLaunchRecordingSourceLaw.map_sourceCoordinates
      rate rewards C_star C_h q t control0)
  rw [Measure.map_apply
      (ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceCoordinates
        rate rewards C_star C_h q t control0) (hB.prod MeasurableSet.univ),
    Measure.prod_prod] at hm
  have heq : coords ⁻¹' (B ×ˢ Set.univ) = {z : Zbirth | z.val.1.1 ∈ A} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, B, Set.mem_ofPred_eq,
      sourceCoordinates_originalID rate rewards C_star C_h q t control0 z]
  rw [heq] at hm
  simpa only [measure_univ, mul_one] using hm

private theorem birth_originalID_firstMoment
    (A : Set (CompletePublicTable.IDArray p)) (hA : MeasurableSet A) :
    (∫ z in {z : Zbirth | z.val.1.1 ∈ A}, birthY z a ∂muBirth) ≤
      (muBirth).real {z : Zbirth | z.val.1.1 ∈ A} := by
  let B : Set X := {x | x.val.1.1 ∈ A}
  have hB : MeasurableSet B := hA.preimage
    ((measurable_fst.comp measurable_fst).comp measurable_subtype_coe)
  have hmom := ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
    rate rewards C_star C_h q t control0 a B Set.univ hB MeasurableSet.univ
  have heq : {z : Zbirth | (coords z).1 ∈ B ∧ (coords z).2.1 ∈ Set.univ} =
      {z : Zbirth | z.val.1.1 ∈ A} := by
    ext z
    simp only [Set.mem_univ, and_true, Set.mem_ofPred_eq, B,
      sourceCoordinates_originalID rate rewards C_star C_h q t control0 z]
  have hfirst := hmom.2.2.2.2.1
  rw [heq] at hfirst
  have hmass := congrArg ENNReal.toReal
    (birth_originalID_mass rate rewards C_star C_h q t control0 A hA)
  have hcoef := ReferenceFirstLaunchCommonUpdateSource.first_update_moment_coefficients_bounds
    rate rewards t a
  have hrho : ((rewards t a).val : ℝ) / (D p : ℝ) ≤ 1 := by
    apply (div_le_one (Nat.cast_pos.mpr (D_pos p))).mpr
    exact_mod_cast Nat.le_of_lt_succ (rewards t a).isLt
  have hc := hcoef.2.1.trans hrho
  rw [hfirst]
  simp only [measure_univ, ENNReal.toReal_one, mul_one]
  rw [show (muC B).toReal = (muBirth).real {z : Zbirth | z.val.1.1 ∈ A} from hmass.symm]
  simpa only [mul_assoc, mul_one] using
    mul_le_mul_of_nonneg_left hc
      (measureReal_nonneg (μ := muBirth) (s := {z : Zbirth | z.val.1.1 ∈ A}))

private theorem birth_readout_bounds (z : Zbirth) (j : Fin p.K) :
    0 ≤ birthY z j ∧ birthY z j ≤ 1 / beta := by
  let rho : ℝ := ((rewards t j).val : ℝ) / (D p : ℝ)
  let xi : ℝ := CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j
  let value : ℝ := QuantizedRecordingMoments.quantizedValue
    (D p) rate.eta.val xi rho
  have hD : 0 < (D p : ℝ) := Nat.cast_pos.mpr (D_pos p)
  have hrho : rho ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [rho]
    refine ⟨div_nonneg (Nat.cast_nonneg _) hD.le, (div_le_one hD).2 ?_⟩
    exact_mod_cast Nat.le_of_lt_succ (rewards t j).isLt
  have hbeta : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hxi : 0 < xi := by
    exact CanonicalRecordingRates.xi_pos p rate.eta.property (fun _ => 1) j
  have hbetaxi : beta ≤ xi := by
    exact CanonicalRecordingRates.beta_le_xi p rate.eta.property (fun _ => 1) j
  have hvalue_nonneg := QuantizedRecordingMoments.quantizedValue_nonneg
    (D p) rate.eta.val xi rho rate.eta.property
  have hvalue_bound := QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le
    (D p) rate.eta.val xi rho beta (D_pos p) rate.eta.property hxi hrho hbeta hbetaxi
  have hreadout := ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout_eq_sourceMarker
    rate rewards C_star C_h q t control0 z j
  change birthY z j = (if
    ReferenceFirstLaunchRecordingSourceLaw.sourceMarker rate rewards C_star C_h q t control0 z = some j
    then value else 0) at hreadout
  by_cases hmarker : ReferenceFirstLaunchRecordingSourceLaw.sourceMarker
      rate rewards C_star C_h q t control0 z = some j
  · rw [hreadout, ite_eq_left hmarker]
    exact ⟨hvalue_nonneg, hvalue_bound⟩
  · rw [hreadout, ite_eq_right hmarker]
    exact ⟨by norm_num, (one_div_pos.mpr hbeta).le⟩

private theorem birth_backlog_eq_max (z : Zbirth) (j : Fin p.K) :
    StoppedQueueBound.normalizedBacklog Q (firstUpdate z) j =
      max 0 (birthY z j - 4) := by
  have hstep := ReferenceFirstLaunchCommonUpdateSource.source_first_update
    rate rewards C_star C_h q t control0 z
  have hreadout : birthY z j =
      (ReferenceFirstLaunchCommonUpdateSource.firstArrival
        rate rewards C_star C_h q t control0 z j : ℝ) /
        (rate.n : ℝ) := by
    have htotal := (hstep.1 j).2.2
    have hcast :
        ((((firstUpdate z).registers j).1 + ((firstUpdate z).registers j).2 : ℕ) : ℝ) =
          (ReferenceFirstLaunchCommonUpdateSource.firstArrival
            rate rewards C_star C_h q t control0 z j : ℝ) := by
      exact_mod_cast htotal
    change ((((firstUpdate z).registers j).1 + ((firstUpdate z).registers j).2 : ℕ) : ℝ) /
        (rate.eta.val * (D p : ℝ)) = _
    rw [hcast]
    rw [rate.n_scale]
  have henabled :
      (ReferenceFirstLaunchCommonUpdateSource.firstCell
        rate rewards C_star C_h q t control0 z).enabled = true := rfl
  have hraw :
      RecordedRoundMoments.rawEstimate Q (RecordedQueueRun.initialState p.K)
        (ReferenceFirstLaunchCommonUpdateSource.firstCell
          rate rewards C_star C_h q t control0 z) j = birthY z j := by
    rw [RecordedRoundMoments.rawEstimate_eq_normalizedQuantizedArrival_of_enabled
      Q (RecordedQueueRun.initialState p.K)
      (ReferenceFirstLaunchCommonUpdateSource.firstCell
        rate rewards C_star C_h q t control0 z) j henabled rfl]
    unfold RecordedRoundMoments.normalizedQuantizedArrival
    change (ReferenceFirstLaunchCommonUpdateSource.firstArrival
      rate rewards C_star C_h q t control0 z j : ℝ) /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) = birthY z j
    rw [hreadout]
    simp [ReferenceFirstLaunchNumericalCell.queueParameters]
  change StoppedQueueBound.normalizedBacklog Q
      (RecordedQueueRun.step Q (RecordedQueueRun.initialState p.K)
        (ReferenceFirstLaunchCommonUpdateSource.firstCell
          rate rewards C_star C_h q t control0 z)) j = _
  rw [RecordedWeightedDrift.normalizedBacklog_step_eq_queueNext
    Q (RecordedQueueRun.initialState p.K)
    (ReferenceFirstLaunchCommonUpdateSource.firstCell
      rate rewards C_star C_h q t control0 z) henabled rfl j,
    hraw]
  simp [QueueSquareDrift.queueNext, RecordedQueueRun.initialState,
    StoppedQueueBound.normalizedBacklog]

include control0 in
/-- Birth is localized through the retained remainder cylinder. The chord
bound and the four-unit service deduction are applied on that very set. -/
theorem integral_exp_birth_originalID_step
    (A : Set (CompletePublicTable.IDArray p)) (hA : MeasurableSet A) :
    (∫ z in {z : Zbirth | z.val.1.1 ∈ A},
      expAt (t.val + 1) z.val - expAt t.val z.val ∂muBirth) ≤
      (muBirth).real {z : Zbirth | z.val.1.1 ∈ A} := by
  let D : Set Zbirth := {z | z.val.1.1 ∈ A}
  let Y : Zbirth → ℝ := fun z => birthY z a
  let c : ℝ := Real.exp (-4 * beta)
  have hbeta : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hmom := ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
    rate rewards C_star C_h q t control0 a Set.univ Set.univ
      MeasurableSet.univ MeasurableSet.univ
  have hY : Integrable Y ((muBirth).restrict D) := hmom.2.2.1.integrableOn
  have hbefore : (fun z : Zbirth => expAt t.val z.val) = fun _ => (1 : ℝ) := by
    funext z
    dsimp only
    rw [ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt_birth_before
      rate rewards C_star C_h q t z a]
    simp only [mul_zero, Real.exp_zero]
  have hafter : (fun z : Zbirth => expAt (t.val + 1) z.val) =
      ReferenceFirstLaunchEnergyInitialization.birthBacklogExponential
        rate rewards C_star C_h q t control0 a := by
    funext z
    dsimp only
    rw [ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt_birth_after
      rate rewards C_star C_h q t control0 z a]
    rfl
  have ha : Integrable (fun z : Zbirth => expAt (t.val + 1) z.val)
      ((muBirth).restrict D) := by
    rw [hafter]
    exact (ReferenceFirstLaunchEnergyInitialization.integrable_birthExponential
      rate rewards C_star C_h q t control0 a).integrableOn
  have hb : Integrable (fun z : Zbirth => expAt t.val z.val)
      ((muBirth).restrict D) := by
    rw [hbefore]
    exact integrable_const _
  have hlinear : Integrable (fun z : Zbirth => c * (1 + (2 * beta) * Y z))
      ((muBirth).restrict D) :=
    ((integrable_const (1 : ℝ)).add (hY.const_mul (2 * beta))).const_mul c
  have hp (z : Zbirth) : expAt (t.val + 1) z.val - expAt t.val z.val ≤
      c * (1 + (2 * beta) * Y z) := by
    have hy := birth_readout_bounds rate rewards C_star C_h q t control0 z a
    have hscaled : beta * Y z ≤ 1 := by
      exact (mul_le_mul_of_nonneg_left hy.2 hbeta.le).trans_eq
        (by field_simp)
    have hchord := RecordedMarginalGrowth.exp_le_one_add_two_mul_of_mem_unit_interval
      (beta * Y z) (mul_nonneg hbeta.le hy.1) hscaled
    have hreflect : ReferenceFirstLaunchEnergyInitialization.birthBacklogExponential
        rate rewards C_star C_h q t control0 a z ≤
        1 + Real.exp (beta * (Y z - 4)) := by
      change Real.exp (beta * StoppedQueueBound.normalizedBacklog Q (firstUpdate z) a) ≤ _
      rw [birth_backlog_eq_max rate rewards C_star C_h q t control0 z a]
      by_cases h : Y z - 4 ≤ 0
      · rw [max_eq_left h]
        simp only [mul_zero, Real.exp_zero]
        linarith only [Real.exp_pos (beta * (Y z - 4))]
      · rw [max_eq_right (le_of_not_ge h)]
        linarith
    have hshift : Real.exp (beta * (Y z - 4)) = c * Real.exp (beta * Y z) := by
      rw [show beta * (Y z - 4) = -4 * beta + beta * Y z by ring, Real.exp_add]
    rw [congrFun hafter z, congrFun hbefore z]
    calc
      _ ≤ Real.exp (beta * (Y z - 4)) := by linarith only [hreflect]
      _ = c * Real.exp (beta * Y z) := hshift
      _ ≤ c * (1 + (2 * beta) * Y z) := by
        have hc : 0 ≤ c := Real.exp_nonneg _
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hchord hc
  have hm := integral_mono (ha.sub hb) hlinear hp
  have hfirst := birth_originalID_firstMoment rate rewards C_star C_h q t control0 a A hA
  have hfactor : c * (1 + 2 * beta) ≤ 1 := by
    have hlower : 1 + 2 * beta ≤ Real.exp (4 * beta) := by
      linarith only [Real.add_one_le_exp (4 * beta), hbeta]
    calc
      c * (1 + 2 * beta) = (1 + 2 * beta) / Real.exp (4 * beta) := by
        dsimp only [c]
        rw [show -4 * beta = -(4 * beta) by ring, Real.exp_neg]
        ring
      _ ≤ 1 := (div_le_iff₀ (Real.exp_pos _)).mpr (by simpa only [one_mul] using hlower)
  calc
    _ ≤ ∫ z in D, c * (1 + (2 * beta) * Y z) ∂muBirth := hm
    _ = c * ((muBirth).real D + (2 * beta) * (∫ z in D, Y z ∂muBirth)) := by
      rw [integral_const_mul, integral_add (integrable_const (1 : ℝ))
        (hY.const_mul (2 * beta)), integral_const_mul]
      simp only [integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ]
    _ ≤ c * ((muBirth).real D + (2 * beta) * (muBirth).real D) := by
      have hscale : (2 * beta) * (∫ z in D, Y z ∂muBirth) ≤
          (2 * beta) * (muBirth).real D :=
        mul_le_mul_of_nonneg_left hfirst (by positivity)
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hscale) (Real.exp_nonneg _)
    _ = (c * (1 + 2 * beta)) * (muBirth).real D := by ring
    _ ≤ (muBirth).real D := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor measureReal_nonneg

end Birth

section Assembly

local notation "phase" => ReferenceFirstLiveSourcePhasePartition.sourcePhase
  rate rewards C_star C_h t
local notation "birthM" => fun (q : Fin (ConstructorDimensions.M p)) =>
  Measure.map
    (Subtype.val : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t) → S)
    (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t))
local notation "plusM" => fun (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)) =>
  Measure.map
    (ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t
      (Fin.val v) (Nat.lt_succ_iff.mp (Fin.isLt v)) control0)
    (ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
      (Fin.val v) (Nat.lt_succ_iff.mp (Fin.isLt v)) control0)
local notation "emptyM" => fun (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)) =>
  Measure.map
    (ReferenceFirstLiveSourcePhasePartition.forgetEmpty rate rewards C_star C_h q t
      (Fin.val v) (Nat.lt_succ_iff.mp (Fin.isLt v)) control0)
    (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
      (Fin.val v) (Nat.lt_succ_iff.mp (Fin.isLt v)) control0)

private theorem integral_source_cells {f : S → ℝ} (hf : Integrable f mu) :
    (∫ z, f z ∂mu) =
      (∫ z in phase 0, f z ∂mu) + (∫ z in phase 1, f z ∂mu) +
      (∫ z in phase 5, f z ∂mu) +
      (∑ q : Fin (ConstructorDimensions.M p), ∫ z, f z ∂birthM q) +
      ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
        ((∫ z, f z ∂plusM q v) + (∫ z, f z ∂emptyM q v)) := by
  have hd := ReferenceFirstLiveCalendarIntegralAssembly.original_source_measure_decomposition
    rate rewards C_star C_h t control0
  have hi := hf
  rw [hd] at hi
  have hiO := hi.left_of_add_measure.left_of_add_measure
  have hiB := hi.left_of_add_measure.right_of_add_measure
  have hiC := hi.right_of_add_measure
  have hB := integral_finsetSum_measure (integrable_finsetSum_measure.mp hiB)
  have hC : (∫ z, f z ∂(∑ q : Fin (ConstructorDimensions.M p),
      ∑ v : Fin (t.val + 1), (plusM q v + emptyM q v))) =
      ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
        ((∫ z, f z ∂plusM q v) + (∫ z, f z ∂emptyM q v)) := by
    rw [integral_finsetSum_measure (integrable_finsetSum_measure.mp hiC)]
    apply Finset.sum_congr rfl
    intro q hq
    have hqInt := integrable_finsetSum_measure.mp hiC q hq
    rw [integral_finsetSum_measure (integrable_finsetSum_measure.mp hqInt)]
    apply Finset.sum_congr rfl
    intro v hv
    have hvInt := integrable_finsetSum_measure.mp hqInt v hv
    exact integral_add_measure hvInt.left_of_add_measure hvInt.right_of_add_measure
  calc
    _ = ∫ z, f z ∂((mu).restrict (phase 0) + (mu).restrict (phase 1) +
        (mu).restrict (phase 5) + (∑ q : Fin (ConstructorDimensions.M p), birthM q) +
        ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
          (plusM q v + emptyM q v)) := by rw [← hd]
    _ = _ := by
      rw [integral_add_measure hi.left_of_add_measure hi.right_of_add_measure,
        integral_add_measure hiO hiB,
        integral_add_measure hiO.left_of_add_measure hiO.right_of_add_measure,
        integral_add_measure hiO.left_of_add_measure.left_of_add_measure
          hiO.left_of_add_measure.right_of_add_measure, hB, hC]

private theorem calendar_increment_zero_on_exception (z : S)
    (hz : z ∈ phase 0 ∨ z ∈ phase 1 ∨ z ∈ phase 5) :
    expAt (t.val + 1) z - expAt t.val z = 0 := by
  have hprefix : (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
        rate rewards C_star C_h z).take
        (t.val + 1 - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) =
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
        rate rewards C_star C_h z).take
        (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) := by
    rcases hz with h0 | h1 | h5
    · change (ReferenceCompletePhysicalHistory.generatedBoundary
        rate z rewards C_star C_h).crossing = none at h0
      rw [(ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
        rate rewards C_star C_h z h0).2.1]
      simp only [List.take_nil]
    · change (ReferenceCompletePhysicalHistory.generatedBoundary
        rate z rewards C_star C_h).crossing.isSome = true ∧
        t.val < ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h at h1
      have hbefore : t.val - ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h = 0 := by omega
      have hafter : t.val + 1 - ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h = 0 := by omega
      rw [hbefore, hafter]
    · change (ReferenceCompletePhysicalHistory.generatedBoundary
        rate z rewards C_star C_h).crossing.isSome = true ∧
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h < t.val ∧
        (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h z).length ≤
          t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h at h5
      have hlen := ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveCells_length
        rate rewards C_star C_h z
      have hb : (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
          rate rewards C_star C_h z).length ≤
          t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
        rw [hlen]
        exact h5.2.2
      have ha : (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
          rate rewards C_star C_h z).length ≤
          t.val + 1 - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
        omega
      rw [List.take_of_length_le ha, List.take_of_length_le hb]
  dsimp only
  simp only [ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt, hprefix, sub_self]

include control0 in
/-- One actual LIVE calendar exponential increment localized on any measurable
set of the retained original identification array. No branch positivity,
no-error, launch, survival, or conditional-moment premise is required.
The named downstream consumer is `ReferenceFirstCollectionPrecallFixedIDMean`.
-/
theorem integral_exp_calendar_originalID_step
    (A : Set (CompletePublicTable.IDArray p)) (hA : MeasurableSet A) :
    (∫ z in originalIDSet A,
      expAt (t.val + 1) z - expAt t.val z ∂mu) ≤
      (mu).real (originalIDSet A ∩ (phase 2 ∪ phase 3 ∪ phase 4)) := by
  let D := originalIDSet A
  let E := phase 2 ∪ phase 3 ∪ phase 4
  let delta : S → ℝ := fun z => expAt (t.val + 1) z - expAt t.val z
  let f : S → ℝ := D.indicator delta
  let g : S → ℝ := (D ∩ E).indicator (fun _ => 1)
  have hD : MeasurableSet D := measurableSet_originalIDSet A hA
  have hE : MeasurableSet E :=
    ((ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
      rate rewards C_star C_h t control0 2).union
      (ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
        rate rewards C_star C_h t control0 3)).union
      (ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
        rate rewards C_star C_h t control0 4)
  have hdelta : Integrable delta mu :=
    (ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowExpBacklogAt
      rate rewards C_star C_h a (t.val + 1)).sub
      (ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowExpBacklogAt
        rate rewards C_star C_h a t.val)
  have hf : Integrable f mu := hdelta.indicator hD
  have hg : Integrable g mu := (integrable_const (1 : ℝ)).indicator (hD.inter hE)
  have hg0 : ∀ z, 0 ≤ g z := by
    intro z
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) z
  have hcell : ∀ {Z : Type} [MeasurableSpace Z] (ν : Measure Z) (ι : Z → S),
      Measurable ι → ν.map ι ≤ mu → (∀ z, ι z ∈ E) →
      (∫ z in ι ⁻¹' D, delta (ι z) ∂ν) ≤ ν.real (ι ⁻¹' D) →
      (∫ z, f z ∂ν.map ι) ≤ ∫ z, g z ∂ν.map ι := by
    intro Z _ ν ι hι hdom hactive hstep
    rw [integral_map hι.aemeasurable (hf.mono_measure hdom).aestronglyMeasurable,
      integral_map hι.aemeasurable (hg.mono_measure hdom).aestronglyMeasurable]
    have hleft : (fun z => f (ι z)) = (ι ⁻¹' D).indicator (fun z => delta (ι z)) := by
      funext z
      by_cases hz : ι z ∈ D
      · have hz' : z ∈ ι ⁻¹' D := hz
        simp only [f, Set.indicator_of_mem hz, Set.indicator_of_mem hz']
      · have hz' : z ∉ ι ⁻¹' D := hz
        simp only [f, Set.indicator_of_notMem hz, Set.indicator_of_notMem hz']
    have hright : (fun z => g (ι z)) = (ι ⁻¹' D).indicator (fun _ => (1 : ℝ)) := by
      funext z
      have he := hactive z
      by_cases hz : ι z ∈ D
      · have hz' : z ∈ ι ⁻¹' D := hz
        simp only [g, Set.indicator_of_mem hz', Set.indicator_of_mem (Set.mem_inter hz he)]
      · have hn : ι z ∉ D ∩ E := fun h => hz h.1
        have hz' : z ∉ ι ⁻¹' D := hz
        simp only [g, Set.indicator_of_notMem hz', Set.indicator_of_notMem hn]
    rw [hleft, hright, integral_indicator (hD.preimage hι),
      integral_indicator (hD.preimage hι), integral_const]
    simpa only [smul_eq_mul, mul_one, measureReal_restrict_apply_univ] using hstep
  have hbirth : ∀ q : Fin (ConstructorDimensions.M p),
      (∫ z, f z ∂birthM q) ≤ ∫ z, g z ∂birthM q := by
    intro q
    apply hcell _ Subtype.val measurable_subtype_coe
    · rw [ReferenceTotalSourceDisintegration.sourceStratumMeasure_map
        rate rewards C_star C_h t control0]
      exact Measure.restrict_le_self
    · intro z
      have hz : z.val ∈ phase 2 := by
        rw [ReferenceFirstLiveCalendarIntegralAssembly.sourcePhase_birth_iUnion
          rate rewards C_star C_h t]
        exact Set.mem_iUnion.mpr ⟨q, z.property⟩
      exact Or.inl (Or.inl hz)
    · exact integral_exp_birth_originalID_step
        rate rewards C_star C_h q t control0 a A hA
  have hplus : ∀ (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)),
      (∫ z, f z ∂plusM q v) ≤ ∫ z, g z ∂plusM q v := by
    intro q v
    apply hcell _ (ReferenceFirstLiveBranchIntegralTransport.forgetBranch
      rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0)
      (measurable_subtype_coe.comp measurable_subtype_coe)
    · rw [ReferenceFirstLiveBranchIntegralTransport.branchSourceMeasure_map_original]
      exact Measure.restrict_le_self
    · intro z
      have hz : z.val.val ∈ phase 3 := by
        rw [ReferenceFirstLiveCalendarIntegralAssembly.sourcePhase_nonempty_iUnion
          rate rewards C_star C_h t control0]
        refine Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨v, ?_⟩⟩
        exact ⟨z.val, z.property, rfl⟩
      exact Or.inl (Or.inr hz)
    · exact integral_exp_nonempty_originalID_step rate rewards C_star C_h q t
        v.val (Nat.lt_succ_iff.mp v.isLt) control0 a A hA
  have hempty : ∀ (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)),
      (∫ z, f z ∂emptyM q v) ≤ ∫ z, g z ∂emptyM q v := by
    intro q v
    apply hcell _ (ReferenceFirstLiveSourcePhasePartition.forgetEmpty
      rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0)
      (measurable_subtype_coe.comp measurable_subtype_coe)
    · rw [ReferenceFirstLiveSourcePhasePartition.muEmpty_map_original]
      exact Measure.restrict_le_self
    · intro z
      have hz : z.val.val ∈ phase 4 := by
        rw [ReferenceFirstLiveCalendarIntegralAssembly.sourcePhase_empty_iUnion
          rate rewards C_star C_h t control0]
        refine Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨v, ?_⟩⟩
        exact ⟨z.val, z.property, rfl⟩
      exact Or.inr hz
    · exact integral_exp_empty_originalID_step rate rewards C_star C_h q t
        v.val (Nat.lt_succ_iff.mp v.isLt) control0 a A hA
  have hexception : ∀ (i : Fin 6), i = 0 ∨ i = 1 ∨ i = 5 →
      (∫ z in phase i, f z ∂mu) ≤ ∫ z in phase i, g z ∂mu := by
    intro i hi
    have hz : (∫ z in phase i, f z ∂mu) = 0 := by
      apply integral_eq_zero_of_ae
      apply (ae_restrict_iff'
        (ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
          rate rewards C_star C_h t control0 i)).mpr
      filter_upwards [] with z hz
      change f z = (0 : ℝ)
      have hm : z ∈ phase 0 ∨ z ∈ phase 1 ∨ z ∈ phase 5 := by
        rcases hi with rfl | rfl | rfl
        · exact Or.inl hz
        · exact Or.inr (Or.inl hz)
        · exact Or.inr (Or.inr hz)
      have hd := calendar_increment_zero_on_exception rate rewards C_star C_h t a z hm
      by_cases hmem : z ∈ D
      · simpa only [f, Set.indicator_of_mem hmem, delta] using hd
      · exact Set.indicator_of_notMem hmem delta
    rw [hz]
    exact integral_nonneg (fun z => hg0 z)
  have htotal : (∫ z, f z ∂mu) ≤ ∫ z, g z ∂mu := by
    rw [integral_source_cells rate rewards C_star C_h t control0 hf,
      integral_source_cells rate rewards C_star C_h t control0 hg]
    apply add_le_add
    · apply add_le_add
      · exact add_le_add (add_le_add
          (hexception 0 (Or.inl rfl)) (hexception 1 (Or.inr (Or.inl rfl))))
          (hexception 5 (Or.inr (Or.inr rfl)))
      · exact Finset.sum_le_sum (fun q _ => hbirth q)
    · apply Finset.sum_le_sum
      intro q _
      exact Finset.sum_le_sum (fun v _ => add_le_add (hplus q v) (hempty q v))
  change (∫ z in D, delta z ∂mu) ≤ (mu).real (D ∩ E)
  calc
    _ = ∫ z, f z ∂mu := (integral_indicator hD).symm
    _ ≤ ∫ z, g z ∂mu := htotal
    _ = (mu).real (D ∩ E) := by
      dsimp only [g]
      rw [integral_indicator (hD.inter hE), integral_const]
      simp only [smul_eq_mul, mul_one, measureReal_restrict_apply_univ]

end Assembly

end Bandits.Support.ReferenceFirstLiveRetainedIDExponentialStep

end
