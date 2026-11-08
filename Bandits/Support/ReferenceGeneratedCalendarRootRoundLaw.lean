/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarPathAgreement
public import Bandits.Support.ReferenceGeneratedCalendarJointRebase

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Root observers on the actual generated calendar

Sources: ZIP4 `06_interruptions.tex:391-397,408-426`,
`04_slow_fast_learner.tex:142-215,329-363`, and
`08_main_theorem.tex:78-100`.

The root is the existing calendar initializer, on its original unnormalized
first-call event. The proper past keeps the strict physical prefix, current
logical slow set, and entire earlier archive. Its full assignment vector is
retained jointly. Renewal uses original label one for initialization and
original label zero for the UPDATE; retention makes no new initial draw.

These are internal component results, without an episode or manuscript
closure claim.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstNextInstallationCellFactors
open ReferenceFirstNextInstallationTransitionLaw
open ReferenceFirstNextInvocationJointLift
open ReferencePostInvocationNoncallGeometry
open ReferencePostInvocationPrefixLocality
open ReferencePostInvocationSupportedDisintegration
open ReferencePostInvocationKilledJointLaw
open ReferenceGeneratedRankCalendarFoundation
open ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarNativePreservation
open ReferenceGeneratedCalendarPathAgreement
open ReferenceFirstLiveActualRefreshTestLaw
  (ErasedAuxiliaryArray actualRefreshScalarSplit erasedAuxiliaryLaw
    insertActualRefreshCoordinate measurable_insertActualRefreshCoordinate scalarZero)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix)

namespace Bandits.Support.ReferenceGeneratedCalendarRootRoundLaw

variable {p : ConstructorDimensions.Parameters}

local instance sourceMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance controlMeasurableSpace :
    MeasurableSpace (ContinuousLearningRows.TimeControl p) := by
  unfold ContinuousLearningRows.TimeControl
  infer_instance

local instance optionMeasurableSpace {X : Type*} [MeasurableSpace X] :
    MeasurableSpace (Option X) := LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance sumSingleton {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y] : MeasurableSingletonClass (X ⊕ Y) where
  measurableSet_singleton x := by
    cases x with
    | inl a => simpa only [Set.image_singleton] using (measurableSet_singleton a).inl_image
    | inr b => simpa only [Set.image_singleton] using (measurableSet_singleton b).inr_image

local instance optionSingleton {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] : MeasurableSingletonClass (Option X) where
  measurableSet_singleton x := by
    have h := (comap_measurable (Equiv.optionEquivSumPUnit X))
      (measurableSet_singleton ((Equiv.optionEquivSumPUnit X) x))
    convert h using 1
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact (Equiv.optionEquivSumPUnit X).injective.eq_iff.symm

abbrev RootPast (rate : ReferenceActivePhysicalStep.RateInput p) :=
  BootstrapPrivateRoundStreams.SourceInput p × (SlowSet p × List (LogicalCell p rate))

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p) (b0 : Bool) (u0 t0 : Fin p.T)

local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p
local notation "Auxiliary" => ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p
local notation "Vector" => AssignmentParameterFibreKernel.AssignmentVector p
local notation "Scalar" => ContinuousControlSlice.Scalar
local notation "Cell" => LogicalCell p rate
local notation "Sample" => CalendarSample rate rewards C_star C_h b0 u0 t0 0
local notation "rootCell" => calendarRootCell rate rewards C_star C_h control0 b0 u0 t0
local notation "rootSource" => calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 0
local notation "observe" => calendarObservation rate rewards C_star C_h control0 b0 u0 t0 0
local notation "law" => calendarLaw rate rewards C_star C_h control0 b0 u0 t0 0

/-- The literal proper root past; the complete source is truncated before
the current innovation, while the old archive is retained in full. -/
def calendarRootPast (w : Sample) : RootPast rate :=
  (sourcePrefix control0 t0.val (rootSource (by omega) w),
    ((rootCell w).slowSet,
      calendarNativePrelist rate rewards C_star C_h control0 b0 u0 t0 0 (by omega) w))

/-- After assignment and before the current innovation, keep the WHOLE
original K+1 vector jointly with the proper past. -/
def calendarRootAssignedPast (w : Sample) : RootPast rate × Vector :=
  (calendarRootPast rate rewards C_star C_h control0 b0 u0 t0 w,
    (calendarOriginalLift rate rewards C_star C_h b0 u0 t0 0 w).2)

theorem measurable_calendarRootCell : Measurable rootCell := by
  cases b0
  · exact measurable_nonrenewedFirstCell rate rewards C_star C_h control0 t0 u0
  · exact measurable_renewedFirstCell rate rewards C_star C_h control0 t0 u0

/-- The native root prelist is the complete original earlier archive. -/
theorem calendarNativePrelist_root (w : Sample) :
    calendarNativePrelist rate rewards C_star C_h control0 b0 u0 t0 0 (by omega) w =
      ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
        t0.castSucc (w.1.1.val, w.1.2) := by
  unfold calendarNativePrelist
  rw [(calendarObservation_root rate rewards C_star C_h control0 b0 u0 t0 (by omega) w).2.2]
  cases b0 <;>
    simp only [branchInitial, nonrenewedInitialObservation, renewedInitialObservation,
      initialExtension, postHistory, nonrenewedTransition, renewedTransition,
      List.dropLast_append_cons, List.dropLast_singleton, List.append_nil]

theorem measurable_calendarRootPast :
    Measurable (calendarRootPast rate rewards C_star C_h control0 b0 u0 t0) := by
  have hp := (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 t0.val).comp
    (measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 0 (by omega))
  have hs : Measurable (fun w : Sample => (rootCell w).slowSet) :=
    (ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_slowSet.comp
      (measurable_calendarRootCell rate rewards C_star C_h control0 b0 u0 t0)).mono le_rfl le_top
  have hsource : Measurable (fun w : Sample => (w.1.1.val, w.1.2)) := by
    cases b0 <;> exact (measurable_subtype_coe.comp measurable_fst.fst).prodMk measurable_fst.snd
  have hL := (ReferenceFirstCollectionLogicalPrefixExtension.measurable_extendedPast
    rate rewards C_star C_h control0 t0.castSucc).comp hsource
  have hL' : Measurable (fun w : Sample =>
      calendarNativePrelist rate rewards C_star C_h control0 b0 u0 t0 0 (by omega) w) := by
    convert hL using 1
    funext w
    exact calendarNativePrelist_root rate rewards C_star C_h control0 b0 u0 t0 w
  exact hp.prodMk (hs.prodMk hL')

theorem measurable_calendarRootAssignedPast :
    Measurable (calendarRootAssignedPast rate rewards C_star C_h control0 b0 u0 t0) :=
  (measurable_calendarRootPast rate rewards C_star C_h control0 b0 u0 t0).prodMk
    (measurable_calendarOriginalLift rate rewards C_star C_h b0 u0 t0 0).snd

omit b0 u0 in
/-- Before renewal's initial draw: no new seed, assignment vector, or
initialization scalar occurs in this observer. -/
def rootBeforeInitialization (za : Source × Auxiliary) : Source × List Cell :=
  (sourcePrefix control0 t0.val za.1,
    ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
      t0.castSucc za)

omit b0 u0 in
theorem measurable_rootBeforeInitialization :
    Measurable (rootBeforeInitialization rate rewards C_star C_h control0 t0) :=
  ((ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 t0.val).comp
    measurable_fst).prodMk
      (ReferenceFirstCollectionLogicalPrefixExtension.measurable_extendedPast
        rate rewards C_star C_h control0 t0.castSucc)

omit b0 u0 in
/-- Changing the initialization scalar leaves EVERY earlier cell unchanged.
All coordinates outside that one scalar stay in the erased FULL array. -/
theorem rootBeforeInitialization_scalar_nonuse (z : Source)
    (e : ErasedAuxiliaryArray t0) (x y : Scalar) :
    rootBeforeInitialization rate rewards C_star C_h control0 t0
        (z, insertActualRefreshCoordinate t0 e x) =
      rootBeforeInitialization rate rewards C_star C_h control0 t0
        (z, insertActualRefreshCoordinate t0 e y) := by
  unfold rootBeforeInitialization
  apply Prod.ext
  · rfl
  apply congrArg Prod.snd
    (ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_auxiliary_ext
      rate rewards C_star C_h t0.val t0.isLt.le z _ _ ?_)
  intro v hv l
  have hne : (v, l) ≠ (t0, (1 : Fin 2)) := by
    intro he
    have he' : v = t0 := congrArg Prod.fst he
    subst v
    exact Nat.lt_irrefl _ hv
  simp only [insertActualRefreshCoordinate, hne, dite_false]

omit b0 in
/-- The actual renewal scalar law, derived from its literal categorical
fibres, including all zero-mass outcomes. -/
theorem rootInitialization_scalar_law
    (z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
      rate rewards C_star C_h u0 t0) :
    ContinuousControlSlice.scalarLaw.map
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalScalarSample rate rewards C_star C_h u0 t0 z) =
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSlowSetPMF rate rewards C_star C_h u0 t0 z).toMeasure := by
  apply Measure.ext_of_singleton
  intro U
  have hm : Measurable
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalScalarSample rate rewards C_star C_h u0 t0 z) :=
    ((ReferenceFirstCollectionRenewalAuxiliaryLaw.measurable_renewalScalarSample
      rate rewards C_star C_h u0 t0).comp (measurable_const.prodMk measurable_id)).mono le_rfl le_top
  rw [Measure.map_apply hm (measurableSet_singleton U),
    PMF.toMeasure_apply_singleton _ U (measurableSet_singleton U)]
  exact ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalScalarSample_fibre
    rate rewards C_star C_h u0 t0 z U

omit b0 control0 in
private theorem initialization_array_test
    (z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
      rate rewards C_star C_h u0 t0)
    (f : ErasedAuxiliaryArray t0 × SlowSet p → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ a, f ((actualRefreshScalarSplit t0 a).1,
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
        rate rewards C_star C_h u0 t0 z a)
      ∂ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p) =
    ∫⁻ e, ∫⁻ U, f (e, U)
      ∂(ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSlowSetPMF
        rate rewards C_star C_h u0 t0 z).toMeasure ∂erasedAuxiliaryLaw t0 := by
  let draw := ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalScalarSample
    rate rewards C_star C_h u0 t0 z
  have hd : Measurable draw := by
    dsimp only [draw]
    exact ((ReferenceFirstCollectionRenewalAuxiliaryLaw.measurable_renewalScalarSample
      rate rewards C_star C_h u0 t0).comp (measurable_const.prodMk measurable_id)).mono le_rfl le_top
  let g : ErasedAuxiliaryArray t0 × Scalar → ℝ≥0∞ := fun ex => f (ex.1, draw ex.2)
  have hg : Measurable g := hf.comp (measurable_fst.prodMk (hd.comp measurable_snd))
  have hs := ReferenceFirstLiveActualRefreshTestLaw.measurePreserving_actualRefreshScalarSplit (p := p) t0
  calc
    _ = ∫⁻ a, g (actualRefreshScalarSplit t0 a)
        ∂ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p := by
      apply lintegral_congr
      intro a
      have hr := (actualRefreshScalarSplit t0).symm_apply_apply a
      rw [ReferenceFirstLiveActualRefreshTestLaw.actualRefreshScalarSplit_symm_apply] at hr
      have hx : (actualRefreshScalarSplit t0 a).2 = a (t0, 1) := by
        have h := congrArg (fun b : Auxiliary => b (t0, 1)) hr
        simpa only [insertActualRefreshCoordinate, dite_true] using h
      dsimp only [g, draw, ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample]
      rw [hx]
    _ = ∫⁻ ex, g ex ∂(erasedAuxiliaryLaw t0).prod ContinuousControlSlice.scalarLaw :=
      hs.lintegral_comp hg
    _ = _ := by
      rw [lintegral_prod _ hg.aemeasurable]
      apply lintegral_congr
      intro e
      rw [← rootInitialization_scalar_law rate rewards C_star C_h u0 t0 z]
      exact (lintegral_map (hf.comp (measurable_const.prodMk measurable_id)) hd).symm

omit b0 in
/-- Renewal's actual initial distribution jointly with the SAME entire
earlier archive and the erased FULL auxiliary array. This is an unnormalized
fixed first-call event law, not an unconditional episode law. -/
theorem rootInitialization_base_test
    (Phi : ((Source × List Cell) ×
      ((Source × ErasedAuxiliaryArray t0) × SlowSet p)) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    (∫⁻ za, Phi
      (rootBeforeInitialization rate rewards C_star C_h control0 t0 (za.1.val, za.2),
        ((za.1.val, (actualRefreshScalarSplit t0 za.2).1),
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
            rate rewards C_star C_h u0 t0 za.1 za.2))
      ∂(ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u0 t0).prod
          (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) =
    ∫⁻ z, ∫⁻ e : ErasedAuxiliaryArray t0, ∫⁻ U,
      Phi (rootBeforeInitialization rate rewards C_star C_h control0 t0
        (z.val, insertActualRefreshCoordinate t0 e scalarZero), ((z.val, e), U))
      ∂(ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSlowSetPMF
        rate rewards C_star C_h u0 t0 z).toMeasure
      ∂erasedAuxiliaryLaw t0
      ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u0 t0 := by
  let Z := ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u0 t0
  let mu := ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u0 t0
  have hz : Measurable (fun za : Z × Auxiliary => za.1.val) :=
    measurable_subtype_coe.comp measurable_fst
  have he : Measurable (fun za : Z × Auxiliary => (actualRefreshScalarSplit t0 za.2).1) :=
    ((actualRefreshScalarSplit t0).measurable.comp measurable_snd).fst
  have hseed : Measurable (fun za : Z × Auxiliary =>
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
        rate rewards C_star C_h u0 t0 za.1 za.2) :=
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurable_renewalAuxiliarySample
      rate rewards C_star C_h u0 t0).mono le_rfl le_top
  have hpast := (measurable_rootBeforeInitialization rate rewards C_star C_h control0 t0).comp
    (hz.prodMk (measurable_snd : Measurable (Prod.snd : Z × Auxiliary → Auxiliary)))
  have htotal : Measurable (fun za : Z × Auxiliary => Phi
      (rootBeforeInitialization rate rewards C_star C_h control0 t0 (za.1.val, za.2),
        ((za.1.val, (actualRefreshScalarSplit t0 za.2).1),
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
            rate rewards C_star C_h u0 t0 za.1 za.2))) :=
    hPhi.comp (hpast.prodMk ((hz.prodMk he).prodMk hseed))
  rw [lintegral_prod _ htotal.aemeasurable]
  apply lintegral_congr
  intro z
  let f : ErasedAuxiliaryArray t0 × SlowSet p → ℝ≥0∞ := fun eU =>
    Phi (rootBeforeInitialization rate rewards C_star C_h control0 t0
      (z.val, insertActualRefreshCoordinate t0 eU.1 scalarZero), ((z.val, eU.1), eU.2))
  have ha : Measurable (fun eU : ErasedAuxiliaryArray t0 × SlowSet p =>
      insertActualRefreshCoordinate t0 eU.1 scalarZero) :=
    (measurable_insertActualRefreshCoordinate t0).comp (measurable_fst.prodMk measurable_const)
  have hp := (measurable_rootBeforeInitialization rate rewards C_star C_h control0 t0).comp
    ((measurable_const (a := z.val)).prodMk ha)
  have hf : Measurable f := hPhi.comp
    (hp.prodMk (((measurable_const (a := z.val)).prodMk measurable_fst).prodMk measurable_snd))
  calc
    _ = ∫⁻ a, f ((actualRefreshScalarSplit t0 a).1,
        ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
          rate rewards C_star C_h u0 t0 z a)
        ∂ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p := by
      apply lintegral_congr
      intro a
      have hr := (actualRefreshScalarSplit t0).symm_apply_apply a
      rw [ReferenceFirstLiveActualRefreshTestLaw.actualRefreshScalarSplit_symm_apply] at hr
      have hp := rootBeforeInitialization_scalar_nonuse rate rewards C_star C_h control0 t0
        z.val (actualRefreshScalarSplit t0 a).1 (actualRefreshScalarSplit t0 a).2 scalarZero
      rw [hr] at hp
      exact congrArg (fun H => Phi (H, ((z.val, (actualRefreshScalarSplit t0 a).1),
        ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
          rate rewards C_star C_h u0 t0 z a))) hp
    _ = _ := initialization_array_test rate rewards C_star C_h u0 t0 z f hf

section RootDraws

omit b0 u0 in
/-- The root current-control output keeps the correlated pair and full
numerical update together with the independent physical proposal. -/
def rootControlDraw (z : FirstInvocationSource rate rewards C_star C_h t0)
    (c : ContinuousLearningRows.TimeControl p) :
    ReferenceRankInstallationCommonUpdateJointLaw.PairUpdate p × Bool :=
  (firstPairUpdateDraw rate rewards C_star C_h control0 t0 z c,
    ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate c)

omit b0 u0 in
def rootControlLaw (z : FirstInvocationSource rate rewards C_star C_h t0) :
    Measure (ReferenceRankInstallationCommonUpdateJointLaw.PairUpdate p × Bool) :=
  (ReferenceRankInstallationCommonUpdateJointLaw.commonUpdateKernel rate rewards t0
    (firstSourceCell rate rewards C_star C_h t0 z).selected.view
    (ReferenceRankInstallationRecorderFastLaw.actualInstallationView_valid
      rate rewards C_star C_h t0 z.val _
      (actualFirstCell_view rate rewards C_star C_h control0 t0 z))
    (ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
      rate rewards C_star C_h control0 t0 z.val)).prod
    (ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate)

omit b0 u0 in
theorem measurable_rootControlDraw (z : FirstInvocationSource rate rewards C_star C_h t0) :
    Measurable (rootControlDraw rate rewards C_star C_h control0 t0 z) :=
  (measurable_firstPairUpdateDraw rate rewards C_star C_h control0 t0 z).prodMk
    (ReferenceFirstLivePostUpdateProposalLaw.measurable_physicalProposalBit rate)

omit b0 u0 in
theorem rootControlDraw_law (z : FirstInvocationSource rate rewards C_star C_h t0) :
    (ContinuousLearningRows.timeControlLaw p).map
      (rootControlDraw rate rewards C_star C_h control0 t0 z) =
      rootControlLaw rate rewards C_star C_h control0 t0 z := by
  exact (firstPairUpdateDraw_joint_proposal rate rewards C_star C_h control0 t0 z).trans
    (congrArg (fun m => m.prod (ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate))
      (firstPairUpdateDraw_law rate rewards C_star C_h control0 t0 z))

private theorem countable_fibre_lintegral {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSingletonClass Y] [Countable Y]
    (mu : Measure X) [IsProbabilityMeasure mu] (f : X → Y) (hf : Measurable f)
    (g : X → ℝ≥0∞) :
    (∫⁻ x, g x ∂mu) = ∫⁻ y, ∫⁻ x, g x ∂FiniteFibreLift.fibreMeasure mu f y ∂mu.map f := by
  have hpartition : mu = Measure.sum (fun y => mu.restrict (FiniteFibreLift.fibre f y)) := by
    have he : (⋃ y, FiniteFibreLift.fibre f y) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      exact Set.mem_iUnion.mpr ⟨f x, rfl⟩
    have hp := Measure.restrict_iUnion (μ := mu) (pairwise_disjoint_fiber f)
      (fun y => FiniteFibreLift.measurableSet_fibre f y hf)
    change mu.restrict (⋃ y, FiniteFibreLift.fibre f y) =
      Measure.sum (fun y => mu.restrict (FiniteFibreLift.fibre f y)) at hp
    rw [he, Measure.restrict_univ] at hp
    exact hp
  conv_rhs => rw [lintegral_countable']
  conv_lhs => rw [hpartition, lintegral_sum_measure]
  apply tsum_congr
  intro y
  rw [Measure.map_apply hf (measurableSet_singleton y), mul_comm]
  have hc := congrArg (fun m => ∫⁻ x, g x ∂m)
    (FiniteFibreLift.fibreMass_smul_fibreMeasure mu f y)
  rw [lintegral_smul_measure, smul_eq_mul] at hc
  exact hc.symm

omit b0 u0 in
/-- Conditional reconstruction retains all physical coordinates as a
correlated graph coordinate. Its null-fibre convention is the original law. -/
def rootControlFibre (z : FirstInvocationSource rate rewards C_star C_h t0)
    (y : ReferenceRankInstallationCommonUpdateJointLaw.PairUpdate p × Bool) :
    Measure (ContinuousLearningRows.TimeControl p) :=
  FiniteFibreLift.fibreMeasure (ContinuousLearningRows.timeControlLaw p)
    (rootControlDraw rate rewards C_star C_h control0 t0 z) y

omit b0 u0 in
/-- Evaluate the current draw by the correlated common-update kernel and
the independent physical proposal, while retaining a complete source graph. -/
theorem rootControl_test (z : FirstInvocationSource rate rewards C_star C_h t0)
    (f : ContinuousLearningRows.TimeControl p → ℝ≥0∞) :
    (∫⁻ c, f c ∂ContinuousLearningRows.timeControlLaw p) =
      ∫⁻ y, ∫⁻ c, f c ∂rootControlFibre rate rewards C_star C_h control0 t0 z y
        ∂rootControlLaw rate rewards C_star C_h control0 t0 z := by
  rw [← rootControlDraw_law rate rewards C_star C_h control0 t0 z]
  exact countable_fibre_lintegral _ _
    (measurable_rootControlDraw rate rewards C_star C_h control0 t0 z) f

omit b0 u0 in
/-- The actual selected UPDATE's next-set readout, with the source held
fixed after its full numerical update and physical proposal. -/
def rootRefreshDraw (z : FirstInvocationSource rate rewards C_star C_h t0) (x : Scalar) : SlowSet p :=
  (actualFirstCell rate rewards C_star C_h control0 t0 z x).nextSlowSet

omit b0 u0 in
theorem rootRefreshDraw_law (z : FirstInvocationSource rate rewards C_star C_h t0) :
    ContinuousControlSlice.scalarLaw.map
      (rootRefreshDraw rate rewards C_star C_h control0 t0 z) =
      firstResidualLaw rate rewards C_star C_h control0 t0 z := by
  have hcell : Measurable (actualFirstCell rate rewards C_star C_h control0 t0 z) :=
    Measurable.of_uncurry_left (measurable_actualFirstCell rate rewards C_star C_h control0 t0)
  have hn : Measurable (fun c : Cell => c.nextSlowSet) :=
    ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_nextSlowSet.mono le_rfl le_top
  change ContinuousControlSlice.scalarLaw.map
    ((fun c : Cell => c.nextSlowSet) ∘ actualFirstCell rate rewards C_star C_h control0 t0 z) = _
  rw [← Measure.map_map hn hcell, actualFirstCell_refresh_law]
  rw [Measure.map_map hn (measurable_of_countable _)]
  change (firstResidualLaw rate rewards C_star C_h control0 t0 z).map id = _
  exact Measure.map_id

omit b0 u0 in
/-- The consumed scalar is retained in the canonical initialized prefix;
its conditional fibre preserves its correlation with the true residual draw. -/
def rootRefreshFibre (z : FirstInvocationSource rate rewards C_star C_h t0) (U : SlowSet p) :
    Measure Scalar :=
  FiniteFibreLift.fibreMeasure ContinuousControlSlice.scalarLaw
    (rootRefreshDraw rate rewards C_star C_h control0 t0 z) U

omit b0 u0 in
theorem rootRefresh_test (z : FirstInvocationSource rate rewards C_star C_h t0) (f : Scalar → ℝ≥0∞) :
    (∫⁻ x, f x ∂ContinuousControlSlice.scalarLaw) =
      ∫⁻ U, ∫⁻ x, f x ∂rootRefreshFibre rate rewards C_star C_h control0 t0 z U
        ∂firstResidualLaw rate rewards C_star C_h control0 t0 z := by
  rw [← rootRefreshDraw_law rate rewards C_star C_h control0 t0 z]
  have hm : Measurable (rootRefreshDraw rate rewards C_star C_h control0 t0 z) :=
    (ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_nextSlowSet.comp
      (Measurable.of_uncurry_left (measurable_actualFirstCell rate rewards C_star C_h control0 t0))).mono le_rfl le_top
  exact countable_fibre_lintegral _ _ hm f

end RootDraws

section NumericalJoin

omit b0 u0 in
/-- The root's native numerical PRE is the prefix of the SAME complete
source word used by the actual installation weight reconstruction. -/
theorem rootBefore_originalWord (z : FirstInvocationSource rate rewards C_star C_h t0) :
    firstBefore rate rewards C_star C_h control0 t0 z =
      RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        ((ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord rate rewards C_star C_h z.val
          (ReferencePostInvocationGeneratedAlignment.firstInvocation_launch rate rewards C_star C_h t0 z)).take
          (t0.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h)) := by
  obtain ⟨L, _c, hfull, _hword, _henabled, _hcurrent, _hpost, hbefore, _hraw, _hupdate⟩ :=
    ReferenceRankInstallationPostUpdateProposalLaw.installationEvent_originalNumericalUpdate
      rate rewards C_star C_h control0 0 t0 z.val z.property
  have hL : L = ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord
      rate rewards C_star C_h z.val
      (ReferencePostInvocationGeneratedAlignment.firstInvocation_launch rate rewards C_star C_h t0 z) :=
    Option.some.inj (hfull.symm.trans
      (ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord_spec rate rewards C_star C_h z.val _))
  rw [hL] at hbefore
  have he := Option.some.inj
    ((firstBefore_spec rate rewards C_star C_h control0 t0 z).symm.trans hbefore)
  exact congrArg (fun v : ReferenceRankInstallationPostUpdateProposalLaw.NumericalState p =>
    (⟨v.1, v.2.1, v.2.2⟩ : RecordedQueueRun.RunState p.K)) he

omit b0 u0 in
/-- On clear PRE, the selected physical complement is precisely the
restriction of the native numerical weight vector. No equality is asserted
on the slow set, where the selected source weights use the anchor. -/
theorem rootSource_numerical_complement (z : FirstInvocationSource rate rewards C_star C_h t0)
    (hclear : (firstBefore rate rewards C_star C_h control0 t0 z).overflow = false) :
    ∀ j : CanonicalFastSampling.FastArm
        (firstSourceCell rate rewards C_star C_h t0 z).selected.view.payload.slowSet,
      (firstSourceCell rate rewards C_star C_h t0 z).selected.view.complementWeights j =
        RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (firstBefore rate rewards C_star C_h control0 t0 z) j.val := by
  let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let hl := ReferencePostInvocationGeneratedAlignment.firstInvocation_launch rate rewards C_star C_h t0 z
  let W := ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord rate rewards C_star C_h z.val hl
  let n := t0.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h
  obtain ⟨L, b, v, hfull, hrecord, hview, hweights⟩ :=
    ReferenceRankInstallationRecorderFoundation.installationEvent_originalComplementWeights
      rate rewards C_star C_h 0 t0 z.val z.property
  have hL : L = W := Option.some.inj (hfull.symm.trans
    (ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord_spec rate rewards C_star C_h z.val hl))
  have hv : v = (firstSourceCell rate rewards C_star C_h t0 z).selected.view :=
    Option.some.inj (hview.symm.trans (actualFirstCell_view rate rewards C_star C_h control0 t0 z))
  subst v
  have ht := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate z.val rewards C_star C_h b.val _ (List.getElem?_eq_getElem b.isLt)
  have hdate := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h t0 z.val _ hrecord).2.2.1
  have hn : n = b.val := by
    have h := congrArg Fin.val hdate
    dsimp only [n]
    omega
  have hlen : n ≤ W.length := by
    rw [ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord_length, hn]
    exact b.isLt.le
  have hbefore : firstBefore rate rewards C_star C_h control0 t0 z =
      RecordedQueueRun.run Q (W.take n) := rootBefore_originalWord rate rewards C_star C_h control0 t0 z
  have hc : (RecordedQueueRun.run Q (W.take n)).overflow = false := by
    rw [← hbefore]
    exact hclear
  have hpre : n ≤ UnstoppedRecordedQueueComparison.firstOverflowPrefix Q W := by
    by_contra hnot
    have hf := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
      Q W n hlen).mpr (by omega)
    rw [hc] at hf
    cases hf
  have hnum := (ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord_numericalPrefix
    rate rewards C_star C_h z.val hl n hlen).2.1
  change RecordedQueueRun.scoreWeight Q (RecordedQueueRun.run Q (W.take n)) =
    (fun i => AssignmentScoreReconstruction.sourceWeightBase p ^
      (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate W i
        (min n (UnstoppedRecordedQueueComparison.firstOverflowPrefix Q W))).1) at hnum
  rw [Nat.min_eq_left hpre] at hnum
  intro j
  rw [hbefore, hnum, hweights j, hL, ← hn]

end NumericalJoin

section RootRefill

local notation "Event" => branchEvent rate rewards C_star C_h b0 u0 t0
local notation "Z" => BranchSource rate rewards C_star C_h b0 u0 t0

include control0 in
/-- Root event invariance uses the root-specific first-call laws, including
renewal's anchor-boundary test. No later-date freshness assertion is used. -/
theorem rootEvent_control_invariant (z : Source) (c : ContinuousLearningRows.TimeControl p) :
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t0 z c ∈ Event ↔ z ∈ Event := by
  cases b0
  · exact nonrenewedEvent_control_invariant rate rewards C_star C_h u0 t0 z c
  · exact renewedEvent_control_invariant rate rewards C_star C_h control0 u0 t0 z c

omit control0 in
theorem measurableSet_rootEvent : MeasurableSet Event := by
  cases b0
  · exact ReferenceFirstLiveCollectionPathJoin.measurableSet_firstLiveCollectionEvent
      rate rewards C_star C_h u0 t0
  · exact ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
      rate rewards C_star C_h u0 t0

/-- The accepted assignment fibre on the root's original source and array. -/
def rootVectorKernel : ProbabilityTheory.Kernel (Z × Auxiliary) Vector := by
  cases b0
  · exact nonrenewedVectorKernel rate rewards C_star C_h u0 t0 control0
  · exact ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel
      rate rewards C_star C_h u0 t0

instance rootVectorKernel_markov : ProbabilityTheory.IsMarkovKernel
    (rootVectorKernel rate rewards C_star C_h control0 b0 u0 t0) := by
  cases b0
  · exact nonrenewedVectorKernel_markov rate rewards C_star C_h u0 t0 control0
  · exact ReferenceFirstCollectionRenewalFibreExtension.renewalAssignmentFibreKernel_markov
      rate rewards C_star C_h u0 t0

omit rate rewards C_star C_h control0 u0 in
/-- Only the actual root UPDATE label is removed. Retained roots consume
original label one; renewed roots consume original label zero. -/
def rootUpdateSplit : Auxiliary ≃ᵐ ErasedAuxiliaryArray t0 × Scalar :=
  if b0 then renewalRefreshScalarSplit t0 else actualRefreshScalarSplit t0

omit rate rewards C_star C_h control0 u0 in
theorem measurePreserving_rootUpdateSplit :
    MeasurePreserving (rootUpdateSplit b0 t0)
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)
      ((erasedAuxiliaryLaw t0).prod ContinuousControlSlice.scalarLaw) := by
  cases b0
  · exact ReferenceFirstLiveActualRefreshTestLaw.measurePreserving_actualRefreshScalarSplit t0
  · exact measurePreserving_renewalRefreshScalarSplit t0

theorem rootVectorKernel_update_nonuse (z : Z) (e : ErasedAuxiliaryArray t0) (x y : Scalar) :
    rootVectorKernel rate rewards C_star C_h control0 b0 u0 t0
        (z, (rootUpdateSplit b0 t0).symm (e, x)) =
      rootVectorKernel rate rewards C_star C_h control0 b0 u0 t0
        (z, (rootUpdateSplit b0 t0).symm (e, y)) := by
  cases b0
  · change nonrenewedVectorKernel rate rewards C_star C_h u0 t0 control0
      (z, (actualRefreshScalarSplit t0).symm (e, x)) =
        nonrenewedVectorKernel rate rewards C_star C_h u0 t0 control0
          (z, (actualRefreshScalarSplit t0).symm (e, y))
    rw [ReferenceFirstLiveActualRefreshTestLaw.actualRefreshScalarSplit_symm_apply,
      ReferenceFirstLiveActualRefreshTestLaw.actualRefreshScalarSplit_symm_apply]
    exact nonrenewedVectorKernel_refreshScalar_ext rate rewards C_star C_h u0 t0 control0 z e x y
  · exact renewalKernel_refreshScalar_ext rate rewards C_star C_h t0 u0 z e x y

theorem rootVectorKernel_prefix_ext (z z' : Z)
    (hp : sourcePrefix control0 t0.val z.val = sourcePrefix control0 t0.val z'.val)
    (a : Auxiliary) :
    rootVectorKernel rate rewards C_star C_h control0 b0 u0 t0 (z, a) =
      rootVectorKernel rate rewards C_star C_h control0 b0 u0 t0 (z', a) := by
  cases b0
  · exact nonrenewedVectorKernel_prefix_ext rate rewards C_star C_h control0 u0 t0 z z' hp a
  · exact renewedVectorKernel_prefix_ext rate rewards C_star C_h control0 u0 t0 z z' hp a

/-- The same installed root source, extracted from the actual branch. -/
def rootInstalledSource (z : Z) (v : Vector) : FirstInvocationSource rate rewards C_star C_h t0 := by
  cases b0
  · exact nonrenewedFirstSource rate rewards C_star C_h t0 u0 z v
  · exact renewedFirstSource rate rewards C_star C_h t0 u0
      (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u0 t0 z v)

theorem measurable_rootInstalledSource : Measurable (fun zv : Z × Vector =>
    rootInstalledSource rate rewards C_star C_h b0 u0 t0 zv.1 zv.2) := by
  cases b0
  · exact measurable_nonrenewedFirstSource rate rewards C_star C_h t0 u0
  · exact (measurable_renewedFirstSource rate rewards C_star C_h t0 u0).comp
      (ReferenceFirstCollectionRenewalVectorInsertion.measurable_put rate rewards C_star C_h u0 t0)

/-- Reconstruct the literal original branch lift. No source, calendar, or
archive is restarted in this map. -/
def rootRestore (q : Fin (M p)) (r : EventRemainder control0 t0 Event q)
    (e : ErasedAuxiliaryArray t0) (v : Vector)
    (c : ContinuousLearningRows.TimeControl p) (x : Scalar) : Sample :=
  ((restoreEventSource control0 t0 Event
    (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) q (r, c),
      (rootUpdateSplit b0 t0).symm (e, x)), v)

theorem rootRestore_currentSource (q : Fin (M p)) (r : EventRemainder control0 t0 Event q)
    (e : ErasedAuxiliaryArray t0) (v : Vector)
    (c : ContinuousLearningRows.TimeControl p) (x : Scalar) :
    rootSource (by omega) (rootRestore rate rewards C_star C_h control0 b0 u0 t0 q r e v c x) =
      (rootInstalledSource rate rewards C_star C_h b0 u0 t0
        (restoreEventSource control0 t0 Event
          (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) q (r, c)) v).val := by
  cases b0 <;> rfl

theorem rootRestore_cell (q : Fin (M p)) (r : EventRemainder control0 t0 Event q)
    (e : ErasedAuxiliaryArray t0) (v : Vector)
    (c : ContinuousLearningRows.TimeControl p) (x : Scalar) :
    rootCell (rootRestore rate rewards C_star C_h control0 b0 u0 t0 q r e v c x) =
      actualFirstCell rate rewards C_star C_h control0 t0
        (rootInstalledSource rate rewards C_star C_h b0 u0 t0
          (restoreEventSource control0 t0 Event
            (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) q (r, c)) v) x := by
  cases b0
  · change actualFirstCell rate rewards C_star C_h control0 t0 _
      (((actualRefreshScalarSplit t0).symm (e, x)) (t0, 1)) = _
    rw [ReferenceFirstLiveActualRefreshTestLaw.actualRefreshScalarSplit_symm_apply]
    simp only [insertActualRefreshCoordinate, dite_true]
    rfl
  · change actualFirstCell rate rewards C_star C_h control0 t0 _
      (insertRenewalRefreshScalar t0 e x (t0, 0)) = _
    rw [insertRenewalRefreshScalar_current]
    rfl

private theorem auxiliary_refill_test {A V : Type*}
    [MeasurableSpace A] [MeasurableSpace V] (mu : Measure A) [IsFiniteMeasure mu]
    (split : Auxiliary ≃ᵐ ErasedAuxiliaryArray t0 × Scalar)
    (hpres : MeasurePreserving split (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)
      ((erasedAuxiliaryLaw t0).prod ContinuousControlSlice.scalarLaw))
    (k : ProbabilityTheory.Kernel (A × Auxiliary) V) [ProbabilityTheory.IsMarkovKernel k]
    (hk : ∀ a e x y, k (a, split.symm (e, x)) = k (a, split.symm (e, y)))
    (f : (A × Auxiliary) × V → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ w, f w ∂(mu.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).compProd k) =
      ∫⁻ a, ∫⁻ e, ∫⁻ v, ∫⁻ x, f ((a, split.symm (e, x)), v)
        ∂ContinuousControlSlice.scalarLaw ∂k (a, split.symm (e, scalarZero))
        ∂erasedAuxiliaryLaw t0 ∂mu := by
  let restore : A × (ErasedAuxiliaryArray t0 × Scalar) → A × Auxiliary :=
    fun w => (w.1, split.symm w.2)
  have hr : Measurable restore := measurable_fst.prodMk (split.symm.measurable.comp measurable_snd)
  let K := k.comap restore hr
  let F : (A × (ErasedAuxiliaryArray t0 × Scalar)) × V → ℝ≥0∞ :=
    fun w => f (restore w.1, w.2)
  have hF : Measurable F := hf.comp ((hr.comp measurable_fst).prodMk measurable_snd)
  have hg : Measurable (fun w => ∫⁻ v, F (w, v) ∂K w) := hF.lintegral_kernel_prod_right'
  have hs := (MeasurePreserving.id mu).prod hpres.symm
  calc
    _ = ∫⁻ w, ∫⁻ v, f (w, v) ∂k w
        ∂mu.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p) :=
      Measure.lintegral_compProd hf
    _ = ∫⁻ w, ∫⁻ v, F (w, v) ∂K w
        ∂mu.prod ((erasedAuxiliaryLaw t0).prod ContinuousControlSlice.scalarLaw) :=
      (hs.lintegral_comp hf.lintegral_kernel_prod_right').symm
    _ = ∫⁻ a, ∫⁻ e, ∫⁻ x, ∫⁻ v, f ((a, split.symm (e, x)), v)
        ∂k (a, split.symm (e, x)) ∂ContinuousControlSlice.scalarLaw ∂erasedAuxiliaryLaw t0 ∂mu := by
      rw [lintegral_prod _ hg.aemeasurable]
      apply lintegral_congr
      intro a
      exact lintegral_prod _ ((hg.comp (measurable_const.prodMk measurable_id)).aemeasurable)
    _ = _ := by
      apply lintegral_congr
      intro a
      apply lintegral_congr
      intro e
      simp_rw [hk a e _ scalarZero]
      apply lintegral_lintegral_swap
      exact (hf.comp
        ((measurable_const.prodMk
          (split.symm.measurable.comp (measurable_const.prodMk measurable_fst))).prodMk
            measurable_snd)).aemeasurable

private theorem kernel_control_swap {C E V : Type*}
    [MeasurableSpace C] [MeasurableSpace E] [MeasurableSpace V]
    (mu : Measure C) [SFinite mu] (nu : Measure E) [SFinite nu]
    (k : ProbabilityTheory.Kernel E V) [ProbabilityTheory.IsMarkovKernel k]
    (f : (C × E) × V → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ c, ∫⁻ e, ∫⁻ v, f ((c, e), v) ∂k e ∂nu ∂mu) =
      ∫⁻ e, ∫⁻ v, ∫⁻ c, f ((c, e), v) ∂mu ∂k e ∂nu := by
  let K : ProbabilityTheory.Kernel (C × E) V :=
    k.comap (Prod.snd : C × E → E) measurable_snd
  have hg : Measurable (fun ce : C × E => ∫⁻ v, f (ce, v) ∂K ce) :=
    hf.lintegral_kernel_prod_right'
  calc
    _ = ∫⁻ e, ∫⁻ c, ∫⁻ v, f ((c, e), v) ∂k e ∂mu ∂nu :=
      lintegral_lintegral_swap hg.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro e
      exact lintegral_lintegral_swap (hf.comp
        ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)).aemeasurable

/-- The actual root lift with the current control and selected UPDATE scalar
exposed after the proper assignment fibre. Every other original coordinate
is retained; event and private-index weights remain unnormalized. -/
theorem calendarLaw_root_refill_test (f : Sample → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ w, f w ∂law (by omega)) =
      ∑ q : Fin (M p), ∫⁻ r : EventRemainder control0 t0 Event q,
        ∫⁻ e : ErasedAuxiliaryArray t0, ∫⁻ v : Vector,
          ∫⁻ c, ∫⁻ x, f (rootRestore rate rewards C_star C_h control0 b0 u0 t0 q r e v c x)
            ∂ContinuousControlSlice.scalarLaw ∂ContinuousLearningRows.timeControlLaw p
            ∂rootVectorKernel rate rewards C_star C_h control0 b0 u0 t0
              (restoreEventSource control0 t0 Event
                (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) q (r, control0),
                (rootUpdateSplit b0 t0).symm (e, scalarZero))
            ∂erasedAuxiliaryLaw t0 ∂eventRemainderLaw control0 t0 Event q := by
  let mu : Measure Z := (BootstrapPrivateRoundStreams.sourceInputLaw p).comap Subtype.val
  have hE := measurableSet_rootEvent rate rewards C_star C_h b0 u0 t0
  have : IsFiniteMeasure mu := by
    constructor
    rw [show mu = (BootstrapPrivateRoundStreams.sourceInputLaw p).comap Subtype.val from rfl,
      comap_subtype_coe_apply hE]
    exact measure_lt_top _ _
  let split := rootUpdateSplit b0 t0
  let k := rootVectorKernel rate rewards C_star C_h control0 b0 u0 t0
  let ke := k.comap (fun ze : Z × ErasedAuxiliaryArray t0 => (ze.1, split.symm (ze.2, scalarZero)))
    (measurable_fst.prodMk (split.symm.measurable.comp (measurable_snd.prodMk measurable_const)))
  let F : ((Z × ErasedAuxiliaryArray t0) × Vector) × Scalar → ℝ≥0∞ := fun wx =>
    f ((wx.1.1.1, split.symm (wx.1.1.2, wx.2)), wx.1.2)
  have hF : Measurable F := hf.comp
    ((measurable_fst.fst.fst.prodMk
      (split.symm.measurable.comp (measurable_fst.fst.snd.prodMk measurable_snd))).prodMk
        measurable_fst.snd)
  let G : Z × ErasedAuxiliaryArray t0 → ℝ≥0∞ := fun ze =>
    ∫⁻ v, ∫⁻ x, F ((ze, v), x) ∂ContinuousControlSlice.scalarLaw ∂ke ze
  have hG : Measurable G := hF.lintegral_prod_right'.lintegral_kernel_prod_right'
  have hroot : law (by omega) =
      (mu.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).compProd k := by
    cases b0 <;> rfl
  rw [hroot]
  change (∫⁻ w : (Z × Auxiliary) × Vector, f w
    ∂(mu.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).compProd k) = _
  rw [auxiliary_refill_test t0 mu split
    (measurePreserving_rootUpdateSplit b0 t0) k
    (rootVectorKernel_update_nonuse rate rewards C_star C_h control0 b0 u0 t0) f hf]
  change (∫⁻ z, ∫⁻ e, G (z, e) ∂erasedAuxiliaryLaw t0 ∂mu) = _
  rw [show mu = _ from eventSourceLaw_eq_sum_restore control0 t0 Event hE
    (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0),
    lintegral_sum_measure, tsum_fintype]
  apply Finset.sum_congr rfl
  intro q _
  have hsum : Measurable (fun z : Z => ∫⁻ e, G (z, e) ∂erasedAuxiliaryLaw t0) :=
    hG.lintegral_prod_right'
  rw [lintegral_map hsum (measurable_restoreEventSource control0 t0 Event _ q)]
  have hprod : Measurable (fun rc : EventRemainder control0 t0 Event q ×
      ContinuousLearningRows.TimeControl p => ∫⁻ e,
      G (restoreEventSource control0 t0 Event
        (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) q rc, e)
      ∂erasedAuxiliaryLaw t0) :=
    hsum.comp (measurable_restoreEventSource control0 t0 Event _ q)
  rw [lintegral_prod _ hprod.aemeasurable]
  apply lintegral_congr
  intro r
  let restore := restoreEventSource control0 t0 Event
    (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) q
  let kr := k.comap (fun e : ErasedAuxiliaryArray t0 => (restore (r, control0), split.symm (e, scalarZero)))
    (measurable_const.prodMk (split.symm.measurable.comp (measurable_id.prodMk measurable_const)))
  have hfreeze (c : ContinuousLearningRows.TimeControl p) (e : ErasedAuxiliaryArray t0) :
      ke (restore (r, c), e) = kr e :=
    rootVectorKernel_prefix_ext rate rewards C_star C_h control0 b0 u0 t0 _ _
      (restoreEventSource_prefix control0 t0 Event
        (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) q r c) _
  change (∫⁻ c, ∫⁻ e, ∫⁻ v, ∫⁻ x, F (((restore (r, c), e), v), x)
    ∂ContinuousControlSlice.scalarLaw ∂ke (restore (r, c), e) ∂erasedAuxiliaryLaw t0
      ∂ContinuousLearningRows.timeControlLaw p) = _
  simp_rw [hfreeze]
  let H : ((ContinuousLearningRows.TimeControl p × ErasedAuxiliaryArray t0) × Vector) × Scalar → ℝ≥0∞ :=
    fun wx => F (((restore (r, wx.1.1.1), wx.1.1.2), wx.1.2), wx.2)
  have hr : Measurable (fun c : ContinuousLearningRows.TimeControl p => restore (r, c)) :=
    (measurable_restoreEventSource control0 t0 Event _ q).comp (measurable_const.prodMk measurable_id)
  have hH : Measurable H := hF.comp
    ((((hr.comp measurable_fst.fst.fst).prodMk measurable_fst.fst.snd).prodMk
      measurable_fst.snd).prodMk measurable_snd)
  exact kernel_control_swap (ContinuousLearningRows.timeControlLaw p) (erasedAuxiliaryLaw t0)
    kr (fun w => ∫⁻ x, H (w, x) ∂ContinuousControlSlice.scalarLaw) hH.lintegral_prod_right'

/- The two fibre integrals below retain full current controls and the consumed
UPDATE scalar only as correlated graph coordinates. The independent past is
the separate literal `calendarRootAssignedPast` observer. -/
theorem calendarLaw_root_raw_test (f : Sample → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ w, f w ∂law (by omega)) =
      ∑ q : Fin (M p), ∫⁻ r : EventRemainder control0 t0 Event q,
        ∫⁻ e : ErasedAuxiliaryArray t0, ∫⁻ v : Vector,
          let z0 := rootInstalledSource rate rewards C_star C_h b0 u0 t0
            (restoreEventSource control0 t0 Event
              (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) q (r, control0)) v
          ∫⁻ y, ∫⁻ c,
            let z := rootInstalledSource rate rewards C_star C_h b0 u0 t0
              (restoreEventSource control0 t0 Event
                (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) q (r, c)) v
            ∫⁻ U, ∫⁻ x, f (rootRestore rate rewards C_star C_h control0 b0 u0 t0 q r e v c x)
              ∂rootRefreshFibre rate rewards C_star C_h control0 t0 z U
              ∂firstResidualLaw rate rewards C_star C_h control0 t0 z
              ∂rootControlFibre rate rewards C_star C_h control0 t0 z0 y
              ∂rootControlLaw rate rewards C_star C_h control0 t0 z0
            ∂rootVectorKernel rate rewards C_star C_h control0 b0 u0 t0
              (restoreEventSource control0 t0 Event
                (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) q (r, control0),
                (rootUpdateSplit b0 t0).symm (e, scalarZero))
            ∂erasedAuxiliaryLaw t0 ∂eventRemainderLaw control0 t0 Event q := by
  rw [calendarLaw_root_refill_test rate rewards C_star C_h control0 b0 u0 t0 f hf]
  apply Finset.sum_congr rfl
  intro q _
  apply lintegral_congr
  intro r
  apply lintegral_congr
  intro e
  apply lintegral_congr
  intro v
  dsimp only
  rw [rootControl_test rate rewards C_star C_h control0 t0
    (rootInstalledSource rate rewards C_star C_h b0 u0 t0
      (restoreEventSource control0 t0 Event
        (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) q (r, control0)) v)]
  apply lintegral_congr
  intro y
  apply lintegral_congr
  intro c
  exact rootRefresh_test rate rewards C_star C_h control0 t0 _ _

/-- Joint cylinder carrier for the literal root observer, its correlated
physical pair/full UPDATE/proposal, native cell, initializer and prefix. -/
abbrev RootRoundData :=
  (RootPast rate × Vector) ×
    ((ReferenceRankInstallationCommonUpdateJointLaw.PairUpdate p × Bool) ×
      (Cell × (InitialObservation rate t0 × PrefixObservation rate t0 t0.succ)))

def calendarRootRoundReadout (w : Sample) : RootRoundData rate t0 :=
  (calendarRootAssignedPast rate rewards C_star C_h control0 b0 u0 t0 w,
    (((ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast
        rate rewards C_star C_h t0 (rootSource (by omega) w),
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
        rate rewards C_star C_h control0 t0 (rootSource (by omega) w)),
      ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
        (ReferenceSourceCurrentControlFreshness.u_t p t0 (rootSource (by omega) w))),
      (rootCell w, (branchInitial rate rewards C_star C_h control0 b0 u0 t0 w,
        (observe (by omega) w).2.val))))

theorem measurable_calendarRootRoundReadout :
    Measurable (calendarRootRoundReadout rate rewards C_star C_h control0 b0 u0 t0) := by
  have hs := measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 0 (by omega)
  have hpair := (ReferenceRankInstallationRecorderFastLaw.measurable_actualMarkerReservedFast
    rate rewards C_star C_h t0).comp hs
  have hupdate := (ReferenceRankInstallationPostUpdateProposalLaw.measurable_actualInstallationNumericalUpdate
    rate rewards C_star C_h control0 t0).comp hs
  have hproposal := (ReferenceFirstLivePostUpdateProposalLaw.measurable_physicalProposalBit rate).comp
    ((ReferenceSourceCurrentControlFreshness.measurable_u_t t0).comp hs)
  have hi := measurable_branchInitial rate rewards C_star C_h control0 b0 u0 t0
  have hp : Measurable (fun w : Sample =>
      (show PrefixObservation rate t0 t0.succ from (observe (by omega) w).2.val)) := by
    have he : (fun w : Sample =>
        (show PrefixObservation rate t0 t0.succ from (observe (by omega) w).2.val)) =
        initialExtension rate rewards C_star C_h t0 ∘ branchInitial rate rewards C_star C_h control0 b0 u0 t0 := by
      funext w
      exact calendarObservation_initial rate rewards C_star C_h control0 b0 u0 t0 (by omega) w
    rw [he]
    apply ((measurable_initialExtension rate rewards C_star C_h t0).comp hi).mono le_rfl
    dsimp only [Prod.instMeasurableSpace, MeasurableSpace.prod, optionMeasurableSpace,
      ReferencePostInvocationKilledJointLaw.optionMeasurableSpace,
      LaterAssignmentStartMeasurability.optionMeasurableSpace, Sum.instMeasurableSpace,
      ReferencePostInvocationKilledJointLaw.slowSetMeasurableSpace]
    repeat' first
      | exact le_rfl
      | exact le_top
      | apply sup_le_sup
      | apply inf_le_inf
      | apply MeasurableSpace.comap_mono
      | apply MeasurableSpace.map_mono
  exact (measurable_calendarRootAssignedPast rate rewards C_star C_h control0 b0 u0 t0).prodMk
    (((hpair.prodMk hupdate).prodMk hproposal).prodMk
      ((measurable_calendarRootCell rate rewards C_star C_h control0 b0 u0 t0).prodMk (hi.prodMk hp)))

/-- Evaluate arbitrary measurable nonnegative root cylinders by the actual
correlated common-update/proposal law and the true selected residual law.
The full initializer and canonical initialized prefix remain on that SAME
source and original auxiliary array, including the consumed scalar. -/
theorem calendarLaw_root_round_test (Phi : RootRoundData rate t0 → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ w, Phi (calendarRootRoundReadout rate rewards C_star C_h control0 b0 u0 t0 w)
      ∂law (by omega)) =
      ∑ q : Fin (M p), ∫⁻ r : EventRemainder control0 t0 Event q,
        ∫⁻ e : ErasedAuxiliaryArray t0, ∫⁻ v : Vector,
          let z0 := rootInstalledSource rate rewards C_star C_h b0 u0 t0
            (restoreEventSource control0 t0 Event
              (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) q (r, control0)) v
          ∫⁻ y, ∫⁻ c,
            let z := rootInstalledSource rate rewards C_star C_h b0 u0 t0
              (restoreEventSource control0 t0 Event
                (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) q (r, c)) v
            ∫⁻ U, ∫⁻ x,
              Phi (calendarRootRoundReadout rate rewards C_star C_h control0 b0 u0 t0
                (rootRestore rate rewards C_star C_h control0 b0 u0 t0 q r e v c x))
              ∂rootRefreshFibre rate rewards C_star C_h control0 t0 z U
              ∂firstResidualLaw rate rewards C_star C_h control0 t0 z
              ∂rootControlFibre rate rewards C_star C_h control0 t0 z0 y
              ∂rootControlLaw rate rewards C_star C_h control0 t0 z0
            ∂rootVectorKernel rate rewards C_star C_h control0 b0 u0 t0
              (restoreEventSource control0 t0 Event
                (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) q (r, control0),
                (rootUpdateSplit b0 t0).symm (e, scalarZero))
            ∂erasedAuxiliaryLaw t0 ∂eventRemainderLaw control0 t0 Event q :=
  calendarLaw_root_raw_test rate rewards C_star C_h control0 b0 u0 t0 _
    (hPhi.comp (measurable_calendarRootRoundReadout rate rewards C_star C_h control0 b0 u0 t0))

/-- Final readout is the actual calendar's canonical initialized prefix. -/
theorem calendarRootRoundReadout_prefix (w : Sample) :
    (calendarRootRoundReadout rate rewards C_star C_h control0 b0 u0 t0 w).2.2.2.2 =
      initialExtension rate rewards C_star C_h t0
        (calendarRootRoundReadout rate rewards C_star C_h control0 b0 u0 t0 w).2.2.2.1 :=
  calendarObservation_initial rate rewards C_star C_h control0 b0 u0 t0 (by omega) w

omit control0 in
theorem rootInstalledSource_val (z : Z) (v : Vector) :
    (rootInstalledSource rate rewards C_star C_h b0 u0 t0 z v).val = insertedSource t0 z.val v := by
  cases b0
  · rfl
  · exact ReferenceFirstCollectionRenewalVectorInsertion.put_val rate rewards C_star C_h u0 t0 z v

theorem rootInstalledSource_history (z : Z) (v : Vector) :
    ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 0 t0
      (rootInstalledSource rate rewards C_star C_h b0 u0 t0 z v).val =
      (sourcePrefix control0 t0.val z.val, ([], v)) := by
  change (sourcePrefix control0 t0.val _, ([],
    ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t0 _)) = _
  rw [rootInstalledSource_val]
  change (sourcePrefix control0 t0.val (ReferenceFirstCollectionRenewalVectorInsertion.insert t0 z.val v),
    ([], ReferenceFirstCollectionRenewalVectorInsertion.av t0
      (ReferenceFirstCollectionRenewalVectorInsertion.insert t0 z.val v))) = _
  rw [ReferenceFirstCollectionRenewalVectorInsertion.av_insert]
  exact congrArg (fun s => (s, ([], v)))
    (ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent
      control0 t0 t0.val le_rfl z.val (ReferenceFirstCollectionRenewalVectorInsertion.ctrl t0 z.val v))

private theorem firstBefore_prefix_ext
    (z z' : FirstInvocationSource rate rewards C_star C_h t0)
    (hp : sourcePrefix control0 t0.val z.val = sourcePrefix control0 t0.val z'.val) :
    firstBefore rate rewards C_star C_h control0 t0 z =
      firstBefore rate rewards C_star C_h control0 t0 z' := by
  have hr : ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
      rate rewards C_star C_h control0 t0 z.val =
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
        rate rewards C_star C_h control0 t0 z'.val := by
    change ReferenceFirstCollectionCurrentRetainedGate.prefixReadout? rate rewards C_star C_h t0
      (sourcePrefix control0 t0.val z.val) = _
    rw [hp]
    rfl
  have he := Option.some.inj ((firstBefore_spec rate rewards C_star C_h control0 t0 z).symm.trans
    (hr.trans (firstBefore_spec rate rewards C_star C_h control0 t0 z')))
  exact congrArg (fun s : ReferenceRankInstallationPostUpdateProposalLaw.NumericalState p =>
    (⟨s.1, s.2.1, s.2.2⟩ : RecordedQueueRun.RunState p.K)) he

/-- The literal proper root past and WHOLE assignment vector do not read
the current-control innovation or the selected UPDATE scalar. In particular
the slow set may remain correlated with the vector. -/
theorem rootRestore_assignedPast_nonuse (q : Fin (M p)) (r : EventRemainder control0 t0 Event q)
    (e : ErasedAuxiliaryArray t0) (v : Vector) (c : ContinuousLearningRows.TimeControl p) (x : Scalar) :
    calendarRootAssignedPast rate rewards C_star C_h control0 b0 u0 t0
        (rootRestore rate rewards C_star C_h control0 b0 u0 t0 q r e v c x) =
      calendarRootAssignedPast rate rewards C_star C_h control0 b0 u0 t0
        (rootRestore rate rewards C_star C_h control0 b0 u0 t0 q r e v control0 scalarZero) := by
  let restore := restoreEventSource control0 t0 Event
    (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) q
  let z := rootInstalledSource rate rewards C_star C_h b0 u0 t0 (restore (r, c)) v
  let z0 := rootInstalledSource rate rewards C_star C_h b0 u0 t0 (restore (r, control0)) v
  have hp := restoreEventSource_prefix control0 t0 Event
    (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) q r c
  have hH : ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 0 t0 z.val =
      ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 0 t0 z0.val := by
    rw [rootInstalledSource_history, rootInstalledSource_history, hp]
  have hprefix : sourcePrefix control0 t0.val z.val = sourcePrefix control0 t0.val z0.val :=
    congrArg Prod.fst hH
  have hb := firstBefore_prefix_ext rate rewards C_star C_h control0 t0 z z0 hprefix
  have hv : (firstSourceCell rate rewards C_star C_h t0 z).selected.view =
      (firstSourceCell rate rewards C_star C_h t0 z0).selected.view := by
    apply Option.some.inj
    rw [← actualFirstCell_view rate rewards C_star C_h control0 t0 z,
      ← actualFirstCell_view rate rewards C_star C_h control0 t0 z0,
      ReferenceRankInstallationRecorderFoundation.actualInstallationView_eq_history
        rate rewards C_star C_h control0 0 t0 z.val,
      ReferenceRankInstallationRecorderFoundation.actualInstallationView_eq_history
        rate rewards C_star C_h control0 0 t0 z0.val, hH]
  have hslow : (actualFirstCell rate rewards C_star C_h control0 t0 z x).slowSet =
      (actualFirstCell rate rewards C_star C_h control0 t0 z0 scalarZero).slowSet := by
    change (if (firstBefore rate rewards C_star C_h control0 t0 z).overflow then frozenSlowSet p else
      (firstSourceCell rate rewards C_star C_h t0 z).selected.view.payload.slowSet) = _
    rw [hb, hv]
    rfl
  have haux : ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h t0.castSucc
      ((restore (r, c)).val, (rootUpdateSplit b0 t0).symm (e, x)) =
      ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h t0.castSucc
        ((restore (r, c)).val, (rootUpdateSplit b0 t0).symm (e, scalarZero)) := by
    cases b0
    · change ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h t0.castSucc
        (_, (actualRefreshScalarSplit t0).symm (e, x)) = _
      simp only [rootUpdateSplit, Bool.false_eq_true, ite_false,
        ReferenceFirstLiveActualRefreshTestLaw.actualRefreshScalarSplit_symm_apply]
      exact congrArg (fun H : Source × List Cell => H.2)
        (rootBeforeInitialization_scalar_nonuse rate rewards C_star C_h control0 t0
          (restore (r, c)).val e x scalarZero)
    · exact renewalPast_refreshScalar_ext rate rewards C_star C_h t0 u0 (restore (r, c)) e x scalarZero
  have hL := congrArg Prod.snd
    ((ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_sourcePrefix rate rewards C_star C_h
      control0 t0.val t0.isLt.le (restore (r, c)).val ((rootUpdateSplit b0 t0).symm (e, scalarZero))).trans
      ((congrArg (fun s => ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux
        rate rewards C_star C_h t0.val t0.isLt.le (s, (rootUpdateSplit b0 t0).symm (e, scalarZero))) hp).trans
        (ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_sourcePrefix rate rewards C_star C_h
          control0 t0.val t0.isLt.le (restore (r, control0)).val
          ((rootUpdateSplit b0 t0).symm (e, scalarZero))).symm))
  apply Prod.ext
  · change calendarRootPast rate rewards C_star C_h control0 b0 u0 t0
      (rootRestore rate rewards C_star C_h control0 b0 u0 t0 q r e v c x) =
        calendarRootPast rate rewards C_star C_h control0 b0 u0 t0
          (rootRestore rate rewards C_star C_h control0 b0 u0 t0 q r e v control0 scalarZero)
    dsimp only [calendarRootPast]
    rw [rootRestore_currentSource, rootRestore_currentSource,
      rootRestore_cell, rootRestore_cell, calendarNativePrelist_root, calendarNativePrelist_root]
    exact Prod.ext hprefix (Prod.ext hslow (haux.trans hL))
  · rfl

private theorem physicalProposalBit_fixedVectorControl (v : Vector)
    (c : ContinuousLearningRows.TimeControl p) :
    ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate (fixedVectorControl v c) =
      ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate c := by
  have hl : ¬ ∃ i : Fin (p.K + 1), ReferenceFirstLivePostUpdateProposalLaw.propLabel p =
      ContinuousControlSlice.Label.assign i := by
    rintro ⟨i, hi⟩
    exact Sum.inl_ne_inr hi
  exact congrArg (fun x => FollowerCutoffScan.thresholdProposalBit x
    (FollowerCutoffScan.proposalHazard p rate.eta.val))
      (fixedVectorControl_nonassignment v c ⟨_, hl⟩)

/-- The evaluated pair/UPDATE/proposal is exactly the corresponding
coordinate of the SAME reconstructed calendar observer. -/
theorem rootRestore_control (q : Fin (M p)) (r : EventRemainder control0 t0 Event q)
    (e : ErasedAuxiliaryArray t0) (v : Vector) (c : ContinuousLearningRows.TimeControl p) (x : Scalar) :
    (calendarRootRoundReadout rate rewards C_star C_h control0 b0 u0 t0
      (rootRestore rate rewards C_star C_h control0 b0 u0 t0 q r e v c x)).2.1 =
      rootControlDraw rate rewards C_star C_h control0 t0
        (rootInstalledSource rate rewards C_star C_h b0 u0 t0
          (restoreEventSource control0 t0 Event
            (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) q (r, control0)) v) c := by
  have hc : ReferenceSourceCurrentControlFreshness.u_t p t0
      (rootSource (by omega) (rootRestore rate rewards C_star C_h control0 b0 u0 t0 q r e v c x)) =
        fixedVectorControl v c := by
    rw [rootRestore_currentSource, rootInstalledSource_val]
    change ReferenceSourceCurrentControlFreshness.u_t p t0
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t0 _
        (ReferenceFirstCollectionRenewalVectorInsertion.ctrl t0 _ v)) = _
    rw [currentControl_replaceSourceControl]
    change fixedVectorControl v (ReferenceSourceCurrentControlFreshness.u_t p t0
      (restoreEventSource control0 t0 Event
        (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) q (r, c)).val) = _
    rw [restoreEventSource_currentControl]
  apply Prod.ext
  · change (ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast rate rewards C_star C_h t0
      (rootSource (by omega) _),
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate rate rewards C_star C_h
        control0 t0 (rootSource (by omega) _)) = _
    rw [rootRestore_currentSource]
    cases b0
    · exact nonrenewedSourceAt_pairUpdate rate rewards C_star C_h control0 u0 t0 q r c v
    · exact renewedSourceAt_pairUpdate rate rewards C_star C_h control0 u0 t0 q r c v
  · change ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
      (ReferenceSourceCurrentControlFreshness.u_t p t0 (rootSource (by omega) _)) = _
    rw [hc, physicalProposalBit_fixedVectorControl]
    rfl

omit b0 u0 in
/-- Positive conditional fibres recover their prescribed correlated output.
The integral law itself includes the zero coefficients without restriction. -/
theorem rootControlFibre_support (z : FirstInvocationSource rate rewards C_star C_h t0)
    (y : ReferenceRankInstallationCommonUpdateJointLaw.PairUpdate p × Bool)
    (hy : rootControlLaw rate rewards C_star C_h control0 t0 z {y} ≠ 0) :
    ∀ᵐ c ∂rootControlFibre rate rewards C_star C_h control0 t0 z y,
      rootControlDraw rate rewards C_star C_h control0 t0 z c = y := by
  rw [← rootControlDraw_law rate rewards C_star C_h control0 t0 z,
    Measure.map_apply (measurable_rootControlDraw rate rewards C_star C_h control0 t0 z)
      (measurableSet_singleton y)] at hy
  exact FiniteFibreLift.ae_fibreMeasure_eq _ _ _
    (measurable_rootControlDraw rate rewards C_star C_h control0 t0 z) hy

omit b0 u0 in
theorem rootRefreshFibre_support (z : FirstInvocationSource rate rewards C_star C_h t0) (U : SlowSet p)
    (hU : firstResidualLaw rate rewards C_star C_h control0 t0 z {U} ≠ 0) :
    ∀ᵐ x ∂rootRefreshFibre rate rewards C_star C_h control0 t0 z U,
      rootRefreshDraw rate rewards C_star C_h control0 t0 z x = U := by
  have hm : Measurable (rootRefreshDraw rate rewards C_star C_h control0 t0 z) :=
    (ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_nextSlowSet.comp
      (Measurable.of_uncurry_left (measurable_actualFirstCell rate rewards C_star C_h control0 t0))).mono le_rfl le_top
  rw [← rootRefreshDraw_law rate rewards C_star C_h control0 t0 z,
    Measure.map_apply hm (measurableSet_singleton U)] at hU
  exact FiniteFibreLift.ae_fibreMeasure_eq _ _ _ hm hU

end RootRefill

section RenewalNumericalJoin

omit b0 in
/-- Renewal's initial sampler uses the SAME numerical PRE weights. The
clear-PRE condition is local to this interpretation; the total root law
also retains every already-stopped physical branch. -/
theorem rootRenewal_initialWeight
    (z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u0 t0)
    (hclear : (firstBefore rate rewards C_star C_h control0 t0
      (renewedFirstSource rate rewards C_star C_h t0 u0 z)).overflow = false) :
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter rate rewards C_star C_h u0 t0 z).2 =
      RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (firstBefore rate rewards C_star C_h control0 t0
          (renewedFirstSource rate rewards C_star C_h t0 u0 z)) := by
  let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let s := renewedFirstSource rate rewards C_star C_h t0 u0 z
  let hl := ReferencePostInvocationGeneratedAlignment.firstInvocation_launch rate rewards C_star C_h t0 s
  let W := ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord rate rewards C_star C_h z.val hl
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h
  obtain ⟨d, consistent, output, hlocal, hresult, hvector, hrec, hsample, hslow,
    hinstalledPayload, hinstalledVector, hinstalledRec, hanchor, hqueues, hbase,
    selection, hchoice, hdispatch, hprep, hcoord, htail⟩ :=
    ReferenceFirstCollectionRenewalSampleInstallation.actual_renewal_call_installation
      rate rewards C_star C_h u0 t0 z
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp d.record_mem
  let b : Fin R.length := ⟨n, (List.getElem?_eq_some_iff.mp hn).1⟩
  have hb : R[b.val] = d.record := (List.getElem?_eq_some_iff.mp hn).2
  have hrestore := ReferenceCompleteOriginalCalendarWeightMarginalRestoration.complete_original_installation_weight_marginal_restoration
    rate rewards C_star C_h z.val
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z.val rewards C_star C_h =
      some (Classical.choose hl) := Classical.choose_spec hl
  dsimp only at hrestore
  rw [hlaunch] at hrestore
  obtain ⟨L, _hlen, _hprefix, hfull, _hunique, hbirths, _hbranches, _hstates⟩ := hrestore
  have hL : L = W := Option.some.inj (hfull.symm.trans
    (ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord_spec rate rewards C_star C_h z.val hl))
  obtain ⟨b', rb, _qb, _beta, hr, _heq, _hchosen, _hnext, hbirth, _hpay⟩ :=
    ReferencePostInvocationGeneratedAlignment.firstInvocation_installation rate rewards C_star C_h t0 s
  have ht' := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate z.val rewards C_star C_h b'.val _ (List.getElem?_eq_getElem b'.isLt)
  have hdate := congrArg Fin.val ((ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h t0 z.val _ hr).2.2.1)
  have ht := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate z.val rewards C_star C_h b.val _ (List.getElem?_eq_getElem b.isLt)
  rw [hb, d.time_eq] at ht
  have heq : b' = b := Fin.ext (by omega)
  subst b'
  obtain ⟨_rho, _P, _hrho, _hroot, _hepisode, hscore, _⟩ := hbirths b rb.payload hbirth
  rw [hb] at hscore
  unfold ReferenceCompleteLiveComplementScoreSpan.installationScoreVector at hscore
  rw [hcoord, hdispatch] at hscore
  have hweights : AssignmentScoreReconstruction.currentWeight output.reconstruction =
      (fun i => AssignmentScoreReconstruction.sourceWeightBase p ^
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L i b.val).1) := by
    funext i
    exact congrArg (fun n : ℕ => AssignmentScoreReconstruction.sourceWeightBase p ^ n)
      (congrFun hscore.2.1 i).symm
  have hpar : (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
      rate rewards C_star C_h u0 t0 z).2 = AssignmentScoreReconstruction.currentWeight d.out := by
    rw [d.parameter_eq]
    exact (LaterAssignmentStartMeasurability.selectedSamplerParameters_renewal
      d.old _ d.instruction d.out d.reconstruction_eq d.renewal).1
  rw [hrec, hL] at hweights
  have hindex : t0.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = b.val := by
    omega
  have hbefore : firstBefore rate rewards C_star C_h control0 t0 s =
      RecordedQueueRun.run Q (W.take b.val) := by
    have h := rootBefore_originalWord rate rewards C_star C_h control0 t0 s
    change firstBefore rate rewards C_star C_h control0 t0 s =
      RecordedQueueRun.run Q (W.take
        (t0.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h)) at h
    rw [hindex] at h
    exact h
  have hlength : b.val ≤ W.length := by
    rw [← hL, _hlen]
    exact b.isLt.le
  have hc : (RecordedQueueRun.run Q (W.take b.val)).overflow = false := by
    rw [← hbefore]
    exact hclear
  have hpre : b.val ≤ UnstoppedRecordedQueueComparison.firstOverflowPrefix Q W := by
    by_contra hnot
    have hf := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
      Q W b.val hlength).mpr (by omega)
    rw [hc] at hf
    cases hf
  have hnum := (ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord_numericalPrefix
    rate rewards C_star C_h z.val hl b.val hlength).2.1
  change RecordedQueueRun.scoreWeight Q (RecordedQueueRun.run Q (W.take b.val)) =
    (fun i => AssignmentScoreReconstruction.sourceWeightBase p ^
      (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate W i
        (min b.val (UnstoppedRecordedQueueComparison.firstOverflowPrefix Q W))).1) at hnum
  rw [Nat.min_eq_left hpre] at hnum
  rw [hpar, hbefore, hnum]
  exact hweights

end RenewalNumericalJoin

section ActualRenewalInitialization

omit b0 in
/-- Inserting the WHOLE root assignment vector leaves renewal's numerical
PRE fixed, so its original initialization weights are the installed native
PRE weights as well. -/
theorem rootRenewal_installed_initialWeight
    (z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u0 t0)
    (v : Vector)
    (hclear : (firstBefore rate rewards C_star C_h control0 t0
      (rootInstalledSource rate rewards C_star C_h true u0 t0 z v)).overflow = false) :
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter rate rewards C_star C_h u0 t0 z).2 =
      RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (firstBefore rate rewards C_star C_h control0 t0
          (rootInstalledSource rate rewards C_star C_h true u0 t0 z v)) := by
  have hp : sourcePrefix control0 t0.val
      (rootInstalledSource rate rewards C_star C_h true u0 t0 z v).val =
      sourcePrefix control0 t0.val (renewedFirstSource rate rewards C_star C_h t0 u0 z).val := by
    change sourcePrefix control0 t0.val
      (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u0 t0 z v).val =
        sourcePrefix control0 t0.val z.val
    rw [ReferenceFirstCollectionRenewalVectorInsertion.put_val]
    exact ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent
      control0 t0 t0.val le_rfl z.val (ReferenceFirstCollectionRenewalVectorInsertion.ctrl t0 z.val v)
  have hb := firstBefore_prefix_ext rate rewards C_star C_h control0 t0 _ _ hp
  rw [hb] at hclear ⊢
  exact rootRenewal_initialWeight rate rewards C_star C_h control0 u0 t0 z hclear

omit b0 in
/-- Actual calendar-root before-initial-draw law. The full earlier archive
and FULL erased array are retained, with no vector/seed/initial scalar in
the before-draw observer. The assignment fibre is integrated, not assumed. -/
theorem calendarLaw_root_initializer_test
    (Phi : ((Source × List Cell) × ((Source × ErasedAuxiliaryArray t0) × SlowSet p)) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    (∫⁻ w : CalendarSample rate rewards C_star C_h true u0 t0 0, Phi
      (rootBeforeInitialization rate rewards C_star C_h control0 t0 (w.1.1.val, w.1.2),
        ((w.1.1.val, (actualRefreshScalarSplit t0 w.1.2).1),
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
            rate rewards C_star C_h u0 t0 w.1.1 w.1.2))
      ∂calendarLaw rate rewards C_star C_h control0 true u0 t0 0 (by omega)) =
    ∫⁻ z, ∫⁻ e : ErasedAuxiliaryArray t0, ∫⁻ U,
      Phi (rootBeforeInitialization rate rewards C_star C_h control0 t0
        (z.val, insertActualRefreshCoordinate t0 e scalarZero), ((z.val, e), U))
      ∂(ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSlowSetPMF rate rewards C_star C_h u0 t0 z).toMeasure
      ∂erasedAuxiliaryLaw t0
      ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u0 t0 := by
  let Z := ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u0 t0
  let f : Z × Auxiliary → ℝ≥0∞ := fun za => Phi
    (rootBeforeInitialization rate rewards C_star C_h control0 t0 (za.1.val, za.2),
      ((za.1.val, (actualRefreshScalarSplit t0 za.2).1),
        ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
          rate rewards C_star C_h u0 t0 za.1 za.2))
  have hz : Measurable (fun za : Z × Auxiliary => za.1.val) :=
    measurable_subtype_coe.comp measurable_fst
  have he : Measurable (fun za : Z × Auxiliary => (actualRefreshScalarSplit t0 za.2).1) :=
    ((actualRefreshScalarSplit t0).measurable.comp measurable_snd).fst
  have hseed : Measurable (fun za : Z × Auxiliary =>
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
        rate rewards C_star C_h u0 t0 za.1 za.2) :=
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurable_renewalAuxiliarySample
      rate rewards C_star C_h u0 t0).mono le_rfl le_top
  have hpast := (measurable_rootBeforeInitialization rate rewards C_star C_h control0 t0).comp
    (hz.prodMk (measurable_snd : Measurable (Prod.snd : Z × Auxiliary → Auxiliary)))
  have hf : Measurable f := hPhi.comp (hpast.prodMk ((hz.prodMk he).prodMk hseed))
  calc
    _ = ∫⁻ za, f za ∂(calendarLaw rate rewards C_star C_h control0 true u0 t0 0 (by omega)).map Prod.fst :=
      (lintegral_map hf measurable_fst).symm
    _ = ∫⁻ za, f za ∂(ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u0 t0).prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p) := by
      rw [show (calendarLaw rate rewards C_star C_h control0 true u0 t0 0 (by omega)).map Prod.fst = _ from
        ReferenceFirstCollectionRenewalFibreExtension.renewalLiftLaw_map_fst rate rewards C_star C_h u0 t0]
      rfl
    _ = _ := rootInitialization_base_test rate rewards C_star C_h control0 u0 t0 Phi hPhi

omit b0 in
/-- The seed sampled by the preceding before-draw law is the SAME actual
root slow set on clear PRE. Stopped PREs remain in the total round law. -/
theorem ae_calendarLaw_root_renewal_initialSlowSet :
    ∀ᵐ w ∂calendarLaw rate rewards C_star C_h control0 true u0 t0 0 (by omega),
      (calendarRootCell rate rewards C_star C_h control0 true u0 t0 w).before.overflow = false →
        (calendarRootCell rate rewards C_star C_h control0 true u0 t0 w).slowSet =
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
            rate rewards C_star C_h u0 t0 w.1.1 w.1.2 := by
  filter_upwards [ae_calendarLaw_root_join rate rewards C_star C_h control0 true u0 t0 (by omega)]
    with w hw
  rw [(calendarObservation_root rate rewards C_star C_h control0 true u0 t0 (by omega) w).1] at hw
  intro hc
  exact (Option.some.inj (hw hc)).symm

end ActualRenewalInitialization

/-- Full actual numerical UPDATE and native cell agree on all fields,
including raw versus accepted arrivals, all-arm service, and POST overflow.
Only PRE overflow freezes the logical step. -/
theorem calendarRootCell_wholeUpdate (w : Sample) :
    ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
      rate rewards C_star C_h control0 t0 (rootSource (by omega) w) =
      some (show ReferenceFirstLivePostUpdateProposalLaw.NumericalUpdateFields p from
        { raw := RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (firstSourceCell rate rewards C_star C_h t0
              (rootInstalledSource rate rewards C_star C_h b0 u0 t0 w.1.1 w.2)).input
          beforeRegisters := (rootCell w).before.registers
          beforeOverflow := (rootCell w).before.overflow
          beforeRecords := (rootCell w).before.records
          accepted := (rootCell w).arrivals
          service := (rootCell w).service
          afterRegisters := (rootCell w).after.registers
          afterOverflow := (rootCell w).after.overflow
          afterRecords := (rootCell w).after.records }) := by
  cases b0
  · exact actualFirstCell_wholeUpdate rate rewards C_star C_h control0 t0
      (nonrenewedFirstSource rate rewards C_star C_h t0 u0 w.1.1 w.2) (w.1.2 (t0, 1))
  · exact actualFirstCell_wholeUpdate rate rewards C_star C_h control0 t0
      (renewedFirstSource rate rewards C_star C_h t0 u0
        (ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u0 t0 w).2)
        (w.1.2 (t0, 0))

/-- Both actual root orientations join their generated initial endpoint
on clear PRE, with no positive branch-mass assumption. The retained endpoint
is the earlier generated seed, rather than a fresh initialization draw. -/
theorem ae_calendarLaw_root_endpoint :
    ∀ᵐ w ∂law (by omega), (rootCell w).before.overflow = false →
      calendarRootEndpoint rate rewards C_star C_h b0 u0 t0 w = some (rootCell w).slowSet := by
  filter_upwards [ae_calendarLaw_root_join rate rewards C_star C_h control0 b0 u0 t0 (by omega)]
    with w hw
  rw [(calendarObservation_root rate rewards C_star C_h control0 b0 u0 t0 (by omega) w).1] at hw
  exact hw

end Bandits.Support.ReferenceGeneratedCalendarRootRoundLaw
