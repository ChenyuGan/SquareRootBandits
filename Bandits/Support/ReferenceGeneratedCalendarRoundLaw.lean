/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarRootRoundLaw
public import Bandits.Support.ReferenceGeneratedCalendarNoncallRoundLaw

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Tactic

/-!
# Actual generated calendar round laws

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`08_main_theorem.tex:85-109`.

All tests retain the original unnormalized first-branch mass and the literal
strict source prefix, current slow seed and whole earlier native archive.
Current physical readouts, installed vectors and auxiliary outcomes remain
joint. These are local laws, with no episode or regret closure assertion.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical BigOperators
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstNextInstallationCellFactors
open ReferenceFirstNextInstallationTransitionLaw
open ReferencePostInvocationNoncallGeometry
open ReferencePostInvocationPrefixLocality
open ReferencePostInvocationSupportedDisintegration
open ReferencePostInvocationKilledJointLaw
open ReferenceGeneratedInvocationCallSplice
open ReferenceGeneratedRankCalendarFoundation
open ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarNativePreservation
open ReferenceGeneratedCalendarEndpointMixture
open ReferenceGeneratedCalendarPathAgreement
open ReferenceGeneratedCalendarJointRebase
open ReferenceGeneratedCalendarRoundInnovation
open ReferenceGeneratedCalendarNoncallRoundLaw
open ReferenceGeneratedNativeInvocationGeometry
open ReferenceFirstLivePostUpdateProposalLaw
open ReferenceFirstLiveActualRefreshTestLaw (scalarZero)
open LaunchAssignmentCoordinateSplit
open ReferenceFirstNextLiftFutureAuxiliaryPairLaw (auxiliaryPair measurable_auxiliaryPair)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix)
open ReferenceGeneratedCalendarRootRoundLaw
open ReferenceFirstLiveActualRefreshTestLaw (ErasedAuxiliaryArray erasedAuxiliaryLaw)

namespace Bandits.Support.ReferenceGeneratedCalendarRoundLaw

variable {p : ConstructorDimensions.Parameters}

local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p
local notation "Control" => ContinuousLearningRows.TimeControl p
local notation "Vector" => AssignmentParameterFibreKernel.AssignmentVector p
local notation "Scalar" => ContinuousControlSlice.Scalar
local notation "PairUpdate" => ReferenceRankInstallationCommonUpdateJointLaw.PairUpdate p

local instance sourceMeasurableSpace : MeasurableSpace Source := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance
local instance controlMeasurableSpace : MeasurableSpace Control :=
  ReferencePostInvocationSupportedDisintegration.controlMeasurableSpace
local instance optionMeasurableSpace {X : Type*} [MeasurableSpace X] : MeasurableSpace (Option X) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace
local instance outcomeMeasurableSpace : MeasurableSpace (AssignmentParameterFibreKernel.Outcome p) := ⊤
local instance outcomeDiscrete : DiscreteMeasurableSpace (AssignmentParameterFibreKernel.Outcome p) :=
  ⟨fun _ => trivial⟩
local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩

attribute [local instance] ReferenceRankInstallationPostUpdateProposalLaw.sumMeasurableSingleton
  ReferenceRankInstallationPostUpdateProposalLaw.listMeasurableSingleton

local instance optionSingleton {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] : MeasurableSingletonClass (Option X) where
  measurableSet_singleton x := by
    have h := (comap_measurable (Equiv.optionEquivSumPUnit X))
      (measurableSet_singleton ((Equiv.optionEquivSumPUnit X) x))
    convert h using 1
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact (Equiv.optionEquivSumPUnit X).injective.eq_iff.symm


variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p)


section NativeDraw

attribute [-instance] slowSetMeasurableSpace slowSetDiscrete


private theorem callNative_commonUpdateKernel (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h t) :
    (ReferenceLaterOptionalControlResampling.controlRemainderLaw p).map
      (ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
        rate rewards C_star C_h control0 t
        (ReferenceRankInstallationRecorderFoundation.history
          rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h t z.val) t z.val)) =
    ReferenceRankInstallationCommonUpdateJointLaw.commonUpdateKernel rate rewards t
      (nativeSourceCell rate rewards C_star C_h t z).selected.view
      (ReferenceRankInstallationRecorderFastLaw.actualInstallationView_valid
        rate rewards C_star C_h t z.val _
        (nativeCell_view rate rewards C_star C_h control0 t z))
      (ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
        rate rewards C_star C_h control0 t z.val) := by
  classical
  let H := ReferenceRankInstallationRecorderFoundation.history
    rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h t z.val) t z.val
  let f := ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
    rate rewards C_star C_h control0 t H
  have hrec : Measurable (fun q : ReferenceRankInstallationCommonUpdateJointLaw.History p ×
      ReferenceRankInstallationCommonUpdateJointLaw.Remainder p =>
      ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
        rate rewards C_star C_h control0 t q.1 q.2) :=
    ReferenceRankInstallationCommonUpdateJointLaw.measurable_reconstructedPairUpdate
      rate rewards C_star C_h control0 t
  have hf : Measurable f := Measurable.of_uncurry_left
    (f := ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
      rate rewards C_star C_h control0 t) (x := H) hrec
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply hf hB]
  calc
    _ = ∫⁻ d, if f d ∈ B then 1 else 0
        ∂ReferenceLaterOptionalControlResampling.controlRemainderLaw p := by
      simpa only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply] using
        (lintegral_indicator_one (hB.preimage hf)).symm
    _ = _ := ReferenceRankInstallationCommonUpdateJointLaw.sourceLawCommonUpdateTestCoefficient_eq_kernel
      rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h t z.val) t z.val (native_installation rate rewards C_star C_h t z) _ _
      (nativeCell_view rate rewards C_star C_h control0 t z) B hB

private def callNativePairUpdateDraw (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h t) (c : ContinuousLearningRows.TimeControl p) :
    ReferenceRankInstallationCommonUpdateJointLaw.PairUpdate p :=
  ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate rate rewards C_star C_h control0 t
    (ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h t z.val) t z.val)
    (controlAssignmentSplitEquiv p c).2

private theorem measurable_callNativePairUpdateDraw (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h t) :
    Measurable (callNativePairUpdateDraw rate rewards C_star C_h control0 t z) := by
  let H : ReferenceRankInstallationCommonUpdateJointLaw.History p :=
    ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h t z.val) t z.val
  have hf : Measurable (fun d : ReferenceLaterOptionalControlResampling.ControlRemainder p =>
      ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
        rate rewards C_star C_h control0 t H d) :=
    Measurable.of_uncurry_left
      (ReferenceRankInstallationCommonUpdateJointLaw.measurable_reconstructedPairUpdate
        rate rewards C_star C_h control0 t)
  exact hf.comp (measurable_snd.comp (controlAssignmentSplitEquiv p).measurable)

/-- No current proposal coordinate is present in the actual reconstructed
view/recorder/FAST/whole-update observer. The PRE includes every arm's full
record stream and comes from the strict source prefix. -/
private theorem callNativePairUpdateDraw_replaceProposalScalar (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h t) (c : ContinuousLearningRows.TimeControl p) (a : Scalar) :
    callNativePairUpdateDraw rate rewards C_star C_h control0 t z (replaceProposalScalar p c a) =
      callNativePairUpdateDraw rate rewards C_star C_h control0 t z c := by
  let H := ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h t z.val) t z.val
  let x := ReferenceRankInstallationRecorderFastSourceLaw.sourceFromHistoryRemainder
    t H (controlAssignmentSplitEquiv p c).2
  obtain ⟨_v, _valid, _before, _round, _hv, _enabled, _pre, _raw, _post, hall⟩ :=
    ReferenceRankInstallationCommonUpdateJointLaw.reconstructedObserver_and_originalQueueStep
      rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h t z.val) t z.val (native_installation rate rewards C_star C_h t z)
  have hx := (hall (controlAssignmentSplitEquiv p c).2).1
  have heq : ReferenceRankInstallationRecorderFastSourceLaw.sourceFromHistoryRemainder t H
      (controlAssignmentSplitEquiv p (replaceProposalScalar p c a)).2 =
      ReferenceRankInstallationPostUpdateProposalLaw.replaceSelectedProp t x a := by
    change ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t H.1
      (fixedVectorControl H.2.2 (replaceProposalScalar p c a)) = _
    rw [fixedVectorControl_replaceProposalScalar]
    unfold ReferenceRankInstallationPostUpdateProposalLaw.replaceSelectedProp
    rw [show ReferenceSourceCurrentControlFreshness.u_t p t x = fixedVectorControl H.2.2 c from
      currentControl_replaceSourceControl t H.1 (fixedVectorControl H.2.2 c)]
    exact (replaceSourceControl_twice t H.1 (fixedVectorControl H.2.2 c)
      (replaceProposalScalar p (fixedVectorControl H.2.2 c) a)).symm
  have ho := ReferenceRankInstallationPostUpdateProposalLaw.actualRankPreProposalObserver_replaceSelectedProp
    rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h t z.val) t x hx a
  have hpair := congrArg Prod.snd ho
  change callNativePairUpdateDraw rate rewards C_star C_h control0 t z (replaceProposalScalar p c a) = _
  unfold callNativePairUpdateDraw ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
    ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder
  rw [heq]
  exact hpair

/-- The current-control draw has exactly the accepted correlated common-update
kernel at its actual source-derived view and PRE state. -/
private theorem callNativePairUpdateDraw_law (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h t) :
    (ContinuousLearningRows.timeControlLaw p).map
      (callNativePairUpdateDraw rate rewards C_star C_h control0 t z) =
    ReferenceRankInstallationCommonUpdateJointLaw.commonUpdateKernel rate rewards t
      (nativeSourceCell rate rewards C_star C_h t z).selected.view
      (ReferenceRankInstallationRecorderFastLaw.actualInstallationView_valid rate rewards C_star C_h t z.val _
        (nativeCell_view rate rewards C_star C_h control0 t z))
      (ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
        rate rewards C_star C_h control0 t z.val) := by
  have hrem := (measurePreserving_snd
    (μ := ContinuousControlSlice.assignmentLaw p.K)
    (ν := ReferenceLaterOptionalControlResampling.controlRemainderLaw p)).comp
      (measurePreserving_controlAssignmentSplitEquiv p)
  have hf : Measurable (fun d : ReferenceLaterOptionalControlResampling.ControlRemainder p =>
      ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate rate rewards C_star C_h control0 t
        (ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h t z.val) t z.val) d) :=
    Measurable.of_uncurry_left (ReferenceRankInstallationCommonUpdateJointLaw.measurable_reconstructedPairUpdate
      rate rewards C_star C_h control0 t)
  change (ContinuousLearningRows.timeControlLaw p).map
    ((fun d => ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
      rate rewards C_star C_h control0 t
      (ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h t z.val) t z.val) d) ∘
      (Prod.snd ∘ controlAssignmentSplitEquiv p)) = _
  rw [← Measure.map_map hf hrem.measurable, hrem.map_eq]
  exact callNative_commonUpdateKernel rate rewards C_star C_h control0 t z

/-- The SAME correlated draw and whole-arm update have an independent actual
physical Bernoulli proposal. This uses the existing proposal-factor API;
recorder and FAST are never replaced by independent draws. -/
private theorem callNativePairUpdateDraw_joint_proposal (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h t) :
    (ContinuousLearningRows.timeControlLaw p).map (fun c =>
      (callNativePairUpdateDraw rate rewards C_star C_h control0 t z c, physicalProposalBit rate c)) =
    ((ContinuousLearningRows.timeControlLaw p).map
      (callNativePairUpdateDraw rate rewards C_star C_h control0 t z)).prod (proposalBitLaw rate) := by
  let draw := callNativePairUpdateDraw rate rewards C_star C_h control0 t z
  have hdraw := measurable_callNativePairUpdateDraw rate rewards C_star C_h control0 t z
  let g : Unit × PropRestControl p → ReferenceRankInstallationCommonUpdateJointLaw.PairUpdate p :=
    fun r => draw ((proposalControlSplit p).symm (scalarZero, r.2))
  have hg : Measurable g := hdraw.comp ((proposalControlSplit p).symm.measurable.comp
    (measurable_const.prodMk measurable_snd))
  have hp := proposalSplit_joint_pushforward (Measure.dirac ()) g hg rate
  have hpoint (c : ContinuousLearningRows.TimeControl p) : g ((), (proposalControlSplit p c).2) = draw c := by
    have he := proposalControlSplit_symm_replace p scalarZero
      (proposalControlSplit p c).1 (proposalControlSplit p c).2
    rw [Prod.mk.eta, MeasurableEquiv.symm_apply_apply] at he
    change draw ((proposalControlSplit p).symm (scalarZero, (proposalControlSplit p c).2)) = draw c
    rw [he]
    exact callNativePairUpdateDraw_replaceProposalScalar rate rewards C_star C_h control0 t z c scalarZero
  have hj : (ContinuousLearningRows.timeControlLaw p).map (fun c => (draw c, physicalProposalBit rate c)) =
      (((Measure.dirac ()).prod (proposalRestControlLaw p)).map g).prod (proposalBitLaw rate) := by
    calc
      _ = ((Measure.dirac ()).prod (ContinuousLearningRows.timeControlLaw p)).map
          (fun uc => (draw uc.2, physicalProposalBit rate uc.2)) := by
        rw [Measure.dirac_prod]
        have htest : Measurable (fun uc : Unit × ContinuousLearningRows.TimeControl p =>
            (draw uc.2, physicalProposalBit rate uc.2)) :=
          (hdraw.comp measurable_snd).prodMk
            ((measurable_physicalProposalBit rate).comp measurable_snd)
        exact (Measure.map_map htest measurable_prodMk_left).symm
      _ = _ := by
        convert hp using 1
        congr 1
        funext uc
        cases uc.1
        rw [hpoint]
  have hm := congrArg (Measure.map Prod.fst) hj
  rw [Measure.map_map measurable_fst (hdraw.prodMk (measurable_physicalProposalBit rate)),
    Measure.map_fst_prod, measure_univ, one_smul] at hm
  change (ContinuousLearningRows.timeControlLaw p).map draw =
    ((Measure.dirac ()).prod (proposalRestControlLaw p)).map g at hm
  rw [hj, hm]

private theorem callNative_pairUpdate_reconstruction (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h t) :
    (ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast
        rate rewards C_star C_h t z.val,
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
        rate rewards C_star C_h control0 t z.val) =
    ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
      rate rewards C_star C_h control0 t
      (ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h t z.val) t z.val)
      (ReferenceFirstNextInvocationJointLift.currentRemainder t z.val) := by
  obtain ⟨v, valid, hv, hall⟩ :=
    ReferenceRankInstallationCommonUpdateJointLaw.reconstructedObserver_eq_commonReadout
      rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h t z.val) t z.val (native_installation rate rewards C_star C_h t z)
  have hp := ReferenceRankInstallationRecorderFastSourceLaw.actualPair_eq_historyRemainder_of_installation
    rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h t z.val) t z.val (native_installation rate rewards C_star C_h t z)
  have hu := ReferenceRankInstallationCommonUpdateJointLaw.actualInstallationNumericalUpdate_eq_updateFromPair
    rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h t z.val) t z.val (native_installation rate rewards C_star C_h t z) v hv
  have hr := congrArg (fun o : ReferenceRankInstallationPostUpdateProposalLaw.Observer p rate.eta => o.2.2)
    (hall (ReferenceFirstNextInvocationJointLift.currentRemainder t z.val)).2
  change (_, _) = (_, _)
  apply Prod.ext hp
  exact hu.trans ((congrArg
    (ReferenceRankInstallationCommonUpdateJointLaw.updateFromPair rate rewards t v
      (ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
        rate rewards C_star C_h control0 t z.val)) hp).trans hr.symm)


private theorem invocation_numerical_complement (control0 : ContinuousLearningRows.TimeControl p) (t0 : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h t0)
    (hclear : (nativeBefore rate rewards C_star C_h control0 t0 z).overflow = false) :
    ∀ j : CanonicalFastSampling.FastArm
        (nativeSourceCell rate rewards C_star C_h t0 z).selected.view.payload.slowSet,
      (nativeSourceCell rate rewards C_star C_h t0 z).selected.view.complementWeights j =
        RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (nativeBefore rate rewards C_star C_h control0 t0 z) j.val := by
  let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let hl := nativeInvocation_launch rate rewards C_star C_h t0 z
  let W := ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord rate rewards C_star C_h z.val hl
  let n := t0.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h
  obtain ⟨L, b, v, hfull, hrecord, hview, hweights⟩ :=
    ReferenceRankInstallationRecorderFoundation.installationEvent_originalComplementWeights
      rate rewards C_star C_h (nativeRank rate rewards C_star C_h t0 z.val) t0 z.val
      (native_installation rate rewards C_star C_h t0 z)
  have hL : L = W := Option.some.inj (hfull.symm.trans
    (ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord_spec rate rewards C_star C_h z.val hl))
  have hv : v = (nativeSourceCell rate rewards C_star C_h t0 z).selected.view :=
    Option.some.inj (hview.symm.trans (nativeCell_view rate rewards C_star C_h control0 t0 z))
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
  have hbefore : nativeBefore rate rewards C_star C_h control0 t0 z =
      RecordedQueueRun.run Q (W.take n) := nativeCell_before_word rate rewards C_star C_h control0 t0 z scalarZero
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


private def invocationControlLaw (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h t) : Measure (PairUpdate × Bool) :=
  (ReferenceRankInstallationCommonUpdateJointLaw.commonUpdateKernel rate rewards t
    (nativeSourceCell rate rewards C_star C_h t z).selected.view
    (ReferenceRankInstallationRecorderFastLaw.actualInstallationView_valid
      rate rewards C_star C_h t z.val _ (nativeCell_view rate rewards C_star C_h control0 t z))
    (some ((nativeBefore rate rewards C_star C_h control0 t z).registers,
      (nativeBefore rate rewards C_star C_h control0 t z).overflow,
      (nativeBefore rate rewards C_star C_h control0 t z).records))).prod (proposalBitLaw rate)

private def invocationControlDraw (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h t) (c : Control) : PairUpdate × Bool :=
  (callNativePairUpdateDraw rate rewards C_star C_h control0 t z c, physicalProposalBit rate c)

private theorem measurable_invocationControlDraw (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h t) :
    Measurable (invocationControlDraw rate rewards C_star C_h control0 t z) :=
  (measurable_callNativePairUpdateDraw rate rewards C_star C_h control0 t z).prodMk
    (measurable_physicalProposalBit rate)

private theorem invocationControlDraw_law (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h t) :
    (ContinuousLearningRows.timeControlLaw p).map
      (invocationControlDraw rate rewards C_star C_h control0 t z) =
    invocationControlLaw rate rewards C_star C_h control0 t z := by
  have hmap := (callNativePairUpdateDraw_joint_proposal rate rewards C_star C_h control0 t z).trans
    (congrArg (fun mu => mu.prod (proposalBitLaw rate))
      (callNativePairUpdateDraw_law rate rewards C_star C_h control0 t z))
  rw [nativeBefore_spec rate rewards C_star C_h control0 t z] at hmap
  exact hmap

private def invocationControlFibre (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h t) (y : PairUpdate × Bool) : Measure Control :=
  FiniteFibreLift.fibreMeasure (ContinuousLearningRows.timeControlLaw p)
    (invocationControlDraw rate rewards C_star C_h control0 t z) y

private theorem invocationControl_test (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h t) (f : Control → ℝ≥0∞) :
    (∫⁻ c, f c ∂ContinuousLearningRows.timeControlLaw p) =
      ∫⁻ y, ∫⁻ c, f c ∂invocationControlFibre rate rewards C_star C_h control0 t z y
        ∂invocationControlLaw rate rewards C_star C_h control0 t z := by
  rw [← invocationControlDraw_law rate rewards C_star C_h control0 t z]
  exact countable_fibre_lintegral _ _
    (measurable_invocationControlDraw rate rewards C_star C_h control0 t z) f

private def invocationRefreshDraw (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h t) (x : Scalar) : SlowSet p :=
  (nativeCell rate rewards C_star C_h control0 t z x).nextSlowSet

private def invocationRefreshLaw (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h t) : Measure (SlowSet p) :=
  ReferenceFirstLiveCalendarMarkedTransition.logicalCellResidualLaw rate
    (nativeRecord rate rewards C_star C_h t z) (nativeSourceCell rate rewards C_star C_h t z)
    (nativeBefore rate rewards C_star C_h control0 t z)

private theorem measurable_invocationRefreshDraw (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h t) :
    Measurable (invocationRefreshDraw rate rewards C_star C_h control0 t z) :=
  (ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_nextSlowSet.mono
    le_rfl le_top).comp
    (Measurable.of_uncurry_left (measurable_nativeCell rate rewards C_star C_h control0 t))

private theorem invocationRefreshDraw_law (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h t) :
    ContinuousControlSlice.scalarLaw.map (invocationRefreshDraw rate rewards C_star C_h control0 t z) =
      invocationRefreshLaw rate rewards C_star C_h control0 t z := by
  have hc : Measurable (nativeCell rate rewards C_star C_h control0 t z) :=
    Measurable.of_uncurry_left (measurable_nativeCell rate rewards C_star C_h control0 t)
  have hn : Measurable (fun c : LogicalCell p rate => c.nextSlowSet) :=
    ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_nextSlowSet.mono le_rfl le_top
  change ContinuousControlSlice.scalarLaw.map
    ((fun c : LogicalCell p rate => c.nextSlowSet) ∘ nativeCell rate rewards C_star C_h control0 t z) = _
  rw [← Measure.map_map hn hc]
  rw [show ContinuousControlSlice.scalarLaw.map (nativeCell rate rewards C_star C_h control0 t z) =
    (invocationRefreshLaw rate rewards C_star C_h control0 t z).map
      (ReferenceFirstLiveCalendarMarkedTransition.logicalCellWithNext rate
        (nativeRecord rate rewards C_star C_h t z) (nativeSourceCell rate rewards C_star C_h t z)
        (nativeBefore rate rewards C_star C_h control0 t z)) from
    ReferenceFirstLiveCalendarMarkedTransition.appendLogicalCell_residual_law rate _ _ _]
  rw [Measure.map_map hn (measurable_of_countable _)]
  exact Measure.map_id

private def invocationRefreshFibre (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h t) (U : SlowSet p) : Measure Scalar :=
  FiniteFibreLift.fibreMeasure ContinuousControlSlice.scalarLaw
    (invocationRefreshDraw rate rewards C_star C_h control0 t z) U

private theorem invocationRefresh_test (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h t) (f : Scalar → ℝ≥0∞) :
    (∫⁻ x, f x ∂ContinuousControlSlice.scalarLaw) =
      ∫⁻ U, ∫⁻ x, f x ∂invocationRefreshFibre rate rewards C_star C_h control0 t z U
        ∂invocationRefreshLaw rate rewards C_star C_h control0 t z := by
  rw [← invocationRefreshDraw_law rate rewards C_star C_h control0 t z]
  exact countable_fibre_lintegral _ _
    (measurable_invocationRefreshDraw rate rewards C_star C_h control0 t z) f

end NativeDraw


private theorem lintegral_pair_resample (b : Bool) (f : Scalar × Scalar → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ a, f a ∂auxiliaryPairLaw) =
      ∫⁻ a, ∫⁻ x, f (if b then (x, a.2) else (a.1, x))
        ∂ContinuousControlSlice.scalarLaw ∂auxiliaryPairLaw := by
  unfold auxiliaryPairLaw
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    change (∫⁻ a, f a ∂ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw) = _
    rw [lintegral_prod _ hf.aemeasurable]
    have hg : Measurable (fun a : Scalar × Scalar => ∫⁻ x, f (a.1, x) ∂ContinuousControlSlice.scalarLaw) :=
      hf.lintegral_prod_right'.comp measurable_fst
    conv_rhs => rw [lintegral_prod _ hg.aemeasurable]
    simp only [lintegral_const, measure_univ, mul_one]
  | true =>
    simp only [ite_true]
    change (∫⁻ a, f a ∂ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw) = _
    rw [lintegral_prod _ hf.aemeasurable]
    have hg : Measurable (fun a : Scalar × Scalar => ∫⁻ x, f (x, a.2) ∂ContinuousControlSlice.scalarLaw) :=
      hf.lintegral_prod_left'.comp measurable_snd
    conv_rhs => rw [lintegral_prod _ hg.aemeasurable]
    dsimp only [Prod.snd]
    rw [lintegral_const]
    simp only [measure_univ, mul_one]
    exact lintegral_lintegral_swap hf.aemeasurable

private theorem lintegral_control_pair_kernel {A V : Type*} [MeasurableSpace A] [MeasurableSpace V]
    (mu : Measure Control) [SFinite mu] (nu : Measure A) [SFinite nu]
    (kernel : ProbabilityTheory.Kernel A V) [ProbabilityTheory.IsSFiniteKernel kernel]
    (f : Control × (A × V) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ca, ∫⁻ v, f (ca.1, (ca.2, v)) ∂kernel ca.2 ∂mu.prod nu) =
      ∫⁻ a, ∫⁻ v, ∫⁻ c, f (c, (a, v)) ∂mu ∂kernel a ∂nu := by
  have h : Measurable (fun ca : Control × A => ∫⁻ v, f (ca.1, (ca.2, v)) ∂kernel ca.2) :=
    (hf.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))).lintegral_kernel_prod_right'
      (κ := kernel.comap Prod.snd measurable_snd)
  rw [lintegral_prod _ h.aemeasurable]
  calc
    _ = ∫⁻ c, ∫⁻ av, f (c, av) ∂nu.compProd kernel ∂mu := by
      apply lintegral_congr
      intro c
      exact (Measure.lintegral_compProd (hf.comp (measurable_const.prodMk measurable_id))).symm
    _ = ∫⁻ av, ∫⁻ c, f (c, av) ∂mu ∂nu.compProd kernel :=
      lintegral_lintegral_swap hf.aemeasurable
    _ = _ := Measure.lintegral_compProd hf.lintegral_prod_left'

private theorem lintegral_pair_kernel_resample {V : Type*} [MeasurableSpace V]
    (mu : Measure Control) [SFinite mu]
    (K : ProbabilityTheory.Kernel (Scalar × Scalar) V) [ProbabilityTheory.IsSFiniteKernel K]
    (b : Bool) (f : Control × ((Scalar × Scalar) × V) → ℝ≥0∞) (hf : Measurable f)
    (hK : ∀ a x, K (if b then (x, a.2) else (a.1, x)) = K a) :
    (∫⁻ a, ∫⁻ v, ∫⁻ c, f (c, (a, v)) ∂mu ∂K a ∂auxiliaryPairLaw) =
    ∫⁻ a, ∫⁻ v, ∫⁻ c, ∫⁻ x, f (c, (if b then (x, a.2) else (a.1, x), v))
      ∂ContinuousControlSlice.scalarLaw ∂mu ∂K a ∂auxiliaryPairLaw := by
  have hg : Measurable (fun av : (Scalar × Scalar) × V =>
      ∫⁻ c, f (c, av) ∂mu) :=
    (hf.comp (measurable_snd.prodMk measurable_fst)).lintegral_prod_right'
  have hG : Measurable (fun a : Scalar × Scalar =>
      ∫⁻ v, ∫⁻ c, f (c, (a, v)) ∂mu ∂K a) :=
    hg.lintegral_kernel_prod_right'
  rw [lintegral_pair_resample b _ hG]
  apply lintegral_congr
  intro a
  let pairAt : Scalar → Scalar × Scalar := fun x =>
    if b then (x, a.2) else (a.1, x)
  have hp : Measurable pairAt := by
    dsimp only [pairAt]
    split
    · exact measurable_id.prodMk measurable_const
    · exact measurable_const.prodMk measurable_id
  have hka (x : Scalar) : K (pairAt x) = K a := hK a x
  change (∫⁻ x, ∫⁻ v, ∫⁻ c, f (c, (pairAt x, v))
    ∂mu ∂K (pairAt x) ∂ContinuousControlSlice.scalarLaw) = _
  simp_rw [hka]
  have hxv : Measurable (fun z : Scalar × V =>
      ∫⁻ c, f (c, (pairAt z.1, z.2)) ∂mu) :=
    (hf.comp (measurable_snd.prodMk ((hp.comp measurable_fst.fst).prodMk measurable_fst.snd))).lintegral_prod_right'
  rw [lintegral_lintegral_swap hxv.aemeasurable]
  apply lintegral_congr
  intro v
  have hxc : Measurable (fun z : Scalar × Control => f (z.2, (pairAt z.1, v))) :=
    hf.comp (measurable_snd.prodMk ((hp.comp measurable_fst).prodMk measurable_const))
  rw [lintegral_lintegral_swap hxc.aemeasurable]

private theorem lintegral_control_assignment (f : Control × Vector → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ c, f (c, (controlAssignmentSplitEquiv p c).1) ∂ContinuousLearningRows.timeControlLaw p) =
      ∫⁻ v, ∫⁻ c, f (fixedVectorControl v c, v)
        ∂ContinuousLearningRows.timeControlLaw p ∂ContinuousControlSlice.assignmentLaw p.K := by
  let e := controlAssignmentSplitEquiv p
  let g : Vector × ReferenceLaterOptionalControlResampling.ControlRemainder p → ℝ≥0∞ :=
    fun z => f (e.symm z, z.1)
  have hg : Measurable g := hf.comp (e.symm.measurable.prodMk measurable_fst)
  have hsplit := measurePreserving_controlAssignmentSplitEquiv p
  have hrem := (measurePreserving_snd (μ := ContinuousControlSlice.assignmentLaw p.K)
    (ν := ReferenceLaterOptionalControlResampling.controlRemainderLaw p)).comp hsplit
  calc
    _ = ∫⁻ c, g (e c) ∂ContinuousLearningRows.timeControlLaw p := by
      apply lintegral_congr
      intro c
      simp only [g, e, MeasurableEquiv.symm_apply_apply]
    _ = ∫⁻ z, g z ∂(ContinuousControlSlice.assignmentLaw p.K).prod
        (ReferenceLaterOptionalControlResampling.controlRemainderLaw p) := hsplit.lintegral_comp hg
    _ = ∫⁻ v, ∫⁻ d, g (v, d) ∂ReferenceLaterOptionalControlResampling.controlRemainderLaw p
        ∂ContinuousControlSlice.assignmentLaw p.K := lintegral_prod _ hg.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro v
      exact (hrem.lintegral_comp (hg.comp (measurable_const.prodMk measurable_id))).symm

section GeneratedCall

attribute [-instance] outcomeMeasurableSpace outcomeDiscrete
attribute [local instance] slowSetMeasurableSpace slowSetDiscrete

variable (b0 : Bool) (u0 t0 : Fin p.T)

include control0

local notation "Sample" => CalendarSample rate rewards C_star C_h b0 u0 t0
local notation "past" => calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0
local notation "current" => calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0
local notation "original" => calendarOriginalLift rate rewards C_star C_h b0 u0 t0
local notation "pending" => calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0
local notation "callFlag" => calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0
local notation "law" => calendarLaw rate rewards C_star C_h control0 b0 u0 t0
local notation "extension" => calendarExtensionKernel rate rewards C_star C_h control0 b0 u0 t0
local notation "fillPair" => calendarFillPair rate rewards C_star C_h b0 u0 t0
local notation "Cell" => LogicalCell p rate
local notation "Past" => Source × (SlowSet p × List Cell)

variable (k : ℕ) (hk : t0.val + 1 + k < p.T)

local notation "q" => (Fin.mk (t0.val + 1 + k) hk)
local notation "htq" => (noncallDate_after t0 k)
local notation "putControl" => calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k
local notation "withUpdate" => calendarWithUpdateScalar rate rewards C_star C_h control0 b0 u0 t0 k hk
local notation "invoke" => calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk

/-- Refill the SAME original sample, changing only this physical control and
its local UPDATE scalar. Renewal selects label zero; retention selects one. -/
def calendarCallRefill (w : Sample k) (a : Scalar × Scalar) (c : Control) (x : Scalar) : Sample k :=
  withUpdate (putControl (fillPair q k (w, a), c), x)

/-- Native source after the physical refill and WHOLE vector insertion. -/
def calendarCallSourceAt (w : Sample k) (v : Vector)
    (hc : callFlag k (by omega) w = true) (c : Control) : InvocationSource rate rewards C_star C_h q :=
  invoke (putControl (w, c)) v
    ((calendarCallFlag_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k hk le_rfl w c).trans hc)

local notation "sourceAt" => calendarCallSourceAt rate rewards C_star C_h control0 b0 u0 t0 k hk

theorem calendarCallSourceAt_val (w : Sample k) (v : Vector)
    (hc : callFlag k (by omega) w = true) (c : Control) :
    (sourceAt w v hc c).val = ReferenceFirstCollectionRenewalVectorInsertion.insert q
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q (current k hk.le w) c) v := by
  change ReferenceFirstCollectionRenewalVectorInsertion.insert q
    (current k hk.le (putControl (w, c))) v = _
  rw [calendarCurrentSource_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k hk.le le_rfl]

private theorem calendarInvocation_history (w : Sample k) (v : Vector)
    (hc : callFlag k (by omega) w = true) :
    ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0
      (nativeRank rate rewards C_star C_h q (invoke w v hc).val) q (invoke w v hc).val =
    ReferenceRankInstallationRecorderFoundation.prefixVectorHistory rate rewards C_star C_h control0 q
      ((past k hk.le w).1, v) := by
  rw [ReferenceRankInstallationRecorderFoundation.history_eq_prefixVectorHistory_of_installation
    rate rewards C_star C_h control0 _ _ _ (native_installation rate rewards C_star C_h _ _)]
  congr 1
  apply Prod.ext
  · exact ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q _ le_rfl _ _
  · exact ReferenceFirstCollectionRenewalVectorInsertion.av_insert _ _ v

theorem calendarCallSourceAt_control (w : Sample k) (v : Vector)
    (hc : callFlag k (by omega) w = true) (c : Control) :
    ReferenceSourceCurrentControlFreshness.u_t p q (sourceAt w v hc c).val = fixedVectorControl v c := by
  rw [calendarCallSourceAt_val]
  change ReferenceSourceCurrentControlFreshness.u_t p q
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q (current k hk.le w) c)
      (fixedVectorControl v (ReferenceSourceCurrentControlFreshness.u_t p q
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q (current k hk.le w) c)))) = _
  rw [currentControl_replaceSourceControl, currentControl_replaceSourceControl]

omit control0 in
/-- The physical proposal is unchanged by assignment-vector insertion. -/
private theorem physicalProposalBit_fixedVectorControl (v : Vector) (c : Control) :
    physicalProposalBit rate (fixedVectorControl v c) = physicalProposalBit rate c := by
  have hl : ¬ ∃ i : Fin (p.K + 1), propLabel p = ContinuousControlSlice.Label.assign i := by
    rintro ⟨i, hi⟩
    exact Sum.inl_ne_inr hi
  exact congrArg (fun x => FollowerCutoffScan.thresholdProposalBit x
    (FollowerCutoffScan.proposalHazard p rate.eta.val))
      (fixedVectorControl_nonassignment v c ⟨_, hl⟩)

/-- Current physical draw on the actual generated invocation, reconstructed
from its strict history and installed vector. -/
def calendarCallControlDraw (w : Sample k) (v : Vector)
    (hc : callFlag k (by omega) w = true) (c : Control) : PairUpdate × Bool :=
  ((ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate rate rewards C_star C_h control0 q
    (ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0
      (nativeRank rate rewards C_star C_h q (invoke w v hc).val) q (invoke w v hc).val)
    (controlAssignmentSplitEquiv p c).2), physicalProposalBit rate c)

/-- The evaluated observer is the actual source pair, full numerical POST
and physical proposal, on this SAME original native source. -/
theorem calendarCallControlDraw_readout (w : Sample k) (v : Vector)
    (hc : callFlag k (by omega) w = true) (c : Control) :
    calendarCallControlDraw rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc c =
      ((ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast rate rewards C_star C_h q
          (sourceAt w v hc c).val,
        ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
          rate rewards C_star C_h control0 q (sourceAt w v hc c).val),
        physicalProposalBit rate (ReferenceSourceCurrentControlFreshness.u_t p q (sourceAt w v hc c).val)) := by
  have hc' : callFlag k (by omega) (putControl (w, c)) = true :=
    (calendarCallFlag_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k hk le_rfl w c).trans hc
  have hh := calendarInvocation_history rate rewards C_star C_h control0 b0 u0 t0 k hk
    (putControl (w, c)) v hc'
  rw [calendarRoundPast_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k hk.le le_rfl] at hh
  have hh0 := calendarInvocation_history rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  have hrem : ReferenceFirstNextInvocationJointLift.currentRemainder q (sourceAt w v hc c).val =
      (controlAssignmentSplitEquiv p c).2 := by
    change (controlAssignmentSplitEquiv p
      (ReferenceSourceCurrentControlFreshness.u_t p q (sourceAt w v hc c).val)).2 = _
    rw [calendarCallSourceAt_control]
    change ((controlAssignmentSplitEquiv p)
      ((controlAssignmentSplitEquiv p).symm (v, (controlAssignmentSplitEquiv p c).2))).2 = _
    rw [MeasurableEquiv.apply_symm_apply]
  apply Prod.ext
  · change ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
      rate rewards C_star C_h control0 q _ _ = _
    have hrec := callNative_pairUpdate_reconstruction rate rewards C_star C_h control0 q (sourceAt w v hc c)
    exact (congrArg₂ (ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
      rate rewards C_star C_h control0 q) (hh0.trans hh.symm) hrem.symm).trans hrec.symm
  · dsimp only [calendarCallControlDraw]
    rw [calendarCallSourceAt_control, physicalProposalBit_fixedVectorControl]

/-- The numerical PRE and selected complement are identified internally at
arbitrary rank, on the actual original word, with no envelope premise. -/
theorem calendarInvocationCell_numerical_complement (w : Sample k) (v : Vector)
    (hc : callFlag k (by omega) w = true)
    (hclear : (pending k (by omega) w).2 = true) :
    ∀ j : CanonicalFastSampling.FastArm
      (nativeSourceCell rate rewards C_star C_h q (invoke w v hc)).selected.view.payload.slowSet,
      (nativeSourceCell rate rewards C_star C_h q (invoke w v hc)).selected.view.complementWeights j =
        RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (nativeBefore rate rewards C_star C_h control0 q (invoke w v hc)) j.val := by
  have hb := calendarInvocationCell_before rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  change (calendarObservation rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).2.val.2.2.1.any
    (fun S => !S.overflow) = true at hclear
  rw [← hb, Option.any_some, Bool.not_eq_true'] at hclear
  exact invocation_numerical_complement rate rewards C_star C_h control0 q (invoke w v hc) hclear

/-- The correlated common-update law and independent physical proposal on
this actual generated native source. -/
def calendarCallControlLaw (w : Sample k) (v : Vector) (hc : callFlag k (by omega) w = true) :=
  (ReferenceRankInstallationCommonUpdateJointLaw.commonUpdateKernel rate rewards q
    (nativeSourceCell rate rewards C_star C_h q (invoke w v hc)).selected.view
    (ReferenceRankInstallationRecorderFastLaw.actualInstallationView_valid
      rate rewards C_star C_h q (invoke w v hc).val _
      (nativeCell_view rate rewards C_star C_h control0 q (invoke w v hc)))
    (some ((nativeBefore rate rewards C_star C_h control0 q (invoke w v hc)).registers,
      (nativeBefore rate rewards C_star C_h control0 q (invoke w v hc)).overflow,
      (nativeBefore rate rewards C_star C_h control0 q (invoke w v hc)).records))).prod (proposalBitLaw rate)

def calendarCallControlFibre (w : Sample k) (v : Vector) (hc : callFlag k (by omega) w = true)
    (y : PairUpdate × Bool) :=
  FiniteFibreLift.fibreMeasure (ContinuousLearningRows.timeControlLaw p)
    (calendarCallControlDraw rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc) y

/-- True fixed-anchor residual after the SAME physical numerical update.
The gate is incoming PRE overflow, so detecting POST overflow retains refresh. -/
def calendarCallRefreshLaw (w : Sample k) (v : Vector) (hc : callFlag k (by omega) w = true) (c : Control) :=
  ReferenceFirstLiveCalendarMarkedTransition.logicalCellResidualLaw rate
    (nativeRecord rate rewards C_star C_h q (sourceAt w v hc c))
    (nativeSourceCell rate rewards C_star C_h q (sourceAt w v hc c))
    (nativeBefore rate rewards C_star C_h control0 q (sourceAt w v hc c))

def calendarCallRefreshFibre (w : Sample k) (v : Vector) (hc : callFlag k (by omega) w = true)
    (c : Control) (U : SlowSet p) :=
  FiniteFibreLift.fibreMeasure ContinuousControlSlice.scalarLaw
    (fun x => (nativeCell rate rewards C_star C_h control0 q (sourceAt w v hc c) x).nextSlowSet) U

omit control0 in
private theorem withAuxiliary_twice (j : ℕ) (w : Sample j)
    (a b : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :
    calendarWithAuxiliary rate rewards C_star C_h b0 u0 t0 j
      (calendarWithAuxiliary rate rewards C_star C_h b0 u0 t0 j (w, a), b) =
    calendarWithAuxiliary rate rewards C_star C_h b0 u0 t0 j (w, b) := by
  induction j with
  | zero => rfl
  | succ j ih => exact Prod.ext (ih w.1) rfl

private theorem replaceControl_withAuxiliary (j : ℕ) (w : Sample j)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) (c : Control) :
    calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq j
      (calendarWithAuxiliary rate rewards C_star C_h b0 u0 t0 j (w, a), c) =
    calendarWithAuxiliary rate rewards C_star C_h b0 u0 t0 j
      (calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq j (w, c), a) := by
  induction j with
  | zero => rfl
  | succ j ih => exact Prod.ext (ih w.1) rfl

omit rate rewards C_star C_h control0 b0 u0 in
private theorem fillAuxiliaryPair_update (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (b : Bool) (z : Scalar × Scalar) (x : Scalar) :
    Function.update (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q a z)
      (q, if b then 0 else 1) x =
    ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q a
      (if b then (x, z.2) else (z.1, x)) := by
  cases b <;> funext i
  all_goals
    by_cases h0 : i = (q, (0 : Fin 2))
    · subst i
      simp [ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair]
    · by_cases h1 : i = (q, (1 : Fin 2))
      · subst i
        simp [ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair]
      · simp [ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair, h0, h1]

private theorem calendarCallRefill_eq (w : Sample k) (hc : callFlag k (by omega) w = true)
    (a : Scalar × Scalar) (c : Control) (x : Scalar) :
    calendarCallRefill rate rewards C_star C_h control0 b0 u0 t0 k hk w a c x =
      putControl (fillPair q k (w, if (pending k (by omega) w).1 then (x, a.2) else (a.1, x)), c) := by
  have hp := calendarPendingRenewal_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k hk le_rfl
    (fillPair q k (w, a)) c (by
      rw [calendarFillPair_eq_withAuxiliary, calendarCallFlag_withAuxiliary]
      exact hc)
  rw [calendarFillPair_eq_withAuxiliary, calendarPendingFlags_withAuxiliary] at hp
  unfold calendarCallRefill calendarWithUpdateScalar
  dsimp only [Prod.fst, Prod.snd]
  rw [calendarFillPair_eq_withAuxiliary, hp, calendarOriginalLift_replaceControl, calendarFillPair_eq_withAuxiliary,
    calendarOriginalLift_withAuxiliary, replaceControl_withAuxiliary, withAuxiliary_twice,
    fillAuxiliaryPair_update, replaceControl_withAuxiliary]

private theorem measurable_calendarCallRefill (w : Sample k) :
    Measurable (fun z : (Control × (Scalar × Scalar)) × Scalar =>
      calendarCallRefill rate rewards C_star C_h control0 b0 u0 t0 k hk w z.1.2 z.1.1 z.2) := by
  have ha : Measurable (fun z : (Control × (Scalar × Scalar)) × Scalar =>
      fillPair q k (w, z.1.2)) := (measurable_calendarFillPair rate rewards C_star C_h b0 u0 t0 q k).comp
    (measurable_const.prodMk measurable_fst.snd)
  have hc : Measurable (fun z : (Control × (Scalar × Scalar)) × Scalar =>
      putControl (fillPair q k (w, z.1.2), z.1.1)) := (measurable_calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k).comp
    (ha.prodMk measurable_fst.fst)
  exact (measurable_calendarWithUpdateScalar rate rewards C_star C_h control0 b0 u0 t0 k hk).comp
    (hc.prodMk measurable_snd)

private theorem calendarReplaceControl_original (j : ℕ) (w : Sample j) :
    calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq j
      (w, ReferenceSourceCurrentControlFreshness.u_t p q (original j w).1.1.val) = w := by
  induction j with
  | zero =>
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact ReferenceFixedTimeSourceControlCoupling.replaceSourceControl_original p q w.1.1.val
      · rfl
    · rfl
  | succ j ih => exact Prod.ext (ih w.1) rfl

private theorem calendarExtensionKernel_pair_update (w : Sample k)
    (hc : callFlag k (by omega) w = true) (a : Scalar × Scalar) (x : Scalar) :
    extension k (by omega)
      (fillPair q k (w, if (pending k (by omega) w).1 then (x, a.2) else (a.1, x))) =
    extension k (by omega) (fillPair q k (w, a)) := by
  let c := ReferenceSourceCurrentControlFreshness.u_t p q (original k w).1.1.val
  have hid (b : Scalar × Scalar) : putControl (fillPair q k (w, b), c) = fillPair q k (w, b) := by
    rw [calendarFillPair_eq_withAuxiliary, replaceControl_withAuxiliary]
    exact congrArg (fun z => calendarWithAuxiliary rate rewards C_star C_h b0 u0 t0 k
      (z, ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q (original k w).1.2 b))
      (calendarReplaceControl_original rate rewards C_star C_h control0 b0 u0 t0 k hk k w)
  have he := calendarCallRefill_eq rate rewards C_star C_h control0 b0 u0 t0 k hk w hc a c x
  rw [calendarCallRefill, hid, hid] at he
  rw [← he]
  exact calendarExtensionKernel_withUpdateScalar rate rewards C_star C_h control0 b0 u0 t0 k hk _ x

private theorem calendarCall_refill_integral (w : Sample k)
    (hc : callFlag k (by omega) w = true) (hclear : (pending k (by omega) w).2 = true)
    (F : Sample k × Vector → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, ∫⁻ v, F (calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k (w, z), v)
      ∂extension k (by omega) (calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k (w, z))
      ∂innovationLaw (p := p)) =
    ∫⁻ a, ∫⁻ v, ∫⁻ c, ∫⁻ x,
      F (calendarCallRefill rate rewards C_star C_h control0 b0 u0 t0 k hk w a c x, v)
      ∂ContinuousControlSlice.scalarLaw ∂ContinuousLearningRows.timeControlLaw p
      ∂extension k (by omega) (fillPair q k (w, a)) ∂auxiliaryPairLaw := by
  let K := (extension k (by omega)).comap (fun a => fillPair q k (w, a))
    ((measurable_calendarFillPair rate rewards C_star C_h b0 u0 t0 q k).comp
      (measurable_const.prodMk measurable_id))
  let f : Control × ((Scalar × Scalar) × Vector) → ℝ≥0∞ := fun z =>
    F (putControl (fillPair q k (w, z.2.1), z.1), z.2.2)
  have hfill : Measurable (fun z : Control × ((Scalar × Scalar) × Vector) => fillPair q k (w, z.2.1)) :=
    (measurable_calendarFillPair rate rewards C_star C_h b0 u0 t0 q k).comp
      (measurable_const.prodMk measurable_snd.fst)
  have hput := (measurable_calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k).comp
    (hfill.prodMk measurable_fst)
  have hf : Measurable f := hF.comp (hput.prodMk measurable_snd.snd)
  have hK (z : Innovation p) : extension k (by omega)
      (calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k (w, z)) = K z.2 := by
    apply calendarExtensionKernel_active_currentControl rate rewards C_star C_h control0 b0 u0 t0 k hk
    · rw [calendarFillPair_eq_withAuxiliary, calendarCallFlag_withAuxiliary]
      exact hc
    · rw [calendarFillPair_eq_withAuxiliary, calendarPendingFlags_withAuxiliary]
      exact hclear
  change (∫⁻ z, ∫⁻ v, f (z.1, (z.2, v)) ∂extension k (by omega)
    (calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k (w, z))
    ∂(ContinuousLearningRows.timeControlLaw p).prod auxiliaryPairLaw) = _
  simp_rw [hK]
  rw [lintegral_control_pair_kernel (ContinuousLearningRows.timeControlLaw p) auxiliaryPairLaw K f hf]
  refine (lintegral_pair_kernel_resample (ContinuousLearningRows.timeControlLaw p) K
    (pending k (by omega) w).1 f hf
    (calendarExtensionKernel_pair_update rate rewards C_star C_h control0 b0 u0 t0 k hk w hc)).trans ?_
  apply lintegral_congr
  intro a
  apply lintegral_congr
  intro v
  apply lintegral_congr
  intro c
  apply lintegral_congr
  intro x
  exact congrArg (fun y => F (y, v))
    (calendarCallRefill_eq rate rewards C_star C_h control0 b0 u0 t0 k hk w hc a c x).symm

/-- The complete generated CALL coefficient. Both actual call and incoming
PRE-clear gates are inside the unnormalized test. Physical controls remain
in their correlated fibres; zero coefficients and null fibres are retained. -/
def calendarCallTest (F : Sample k × Vector → ℝ≥0∞) (w : Sample k) : ℝ≥0∞ :=
  if ha : w ∈ calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk then
    ∫⁻ a, ∫⁻ v, ∫⁻ y, ∫⁻ c, ∫⁻ U, ∫⁻ x,
      F (calendarCallRefill rate rewards C_star C_h control0 b0 u0 t0 k hk w a c x, v)
      ∂calendarCallRefreshFibre rate rewards C_star C_h control0 b0 u0 t0 k hk w v ha.1 c U
      ∂calendarCallRefreshLaw rate rewards C_star C_h control0 b0 u0 t0 k hk w v ha.1 c
      ∂calendarCallControlFibre rate rewards C_star C_h control0 b0 u0 t0 k hk w v ha.1 y
      ∂calendarCallControlLaw rate rewards C_star C_h control0 b0 u0 t0 k hk w v ha.1
      ∂extension k (by omega) (fillPair q k (w, a)) ∂auxiliaryPairLaw
  else 0

private theorem calendarCallTest_eq_refill (F : Sample k × Vector → ℝ≥0∞) (hF : Measurable F)
    (w : Sample k) :
    calendarCallTest rate rewards C_star C_h control0 b0 u0 t0 k hk F w =
      if w ∈ calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk then
        ∫⁻ z, ∫⁻ v, F (calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k (w, z), v)
          ∂extension k (by omega) (calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k (w, z))
          ∂innovationLaw (p := p) else 0 := by
  unfold calendarCallTest
  split
  next ha =>
    rw [calendarCall_refill_integral rate rewards C_star C_h control0 b0 u0 t0 k hk w ha.1 ha.2 F hF]
    apply lintegral_congr
    intro a
    apply lintegral_congr
    intro v
    change (∫⁻ y, ∫⁻ c, ∫⁻ U, ∫⁻ x,
      F (calendarCallRefill rate rewards C_star C_h control0 b0 u0 t0 k hk w a c x, v)
      ∂invocationRefreshFibre rate rewards C_star C_h control0 q (sourceAt w v ha.1 c) U
      ∂invocationRefreshLaw rate rewards C_star C_h control0 q (sourceAt w v ha.1 c)
      ∂invocationControlFibre rate rewards C_star C_h control0 q (invoke w v ha.1) y
      ∂invocationControlLaw rate rewards C_star C_h control0 q (invoke w v ha.1)) = _
    rw [← invocationControl_test rate rewards C_star C_h control0 q (invoke w v ha.1)]
    apply lintegral_congr
    intro c
    exact (invocationRefresh_test rate rewards C_star C_h control0 q (sourceAt w v ha.1 c) _).symm
  next _ => rfl

private theorem calendarActive_fillInnovation (w : Sample k) (z : Innovation p) :
    calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k (w, z) ∈
        calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk ↔
      w ∈ calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk := by
  change (callFlag k (by omega) (calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k
    (fillPair q k (w, z.2), z.1)) = true ∧
    (pending k (by omega) (calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k
      (fillPair q k (w, z.2), z.1))).2 = true) ↔ _
  rw [calendarCallFlag_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k hk le_rfl,
    calendarPendingClear_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k hk le_rfl,
    calendarFillPair_eq_withAuxiliary, calendarCallFlag_withAuxiliary, calendarPendingFlags_withAuxiliary]
  rfl

/-- Evaluated physical numerical/proposal/selected residual law on actual
later calls. Arbitrary Borel joint tests can inspect the entire raw sample,
original private arrays, installed vector, native PRE and complete native POST. -/
theorem calendarLaw_call_round_test (F : Sample k × Vector → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ wv : Sample k × Vector,
      if wv.1 ∈ calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk then F wv else 0
      ∂law (k + 1) (by omega)) =
      ∫⁻ w, calendarCallTest rate rewards C_star C_h control0 b0 u0 t0 k hk F w
        ∂(law k hk.le).map (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k) := by
  let active := calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk
  let test : Sample k × Vector → ℝ≥0∞ := fun wv => if wv.1 ∈ active then F wv else 0
  have ht : Measurable test := hF.ite
    ((measurableSet_calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk).preimage measurable_fst)
    measurable_const
  refine (calendarLaw_round_innovation_test rate rewards C_star C_h control0 b0 u0 t0 q htq k hk le_rfl test ht).trans ?_
  apply lintegral_congr
  intro w
  rw [calendarCallTest_eq_refill rate rewards C_star C_h control0 b0 u0 t0 k hk F hF w]
  have hflags := calendarActive_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 k hk w
  by_cases ha : w ∈ active
  · rw [ite_eq_left ha]
    apply lintegral_congr
    intro z
    apply lintegral_congr
    intro v
    exact ite_eq_left ((hflags z).mpr ha)
  · rw [ite_eq_right ha]
    have he (z : Innovation p) (v : Vector) :
        test (calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k (w, z), v) = 0 :=
      ite_eq_right (fun h => ha ((hflags z).mp h))
    simp_rw [he, lintegral_zero]

theorem calendarCallRefill_call (w : Sample k) (hc : callFlag k (by omega) w = true)
    (a : Scalar × Scalar) (c : Control) (x : Scalar) :
    callFlag k (by omega) (calendarCallRefill rate rewards C_star C_h control0 b0 u0 t0 k hk w a c x) = true := by
  unfold calendarCallRefill calendarWithUpdateScalar
  dsimp only [Prod.fst, Prod.snd]
  rw [calendarCallFlag_withAuxiliary,
    calendarCallFlag_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k hk le_rfl,
    calendarFillPair_eq_withAuxiliary, calendarCallFlag_withAuxiliary]
  exact hc

/-- Actual selected UPDATE scalar, rather than a surrogate draw. The entire
native cell, including the first detecting overflow UPDATE, is retained. -/
theorem calendarCallRefill_cell (w : Sample k) (v : Vector) (hc : callFlag k (by omega) w = true)
    (a : Scalar × Scalar) (c : Control) (x : Scalar) :
    calendarInvocationCell rate rewards C_star C_h control0 b0 u0 t0 k hk
      (calendarCallRefill rate rewards C_star C_h control0 b0 u0 t0 k hk w a c x) v
      (calendarCallRefill_call rate rewards C_star C_h control0 b0 u0 t0 k hk w hc a c x) =
    nativeCell rate rewards C_star C_h control0 q (sourceAt w v hc c) x := by
  let w0 := putControl (fillPair q k (w, a), c)
  have hc0 : callFlag k (by omega) w0 = true := by
    rw [calendarCallFlag_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k hk le_rfl,
      calendarFillPair_eq_withAuxiliary, calendarCallFlag_withAuxiliary]
    exact hc
  have hz : invoke w0 v hc0 = sourceAt w v hc c := by
    apply Subtype.ext
    change ReferenceFirstCollectionRenewalVectorInsertion.insert q (current k hk.le w0) v = _
    rw [calendarCallSourceAt_val]
    exact congrArg (fun z => ReferenceFirstCollectionRenewalVectorInsertion.insert q z v)
      (calendarCurrentSource_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 k hk w (c, a))
  have he := calendarInvocationCell_withUpdateScalar rate rewards C_star C_h control0 b0 u0 t0 k hk w0 v hc0 x
  dsimp only at he
  rw [hz] at he
  exact he

/-- An arbitrary joint cylinder may retain BOTH native observers and the
literal physical numerical/proposal readouts, alongside the complete raw
sample and the proper past. -/
abbrev CallRoundData := (Past × Vector) × ((PairUpdate × Bool) ×
  CalendarJointOutput rate rewards C_star C_h b0 u0 t0 k hk)

def calendarCallRoundReadout (wv : Sample k × Vector) :
    CallRoundData rate rewards C_star C_h b0 u0 t0 k hk :=
  ((past k hk.le wv.1, wv.2),
    (((ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast rate rewards C_star C_h q
        (current (k + 1) (by omega) wv),
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
        rate rewards C_star C_h control0 q (current (k + 1) (by omega) wv)),
      physicalProposalBit rate (ReferenceSourceCurrentControlFreshness.u_t p q (current (k + 1) (by omega) wv))),
      calendarJointReadout rate rewards C_star C_h control0 b0 u0 t0 k hk wv))

local instance callPastSpace : MeasurableSpace Past := inferInstance
local instance callVectorSpace : MeasurableSpace Vector := inferInstance
local instance callPairUpdateSpace : MeasurableSpace PairUpdate := inferInstance
local instance callJointSpace : MeasurableSpace (CalendarJointOutput rate rewards C_star C_h b0 u0 t0 k hk) := by
  unfold CalendarJointOutput
  exact Prod.instMeasurableSpace

theorem measurable_calendarCallRoundReadout :
    Measurable (calendarCallRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk) := by
  have hs := measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega)
  have hp := ReferenceRankInstallationRecorderFastLaw.measurable_actualMarkerReservedFast rate rewards C_star C_h q
  have hu := ReferenceRankInstallationPostUpdateProposalLaw.measurable_actualInstallationNumericalUpdate
    rate rewards C_star C_h control0 q
  have hb := (measurable_physicalProposalBit rate).comp (ReferenceSourceCurrentControlFreshness.measurable_u_t q)
  exact (((measurable_calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk.le).comp measurable_fst).prodMk
    measurable_snd).prodMk ((((hp.comp hs).prodMk (hu.comp hs)).prodMk (hb.comp hs)).prodMk
      (measurable_calendarJointReadout rate rewards C_star C_h control0 b0 u0 t0 k hk))

/-- Evaluated numerical/proposal/residual law for arbitrary measurable joint
round tests, with the installed vector and both actual native observers. -/
theorem calendarLaw_call_numerical_test
    (Phi : CallRoundData rate rewards C_star C_h b0 u0 t0 k hk → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ wv : Sample k × Vector,
      if wv.1 ∈ calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk then
        Phi (calendarCallRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk wv) else 0
      ∂law (k + 1) (by omega)) =
    ∫⁻ w, calendarCallTest rate rewards C_star C_h control0 b0 u0 t0 k hk
      (Phi ∘ calendarCallRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk) w
      ∂(law k hk.le).map (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k) :=
  calendarLaw_call_round_test rate rewards C_star C_h control0 b0 u0 t0 k hk _
    (hPhi.comp (measurable_calendarCallRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk))

/-- Analytic test-family measurability is constructed from the actual
innovation kernel, rather than assumed as an input to the local law. -/
theorem measurable_calendarCallTest (F : Sample k × Vector → ℝ≥0∞) (hF : Measurable F) :
    Measurable (calendarCallTest rate rewards C_star C_h control0 b0 u0 t0 k hk F) := by
  let fill := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k
  have hfill := measurable_calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k
  let K := (extension k (by omega)).comap fill hfill
  let g : (Sample k × Innovation p) × Vector → ℝ≥0∞ := fun z => F (fill z.1, z.2)
  have hg : Measurable g := hF.comp ((hfill.comp measurable_fst).prodMk measurable_snd)
  have hinner : Measurable (fun wx : Sample k × Innovation p => ∫⁻ v, g (wx, v) ∂K wx) :=
    hg.lintegral_kernel_prod_right'
  have htotal : Measurable (fun w : Sample k => if w ∈
      calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk then
        ∫⁻ z, ∫⁻ v, g ((w, z), v) ∂K (w, z) ∂innovationLaw (p := p) else 0) :=
    hinner.lintegral_prod_right'.ite
      (measurableSet_calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk) measurable_const
  have he := funext (calendarCallTest_eq_refill rate rewards C_star C_h control0 b0 u0 t0 k hk F hF)
  rw [he]
  exact htotal

private theorem calendarStopped_refill_integral (w : Sample k)
    (hc : callFlag k (by omega) w = true) (hstop : (pending k (by omega) w).2 = false)
    (F : Sample k × Vector → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, ∫⁻ v, F (calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k (w, z), v)
      ∂extension k (by omega) (calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k (w, z))
      ∂innovationLaw (p := p)) =
    ∫⁻ a, ∫⁻ v, ∫⁻ c, ∫⁻ x,
      F (calendarCallRefill rate rewards C_star C_h control0 b0 u0 t0 k hk w a (fixedVectorControl v c) x, v)
      ∂ContinuousControlSlice.scalarLaw ∂ContinuousLearningRows.timeControlLaw p
      ∂ContinuousControlSlice.assignmentLaw p.K ∂auxiliaryPairLaw := by
  let fill := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k
  have hK (z : Innovation p) : extension k (by omega) (fill (w, z)) =
      Measure.dirac (controlAssignmentSplitEquiv p z.1).1 := by
    have hs : (pending k (by omega) (fill (w, z))).2 = false := by
      change (pending k (by omega) (putControl (fillPair q k (w, z.2), z.1))).2 = false
      rw [calendarPendingClear_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k hk le_rfl,
        calendarFillPair_eq_withAuxiliary, calendarPendingFlags_withAuxiliary, hstop]
    rw [calendarExtensionKernel_readout rate rewards C_star C_h control0 b0 u0 t0 k hk]
    have hv : ReferenceFirstCollectionRenewalVectorInsertion.av q (current k hk.le (fill (w, z))) =
        (controlAssignmentSplitEquiv p z.1).1 := by
      rw [calendarCurrentSource_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 k hk]
      change (controlAssignmentSplitEquiv p (ReferenceSourceCurrentControlFreshness.u_t p q
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q (current k hk.le w) z.1))).1 = _
      rw [currentControl_replaceSourceControl]
    cases ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q (current k hk.le (fill (w, z))) <;>
      simp only [hs, Bool.false_eq_true, ite_false, hv]
  change (∫⁻ z, ∫⁻ v, F (fill (w, z), v) ∂extension k (by omega) (fill (w, z))
    ∂innovationLaw (p := p)) = _
  have hcollapse (z : Innovation p) :
      (∫⁻ v, F (fill (w, z), v) ∂extension k (by omega) (fill (w, z))) =
        F (fill (w, z), (controlAssignmentSplitEquiv p z.1).1) := by
    rw [hK z, lintegral_dirac]
  simp_rw [hcollapse]
  let f : Control × ((Scalar × Scalar) × Vector) → ℝ≥0∞ := fun z =>
    F (putControl (fillPair q k (w, z.2.1), z.1), z.2.2)
  have hfa : Measurable (fun z : Control × ((Scalar × Scalar) × Vector) => fillPair q k (w, z.2.1)) :=
    (measurable_calendarFillPair rate rewards C_star C_h b0 u0 t0 q k).comp
      (measurable_const.prodMk measurable_snd.fst)
  have hf : Measurable f := hF.comp
    (((measurable_calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k).comp
      (hfa.prodMk measurable_fst)).prodMk measurable_snd.snd)
  have hca : Measurable (fun z : Control × (Scalar × Scalar) =>
      f (z.1, (z.2, (controlAssignmentSplitEquiv p z.1).1))) :=
    hf.comp (measurable_fst.prodMk (measurable_snd.prodMk
      (((controlAssignmentSplitEquiv p).measurable.comp measurable_fst).fst)))
  change (∫⁻ z, f (z.1, (z.2, (controlAssignmentSplitEquiv p z.1).1))
    ∂(ContinuousLearningRows.timeControlLaw p).prod auxiliaryPairLaw) = _
  rw [lintegral_prod _ hca.aemeasurable, lintegral_lintegral_swap hca.aemeasurable]
  have he (a : Scalar × Scalar) :
      (∫⁻ c, f (c, (a, (controlAssignmentSplitEquiv p c).1)) ∂ContinuousLearningRows.timeControlLaw p) =
      ∫⁻ v, ∫⁻ c, f (fixedVectorControl v c, (a, v)) ∂ContinuousLearningRows.timeControlLaw p
        ∂ContinuousControlSlice.assignmentLaw p.K :=
    lintegral_control_assignment _ (hf.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
  simp_rw [he]
  let f0 : Control × ((Scalar × Scalar) × Vector) → ℝ≥0∞ := fun z =>
    f (fixedVectorControl z.2.2 z.1, z.2)
  have hfixed : Measurable (fun z : Control × ((Scalar × Scalar) × Vector) => fixedVectorControl z.2.2 z.1) :=
    (controlAssignmentSplitEquiv p).symm.measurable.comp
      (measurable_snd.snd.prodMk (((controlAssignmentSplitEquiv p).measurable.comp measurable_fst).snd))
  have hf0 : Measurable f0 := hf.comp (hfixed.prodMk measurable_snd)
  let K := ProbabilityTheory.Kernel.const (Scalar × Scalar) (ContinuousControlSlice.assignmentLaw p.K)
  refine (lintegral_pair_kernel_resample (ContinuousLearningRows.timeControlLaw p) K
    (pending k (by omega) w).1 f0 hf0 (fun _ _ => rfl)).trans ?_
  apply lintegral_congr
  intro a
  apply lintegral_congr
  intro v
  apply lintegral_congr
  intro c
  apply lintegral_congr
  intro x
  exact congrArg (fun y => F (y, v))
    (calendarCallRefill_eq rate rewards C_star C_h control0 b0 u0 t0 k hk w hc a (fixedVectorControl v c) x).symm

/-- Incoming PRE-stopped CALLs retain the effective frozen tuple while the
physical raw numerical data and original source coordinates continue. -/
def calendarStoppedCallTest (F : Sample k × Vector → ℝ≥0∞) (w : Sample k) : ℝ≥0∞ :=
  if hs : callFlag k (by omega) w = true ∧ (pending k (by omega) w).2 = false then
    ∫⁻ a, ∫⁻ v, ∫⁻ y, ∫⁻ c, ∫⁻ U, ∫⁻ x,
      F (calendarCallRefill rate rewards C_star C_h control0 b0 u0 t0 k hk w a (fixedVectorControl v c) x, v)
      ∂calendarCallRefreshFibre rate rewards C_star C_h control0 b0 u0 t0 k hk w v hs.1 (fixedVectorControl v c) U
      ∂calendarCallRefreshLaw rate rewards C_star C_h control0 b0 u0 t0 k hk w v hs.1 (fixedVectorControl v c)
      ∂calendarCallControlFibre rate rewards C_star C_h control0 b0 u0 t0 k hk w v hs.1 y
      ∂calendarCallControlLaw rate rewards C_star C_h control0 b0 u0 t0 k hk w v hs.1
      ∂ContinuousControlSlice.assignmentLaw p.K ∂auxiliaryPairLaw
  else 0

private theorem calendarStoppedCallTest_eq_refill (F : Sample k × Vector → ℝ≥0∞) (hF : Measurable F)
    (w : Sample k) :
    calendarStoppedCallTest rate rewards C_star C_h control0 b0 u0 t0 k hk F w =
      if callFlag k (by omega) w = true ∧ (pending k (by omega) w).2 = false then
        ∫⁻ z, ∫⁻ v, F (calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k (w, z), v)
          ∂extension k (by omega) (calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k (w, z))
          ∂innovationLaw (p := p) else 0 := by
  unfold calendarStoppedCallTest
  split
  next hs =>
    rw [calendarStopped_refill_integral rate rewards C_star C_h control0 b0 u0 t0 k hk w hs.1 hs.2 F hF]
    apply lintegral_congr
    intro a
    apply lintegral_congr
    intro v
    change (∫⁻ y, ∫⁻ c, ∫⁻ U, ∫⁻ x,
      F (calendarCallRefill rate rewards C_star C_h control0 b0 u0 t0 k hk w a (fixedVectorControl v c) x, v)
      ∂invocationRefreshFibre rate rewards C_star C_h control0 q (sourceAt w v hs.1 (fixedVectorControl v c)) U
      ∂invocationRefreshLaw rate rewards C_star C_h control0 q (sourceAt w v hs.1 (fixedVectorControl v c))
      ∂invocationControlFibre rate rewards C_star C_h control0 q (invoke w v hs.1) y
      ∂invocationControlLaw rate rewards C_star C_h control0 q (invoke w v hs.1)) = _
    rw [← invocationControl_test rate rewards C_star C_h control0 q (invoke w v hs.1)]
    apply lintegral_congr
    intro c
    exact (invocationRefresh_test rate rewards C_star C_h control0 q (sourceAt w v hs.1 (fixedVectorControl v c)) _).symm
  next _ => rfl

private theorem calendarStopped_fillInnovation (w : Sample k) (z : Innovation p) :
    (callFlag k (by omega) (calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k (w, z)) = true ∧
      (pending k (by omega) (calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k (w, z))).2 = false) ↔
    (callFlag k (by omega) w = true ∧ (pending k (by omega) w).2 = false) := by
  change (callFlag k (by omega) (putControl (fillPair q k (w, z.2), z.1)) = true ∧
    (pending k (by omega) (putControl (fillPair q k (w, z.2), z.1))).2 = false) ↔ _
  rw [calendarCallFlag_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k hk le_rfl,
    calendarPendingClear_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k hk le_rfl,
    calendarFillPair_eq_withAuxiliary, calendarCallFlag_withAuxiliary, calendarPendingFlags_withAuxiliary]

private theorem measurableSet_stoppedCall : MeasurableSet {w : Sample k |
    callFlag k (by omega) w = true ∧ (pending k (by omega) w).2 = false} :=
  (measurableSet_eq_fun (measurable_calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k (by omega))
    measurable_const).inter
    (measurableSet_eq_fun (measurable_calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0 k (by omega)).snd
      measurable_const)

theorem calendarLaw_stopped_call_round_test (F : Sample k × Vector → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ wv : Sample k × Vector,
      if callFlag k (by omega) wv.1 = true ∧ (pending k (by omega) wv.1).2 = false then F wv else 0
      ∂law (k + 1) (by omega)) =
    ∫⁻ w, calendarStoppedCallTest rate rewards C_star C_h control0 b0 u0 t0 k hk F w
      ∂(law k hk.le).map (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k) := by
  let test : Sample k × Vector → ℝ≥0∞ := fun wv =>
    if callFlag k (by omega) wv.1 = true ∧ (pending k (by omega) wv.1).2 = false then F wv else 0
  have ht : Measurable test := hF.ite
    ((measurableSet_stoppedCall rate rewards C_star C_h control0 b0 u0 t0 k hk).preimage measurable_fst) measurable_const
  refine (calendarLaw_round_innovation_test rate rewards C_star C_h control0 b0 u0 t0 q htq k hk le_rfl test ht).trans ?_
  apply lintegral_congr
  intro w
  rw [calendarStoppedCallTest_eq_refill rate rewards C_star C_h control0 b0 u0 t0 k hk F hF w]
  by_cases hs : callFlag k (by omega) w = true ∧ (pending k (by omega) w).2 = false
  · rw [ite_eq_left hs]
    apply lintegral_congr
    intro z
    apply lintegral_congr
    intro v
    exact ite_eq_left ((calendarStopped_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 k hk w z).mpr hs)
  · rw [ite_eq_right hs]
    have he (z : Innovation p) (v : Vector) :
        test (calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k (w, z), v) = 0 :=
      ite_eq_right (fun h => hs ((calendarStopped_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 k hk w z).mp h))
    simp_rw [he, lintegral_zero]

/-- Actual noncall numerical coordinates, full update and effective output.
The optional tag distinguishes genuine absence from a present bottom record. -/
abbrev NoncallRoundData := Past × (Option (ReferenceFirstLiveOverflowReadout.NumericalCellReadout p) ×
  (Option (NumericalUpdate p) × ReferencePostInvocationCollectionNativeLaw.Outcome p))

def calendarNoncallRoundReadout (w : Sample k) : NoncallRoundData rate :=
  (past k hk.le w, (calendarNoncallNumerical rate rewards C_star C_h control0 b0 u0 t0 k hk w,
    (calendarNoncallUpdate rate rewards C_star C_h control0 b0 u0 t0 k hk w,
      calendarNoncallOutcome rate rewards C_star C_h control0 b0 u0 t0 k hk w)))

theorem measurable_calendarNoncallRoundReadout :
    Measurable (calendarNoncallRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk) :=
  (measurable_calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk.le).prodMk
    ((measurable_calendarNoncallNumerical rate rewards C_star C_h control0 b0 u0 t0 k hk).prodMk
      ((measurable_calendarNoncallUpdate rate rewards C_star C_h control0 b0 u0 t0 k hk).prodMk
        (measurable_calendarNoncallOutcome rate rewards C_star C_h control0 b0 u0 t0 k hk)))

abbrev LaterRoundData := CallRoundData rate rewards C_star C_h b0 u0 t0 k hk ⊕ NoncallRoundData rate

def calendarRoundReadout (wv : Sample k × Vector) : LaterRoundData rate rewards C_star C_h b0 u0 t0 k hk :=
  if callFlag k (by omega) wv.1 then
    .inl (calendarCallRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk wv)
  else .inr (calendarNoncallRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1)

theorem measurable_calendarRoundReadout :
    Measurable (calendarRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk) :=
  (measurable_inl.comp (measurable_calendarCallRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk)).ite
    ((measurableSet_eq_fun (measurable_calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k (by omega))
      measurable_const).preimage measurable_fst)
    ((measurable_inr.comp (measurable_calendarNoncallRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk)).comp
      measurable_fst)

/-- Complete evaluated local CALL/noncall numerical law. Both CALL PRE cases
are evaluated on the same source; the accepted noncall coefficient retains
nominal numerical data beside stopped effective data. No episode law follows
by conditioning on the future fixed first-branch event. -/
theorem calendarLaw_later_round_test
    (Phi : LaterRoundData rate rewards C_star C_h b0 u0 t0 k hk → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ wv, Phi (calendarRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk wv)
      ∂law (k + 1) (by omega)) =
    (∫⁻ w, calendarCallTest rate rewards C_star C_h control0 b0 u0 t0 k hk
      (fun wv => Phi (.inl (calendarCallRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk wv))) w
      ∂(law k hk.le).map (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k)) +
    (∫⁻ w, calendarStoppedCallTest rate rewards C_star C_h control0 b0 u0 t0 k hk
      (fun wv => Phi (.inl (calendarCallRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk wv))) w
      ∂(law k hk.le).map (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k)) +
    ∫⁻ w, if callFlag k (by omega) w = false then
      ∑ i, ∑ o, Phi (.inr (past k hk.le w,
        (calendarNoncallNumericalForRaw rate rewards C_star C_h control0 b0 u0 t0 k hk w i o,
          (calendarNoncallUpdateForOutcome rate rewards C_star C_h control0 b0 u0 t0 k hk w o, o)))) *
        calendarNoncallRawMass rate rewards C_star C_h control0 b0 u0 t0 k hk w i o else 0
      ∂(law k hk.le).map (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k) := by
  let FC : Sample k × Vector → ℝ≥0∞ := fun wv =>
    Phi (.inl (calendarCallRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk wv))
  let FN : NoncallRoundData rate → ℝ≥0∞ := fun z => Phi (.inr z)
  have hFC : Measurable FC := hPhi.comp (measurable_inl.comp
    (measurable_calendarCallRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk))
  have hFN : Measurable FN := hPhi.comp measurable_inr
  let A : Sample k × Vector → ℝ≥0∞ := fun wv =>
    if wv.1 ∈ calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk then FC wv else 0
  let S : Sample k × Vector → ℝ≥0∞ := fun wv =>
    if callFlag k (by omega) wv.1 = true ∧ (pending k (by omega) wv.1).2 = false then FC wv else 0
  let N : Sample k × Vector → ℝ≥0∞ := fun wv =>
    if callFlag k (by omega) wv.1 = false then
      FN (calendarNoncallRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1) else 0
  have hA : Measurable A := hFC.ite
    ((measurableSet_calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk).preimage measurable_fst) measurable_const
  have hS : Measurable S := hFC.ite
    ((measurableSet_stoppedCall rate rewards C_star C_h control0 b0 u0 t0 k hk).preimage measurable_fst) measurable_const
  have he : (fun wv => Phi (calendarRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk wv)) =
      fun wv => (A wv + S wv) + N wv := by
    funext wv
    cases hc : callFlag k (by omega) wv.1 <;> cases hp : (pending k (by omega) wv.1).2 <;>
      simp only [calendarRoundReadout, A, S, N, FC, FN, calendarActiveEvent, Set.mem_ofPred_eq, hc, hp,
        Bool.false_eq_true, Bool.true_eq_false, and_true, and_false,
        ite_true, ite_false, add_zero, zero_add]
  let mu : Measure (Sample k × Vector) := (law k hk.le).compProd (extension k (by omega))
  have hi := congrArg (fun f : Sample k × Vector → ℝ≥0∞ => ∫⁻ wv, f wv ∂mu) he
  have hadd := (lintegral_add_left (μ := mu) (hA.add hS) N).trans
    (congrArg (fun z => z + ∫⁻ wv, N wv ∂mu) (lintegral_add_left (μ := mu) hA S))
  refine hi.trans (hadd.trans ?_)
  exact congrArg₂ (fun x y : ℝ≥0∞ => x + y)
    (congrArg₂ (fun x y : ℝ≥0∞ => x + y)
      (calendarLaw_call_round_test rate rewards C_star C_h control0 b0 u0 t0 k hk FC hFC)
      (calendarLaw_stopped_call_round_test rate rewards C_star C_h control0 b0 u0 t0 k hk FC hFC))
    (calendarLaw_noncall_numerical_test rate rewards C_star C_h control0 b0 u0 t0 k hk FN hFN)

/-- Positive physical fibres recover the actual correlated pair/UPDATE and
proposal; no positivity assumption is needed in the integrated round law. -/
theorem calendarCallControlFibre_support (w : Sample k) (v : Vector)
    (hc : callFlag k (by omega) w = true) (y : PairUpdate × Bool)
    (hy : calendarCallControlLaw rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc {y} ≠ 0) :
    ∀ᵐ c ∂calendarCallControlFibre rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc y,
      calendarCallControlDraw rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc c = y := by
  have hm := measurable_invocationControlDraw rate rewards C_star C_h control0 q (invoke w v hc)
  change invocationControlLaw rate rewards C_star C_h control0 q (invoke w v hc) {y} ≠ 0 at hy
  rw [← invocationControlDraw_law rate rewards C_star C_h control0 q (invoke w v hc),
    Measure.map_apply hm (measurableSet_singleton y)] at hy
  exact FiniteFibreLift.ae_fibreMeasure_eq _ _ _ hm hy

/-- Positive selected-refresh fibres recover the next set of the actual
refilled native cell on the SAME physical numerical POST and fixed anchor. -/
theorem calendarCallRefreshFibre_support (w : Sample k) (v : Vector)
    (hc : callFlag k (by omega) w = true) (a : Scalar × Scalar) (c : Control) (U : SlowSet p)
    (hU : calendarCallRefreshLaw rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc c {U} ≠ 0) :
    ∀ᵐ x ∂calendarCallRefreshFibre rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc c U,
      (calendarInvocationCell rate rewards C_star C_h control0 b0 u0 t0 k hk
        (calendarCallRefill rate rewards C_star C_h control0 b0 u0 t0 k hk w a c x) v
        (calendarCallRefill_call rate rewards C_star C_h control0 b0 u0 t0 k hk w hc a c x)).nextSlowSet = U := by
  let : MeasurableSpace (SlowSet p) := Subtype.instMeasurableSpace
  have hm := measurable_invocationRefreshDraw rate rewards C_star C_h control0 q (sourceAt w v hc c)
  change invocationRefreshLaw rate rewards C_star C_h control0 q (sourceAt w v hc c) {U} ≠ 0 at hU
  rw [← invocationRefreshDraw_law rate rewards C_star C_h control0 q (sourceAt w v hc c),
    Measure.map_apply hm (@measurableSet_singleton (SlowSet p) Subtype.instMeasurableSpace inferInstance U)] at hU
  have h := FiniteFibreLift.ae_fibreMeasure_eq _ _ _ hm hU
  filter_upwards [h] with x hx
  rw [calendarCallRefill_cell]
  exact hx

/-- Both append branches use the actual successor archive. The numerical
identity includes the terminal boundary q+1=T and never requests a control
at that boundary. Genuine optional absence appends nothing. -/
theorem calendarRound_successor (w : Sample k) (v : Vector) :
    calendarStoredState rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega) (w, v) =
      (if hc : callFlag k (by omega) w = true then
        let c := calendarInvocationCell rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
        (c.nextSlowSet, (calendarStoredState rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).2 ++ [c])
      else match calendarNoncallCell rate rewards C_star C_h control0 b0 u0 t0 k hk w with
      | none => calendarStoredState rate rewards C_star C_h control0 b0 u0 t0 k hk.le w
      | some e => (e.nextSlowSet, (calendarStoredState rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).2 ++ [e])) ∧
    (calendarObservation rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega) (w, v)).2.val.2.2.1 =
      prefixNumerical rate rewards C_star C_h (q).succ (current (k + 1) (by omega) (w, v)) := by
  constructor
  · by_cases hc : callFlag k (by omega) w = true
    · rw [dite_eq_left hc]
      exact (calendarObservation_call_append rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc).1
    · rw [dite_eq_right hc]
      exact calendarNoncall_successor rate rewards C_star C_h control0 b0 u0 t0 k hk w v (Bool.eq_false_iff.mpr hc)
  · exact calendarObservation_numerical rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega) (w, v)

/-- R/C/N interface on the existing generated calendar. The root keeps its
accepted initializer, and later CALL/noncall tests use their evaluated actual
laws. All first-branch masses remain unnormalized. This is a local interface
for chronological episode-before-draw/estimate-history consumers, not an
episode law or auxiliary expectation. -/
theorem calendarLaw_RCN_round_test (FR : Sample 0 → ℝ≥0∞) (hFR : Measurable FR)
    (PhiL : LaterRoundData rate rewards C_star C_h b0 u0 t0 k hk → ℝ≥0∞) (hPhiL : Measurable PhiL) :
    ((∫⁻ w, FR w ∂law 0 (by omega)) =
      ∑ rowIdx : Fin (M p), ∫⁻ r : EventRemainder control0 t0 (branchEvent rate rewards C_star C_h b0 u0 t0) rowIdx,
        ∫⁻ e : ErasedAuxiliaryArray t0, ∫⁻ v : Vector,
          let z0 := rootInstalledSource rate rewards C_star C_h b0 u0 t0
            (restoreEventSource control0 t0 (branchEvent rate rewards C_star C_h b0 u0 t0)
              (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) rowIdx (r, control0)) v
          ∫⁻ y, ∫⁻ c,
            let z := rootInstalledSource rate rewards C_star C_h b0 u0 t0
              (restoreEventSource control0 t0 (branchEvent rate rewards C_star C_h b0 u0 t0)
                (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) rowIdx (r, c)) v
            ∫⁻ U, ∫⁻ x, FR (rootRestore rate rewards C_star C_h control0 b0 u0 t0 rowIdx r e v c x)
              ∂rootRefreshFibre rate rewards C_star C_h control0 t0 z U
              ∂firstResidualLaw rate rewards C_star C_h control0 t0 z
              ∂rootControlFibre rate rewards C_star C_h control0 t0 z0 y
              ∂rootControlLaw rate rewards C_star C_h control0 t0 z0
            ∂rootVectorKernel rate rewards C_star C_h control0 b0 u0 t0
              (restoreEventSource control0 t0 (branchEvent rate rewards C_star C_h b0 u0 t0)
                (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) rowIdx (r, control0),
                (rootUpdateSplit b0 t0).symm (e, scalarZero))
            ∂erasedAuxiliaryLaw t0 ∂eventRemainderLaw control0 t0 (branchEvent rate rewards C_star C_h b0 u0 t0) rowIdx) ∧
    ((∫⁻ wv, PhiL (calendarRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk wv)
      ∂law (k + 1) (by omega)) =
    (∫⁻ w, calendarCallTest rate rewards C_star C_h control0 b0 u0 t0 k hk
      (fun wv => PhiL (.inl (calendarCallRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk wv))) w
      ∂(law k hk.le).map (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k)) +
    (∫⁻ w, calendarStoppedCallTest rate rewards C_star C_h control0 b0 u0 t0 k hk
      (fun wv => PhiL (.inl (calendarCallRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk wv))) w
      ∂(law k hk.le).map (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k)) +
    ∫⁻ w, if callFlag k (by omega) w = false then
      ∑ i, ∑ o, PhiL (.inr (past k hk.le w,
        (calendarNoncallNumericalForRaw rate rewards C_star C_h control0 b0 u0 t0 k hk w i o,
          (calendarNoncallUpdateForOutcome rate rewards C_star C_h control0 b0 u0 t0 k hk w o, o)))) *
        calendarNoncallRawMass rate rewards C_star C_h control0 b0 u0 t0 k hk w i o else 0
      ∂(law k hk.le).map (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k)) :=
  ⟨calendarLaw_root_raw_test rate rewards C_star C_h control0 b0 u0 t0 FR hFR,
    calendarLaw_later_round_test rate rewards C_star C_h control0 b0 u0 t0 k hk PhiL hPhiL⟩

/-- The stopped CALL test family is Borel, proved from its actual refill. -/
theorem measurable_calendarStoppedCallTest (F : Sample k × Vector → ℝ≥0∞) (hF : Measurable F) :
    Measurable (calendarStoppedCallTest rate rewards C_star C_h control0 b0 u0 t0 k hk F) := by
  let fill := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k
  have hfill := measurable_calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k
  let K := (extension k (by omega)).comap fill hfill
  let g : (Sample k × Innovation p) × Vector → ℝ≥0∞ := fun z => F (fill z.1, z.2)
  have hg : Measurable g := hF.comp ((hfill.comp measurable_fst).prodMk measurable_snd)
  have hinner : Measurable (fun wx : Sample k × Innovation p => ∫⁻ v, g (wx, v) ∂K wx) :=
    hg.lintegral_kernel_prod_right'
  have htotal : Measurable (fun w : Sample k =>
      if callFlag k (by omega) w = true ∧ (pending k (by omega) w).2 = false then
        ∫⁻ z, ∫⁻ v, g ((w, z), v) ∂K (w, z) ∂innovationLaw (p := p) else 0) :=
    hinner.lintegral_prod_right'.ite
      (measurableSet_stoppedCall rate rewards C_star C_h control0 b0 u0 t0 k hk) measurable_const
  rw [funext (calendarStoppedCallTest_eq_refill rate rewards C_star C_h control0 b0 u0 t0 k hk F hF)]
  exact htotal

/-- The joint physical observer in the evaluated test is the actual
observer of the refilled generated calendar, including its nominal POST. -/
theorem calendarCallRefill_control_readout (w : Sample k) (v : Vector)
    (hc : callFlag k (by omega) w = true) (a : Scalar × Scalar) (c : Control) (x : Scalar) :
    (calendarCallRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk
      (calendarCallRefill rate rewards C_star C_h control0 b0 u0 t0 k hk w a c x, v)).2.1 =
      calendarCallControlDraw rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc c := by
  let w0 := putControl (fillPair q k (w, a), c)
  have hs : current k hk.le (withUpdate (w0, x)) = current k hk.le w0 :=
    congrArg (fun o : TaggedPrefix rate (calendarBoundary t0 k hk.le) => o.2.val.1.1.1.2)
      (calendarObservation_withUpdateScalar rate rewards C_star C_h control0 b0 u0 t0 k hk w0 x)
  have hn : current (k + 1) (by omega)
      (calendarCallRefill rate rewards C_star C_h control0 b0 u0 t0 k hk w a c x, v) = (sourceAt w v hc c).val := by
    rw [calendarCurrentSource_succ rate rewards C_star C_h control0 b0 u0 t0 k hk, ite_eq_left
      (calendarCallRefill_call rate rewards C_star C_h control0 b0 u0 t0 k hk w hc a c x)]
    change ReferenceFirstCollectionRenewalVectorInsertion.insert q (current k hk.le (withUpdate (w0, x))) v = _
    rw [hs, calendarCallSourceAt_val]
    exact congrArg (fun z => ReferenceFirstCollectionRenewalVectorInsertion.insert q z v)
      (calendarCurrentSource_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 k hk w (c, a))
  change ((ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast rate rewards C_star C_h q _,
    ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate rate rewards C_star C_h control0 q _),
    physicalProposalBit rate (ReferenceSourceCurrentControlFreshness.u_t p q _)) = _
  rw [hn]
  exact (calendarCallControlDraw_readout rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc c).symm

theorem calendarCallControlDraw_fixedVectorControl (w : Sample k) (v : Vector)
    (hc : callFlag k (by omega) w = true) (c : Control) :
    calendarCallControlDraw rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc (fixedVectorControl v c) =
      calendarCallControlDraw rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc c := by
  unfold calendarCallControlDraw
  rw [physicalProposalBit_fixedVectorControl]
  rw [fixedVectorControl, MeasurableEquiv.apply_symm_apply]

end GeneratedCall

end Bandits.Support.ReferenceGeneratedCalendarRoundLaw

end
