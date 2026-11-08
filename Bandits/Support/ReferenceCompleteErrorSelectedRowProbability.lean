/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteInclusivePhysicalDecoderErrors
public import Bandits.Support.ReferenceOriginalCalendarNumericalOverflowBound
public import Bandits.Support.ReferenceCompleteSelectedRowExpectation

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Original-index private probability of the complete reference error event

The source event is the literal union of initialization failure, the two
stopped decoder failures, and the complete physical first-overflow event.
Its selected-row sections retain the original private tuple and coordinator
index while integrating over every other complete continuous row.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceCompleteSelectedRowExpectation
open scoped ENNReal

namespace Bandits.Support.ReferenceCompleteErrorSelectedRowProbability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p

variable {p : Parameters}

/-- The actual original-source initialization flag, with its source-selected
whole row and unmodified private coordinates. -/
def sourceInitializationFailureEvent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : Set (SourceInput p) :=
  {z | z.2 ∈ InitializationRowObservables.actualInitializationFailureEvent p
    z.1.1 rewards C_star C_h rate.eta z.1.2}

/-- The manuscript's complete source error event, as one union indicator.
The four constituent events are evaluated on the same actual complete source. -/
def completeErrorEvent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : Set (SourceInput p) :=
  sourceInitializationFailureEvent rate rewards C_star C_h ∪
    ReferenceCompleteInclusivePhysicalDecoderErrors.stoppedOrdinaryWrongCompletionEvent
      rate rewards C_star C_h ∪
    ReferenceCompleteInclusivePhysicalDecoderErrors.stoppedFixedAwaitedAmbiguityEvent
      rate rewards C_star C_h ∪
    ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
      rate rewards C_star C_h

/-- The real indicator of the literal complete-error union. -/
def completeErrorIndicator
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : SourceInput p → ℝ :=
  (completeErrorEvent rate rewards C_star C_h).indicator (fun _ => (1 : ℝ))

/-- The original-index private probability after pinning the entire selected
row and integrating all nuisance rows under their original continuous law. -/
def completeErrorFixedRowProbability
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (M p)) (rho : CompleteRow p) : ℝ :=
  ∫ rows : CompleteRows p, ∫ e : ExtendedPrivateCoordinates p,
    completeErrorIndicator rate rewards C_star C_h
      ((ids, Function.update rows j rho), e)
    ∂selectedIndexPrivateLaw p j ∂completeRowsMeasure p

/-- The original-ID-conditioned row mean of the complete-error probability. -/
def completeErrorMean
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) : ℝ :=
  (1 / (M p : ℝ)) * ∑ j : Fin (M p),
    ∫ rho : CompleteRow p,
      completeErrorFixedRowProbability rate rewards C_star C_h ids j rho
      ∂completeRowMeasure p

/-- The initialization adapter is precisely the generated history's
forced-correction or suppressed-ordinary-DOWN provenance event. -/
theorem sourceInitializationFailureEvent_iff_operational
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : SourceInput p) :
    z ∈ sourceInitializationFailureEvent rate rewards C_star C_h ↔
      InitializationFailureProvenance.operationalInitializationFailure
        (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h) := by
  let row := z.1.2 (PrivateSourceStreams.coordinatorIndex p z.2.1.2)
  let x := ReferenceInitializationIndexMixture.fixedRowInput p z.1.1 rewards C_star C_h
    rate.eta row z.2
  have hx : ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h = x := by
    rfl
  have hb : ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h =
      ReferenceInitializationRun.output x := by
    simp only [ReferenceCompletePhysicalHistory.generatedBoundary, hx]
  have hflag := InitializationRowObservables.actualInitializationFailureEvent_iff_terminalFlag
    p z.1.1 rewards C_star C_h rate.eta z.1.2 z.2
  have hsource : z ∈ sourceInitializationFailureEvent rate rewards C_star C_h ↔
      ∃ i : ActiveRoundActions.Follower p.m,
        ReferenceInitializationRun.initializationFailure x
          (ReferenceInitializationRun.output x) i = true := by
    change z.2 ∈ InitializationRowObservables.actualInitializationFailureEvent
      p z.1.1 rewards C_star C_h rate.eta z.1.2 ↔ _
    exact hflag
  have hterminal := InitializationFailureProvenance.initializationFailure_iff_operational
    (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h)
  have hhistory := ReferenceCompletePhysicalHistory.generated_failure_provenance
    rate z rewards C_star C_h
  have hbridge :
      (∃ i : ActiveRoundActions.Follower p.m,
        ReferenceInitializationRun.initializationFailure
          (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h)
          (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h) i = true) ↔
        (∃ i : ActiveRoundActions.Follower p.m,
          ReferenceInitializationRun.initializationFailure
            (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h)
            (ReferenceInitializationRun.output
              (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h)) i = true) :=
    hhistory.trans hterminal.symm
  have hsourceGenerated : z ∈ sourceInitializationFailureEvent rate rewards C_star C_h ↔
      ∃ i : ActiveRoundActions.Follower p.m,
        ReferenceInitializationRun.initializationFailure
          (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h)
          (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h) i = true := by
    simpa only [x, hx, hb] using hsource
  exact (hsourceGenerated.trans hbridge).trans hterminal

/-- Borelness of the source initialization adapter, with public IDs varying
over their finite source carrier. -/
theorem measurableSet_sourceInitializationFailureEvent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    MeasurableSet (sourceInitializationFailureEvent rate rewards C_star C_h) := by
  have hrepr : sourceInitializationFailureEvent rate rewards C_star C_h =
      ⋃ ids : IDArray p, {z : SourceInput p |
        z.1.1 = ids ∧ z.2 ∈ InitializationRowObservables.actualInitializationFailureEvent
          p ids rewards C_star C_h rate.eta z.1.2} := by
    ext z
    simp only [sourceInitializationFailureEvent, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hz
      exact ⟨z.1.1, rfl, hz⟩
    · rintro ⟨ids, rfl, hz⟩
      exact hz
  rw [hrepr]
  refine MeasurableSet.iUnion fun ids => ?_
  have hfixed := InitializationRowObservables.measurable_actualInitializationFailureEvent_pair
    p ids rewards C_star C_h rate.eta
  have hsource : Measurable (fun z : SourceInput p => (z.1.2, z.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hid : MeasurableSet {z : SourceInput p | z.1.1 = ids} :=
    (measurableSet_singleton ids).preimage (measurable_fst.comp measurable_fst)
  exact hid.inter (hfixed.preimage hsource)

/-- The literal complete union is Borel on the whole original source space. -/
theorem measurableSet_completeErrorEvent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : MeasurableSet (completeErrorEvent rate rewards C_star C_h) := by
  unfold completeErrorEvent
  exact (((measurableSet_sourceInitializationFailureEvent rate rewards C_star C_h).union
    (ReferenceCompleteInclusivePhysicalDecoderErrors.measurableSet_stoppedOrdinaryWrongCompletionEvent
      rate rewards C_star C_h)).union
    (ReferenceCompleteInclusivePhysicalDecoderErrors.measurableSet_stoppedFixedAwaitedAmbiguityEvent
      rate rewards C_star C_h)).union
    (ReferenceOriginalCalendarNumericalOverflowBound.measurableSet_physicalFirstOverflowEvent
      rate rewards C_star C_h)

/-- The actual complete-suffix overflow event is local to the selected whole
row, including optional-readout absence. -/
theorem physicalFirstOverflowEvent_iff_of_source_data
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z z' : SourceInput p) (j : Fin (M p))
    (hids : z.1.1 = z'.1.1) (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j)
    (hrow : z.1.2 j = z'.1.2 j) :
    z ∈ ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
        rate rewards C_star C_h ↔
      z' ∈ ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
        rate rewards C_star C_h := by
  rw [ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent_eq_observedNumericalOverflowEvent
    rate rewards C_star C_h]
  change (∃ n : ℕ, n ≤ p.T ∧ ∃ o,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h n z = some o ∧
      ∃ a : Fin p.K,
        ((o.1 a).2 : ℝ) /
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).n >
            1 / (32 * rate.eta.val)) ↔ _
  constructor
  · rintro ⟨n, hn, o, ho, a, ha⟩
    have hread := ReferenceCompletePrefixReadoutRowLocality.prefixReadout_eq_of_source_data
      rate rewards C_star C_h n z z' j hids hprivate hJ hrow
    exact ⟨n, hn, o, by rw [← hread]; exact ho, a, ha⟩
  · rintro ⟨n, hn, o, ho, a, ha⟩
    have hJ' : ActualInitializationPhysicalStep.selectedRowIndex p z' = j := by
      have hscalar : z.2.1.2 = z'.2.1.2 := congrArg
        (fun e : ExtendedPrivateCoordinates p => e.1.2) hprivate
      change PrivateSourceStreams.coordinatorIndex p z'.2.1.2 = j
      rw [← hscalar]
      exact hJ
    have hread := ReferenceCompletePrefixReadoutRowLocality.prefixReadout_eq_of_source_data
      rate rewards C_star C_h n z' z j hids.symm hprivate.symm hJ' hrow.symm
    exact ⟨n, hn, o, by rw [← hread]; exact ho, a, ha⟩

/-- Exact source-data equivalence for all four complete-error branches. -/
theorem completeErrorEvent_iff_of_source_data
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z z' : SourceInput p) (j : Fin (M p))
    (hids : z.1.1 = z'.1.1) (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j)
    (hrow : z.1.2 j = z'.1.2 j) :
    z ∈ completeErrorEvent rate rewards C_star C_h ↔
      z' ∈ completeErrorEvent rate rewards C_star C_h := by
  have hgenerated := ReferenceCompletePhysicalHistory.generatedInput_and_launch_eq_of_source_data
    rate z z' rewards C_star C_h j hids hprivate hJ hrow
  have hinit : z ∈ sourceInitializationFailureEvent rate rewards C_star C_h ↔
      z' ∈ sourceInitializationFailureEvent rate rewards C_star C_h := by
    rw [sourceInitializationFailureEvent_iff_operational rate rewards C_star C_h z,
      sourceInitializationFailureEvent_iff_operational rate rewards C_star C_h z',
      hgenerated.1]
  have hfalse :=
    ReferenceCompleteInclusivePhysicalDecoderErrors.stoppedOrdinaryWrongCompletionEvent_iff_of_source_data
      rate rewards C_star C_h z z' j hids hprivate hJ hrow
  have hamb :=
    ReferenceCompleteInclusivePhysicalDecoderErrors.stoppedFixedAwaitedAmbiguityEvent_iff_of_source_data
      rate rewards C_star C_h z z' j hids hprivate hJ hrow
  have hqueue := physicalFirstOverflowEvent_iff_of_source_data
    rate rewards C_star C_h z z' j hids hprivate hJ hrow
  simpa only [completeErrorEvent, Set.mem_union] using
    (or_congr (or_congr (or_congr hinit hfalse) hamb) hqueue)

/-- Updating only nonselected complete rows leaves the complete-error event
unchanged when the original private tuple has coordinator index `j`. -/
theorem selectedRow_update_completeErrorEvent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (rows otherRows : CompleteRows p)
    (j : Fin (M p)) (rho : CompleteRow p) (e : ExtendedPrivateCoordinates p)
    (hJ : PrivateSourceStreams.coordinatorIndex p e.1.2 = j) :
    ((ids, Function.update rows j rho), e) ∈ completeErrorEvent rate rewards C_star C_h ↔
      ((ids, Function.update otherRows j rho), e) ∈ completeErrorEvent rate rewards C_star C_h := by
  apply completeErrorEvent_iff_of_source_data rate rewards C_star C_h
    ((ids, Function.update rows j rho), e)
    ((ids, Function.update otherRows j rho), e) j rfl rfl
  · change PrivateSourceStreams.coordinatorIndex p e.1.2 = j
    exact hJ
  · simp

/-- The measurable literal union has a measurable real indicator. -/
theorem measurable_completeErrorIndicator
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : Measurable (completeErrorIndicator rate rewards C_star C_h) :=
  measurable_const.indicator (measurableSet_completeErrorEvent rate rewards C_star C_h)

/-- The source-event indicator is everywhere a real zero-one value. -/
theorem completeErrorIndicator_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : SourceInput p) :
    completeErrorIndicator rate rewards C_star C_h z ∈ Set.Icc 0 1 := by
  by_cases hz : z ∈ completeErrorEvent rate rewards C_star C_h
  · simp [completeErrorIndicator, hz]
  · simp [completeErrorIndicator, hz]

private theorem measurable_completeErrorIndicator_privateSection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (rows : CompleteRows p) :
    Measurable (fun e : ExtendedPrivateCoordinates p =>
      completeErrorIndicator rate rewards C_star C_h ((ids, rows), e)) := by
  exact (measurable_completeErrorIndicator rate rewards C_star C_h).comp
    (measurable_const.prodMk measurable_id)

private theorem integrable_completeErrorIndicator_privateSection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (rows : CompleteRows p)
    (μ : Measure (ExtendedPrivateCoordinates p)) [IsProbabilityMeasure μ] :
    Integrable (fun e : ExtendedPrivateCoordinates p =>
      completeErrorIndicator rate rewards C_star C_h ((ids, rows), e)) μ := by
  apply Integrable.of_mem_Icc 0 1
    (measurable_completeErrorIndicator_privateSection rate rewards C_star C_h ids rows).aemeasurable
  exact ae_of_all _ fun e => completeErrorIndicator_bounds
    rate rewards C_star C_h ((ids, rows), e)

private theorem measurable_updatedCompleteErrorIndicator_joint
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) :
    Measurable (fun z : ((IDArray p × CompleteRow p) × CompleteRows p) ×
        ExtendedPrivateCoordinates p =>
      completeErrorIndicator rate rewards C_star C_h
        ((z.1.1.1, Function.update z.1.2 j z.1.1.2), z.2)) := by
  have hupdate : Measurable (fun z : ((IDArray p × CompleteRow p) × CompleteRows p) ×
      ExtendedPrivateCoordinates p => Function.update z.1.2 j z.1.1.2) :=
    measurable_update'.comp ((measurable_snd.comp measurable_fst).prodMk
      (measurable_snd.comp (measurable_fst.comp measurable_fst)))
  have hsource : Measurable (fun z : ((IDArray p × CompleteRow p) × CompleteRows p) ×
      ExtendedPrivateCoordinates p =>
      ((z.1.1.1, Function.update z.1.2 j z.1.1.2), z.2)) :=
    (((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk hupdate).prodMk
      measurable_snd)
  exact (measurable_completeErrorIndicator rate rewards C_star C_h).comp hsource

/-- The fixed-row probability is jointly Borel in IDs and its pinned whole
continuous row. -/
theorem measurable_completeErrorFixedRowProbability
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) :
    Measurable (fun z : IDArray p × CompleteRow p =>
      completeErrorFixedRowProbability rate rewards C_star C_h z.1 j z.2) := by
  have hf := (measurable_updatedCompleteErrorIndicator_joint
    rate rewards C_star C_h j).stronglyMeasurable
  have he := hf.integral_prod_right' (ν := selectedIndexPrivateLaw p j)
  exact (he.integral_prod_right' (ν := completeRowsMeasure p)).measurable

private theorem measurable_completeErrorIndicator_nuisanceSection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (M p)) (rho : CompleteRow p) :
    Measurable (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      completeErrorIndicator rate rewards C_star C_h
        ((ids, Function.update z.1 j rho), z.2)) := by
  have hrows : Measurable (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      Function.update z.1 j rho) := measurable_update_left.comp measurable_fst
  exact (measurable_completeErrorIndicator rate rewards C_star C_h).comp
    ((measurable_const.prodMk hrows).prodMk measurable_snd)

private theorem completeErrorInnerProbability_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (M p)) (rho : CompleteRow p)
    (rows : CompleteRows p) :
    (∫ e : ExtendedPrivateCoordinates p,
      completeErrorIndicator rate rewards C_star C_h
        ((ids, Function.update rows j rho), e) ∂selectedIndexPrivateLaw p j) ∈ Set.Icc 0 1 := by
  have hf : Integrable (fun e : ExtendedPrivateCoordinates p =>
      completeErrorIndicator rate rewards C_star C_h
        ((ids, Function.update rows j rho), e)) (selectedIndexPrivateLaw p j) := by
    apply Integrable.of_mem_Icc 0 1
      ((measurable_completeErrorIndicator rate rewards C_star C_h).comp
        (measurable_const.prodMk measurable_id)).aemeasurable
    exact ae_of_all _ fun e => completeErrorIndicator_bounds
      rate rewards C_star C_h ((ids, Function.update rows j rho), e)
  constructor
  · exact integral_nonneg fun e =>
      (completeErrorIndicator_bounds rate rewards C_star C_h
        ((ids, Function.update rows j rho), e)).1
  · have hupper := integral_mono hf (integrable_const (1 : ℝ)) fun e =>
      (completeErrorIndicator_bounds rate rewards C_star C_h
        ((ids, Function.update rows j rho), e)).2
    simpa only [integral_const, probReal_univ, one_smul] using hupper

private theorem measurable_completeErrorInnerProbability_nuisanceSection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (M p)) (rho : CompleteRow p) :
    Measurable (fun rows : CompleteRows p =>
      ∫ e : ExtendedPrivateCoordinates p,
        completeErrorIndicator rate rewards C_star C_h
          ((ids, Function.update rows j rho), e) ∂selectedIndexPrivateLaw p j) := by
  have hf := (measurable_completeErrorIndicator_nuisanceSection
    rate rewards C_star C_h ids j rho).stronglyMeasurable
  exact hf.integral_prod_right' (ν := selectedIndexPrivateLaw p j) |>.measurable

/-- Every literal selected-row section is a genuine probability in `[0,1]`. -/
theorem completeErrorFixedRowProbability_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (M p)) (rho : CompleteRow p) :
    completeErrorFixedRowProbability rate rewards C_star C_h ids j rho ∈ Set.Icc 0 1 := by
  have hout : Integrable (fun rows : CompleteRows p =>
      ∫ e : ExtendedPrivateCoordinates p,
        completeErrorIndicator rate rewards C_star C_h
          ((ids, Function.update rows j rho), e) ∂selectedIndexPrivateLaw p j)
      (completeRowsMeasure p) := by
    apply Integrable.of_mem_Icc 0 1
      (measurable_completeErrorInnerProbability_nuisanceSection
        rate rewards C_star C_h ids j rho).aemeasurable
    exact ae_of_all _ fun rows => completeErrorInnerProbability_bounds
      rate rewards C_star C_h ids j rho rows
  constructor
  · exact integral_nonneg fun rows =>
      (completeErrorInnerProbability_bounds rate rewards C_star C_h ids j rho rows).1
  · have hupper := integral_mono hout (integrable_const (1 : ℝ)) fun rows =>
      (completeErrorInnerProbability_bounds rate rewards C_star C_h ids j rho rows).2
    simpa only [completeErrorFixedRowProbability, integral_const, probReal_univ,
      one_smul] using hupper

/-- Every fixed-ID/index complete-row section is Bochner integrable under the
original continuous whole-row law. -/
theorem integrable_completeErrorFixedRowProbability
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (M p)) :
    Integrable (completeErrorFixedRowProbability rate rewards C_star C_h ids j)
      (completeRowMeasure p) := by
  have hmeas : Measurable (completeErrorFixedRowProbability rate rewards C_star C_h ids j) := by
    exact (measurable_completeErrorFixedRowProbability rate rewards C_star C_h j).comp
      (measurable_const.prodMk measurable_id)
  apply Integrable.of_mem_Icc 0 1 hmeas.aemeasurable
  exact ae_of_all _ fun rho => completeErrorFixedRowProbability_bounds
    rate rewards C_star C_h ids j rho

/-- At each complete public output, the selected row cancels every nuisance
row in the section because the original private `J` cell selects that row. -/
theorem completeErrorFixedRowProbability_eq_fixedPublicIntegral
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (M p)) (rows : CompleteRows p) :
    completeErrorFixedRowProbability rate rewards C_star C_h ids j (rows j) =
      ∫ e : ExtendedPrivateCoordinates p,
        completeErrorIndicator rate rewards C_star C_h ((ids, rows), e)
        ∂selectedIndexPrivateLaw p j := by
  unfold completeErrorFixedRowProbability
  have heq (nuisance : CompleteRows p) :
      (∫ e : ExtendedPrivateCoordinates p,
        completeErrorIndicator rate rewards C_star C_h
          ((ids, Function.update nuisance j (rows j)), e) ∂selectedIndexPrivateLaw p j) =
      ∫ e : ExtendedPrivateCoordinates p,
        completeErrorIndicator rate rewards C_star C_h ((ids, rows), e)
        ∂selectedIndexPrivateLaw p j := by
    apply integral_congr_ae
    filter_upwards [ReferenceCompleteSelectedRowExpectation.ae_selectedIndexPrivateLaw_mem p j]
      with e he
    have hJ : ActualInitializationPhysicalStep.selectedRowIndex p
        ((ids, Function.update nuisance j (rows j)), e) = j := by
      change PrivateSourceStreams.coordinatorIndex p e.1.2 = j
      simpa [ReferenceCompleteSelectedRowExpectation.indexCell] using he
    have hiff := completeErrorEvent_iff_of_source_data rate rewards C_star C_h
      ((ids, Function.update nuisance j (rows j)), e) ((ids, rows), e) j rfl rfl hJ (by simp)
    by_cases h : ((ids, Function.update nuisance j (rows j)), e) ∈
        completeErrorEvent rate rewards C_star C_h
    · have h' : ((ids, rows), e) ∈ completeErrorEvent rate rewards C_star C_h := hiff.mp h
      simp only [completeErrorIndicator, Set.indicator_of_mem h, Set.indicator_of_mem h']
    · have h' : ((ids, rows), e) ∉ completeErrorEvent rate rewards C_star C_h :=
        fun h' => h (hiff.mpr h')
      simp only [completeErrorIndicator, Set.indicator_of_notMem h,
        Set.indicator_of_notMem h']
  simp_rw [heq]
  simp only [integral_const, probReal_univ, one_smul]

private theorem integrable_completeErrorFixedRowProbability_rowSection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (M p)) :
    Integrable (fun rows : CompleteRows p =>
      completeErrorFixedRowProbability rate rewards C_star C_h ids j (rows j))
      (completeRowsMeasure p) := by
  have hmeas := (measurable_completeErrorFixedRowProbability rate rewards C_star C_h j).comp
    (show Measurable (fun rows : CompleteRows p => (ids, rows j)) from
      measurable_const.prodMk (measurable_completeRowProjection p j))
  apply Integrable.of_mem_Icc 0 1 hmeas.aemeasurable
  exact ae_of_all _ fun rows => completeErrorFixedRowProbability_bounds
    rate rewards C_star C_h ids j (rows j)

/-- Disintegration over the exhaustive cells of the original coordinator
index, with its original scalar and all other private coordinates retained. -/
theorem completeError_privateExpectation_eq_uniform_fixedRows
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (rows : CompleteRows p) :
    ∫ e : ExtendedPrivateCoordinates p,
      completeErrorIndicator rate rewards C_star C_h ((ids, rows), e)
      ∂extendedPrivateLaw p =
      (1 / (M p : ℝ)) * ∑ j : Fin (M p),
        completeErrorFixedRowProbability rate rewards C_star C_h ids j (rows j) := by
  let f : ExtendedPrivateCoordinates p → ℝ := fun e =>
    completeErrorIndicator rate rewards C_star C_h ((ids, rows), e)
  have hfint : Integrable f (extendedPrivateLaw p) :=
    integrable_completeErrorIndicator_privateSection
      rate rewards C_star C_h ids rows (extendedPrivateLaw p)
  have hdisjoint : Pairwise (fun i j =>
      Disjoint (ReferenceCompleteSelectedRowExpectation.indexCell p i)
        (ReferenceCompleteSelectedRowExpectation.indexCell p j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro e hi hj
    exact hij (hi.symm.trans hj)
  have hcover :
      (⋃ j, ReferenceCompleteSelectedRowExpectation.indexCell p j) = Set.univ := by
    ext e
    simp only [Set.mem_iUnion, ReferenceCompleteSelectedRowExpectation.indexCell,
      Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨PrivateSourceStreams.coordinatorIndex p e.1.2, rfl⟩
  have hpartition := integral_iUnion_fintype (μ := extendedPrivateLaw p) (f := f)
    (fun j => ReferenceCompleteSelectedRowExpectation.measurableSet_indexCell p j)
    hdisjoint (fun j => hfint.integrableOn)
  rw [hcover, setIntegral_univ] at hpartition
  have hprob (j : Fin (M p)) :
      completeErrorFixedRowProbability rate rewards C_star C_h ids j (rows j) =
      (M p : ℝ) * ∫ e in ReferenceCompleteSelectedRowExpectation.indexCell p j,
        f e ∂extendedPrivateLaw p := by
    rw [completeErrorFixedRowProbability_eq_fixedPublicIntegral,
      ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw,
      integral_smul_measure, smul_eq_mul, ENNReal.toReal_ofReal (Nat.cast_nonneg _)]
  have hmne : (M p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (M_pos p).ne'
  have hsum :
      (1 / (M p : ℝ)) * ∑ j : Fin (M p),
        completeErrorFixedRowProbability rate rewards C_star C_h ids j (rows j) =
      ∑ j : Fin (M p),
        ∫ e in ReferenceCompleteSelectedRowExpectation.indexCell p j,
          f e ∂extendedPrivateLaw p := by
    calc
      _ = (1 / (M p : ℝ)) * ∑ j : Fin (M p),
            (M p : ℝ) * ∫ e in ReferenceCompleteSelectedRowExpectation.indexCell p j,
              f e ∂extendedPrivateLaw p := by
        exact congrArg (fun x : ℝ => (1 / (M p : ℝ)) * x)
          (Finset.sum_congr rfl fun j _ => hprob j)
      _ = (1 / (M p : ℝ)) *
            ((M p : ℝ) * ∑ j : Fin (M p),
              ∫ e in ReferenceCompleteSelectedRowExpectation.indexCell p j,
                f e ∂extendedPrivateLaw p) := by
        congr 1
        rw [Finset.mul_sum]
      _ = _ := by rw [← mul_assoc, one_div_mul_cancel hmne, one_mul]
  calc
    _ = ∑ j : Fin (M p),
          ∫ e in ReferenceCompleteSelectedRowExpectation.indexCell p j,
            f e ∂extendedPrivateLaw p := hpartition
    _ = _ := hsum.symm

/-- The original private expectation is the uniform average of the literal
selected-row probabilities at every public output. -/
theorem completeError_privateExpectation_eq_fixedRowAverage
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (rows : CompleteRows p) :
    ∫ e : ExtendedPrivateCoordinates p,
      completeErrorIndicator rate rewards C_star C_h ((ids, rows), e)
      ∂extendedPrivateLaw p =
      (1 / (M p : ℝ)) * ∑ j : Fin (M p),
        completeErrorFixedRowProbability rate rewards C_star C_h ids j (rows j) :=
  completeError_privateExpectation_eq_uniform_fixedRows rate rewards C_star C_h ids rows

private theorem integral_completeErrorFixedRowProbability_projection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (M p)) :
    (∫ rows : CompleteRows p,
      completeErrorFixedRowProbability rate rewards C_star C_h ids j (rows j)
      ∂completeRowsMeasure p) =
      ∫ rho : CompleteRow p,
        completeErrorFixedRowProbability rate rewards C_star C_h ids j rho
        ∂completeRowMeasure p := by
  have hmp := CompletePublicTable.measurePreserving_completeRowProjection p j
  have hmeas : Measurable (fun rho : CompleteRow p =>
      completeErrorFixedRowProbability rate rewards C_star C_h ids j rho) :=
    (measurable_completeErrorFixedRowProbability rate rewards C_star C_h j).comp
      (measurable_const.prodMk measurable_id)
  rw [← hmp.map_eq]
  exact (integral_map hmp.measurable.aemeasurable hmeas.aestronglyMeasurable).symm

/-- The mean over the original continuous row law is Borel in the fixed ID
array. -/
theorem measurable_completeErrorMean
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : Measurable (completeErrorMean rate rewards C_star C_h) := by
  have hrow (j : Fin (M p)) :
      Measurable (fun ids : IDArray p =>
        ∫ rho : CompleteRow p,
          completeErrorFixedRowProbability rate rewards C_star C_h ids j rho
          ∂completeRowMeasure p) := by
    have hf := (measurable_completeErrorFixedRowProbability
      rate rewards C_star C_h j).stronglyMeasurable
    exact hf.integral_prod_right' (ν := completeRowMeasure p) |>.measurable
  change Measurable (fun ids : IDArray p => (1 / (M p : ℝ)) *
    ∑ j : Fin (M p),
      ∫ rho : CompleteRow p,
        completeErrorFixedRowProbability rate rewards C_star C_h ids j rho
        ∂completeRowMeasure p)
  have hsum : Measurable (fun ids : IDArray p =>
      ∑ j : Fin (M p),
        ∫ rho : CompleteRow p,
          completeErrorFixedRowProbability rate rewards C_star C_h ids j rho
          ∂completeRowMeasure p) :=
    Finset.univ.measurable_fun_sum fun j hj => hrow j
  exact measurable_const.mul hsum

/-- For each fixed ID array, the continuous-row mean is exactly the measure of
the same complete source event under the Dirac-inserted original product law. -/
theorem completeErrorMean_eq_fixedID_sourceEvent_measure
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) :
    completeErrorMean rate rewards C_star C_h ids =
      (((Measure.dirac ids).prod (completeRowsMeasure p)).prod
        (extendedPrivateLaw p)).real (completeErrorEvent rate rewards C_star C_h) := by
  let ν := (((Measure.dirac ids).prod (completeRowsMeasure p)).prod
    (extendedPrivateLaw p))
  let I : SourceInput p → ℝ := completeErrorIndicator rate rewards C_star C_h
  let E : Set (SourceInput p) := completeErrorEvent rate rewards C_star C_h
  have hE : MeasurableSet E := measurableSet_completeErrorEvent rate rewards C_star C_h
  have hImeas : Measurable I := measurable_completeErrorIndicator rate rewards C_star C_h
  have hIint : Integrable I ν := by
    apply Integrable.of_mem_Icc 0 1 hImeas.aemeasurable
    exact ae_of_all _ fun source => completeErrorIndicator_bounds
      rate rewards C_star C_h source
  have hinner : Integrable (fun published : PublishedOutput p =>
      ∫ e : ExtendedPrivateCoordinates p, I (published, e) ∂extendedPrivateLaw p)
      ((Measure.dirac ids).prod (completeRowsMeasure p)) := hIint.integral_prod_left
  have hiterated :
      (∫ source : SourceInput p, I source ∂ν) =
        ∫ rows : CompleteRows p,
          ∫ e : ExtendedPrivateCoordinates p, I ((ids, rows), e)
            ∂extendedPrivateLaw p ∂completeRowsMeasure p := by
    calc
      _ = ∫ published : PublishedOutput p,
            ∫ e : ExtendedPrivateCoordinates p, I (published, e)
              ∂extendedPrivateLaw p ∂((Measure.dirac ids).prod (completeRowsMeasure p)) :=
        integral_prod _ hIint
      _ = ∫ id' : IDArray p, ∫ rows : CompleteRows p,
            ∫ e : ExtendedPrivateCoordinates p, I ((id', rows), e)
              ∂extendedPrivateLaw p ∂completeRowsMeasure p ∂Measure.dirac ids :=
        integral_prod _ hinner
      _ = _ := by simp only [integral_dirac]
  have hmeanRows : completeErrorMean rate rewards C_star C_h ids =
      ∫ rows : CompleteRows p,
        ∫ e : ExtendedPrivateCoordinates p, I ((ids, rows), e)
          ∂extendedPrivateLaw p ∂completeRowsMeasure p := by
    have hprojection (j : Fin (M p)) :=
      integral_completeErrorFixedRowProbability_projection rate rewards C_star C_h ids j
    have hterms (j : Fin (M p)) : Integrable (fun rows : CompleteRows p =>
        completeErrorFixedRowProbability rate rewards C_star C_h ids j (rows j))
        (completeRowsMeasure p) :=
      integrable_completeErrorFixedRowProbability_rowSection
        rate rewards C_star C_h ids j
    calc
      _ = ∫ rows : CompleteRows p,
            (1 / (M p : ℝ)) * ∑ j : Fin (M p),
              completeErrorFixedRowProbability rate rewards C_star C_h ids j (rows j)
              ∂completeRowsMeasure p := by
        unfold completeErrorMean
        simp_rw [← hprojection]
        rw [integral_const_mul, integral_finsetSum Finset.univ
          (fun j hj => hterms j)]
      _ = ∫ rows : CompleteRows p,
            ∫ e : ExtendedPrivateCoordinates p, I ((ids, rows), e)
              ∂extendedPrivateLaw p ∂completeRowsMeasure p := by
        exact integral_congr_ae (Filter.Eventually.of_forall fun rows =>
          (completeError_privateExpectation_eq_uniform_fixedRows
            rate rewards C_star C_h ids rows).symm)
  have hmass : (∫ source : SourceInput p, I source ∂ν) = ν.real E := by
    have hindicator : I = fun source => E.indicator (fun _ => (1 : ℝ)) source := by
      funext source
      rfl
    rw [hindicator]
    exact integral_indicator_one hE
  calc
    _ = ∫ rows : CompleteRows p,
          ∫ e : ExtendedPrivateCoordinates p, I ((ids, rows), e)
            ∂extendedPrivateLaw p ∂completeRowsMeasure p := hmeanRows
    _ = ∫ source : SourceInput p, I source ∂ν := hiterated.symm
    _ = ν.real E := hmass

end Bandits.Support.ReferenceCompleteErrorSelectedRowProbability

end
