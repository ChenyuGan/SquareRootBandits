/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceRankInstallationRecorderFastLaw
public import Bandits.Support.ReferenceOriginalCalendarProposalFreePhysicalOperations
public import Bandits.Support.ReferenceFirstLivePostUpdateProposalLaw

import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Original proposal factor at an arbitrary rank installation

This module builds the original-source, pre-Finish observation at a ranked
installation. The current physical recording, logical reserved FAST draw,
strict-past numerical state, current raw arrivals, and complete numerical
update are retained together. Only the current selected-row `prop` scalar is
factored out.

Sources: ZIP4 `06_interruptions.tex:381-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`appendix_a_local_protocol.tex:28-79`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceRankInstallationRecorderFoundation
open Bandits.Support.ReferenceFirstLivePostUpdateProposalLaw

namespace Bandits.Support.ReferenceRankInstallationPostUpdateProposalLaw

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

abbrev SourceInput (p : ConstructorDimensions.Parameters) :=
  ReferenceRankInstallationRecorderFoundation.SourceInput p
abbrev View (p : ConstructorDimensions.Parameters)
    (eta : ReferencePrelaunchFollower.LearningRate) := ReferenceDownReception.ChoiceTimeView p eta
abbrev Observer (p : ConstructorDimensions.Parameters)
    (eta : ReferencePrelaunchFollower.LearningRate) := Option (View p eta) ×
  ((Option (Option (Fin p.K)) × Option (Fin p.K)) ×
    Option (NumericalUpdateFields p))

local notation "prefix" => ReferenceSourcePrefixHistoryFiltration.sourcePrefix
local notation "currentControl" => ReferenceSourceCurrentControlFreshness.u_t p
local notation "historyAt" =>
  ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h
local notation "viewAt" =>
  ReferenceRankInstallationRecorderFoundation.actualInstallationView rate rewards C_star C_h
local notation "markerAt" =>
  ReferenceRankInstallationRecorderFoundation.actualMarker rate rewards C_star C_h
local notation "installEvent" =>
  ReferenceRankInstallationRecorderFoundation.installationEvent rate rewards C_star C_h

local instance sourceInputMeasurableSpace : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {Y : Type*} [MeasurableSpace Y] :
    MeasurableSpace (Option Y) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance outcomeMeasurableSpace :
    MeasurableSpace (ReferenceFirstCollectionPastSamplerFibreLaw.Outcome p) := ⊤

local instance outcomeDiscreteMeasurableSpace :
    DiscreteMeasurableSpace (ReferenceFirstCollectionPastSamplerFibreLaw.Outcome p) :=
  ⟨fun _ => trivial⟩

local instance optionSingleton {Y : Type*} [MeasurableSpace Y]
    [MeasurableSingletonClass Y] : MeasurableSingletonClass (Option Y) := by
  constructor
  intro o
  let e := Equiv.optionEquivSumPUnit Y
  have hset : e ⁻¹' {e o} = {o} := by
    ext x
    exact e.injective.eq_iff
  rw [← hset]
  apply comap_measurable e
  cases he : e o with
  | inl y => simpa only [Set.image_singleton] using
      (measurableSet_singleton y).inl_image (β := PUnit)
  | inr u => simpa only [Set.image_singleton] using
      (measurableSet_singleton u).inr_image (α := Y)

abbrev NumericalState (p : ConstructorDimensions.Parameters) :=
  (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ)))
abbrev RawCoordinates (p : ConstructorDimensions.Parameters) :=
  Bool × (Fin p.K → ℕ)

local instance sumMeasurableSingleton {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) where
  measurableSet_singleton x := by
    cases x with
    | inl a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inl_image
    | inr b => simpa only [Set.image_singleton] using (MeasurableSet.singleton b).inr_image

local instance listMeasurableSingleton {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (List α) where
  measurableSet_singleton L := by
    let hcoords := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
      (α := α)
    have hlen : MeasurableSet {xs : List α | xs.length = L.length} := by
      exact measurableSet_eq_fun (measurable_fst.comp hcoords) measurable_const
    have hentry (n : ℕ) : MeasurableSet {xs : List α |
        ReferenceActiveHorizonMeasurability.listObservationAt xs n =
          ReferenceActiveHorizonMeasurability.listObservationAt L n} := by
      exact (MeasurableSet.singleton
        (ReferenceActiveHorizonMeasurability.listObservationAt L n)).preimage
          ((measurable_pi_apply n).comp (measurable_snd.comp hcoords))
    have hforall : MeasurableSet {xs : List α | ∀ n,
        ReferenceActiveHorizonMeasurability.listObservationAt xs n =
          ReferenceActiveHorizonMeasurability.listObservationAt L n} := by
      convert MeasurableSet.iInter hentry using 1
      ext xs
      simp
    have hset : {L} = {xs : List α | xs.length = L.length ∧
        ∀ n, ReferenceActiveHorizonMeasurability.listObservationAt xs n =
          ReferenceActiveHorizonMeasurability.listObservationAt L n} := by
      ext xs
      simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
      constructor
      · rintro rfl
        exact ⟨rfl, fun _ => rfl⟩
      · rintro ⟨hlen', hentries⟩
        apply List.ext_getElem hlen'
        intro n hnX hnL
        have he := hentries n
        simpa [ReferenceActiveHorizonMeasurability.listObservationAt,
          List.getElem?_eq_getElem hnX, List.getElem?_eq_getElem hnL] using he
    rw [hset]
    exact hlen.inter hforall

/-- The all-arm integer arrival coordinates at the same current actual live
readout used by the accepted installation source cell. -/
def actualInstallationRawCoordinates (t : Fin p.T) (z : SourceInput p) :
    Option (RawCoordinates p) :=
  (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).bind
    fun r => (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).map
      (ReferenceLaterLiveReadoutValuesMeasurability.arrivalCoordinates rate)

/-- The actual all-arm raw-arrival vector read from the current installation
source readout. A present bottom marker gives zero raw arrivals; outer absence
remains absent. The enable bit is retained in the raw coordinates. -/
def actualInstallationRawArrivals (t : Fin p.T) (z : SourceInput p) :
    Option (Fin p.K → ℕ) :=
  (actualInstallationRawCoordinates rate rewards C_star C_h t z).map Prod.snd

/-- Combine only present strict-past and current raw readouts. -/
def numericalUpdateFromReadouts (before : Option (NumericalState p))
    (raw : Option (Fin p.K → ℕ)) : Option (NumericalUpdateFields p) :=
  before.bind fun b => raw.map (numericalUpdateFields rate b)

/-- The original numerical registers, strict-past overflow flag, and complete
accepted-record arrays before the current ranked installation. -/
def actualInstallationNumericalBefore (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) :=
  ReferenceFirstCollectionCurrentRetainedGate.prefixReadout? rate rewards C_star C_h t
    (prefix control0 t.val z)

/-- Apply the shared all-arm numerical update to the actual strict-past state
and the whole current physical raw-arrival vector. -/
def actualInstallationNumericalUpdate (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) : Option (NumericalUpdateFields p) :=
  numericalUpdateFromReadouts rate
    (actualInstallationNumericalBefore rate rewards C_star C_h control0 t z)
    (actualInstallationRawArrivals rate rewards C_star C_h t z)

/-- Literal preproposal observer on the original source. The selected view and
the nested-option actual recorder/reserved-FAST pair stay explicit. -/
def actualRankPreProposalObserver (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) : Observer p rate.eta :=
  (viewAt t z,
    (ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast
      rate rewards C_star C_h t z,
      actualInstallationNumericalUpdate rate rewards C_star C_h control0 t z))

/-- Change only the current original selected-row proposal scalar. The full
source remainder and private coordinates remain in this source. -/
def replaceSelectedProp (t : Fin p.T) (z : SourceInput p)
    (value : ContinuousControlSlice.Scalar) : SourceInput p :=
  ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z
    (replaceProposalScalar p (currentControl t z) value)

private theorem currentControl_replaceSelectedProp
    (t : Fin p.T) (z : SourceInput p) (value : ContinuousControlSlice.Scalar) :
    currentControl t (replaceSelectedProp t z value) =
      replaceProposalScalar p (currentControl t z) value := by
  change ((replaceSelectedProp t z value).1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p
        (replaceSelectedProp t z value))).2 t = _
  rw [show ActualInitializationPhysicalStep.selectedRowIndex p
      (replaceSelectedProp t z value) =
        ActualInitializationPhysicalStep.selectedRowIndex p z by rfl]
  simp [replaceSelectedProp,
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]

private theorem assignmentVector_replaceProposalScalar
    (u : ContinuousLearningRows.TimeControl p)
    (value : ContinuousControlSlice.Scalar) :
    ContinuousControlSlice.assignmentVector (replaceProposalScalar p u value).1 =
      ContinuousControlSlice.assignmentVector u.1 := by
  funext i
  have hlabel : ContinuousControlSlice.Label.assign i ≠ propLabel p := by
    change Sum.inr (Sum.inr (Sum.inr i)) ≠ Sum.inl _
    exact Sum.inr_ne_inl
  change (replaceProposalScalar p u value).1
      (ContinuousControlSlice.Label.assign i) =
    u.1 (ContinuousControlSlice.Label.assign i)
  exact replaceProposalScalar_other p u value _ hlabel

private theorem currentAssignmentVector_replaceSelectedProp
    (t : Fin p.T) (z : SourceInput p) (value : ContinuousControlSlice.Scalar) :
    ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t
        (replaceSelectedProp t z value) =
      ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t z := by
  unfold ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector
  have hu : currentControl t (replaceSelectedProp t z value) =
      replaceProposalScalar p (currentControl t z) value := by
    exact currentControl_replaceSelectedProp t z value
  rw [hu]
  exact assignmentVector_replaceProposalScalar (currentControl t z) value

/-- The accepted actual installation view and the logical reserved FAST draw
are invariant under changing only the original current proposal scalar. -/
theorem actualView_reservedFast_replaceSelectedProp
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : SourceInput p) (value : ContinuousControlSlice.Scalar) :
    viewAt t (replaceSelectedProp t z value) = viewAt t z ∧
      ReferenceRankInstallationRecorderFastLaw.actualReservedFast
        rate rewards C_star C_h t (replaceSelectedProp t z value) =
      ReferenceRankInstallationRecorderFastLaw.actualReservedFast
        rate rewards C_star C_h t z := by
  let z' := replaceSelectedProp t z value
  let u := currentControl t z
  have hprefix : prefix control0 t.val z' = prefix control0 t.val z := by
    exact ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current
      control0 t z (replaceProposalScalar p u value)
  have hvector :
      ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t z' =
        ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t z := by
    exact currentAssignmentVector_replaceSelectedProp t z value
  have hbase : viewAt t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
      p t (prefix control0 t.val z) u) = viewAt t z :=
    ReferenceRankInstallationRecorderFoundation.actualInstallationView_replace
      rate rewards C_star C_h control0 t z u rfl
  have hbase' : viewAt t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
      p t (prefix control0 t.val z') u) = viewAt t z' :=
    ReferenceRankInstallationRecorderFoundation.actualInstallationView_replace
      rate rewards C_star C_h control0 t z' u (by rw [hvector]; rfl)
  have hview : viewAt t z' = viewAt t z := by
    calc
      viewAt t z' = viewAt t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
          p t (prefix control0 t.val z') u) := hbase'.symm
      _ = viewAt t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
          p t (prefix control0 t.val z) u) := by rw [hprefix]
      _ = viewAt t z := hbase
  have hcurrent : currentControl t z' = replaceProposalScalar p u value := by
    have hJ : ActualInitializationPhysicalStep.selectedRowIndex p z' =
        ActualInitializationPhysicalStep.selectedRowIndex p z := rfl
    change (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z')).2 t = _
    rw [hJ]
    simp [z', replaceSelectedProp, u, ReferenceSourceCurrentControlFreshness.u_t,
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
  have hfastLabel : ContinuousControlSlice.Label.fast ≠ propLabel p := by
    intro h
    have h' : ContinuousControlSlice.NamedLabel.fast =
        ContinuousControlSlice.NamedLabel.prop := Sum.inl_injective h
    exact (by decide : ContinuousControlSlice.NamedLabel.fast ≠
      ContinuousControlSlice.NamedLabel.prop) h'
  have hfast : ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
      (currentControl t z').1 =
        ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast u.1 := by
    rw [hcurrent]
    exact replaceProposalScalar_other p u value _ hfastLabel
  constructor
  · exact hview
  · unfold ReferenceRankInstallationRecorderFastLaw.actualReservedFast
    rw [hview, hfast]

/-- The strict-past numerical state is unchanged by replacing the current
proposal scalar. -/
theorem actualInstallationNumericalBefore_replaceSelectedProp
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : SourceInput p) (value : ContinuousControlSlice.Scalar) :
    actualInstallationNumericalBefore rate rewards C_star C_h control0 t
        (replaceSelectedProp t z value) =
      actualInstallationNumericalBefore rate rewards C_star C_h control0 t z := by
  simp only [actualInstallationNumericalBefore, replaceSelectedProp]
  rw [ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current]

/-- The accepted original physical operation projection is preserved by the
proposal replacement, using the public all-branch comparison. -/
theorem actualRecord_physicalOperations_replaceSelectedProp
    (t : Fin p.T) (z : SourceInput p) (value : ContinuousControlSlice.Scalar) :
    let z' := replaceSelectedProp t z value
    (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).map
      (fun r => ((ReferenceActiveDispatchTemporal.dispatchData r.input).2,
        r.actions, r.gridFeedback, r.ownEntries)) =
    (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z').map
      (fun r => ((ReferenceActiveDispatchTemporal.dispatchData r.input).2,
        r.actions, r.gridFeedback, r.ownEntries)) := by
  simpa [replaceSelectedProp, replaceProposalScalar,
    ReferenceFirstLivePostUpdateProposalLaw.propLabel,
    ReferenceSourceCurrentControlFreshness.u_t,
    ReferenceOriginalCalendarProposalFreePhysicalOperations.replaceCurrentProp] using
    (ReferenceOriginalCalendarProposalFreePhysicalOperations.actualRecord_physicalOperations_prop_replacement
      rate rewards C_star C_h t z value)

/-- Actual installation data supply the present accepted record, the enabled
current numerical readout, its raw quantized coordinates, and the valid
canonical choice view from the same original invocation. -/
theorem installationEvent_actualPreProposalData
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ)
    (t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ installEvent k t) :
    (∃ v : View p rate.eta,
      ∃ valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
        v.complementWeights,
        viewAt t z = some v ∧
        ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast
          rate rewards C_star C_h t z =
          (some (ReferenceRankInstallationRecorderFastLaw.installationRecorderFastPair
            rate t v valid ((currentControl t z).1)).1,
            some (ReferenceRankInstallationRecorderFastLaw.installationRecorderFastPair
              rate t v valid ((currentControl t z).1)).2)) ∧
    (∃ b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
      ∃ native : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[b.val],
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
          some (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[b.val] ∧
        actualInstallationRawCoordinates rate rewards C_star C_h t z =
          some (ReferenceLaterLiveReadoutValuesMeasurability.arrivalCoordinates rate
            native.input) ∧
        native.input.enabled = true ∧
        native.input.rate = native.selected.view.payload.rate) := by
  constructor
  · obtain ⟨v, valid, hv, hpair⟩ :=
      ReferenceRankInstallationRecorderFastLaw.installationEvent_actualMarkerReservedFast
        rate rewards C_star C_h control0 k t z hz
    exact ⟨v, valid, hv, hpair⟩
  · obtain ⟨b, native, hr, _ht, _hchosen, _hpositive, _hpending, _hstates,
      hread, _hmarker, henabled, hrate⟩ :=
      ReferenceRankInstallationRecorderFoundation.installationEvent_recordingData
        rate rewards C_star C_h k t z hz
    refine ⟨b, native, hr, ?_, henabled, hrate⟩
    simp [actualInstallationRawCoordinates, hr, hread]

/-- Measurability of the literal current raw-arrival observation. -/
theorem measurable_actualInstallationRawArrivals (t : Fin p.T) :
    Measurable (actualInstallationRawArrivals rate rewards C_star C_h t) := by
  have h := ReferenceOriginalCalendarContinuingLiveRecorderLaw.measurable_actualReadout
    rate rewards C_star C_h
    (fun r => (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).map
      (ReferenceLaterLiveReadoutValuesMeasurability.arrivalCoordinates rate))
    (fun k => (ReferenceLaterLiveCalendarMeasurability.measurable_indexedArrivalReadout
      rate rewards C_star C_h k).comp
        (show Measurable (fun x : ReferenceCompleteSuffixInputMeasurability.IndexedSource
          rate rewards C_star C_h k => ((0 : ℕ), x)) from
          measurable_const.prodMk measurable_id)) t
  have hraw : Measurable (fun q : Option (RawCoordinates p) => q.map Prod.snd) :=
    measurable_of_countable _
  have heq : actualInstallationRawArrivals rate rewards C_star C_h t = fun z =>
      ((ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).bind
        (fun r => (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).map
          (ReferenceLaterLiveReadoutValuesMeasurability.arrivalCoordinates rate))).map Prod.snd :=
    rfl
  rw [heq]
  exact hraw.comp h

/-- The strict-past registers and all prior accepted records form a Borel
readout on the original source. -/
theorem measurable_actualInstallationNumericalBefore
    (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) :
    Measurable (actualInstallationNumericalBefore rate rewards C_star C_h control0 t) := by
  have hreadout := ReferenceFirstCollectionCurrentRetainedGate.prefixReadout_measurable
    rate rewards C_star C_h control0 t
  have hle : ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1) ≤ (inferInstance : MeasurableSpace (SourceInput p)) :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (t.val + 1)
  have hfull : Measurable
      (ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
        rate rewards C_star C_h t) := Measurable.mono hreadout hle le_rfl
  exact hfull.comp (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix
    control0 t.val)

/-- The computed accepted/service/after update is Borel on the original
source, including its optional absence off the actual prefix domain. -/
theorem measurable_actualInstallationNumericalUpdate
    (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) :
    Measurable (actualInstallationNumericalUpdate rate rewards C_star C_h control0 t) := by
  have hcombine : Measurable (fun q : Option (NumericalState p) ×
      Option (Fin p.K → ℕ) => numericalUpdateFromReadouts rate q.1 q.2) :=
    measurable_of_countable _
  exact hcombine.comp
    ((measurable_actualInstallationNumericalBefore rate rewards C_star C_h control0 t).prodMk
      (measurable_actualInstallationRawArrivals rate rewards C_star C_h t))

/-- The actual selected view, recorder, logical reserved FAST, strict-past
numerical state, raw arrivals, and numerical update are jointly Borel. -/
theorem measurable_actualRankPreProposalObserver
    (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) : Measurable (actualRankPreProposalObserver rate rewards C_star C_h
      control0 t) := by
  exact (ReferenceRankInstallationRecorderFoundation.measurable_actualInstallationView
      rate rewards C_star C_h t).prodMk
    ((ReferenceRankInstallationRecorderFastLaw.measurable_actualMarkerReservedFast
      rate rewards C_star C_h t).prodMk
      (measurable_actualInstallationNumericalUpdate rate rewards C_star C_h control0 t))

/-- The installation recording map never reads the proposal coordinate.
The physical action in this snapshot may be a pilot action. -/
theorem installationRecordingMap_replaceProposalScalar
    (t : Fin p.T) (v : View p rate.eta)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights)
    (u : ContinuousLearningRows.TimeControl p) (value : ContinuousControlSlice.Scalar) :
    installationRecordingMap rate t v valid (replaceProposalScalar p u value).1 =
      installationRecordingMap rate t v valid u.1 := by
  classical
  have hother (c : ContinuousControlSlice.Label p.m p.K) (hc : c ≠ propLabel p) :
      ContinuousControlSlice.coordinate c (replaceProposalScalar p u value).1 =
        ContinuousControlSlice.coordinate c u.1 :=
    replaceProposalScalar_other p u value c hc
  have hslot := hother ContinuousControlSlice.Label.slot (by
    intro h
    have h' : ContinuousControlSlice.NamedLabel.slot =
        ContinuousControlSlice.NamedLabel.prop := Sum.inl_injective h
    cases h')
  have hrec := hother ContinuousControlSlice.Label.rec (by
    intro h
    have h' : ContinuousControlSlice.NamedLabel.recorder =
        ContinuousControlSlice.NamedLabel.prop := Sum.inl_injective h
    cases h')
  have hthin := hother ContinuousControlSlice.Label.thin (by
    intro h
    have h' : ContinuousControlSlice.NamedLabel.thin =
        ContinuousControlSlice.NamedLabel.prop := Sum.inl_injective h
    cases h')
  have hfast := hother ContinuousControlSlice.Label.fast (by
    intro h
    have h' : ContinuousControlSlice.NamedLabel.fast =
        ContinuousControlSlice.NamedLabel.prop := Sum.inl_injective h
    cases h')
  have hpilot (i : Fin p.m) : PublicDiscreteDraws.pilotDraw (K_pos p) i
      (replaceProposalScalar p u value).1 = PublicDiscreteDraws.pilotDraw (K_pos p) i u.1 := by
    unfold PublicDiscreteDraws.pilotDraw
    rw [hother (ContinuousControlSlice.Label.pilot i) (by
      exact Sum.inr_ne_inl)]
  let act := SnapshotRecordingKernel.dataAction p
    (.live v.payload.assignment (installationSnapshot v.payload.assignment))
    rate.eta.val rate.eta.property rate.sourceCap v.payload.anchor
    (ReferenceFirstWindowNumericalStream.sourceWeights v.payload v.complementWeights)
    v.payload.anchor_pos
    (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid)
  have haction (i : Fin p.m) : act (replaceProposalScalar p u value).1 i = act u.1 i := by
    dsimp only [act, SnapshotRecordingKernel.dataAction]
    split_ifs
    · rw [hfast]
    · exact hpilot i
    · exact hpilot i
    · rfl
  have hmask (i : Fin p.m) (a : Fin p.K) :
      CanonicalRecordingSlice.recordingMask (K_pos p) i a
          (replaceProposalScalar p u value).1 ↔
        CanonicalRecordingSlice.recordingMask (K_pos p) i a u.1 := by
    simp only [CanonicalRecordingSlice.recordingMask, hpilot]
  unfold installationRecordingMap SnapshotRecordingKernel.recordingMap
  dsimp only [act] at haction
  simp only [hslot, hrec, hthin, hmask, haction]

/-- The original accepted marker is invariant on the actual installation
under replacement of only the current selected-row proposal scalar. -/
theorem actualMarker_replaceSelectedProp
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ installEvent k t)
    (value : ContinuousControlSlice.Scalar) :
    markerAt t (replaceSelectedProp t z value) = markerAt t z := by
  let z' := replaceSelectedProp t z value
  have hz' : z' ∈ installEvent k t :=
    (installationEvent_replaceSourceControl rate rewards C_star C_h control0 k t z
      (replaceProposalScalar p (currentControl t z) value)).mpr hz
  obtain ⟨v, valid, hv, hp⟩ :=
    ReferenceRankInstallationRecorderFastLaw.installationEvent_actualMarkerReservedFast
      rate rewards C_star C_h control0 k t z hz
  obtain ⟨v', valid', hv', hp'⟩ :=
    ReferenceRankInstallationRecorderFastLaw.installationEvent_actualMarkerReservedFast
      rate rewards C_star C_h control0 k t z' hz'
  have hview := (actualView_reservedFast_replaceSelectedProp rate rewards C_star C_h
    control0 t z value).1
  have hvv : v' = v := Option.some.inj (hv'.symm.trans (hview.trans hv))
  subst v'
  have hm := congrArg Prod.fst hp
  have hm' := congrArg Prod.fst hp'
  change markerAt t z = some (installationRecordingMap rate t v valid
    (currentControl t z).1) at hm
  change markerAt t z' = some (installationRecordingMap rate t v valid'
    (currentControl t z').1) at hm'
  rw [hm', hm, currentControl_replaceSelectedProp]
  exact congrArg some (installationRecordingMap_replaceProposalScalar rate t v valid
    (currentControl t z) value)

/-- The current integer arrivals are the original reward quantization at the
actual installation marker and actual selected rate, for every arm together. -/
theorem installationEvent_rawArrivals_formula
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ installEvent k t) :
    ∃ (v : View p rate.eta) (o : Option (Fin p.K)),
      viewAt t z = some v ∧ markerAt t z = some o ∧
      actualInstallationRawCoordinates rate rewards C_star C_h t z =
        some (true, fun a => if o = some a then
          Nat.floor ((D p : ℝ) * rate.eta.val *
            (((rewards t a).val : ℝ) / (D p : ℝ)) / v.payload.rate a) else 0) := by
  obtain ⟨b, native, hr, ht, hb, _hpos, _hpending, _hstates, hread, hm,
    henabled, _hrate⟩ := installationEvent_recordingData rate rewards C_star C_h k t z hz
  obtain ⟨b', native', hr', _ht', hv, _hparams, _hmarker⟩ :=
    installationEvent_marker_formula rate rewards C_star C_h control0 k t z hz
  have hbEq : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[b'.val] =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val] := Option.some.inj (hr'.symm.trans hr)
  have hselection : native'.selected.view = native.selected.view := by
    have hs := native'.selection_actual
    have hs' := native.selection_actual
    have he := congrArg (fun r => r.output.preparation.coordinator.downView) hbEq
    simpa only [ReferenceActivePhysicalStep.DispatchCut.downView, hs, hs',
      Option.map_some, Option.some.injEq] using he
  have hvactual : viewAt t z = some native.selected.view := by
    rw [actualInstallationView_eq_history rate rewards C_star C_h control0 k t z, hv,
      hselection]
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h t z _ hr
  have hn := ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical
    0 _ native.input hread
  obtain ⟨_henabled, selected, hs, _hreward, hrate, harrivals⟩ := hn
  have hselected : selected = native.selected := Option.some.inj
    (hs.symm.trans native.selection_actual)
  subst selected
  refine ⟨native.selected.view, native.input.recordedArm, hvactual, hm, ?_⟩
  simp only [actualInstallationRawCoordinates, hr, Option.bind_some, hread, Option.map_some]
  congr 1
  apply Prod.ext
  · exact henabled
  · funext a
    change RecordedQueueRun.quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) native.input a = _
    rw [harrivals a, ht, hf.2.2.2]

/-- On an actual installation the emitted canonical view is the original
physical dispatch's DOWN view, with record absence preserved by the bind. -/
theorem installationEvent_actualView_dispatchProjection
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ installEvent k t) :
    viewAt t z =
      (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).bind
        (fun r => (ReferenceActiveDispatchTemporal.dispatchData r.input).2.1) := by
  obtain ⟨b, native, hr, _ht, hv, _hparams, _hm⟩ :=
    installationEvent_marker_formula rate rewards C_star C_h control0 k t z hz
  rw [actualInstallationView_eq_history rate rewards C_star C_h control0 k t z, hv, hr]
  simp only [Option.bind_some]
  have hp : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[b.val].output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input := by
    rw [ReferenceActivePhysicalHorizon.RoundRecord.output_eq]
    rfl
  change some native.selected.view =
    (ReferenceActivePhysicalStep.dispatch _).downView
  rw [← hp, ReferenceActivePhysicalStep.DispatchCut.downView, native.selection_actual]
  rfl

/-- The whole current raw vector and its enable bit are preserved on the
actual installation, without identifying the two whole round records. -/
theorem actualInstallationRawCoordinates_replaceSelectedProp
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ installEvent k t)
    (value : ContinuousControlSlice.Scalar) :
    actualInstallationRawCoordinates rate rewards C_star C_h t
        (replaceSelectedProp t z value) =
      actualInstallationRawCoordinates rate rewards C_star C_h t z := by
  let z' := replaceSelectedProp t z value
  have hz' : z' ∈ installEvent k t :=
    (installationEvent_replaceSourceControl rate rewards C_star C_h control0 k t z
      (replaceProposalScalar p (currentControl t z) value)).mpr hz
  obtain ⟨v, o, hv, hm, hraw⟩ := installationEvent_rawArrivals_formula
    rate rewards C_star C_h control0 k t z hz
  obtain ⟨v', o', hv', hm', hraw'⟩ := installationEvent_rawArrivals_formula
    rate rewards C_star C_h control0 k t z' hz'
  have hoperations := actualRecord_physicalOperations_replaceSelectedProp
    rate rewards C_star C_h t z value
  have hdispatch := congrArg (fun o => o.bind (fun fields => fields.1.1)) hoperations
  simp only [Option.bind_map] at hdispatch
  have hview : viewAt t z = viewAt t z' := by
    rw [installationEvent_actualView_dispatchProjection rate rewards C_star C_h
        control0 k t z hz,
      installationEvent_actualView_dispatchProjection rate rewards C_star C_h
        control0 k t z' hz']
    exact hdispatch
  have hvv : v' = v := Option.some.inj (hv'.symm.trans (hview.symm.trans hv))
  have hoo : o' = o := Option.some.inj (hm'.symm.trans
    ((actualMarker_replaceSelectedProp rate rewards C_star C_h
      control0 k t z hz value).trans hm))
  rw [hraw', hraw, hvv, hoo]

/-- The same literal preproposal observer is unchanged by the original
selected-row proposal replacement on every actual rank installation. -/
theorem actualRankPreProposalObserver_replaceSelectedProp
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ installEvent k t)
    (value : ContinuousControlSlice.Scalar) :
    actualRankPreProposalObserver rate rewards C_star C_h control0 t
        (replaceSelectedProp t z value) =
      actualRankPreProposalObserver rate rewards C_star C_h control0 t z := by
  obtain ⟨hv, hfast⟩ := actualView_reservedFast_replaceSelectedProp
    rate rewards C_star C_h control0 t z value
  have hmarker := actualMarker_replaceSelectedProp rate rewards C_star C_h
    control0 k t z hz value
  have hraw := actualInstallationRawCoordinates_replaceSelectedProp
    rate rewards C_star C_h control0 k t z hz value
  simp only [actualRankPreProposalObserver,
    ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast,
    actualInstallationNumericalUpdate, actualInstallationRawArrivals,
    hv, hfast, hmarker, hraw,
    actualInstallationNumericalBefore_replaceSelectedProp rate rewards C_star C_h]

/-- Strict-past source locality identifies the literal numerical prestate
with the current original calendar prefix, rather than a supplied queue. -/
theorem actualInstallationNumericalBefore_eq_original
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) (z : SourceInput p) :
    actualInstallationNumericalBefore rate rewards C_star C_h control0 t z =
      ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
        rate rewards C_star C_h t z := by
  have hm : Measurable[(inferInstance : MeasurableSpace (SourceInput p)).comap
      (prefix control0 t.val)]
      (ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
        rate rewards C_star C_h t) := by
    have h := ReferenceFirstCollectionCurrentRetainedGate.prefixReadout_measurable
      rate rewards C_star C_h control0 t
    change Measurable[(inferInstance : MeasurableSpace (SourceInput p)).comap
      (prefix control0 (t.val + 1 - 1))] _ at h
    simpa only [Nat.add_sub_cancel] using h
  exact hm.factorsThrough (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
    control0 t.val t.val le_rfl z)

/-- Original whole-calendar RAW comparison supplies the unique source word.
Its actual current enabled cell and strict-past run give precisely the shared
numerical update, including the current update that first detects overflow. -/
theorem installationEvent_originalNumericalUpdate
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ installEvent k t) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (c : RecordedQueueRun.RoundInput p.K),
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h p.T z = some L ∧
      ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarSourceWordAndLaterRestoration
        rate rewards C_star C_h z L ∧
      c.enabled = true ∧
      L[t.val - ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h]? = some c ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (t.val + 1) z =
          some (L.take (t.val - ReferenceCompletePhysicalHistory.physicalStart
            rate z rewards C_star C_h + 1)) ∧
      actualInstallationNumericalBefore rate rewards C_star C_h control0 t z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (L.take (t.val - ReferenceCompletePhysicalHistory.physicalStart
              rate z rewards C_star C_h)))) ∧
      actualInstallationRawArrivals rate rewards C_star C_h t z =
        some (RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c) ∧
      actualInstallationNumericalUpdate rate rewards C_star C_h control0 t z =
        some (numericalUpdateFields rate
          (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (L.take (t.val - ReferenceCompletePhysicalHistory.physicalStart
                rate z rewards C_star C_h))))
          (RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) c)) := by
  classical
  obtain ⟨b, native, hr, ht, _hb, _hpositive, _hpending, _hstates, hread, _hm,
    henabled, _hrate⟩ := installationEvent_recordingData rate rewards C_star C_h k t z hz
  have hnonempty : ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h ≠ [] := by
    intro h
    have hb : b.val < (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length := b.isLt
    rw [h] at hb
    exact Nat.not_lt_zero _ hb
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
    exact False.elim (hnonempty (by
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch,
        ↓reduceDIte]))
  | some active =>
    obtain ⟨S, hS⟩ := ProductSetLaw.support_nonempty
      (lt_of_lt_of_le (by decide : 0 < 2) p.two_le_m) p.m_lt_K
    have hcomparison :=
      ReferenceCompleteOriginalCalendarRawLearningComparison.complete_original_calendar_raw_learning_comparison
        rate rewards C_star C_h ⟨S, hS⟩ z
    rw [hlaunch] at hcomparison
    obtain ⟨L, hterminal, hunique, hrestoration, _hbound⟩ := hcomparison
    have hcells := ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_cells
      rate rewards C_star C_h z
    rw [hlaunch] at hcells
    obtain ⟨L0, hlen, hmap, hprefix, _hphases⟩ := hcells
    have hlength := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate z rewards C_star C_h
    have hstart := ReferenceCompletePhysicalHistory.physicalStart_le_T
      rate z rewards C_star C_h
    have hend : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).length = p.T := by omega
    have hterminal0 := hprefix _ (Nat.le_refl _)
    rw [hend, ← hlen, List.take_length] at hterminal0
    have hL : L0 = L := hunique L0 hterminal0
    subst L0
    have htime := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
      rate z rewards C_star C_h b.val _ (List.getElem?_eq_getElem b.isLt)
    rw [ht] at htime
    have hindex : t.val - ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h = b.val := by omega
    have hbL : b.val < L.length := by rw [hlen]; exact b.isLt
    have hcurrent : L[t.val - ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h]? = some native.input := by
      have hentry := congrArg (fun w : List (Option (RecordedQueueRun.RoundInput p.K)) =>
        w[b.val]?) hmap
      simp only [List.getElem?_map, List.getElem?_eq_getElem b.isLt,
        List.getElem?_eq_getElem hbL, Option.map_some] at hentry
      have hcell : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[b.val] = some native.input := by
        simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hread, Option.some_or]
      change some (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[b.val]) = some (some L[b.val]) at hentry
      rw [hcell] at hentry
      have he : native.input = L[b.val] := Option.some.inj (Option.some.inj hentry)
      rw [hindex, List.getElem?_eq_getElem hbL, he]
    have hnext := hprefix (b.val + 1) (Nat.succ_le_of_lt b.isLt)
    have hnextDate : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
        (b.val + 1) = t.val + 1 := by omega
    rw [hnextDate] at hnext
    have hp := hprefix b.val b.isLt.le
    rw [← htime] at hp
    have hbefore : actualInstallationNumericalBefore rate rewards C_star C_h control0 t z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (L.take (t.val - ReferenceCompletePhysicalHistory.physicalStart
              rate z rewards C_star C_h)))) := by
      rw [actualInstallationNumericalBefore_eq_original,
        ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?,
        ← ReferenceFirstCollectionCorrectedFutureRetainedMoment.prefixInputs_eq_pastCells,
        hp, Option.map_some, hindex]
    have hraw : actualInstallationRawArrivals rate rewards C_star C_h t z =
        some (RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) native.input) := by
      simp only [actualInstallationRawArrivals, actualInstallationRawCoordinates,
        hr, Option.bind_some, hread, Option.map_some]
      rfl
    refine ⟨L, native.input, hterminal, hrestoration, henabled, hcurrent, ?_,
      hbefore, hraw, ?_⟩
    · simpa only [hindex] using hnext
    simp only [actualInstallationNumericalUpdate, hbefore, hraw,
      numericalUpdateFromReadouts, Option.bind_some, Option.map_some]

/-- The actual original numerical update equals the existing enabled queue
step. Prior overflow preserves registers; an enabled zero arrival serves. -/
theorem installationEvent_numericalUpdate_eq_step
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ installEvent k t) :
    ∃ (before : RecordedQueueRun.RunState p.K) (c : RecordedQueueRun.RoundInput p.K),
      c.enabled = true ∧
      actualInstallationNumericalBefore rate rewards C_star C_h control0 t z =
        some (before.registers, before.overflow, before.records) ∧
      actualInstallationRawArrivals rate rewards C_star C_h t z =
        some (RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c) ∧
      actualInstallationNumericalUpdate rate rewards C_star C_h control0 t z =
        some
          { raw := RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
            beforeRegisters := before.registers
            beforeOverflow := before.overflow
            beforeRecords := before.records
            accepted := RecordedQueueRun.acceptedRecord
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) before c
            service := fun j => RecordedQueueRun.recordService (4 * rate.n) (before.registers j)
              (RecordedQueueRun.acceptedRecord
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) before c j)
            afterRegisters := (RecordedQueueRun.step
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) before c).registers
            afterOverflow := (RecordedQueueRun.step
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) before c).overflow
            afterRecords := (RecordedQueueRun.step
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) before c).records } := by
  obtain ⟨L, c, _hword, _hrestoration, henabled, _hcurrent, _hnext, hbefore, hraw, hupdate⟩ :=
    installationEvent_originalNumericalUpdate rate rewards C_star C_h control0 k t z hz
  let before := RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (L.take (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))
  refine ⟨before, c, henabled, hbefore, hraw, ?_⟩
  rw [hupdate]
  exact congrArg some (numericalUpdateFields_eq_step rate before c henabled)

/-- All original source coordinates except the current selected-row proposal
scalar. The replacement value is a fixed coordinate of the baseline control. -/
def originalNonProposalSource (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) : SourceInput p :=
  replaceSelectedProp t z (control0.1 (propLabel p))

/-- The full original source remainder is Borel. -/
theorem measurable_originalNonProposalSource
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    Measurable (originalNonProposalSource control0 t : SourceInput p → SourceInput p) := by
  have hcontrol : Measurable (fun z : SourceInput p =>
      replaceProposalScalar p (currentControl t z) (control0.1 (propLabel p))) := by
    unfold replaceProposalScalar
    exact ((measurable_update_left.comp (measurable_fst.comp
      (ReferenceSourceCurrentControlFreshness.measurable_u_t t))).prodMk
        (measurable_snd.comp (ReferenceSourceCurrentControlFreshness.measurable_u_t t)))
  exact (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t).comp
    (measurable_id.prodMk hcontrol)

/-- Earlier rank marks and the whole assignment vector in the original H
are unchanged by replacement of the current proposal scalar on E. -/
theorem history_replaceSelectedProp
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ installEvent k t) (value : ContinuousControlSlice.Scalar) :
    historyAt control0 k t (replaceSelectedProp t z value) = historyAt control0 k t z := by
  have hz' : replaceSelectedProp t z value ∈ installEvent k t :=
    (installationEvent_replaceSourceControl rate rewards C_star C_h
      control0 k t z (replaceProposalScalar p (currentControl t z) value)).mpr hz
  rw [history_eq_prefixVectorHistory_of_installation rate rewards C_star C_h
      control0 k t _ hz',
    history_eq_prefixVectorHistory_of_installation rate rewards C_star C_h control0 k t z hz]
  rw [show prefix control0 t.val (replaceSelectedProp t z value) =
    prefix control0 t.val z from
      ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current control0 t z _,
    currentAssignmentVector_replaceSelectedProp]

/-- Replacing only the proposal coordinate twice retains exactly the latter
replacement and all original other source coordinates. -/
theorem replaceSelectedProp_replaceSelectedProp
    (t : Fin p.T) (z : SourceInput p) (a b : ContinuousControlSlice.Scalar) :
    replaceSelectedProp t (replaceSelectedProp t z a) b = replaceSelectedProp t z b := by
  change ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
    (replaceSelectedProp t z a)
    (replaceProposalScalar p (currentControl t (replaceSelectedProp t z a)) b) = _
  rw [currentControl_replaceSelectedProp]
  simp [replaceSelectedProp, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex, replaceProposalScalar]

abbrev RetainedInstallationObservation (p : ConstructorDimensions.Parameters)
    (eta : ReferencePrelaunchFollower.LearningRate) :=
  ReferenceRankInstallationRecorderFoundation.History p × (SourceInput p × Observer p eta)

local instance retainedInstallationObservationMeasurableSpace :
    MeasurableSpace (RetainedInstallationObservation p rate.eta) := by
  change MeasurableSpace (ReferenceRankInstallationRecorderFoundation.History p ×
    (SourceInput p × Observer p rate.eta))
  infer_instance

/-- The actual event-gated original H/rest/preproposal observation. Off E is
outer absence, distinct from every optional field inside the actual observer. -/
def restrictedInstallationObservation
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : SourceInput p) : Option (RetainedInstallationObservation p rate.eta) := by
  classical
  exact if z ∈ installEvent k t then
    some (historyAt control0 k t z, originalNonProposalSource control0 t z,
      actualRankPreProposalObserver rate rewards C_star C_h control0 t z)
  else none

theorem measurable_restrictedInstallationObservation
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T) :
    Measurable (restrictedInstallationObservation rate rewards C_star C_h control0 k t) := by
  apply Measurable.ite (measurableSet_installationEvent rate rewards C_star C_h control0 k t)
  · exact LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
      ((measurable_history rate rewards C_star C_h control0 k t).prodMk
        ((measurable_originalNonProposalSource control0 t).prodMk
          (measurable_actualRankPreProposalObserver rate rewards C_star C_h control0 t)))
  · exact measurable_const

/-- The constructed, event-gated actual observation factors out only the
original proposal coordinate. No independence of recorder and FAST is used. -/
theorem restrictedInstallationObservation_replaceSelectedProp
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : SourceInput p) (value : ContinuousControlSlice.Scalar) :
    restrictedInstallationObservation rate rewards C_star C_h control0 k t
        (replaceSelectedProp t z value) =
      restrictedInstallationObservation rate rewards C_star C_h control0 k t z := by
  classical
  have he : replaceSelectedProp t z value ∈ installEvent k t ↔ z ∈ installEvent k t :=
    installationEvent_replaceSourceControl rate rewards C_star C_h
      control0 k t z (replaceProposalScalar p (currentControl t z) value)
  by_cases hz : z ∈ installEvent k t
  · simp only [restrictedInstallationObservation, hz, he.mpr hz, ↓reduceIte,
      history_replaceSelectedProp rate rewards C_star C_h control0 k t z hz value,
      originalNonProposalSource, replaceSelectedProp_replaceSelectedProp,
      actualRankPreProposalObserver_replaceSelectedProp rate rewards C_star C_h
        control0 k t z hz value]
  · simp only [restrictedInstallationObservation, hz, he.not.mpr hz, ↓reduceIte]

private theorem originalSource_proposalFactor {β : Type*} [MeasurableSpace β]
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (f : SourceInput p → β) (hf : Measurable f)
    (hinvariant : ∀ z value, f (replaceSelectedProp t z value) = f z) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).map
        (fun z => (f z, physicalProposalBit rate (currentControl t z))) =
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).map f).prod (proposalBitLaw rate) := by
  classical
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let strata := ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p
  let μq := fun q : Fin (M p) => μ.restrict (strata q)
  have hbit : Measurable (fun z : SourceInput p =>
      physicalProposalBit rate (currentControl t z)) :=
    (measurable_physicalProposalBit rate).comp
      (ReferenceSourceCurrentControlFreshness.measurable_u_t t)
  have hstratum (q : Fin (M p)) :
      (μq q).map (fun z => (f z, physicalProposalBit rate (currentControl t z))) =
        ((μq q).map f).prod (proposalBitLaw rate) := by
    let R := ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t
    let S := ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t
    let ν := (ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderLaw p q t).restrict S
    let e := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
    let recover : R × ContinuousLearningRows.TimeControl p → SourceInput p :=
      fun x => e.symm (x.2, x.1)
    have hrecover : Measurable recover := e.symm.measurable.comp measurable_swap
    have hrecoverLaw : (ν.prod (ContinuousLearningRows.timeControlLaw p)).map recover = μq q := by
      change (ν.prod (ContinuousLearningRows.timeControlLaw p)).map
        (e.symm ∘ Prod.swap) = _
      rw [← Measure.map_map e.symm.measurable measurable_swap, Measure.prod_swap]
      exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_privateStratum_map_symm p q t
    let baseline := control0.1 (propLabel p)
    let g : R × PropRestControl p → β := fun x =>
      f (recover (x.1, (proposalControlSplit p).symm (baseline, x.2)))
    have hg : Measurable g := hf.comp (hrecover.comp
      (measurable_fst.prodMk ((proposalControlSplit p).symm.measurable.comp
        (measurable_const.prodMk measurable_snd))))
    have hpoint : ∀ᵐ x ∂ν.prod (ContinuousLearningRows.timeControlLaw p),
        (f (recover x), physicalProposalBit rate (currentControl t (recover x))) =
          (g (x.1, (proposalControlSplit p x.2).2), physicalProposalBit rate x.2) := by
      have hmem : ∀ᵐ x ∂ν.prod (ContinuousLearningRows.timeControlLaw p), x.1 ∈ S :=
        Measure.quasiMeasurePreserving_fst.ae
          (ae_restrict_mem
            (ReferenceFixedTimeSourceControlCoupling.measurableSet_fixedControlRemainderStratum
              p q t))
      filter_upwards [hmem] with x hx
      let z := recover x
      have hq : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z = q :=
        ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
          p q t x.2 x.1 hx
      have hcontrol : currentControl t z = x.2 := by
        change (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 t = x.2
        rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
          hq]
        exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_control p q t x.2 x.1
      have hrest : (e z).2 = x.1 := congrArg Prod.snd (e.apply_symm_apply (x.2, x.1))
      have hbaseline : (proposalControlSplit p).symm
          (baseline, (proposalControlSplit p x.2).2) =
            replaceProposalScalar p x.2 baseline := by
        have h := proposalControlSplit_symm_replace p baseline
          (proposalControlSplit p x.2).1 (proposalControlSplit p x.2).2
        simpa only [Prod.mk.eta, MeasurableEquiv.symm_apply_apply] using h
      have hreplace : recover
          (x.1, (proposalControlSplit p).symm (baseline, (proposalControlSplit p x.2).2)) =
            replaceSelectedProp t z baseline := by
        dsimp only [recover]
        rw [hbaseline]
        have h := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
          p q t z (replaceProposalScalar p x.2 baseline) hq
        change e.symm (_, (e z).2) = _ at h
        rw [hrest] at h
        exact h.trans (congrArg
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z)
          (congrArg (fun u => replaceProposalScalar p u baseline) hcontrol.symm))
      apply Prod.ext
      · change f z = f (recover _)
        rw [hreplace]
        exact (hinvariant z baseline).symm
      · exact congrArg (physicalProposalBit rate) hcontrol
    have hjoint : (μq q).map
        (fun z => (f z, physicalProposalBit rate (currentControl t z))) =
        ((ν.prod (proposalRestControlLaw p)).map g).prod (proposalBitLaw rate) := by
      calc
        _ = (ν.prod (ContinuousLearningRows.timeControlLaw p)).map
            (fun x => (f (recover x), physicalProposalBit rate (currentControl t (recover x)))) := by
          rw [← hrecoverLaw, Measure.map_map (hf.prodMk hbit) hrecover]
          rfl
        _ = (ν.prod (ContinuousLearningRows.timeControlLaw p)).map
            (fun x => (g (x.1, (proposalControlSplit p x.2).2),
              physicalProposalBit rate x.2)) := Measure.map_congr hpoint
        _ = _ := proposalSplit_joint_pushforward ν g hg rate
    have hmarginal : (μq q).map f = (ν.prod (proposalRestControlLaw p)).map g := by
      have h := congrArg (Measure.map Prod.fst) hjoint
      rw [Measure.map_map measurable_fst (hf.prodMk hbit), Measure.map_fst_prod,
        measure_univ, one_smul] at h
      exact h
    rw [hjoint, hmarginal]
  have hdisjoint : Pairwise (fun q r => Disjoint (strata q) (strata r)) := by
    intro q r hqr
    apply Set.disjoint_left.mpr
    intro z hq hr
    exact hqr (hq.symm.trans hr)
  have hcover : (⋃ q : Fin (M p), strata q) = Set.univ := by
    ext z
    constructor
    · intro _
      trivial
    · intro _
      exact Set.mem_iUnion.mpr
        ⟨ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z, rfl⟩
  have hsum : Measure.sum μq = μ := by
    rw [← Measure.restrict_iUnion hdisjoint
      (ReferenceFixedTimeSourceControlCoupling.measurableSet_fixedControlSourceStratum p),
      hcover, Measure.restrict_univ]
  calc
    _ = (Measure.sum μq).map
        (fun z => (f z, physicalProposalBit rate (currentControl t z))) := by rw [hsum]
    _ = Measure.sum (fun q => (μq q).map
        (fun z => (f z, physicalProposalBit rate (currentControl t z)))) :=
      Measure.map_sum (hf.prodMk hbit).aemeasurable
    _ = Measure.sum (fun q => ((μq q).map f).prod (proposalBitLaw rate)) := by
      congr 1
      funext q
      exact hstratum q
    _ = (Measure.sum (fun q => (μq q).map f)).prod (proposalBitLaw rate) :=
      (Measure.prod_sum_left _ _).symm
    _ = ((Measure.sum μq).map f).prod (proposalBitLaw rate) := by
      rw [Measure.map_sum hf.aemeasurable]
    _ = _ := by rw [hsum]

/-- The proposal split is applied to the constructed actual observer, original
H and entire nonproposal source, on the original source probability space. -/
theorem restrictedInstallationObservation_joint_proposal
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).map
        (fun z => (restrictedInstallationObservation rate rewards C_star C_h control0 k t z,
          physicalProposalBit rate (currentControl t z))) =
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).map
        (restrictedInstallationObservation rate rewards C_star C_h control0 k t)).prod
          (proposalBitLaw rate) := by
  exact originalSource_proposalFactor rate control0 t _
    (measurable_restrictedInstallationObservation rate rewards C_star C_h control0 k t)
    (restrictedInstallationObservation_replaceSelectedProp rate rewards C_star C_h control0 k t)

/-- Restricted original E/H/full-rest/actual-observer cylinders factor only
the physical proposal scalar; no recorder/FAST independence is asserted. -/
theorem installationEvent_original_joint_proposal_cylinder
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (B : Set (RetainedInstallationObservation p rate.eta)) (hB : MeasurableSet B)
    (Dset : Set Bool) (hD : MeasurableSet Dset) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
      {z | z ∈ installEvent k t ∧
        (historyAt control0 k t z, originalNonProposalSource control0 t z,
          actualRankPreProposalObserver rate rewards C_star C_h control0 t z) ∈ B ∧
        physicalProposalBit rate (currentControl t z) ∈ Dset} =
      BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ installEvent k t ∧
          (historyAt control0 k t z, originalNonProposalSource control0 t z,
            actualRankPreProposalObserver rate rewards C_star C_h control0 t z) ∈ B} *
        proposalBitLaw rate Dset := by
  classical
  let F := restrictedInstallationObservation rate rewards C_star C_h control0 k t
  have hF := measurable_restrictedInstallationObservation rate rewards C_star C_h control0 k t
  have hbit := (measurable_physicalProposalBit rate).comp
    (ReferenceSourceCurrentControlFreshness.measurable_u_t t)
  have hsome : MeasurableSet (some '' B) := by
    let e := Equiv.optionEquivSumPUnit (RetainedInstallationObservation p rate.eta)
    have heq : some '' B = e ⁻¹' (Sum.inl '' B) := by
      ext x
      cases x <;> simp [e]
    rw [heq]
    exact (comap_measurable e) (MeasurableSet.inl_image hB)
  change Measurable F at hF
  change Measurable (fun z : SourceInput p =>
    physicalProposalBit rate (currentControl t z)) at hbit
  have hjoint := congrArg (fun μ => μ ((some '' B) ×ˢ Dset))
    (restrictedInstallationObservation_joint_proposal rate rewards C_star C_h control0 k t)
  change ((BootstrapPrivateRoundStreams.sourceInputLaw p).map
    (fun z => (F z, physicalProposalBit rate (currentControl t z))))
      ((some '' B) ×ˢ Dset) =
    (((BootstrapPrivateRoundStreams.sourceInputLaw p).map F).prod (proposalBitLaw rate))
      ((some '' B) ×ˢ Dset) at hjoint
  rw [Measure.map_apply (hF.prodMk hbit) (hsome.prod hD), Measure.prod_prod,
    Measure.map_apply hF hsome] at hjoint
  have hpre : (fun z => (F z, physicalProposalBit rate (currentControl t z))) ⁻¹'
      ((some '' B) ×ˢ Dset) = {z | z ∈ installEvent k t ∧
        (historyAt control0 k t z, originalNonProposalSource control0 t z,
          actualRankPreProposalObserver rate rewards C_star C_h control0 t z) ∈ B ∧
        physicalProposalBit rate (currentControl t z) ∈ Dset} := by
    ext z
    by_cases hz : z ∈ installEvent k t <;>
      simp [F, restrictedInstallationObservation, hz]
  have hpreF : F ⁻¹' (some '' B) = {z | z ∈ installEvent k t ∧
      (historyAt control0 k t z, originalNonProposalSource control0 t z,
        actualRankPreProposalObserver rate rewards C_star C_h control0 t z) ∈ B} := by
    ext z
    by_cases hz : z ∈ installEvent k t <;>
      simp [F, restrictedInstallationObservation, hz]
  rw [hpre, hpreF] at hjoint
  exact hjoint

/-- The complete original-source joint Bernoulli law on the actual rank
installation event, with H, all nonproposal source coordinates, and the
constructed actual observer retained together. -/
theorem installationEvent_original_joint_proposal_law
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T) :
    ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)).map
        (fun z => ((historyAt control0 k t z, originalNonProposalSource control0 t z,
          actualRankPreProposalObserver rate rewards C_star C_h control0 t z),
          physicalProposalBit rate (currentControl t z))) =
      (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)).map
        (fun z => (historyAt control0 k t z, originalNonProposalSource control0 t z,
          actualRankPreProposalObserver rate rewards C_star C_h control0 t z))).prod
            (proposalBitLaw rate) := by
  let G := fun z : SourceInput p =>
    (historyAt control0 k t z, originalNonProposalSource control0 t z,
      actualRankPreProposalObserver rate rewards C_star C_h control0 t z)
  have hG : Measurable G := (measurable_history rate rewards C_star C_h control0 k t).prodMk
    ((measurable_originalNonProposalSource control0 t).prodMk
      (measurable_actualRankPreProposalObserver rate rewards C_star C_h control0 t))
  have hbit : Measurable (fun z : SourceInput p =>
      physicalProposalBit rate (currentControl t z)) :=
    (measurable_physicalProposalBit rate).comp
      (ReferenceSourceCurrentControlFreshness.measurable_u_t t)
  apply Measure.ext_prod
  intro B Dset hB hD
  rw [Measure.map_apply (hG.prodMk hbit) (hB.prod hD), Measure.prod_prod,
    Measure.map_apply hG hB, Measure.restrict_apply ((hB.prod hD).preimage (hG.prodMk hbit)),
    Measure.restrict_apply (hB.preimage hG)]
  have hleft : (fun z => (G z, physicalProposalBit rate (currentControl t z))) ⁻¹'
      (B ×ˢ Dset) ∩ installEvent k t =
        {z | z ∈ installEvent k t ∧ G z ∈ B ∧
          physicalProposalBit rate (currentControl t z) ∈ Dset} := by
    ext z
    exact ⟨fun ⟨⟨hB', hD'⟩, hE⟩ => ⟨hE, hB', hD'⟩,
      fun ⟨hE, hB', hD'⟩ => ⟨⟨hB', hD'⟩, hE⟩⟩
  have hright : G ⁻¹' B ∩ installEvent k t =
      {z | z ∈ installEvent k t ∧ G z ∈ B} := by
    ext z
    exact and_comm
  rw [hleft, hright]
  exact installationEvent_original_joint_proposal_cylinder
    rate rewards C_star C_h control0 k t B hB Dset hD

private theorem timeControl_map_physicalProposalBit :
    (ContinuousLearningRows.timeControlLaw p).map (physicalProposalBit rate) =
      proposalBitLaw rate := by
  let ν : Measure Unit := Measure.dirac ()
  have h := congrArg Measure.snd
    (proposalSplit_joint_pushforward ν
      (fun _ : Unit × PropRestControl p => ()) measurable_const rate)
  have hbit : Measurable (fun z : Unit × ContinuousLearningRows.TimeControl p =>
      physicalProposalBit rate z.2) :=
    (measurable_physicalProposalBit rate).comp measurable_snd
  rw [Measure.snd_map_prodMk (measurable_const : Measurable
      (fun _ : Unit × ContinuousLearningRows.TimeControl p => ())) hbit,
    Measure.snd_prod] at h
  have hsnd : (ν.prod (ContinuousLearningRows.timeControlLaw p)).map
      (fun z => physicalProposalBit rate z.2) =
        (ContinuousLearningRows.timeControlLaw p).map (physicalProposalBit rate) := by
    change (ν.prod (ContinuousLearningRows.timeControlLaw p)).map
      (physicalProposalBit rate ∘ Prod.snd) = _
    rw [← Measure.map_map (measurable_physicalProposalBit rate) measurable_snd,
      Measure.map_snd_prod, measure_univ, one_smul]
  exact hsnd.symm.trans h

/-- The PUBLIC installation control cylinder gives the same physical proposal
marginal, without a replacement source or an assumed output kernel. -/
theorem installationEvent_proposal_cylinder
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (Dset : Set Bool) (hD : MeasurableSet Dset) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ installEvent k t ∧ physicalProposalBit rate (currentControl t z) ∈ Dset} =
      BootstrapPrivateRoundStreams.sourceInputLaw p (installEvent k t) *
        proposalBitLaw rate Dset := by
  let e := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  let Cset := (fun x => physicalProposalBit rate (e.symm x)) ⁻¹' Dset
  have hC : MeasurableSet Cset :=
    hD.preimage ((measurable_physicalProposalBit rate).comp e.symm.measurable)
  have hmass : ((ContinuousControlSlice.assignmentLaw p.K).prod
      (ReferenceLaterOptionalControlResampling.controlRemainderLaw p)) Cset =
        proposalBitLaw rate Dset := by
    unfold ReferenceLaterOptionalControlResampling.controlRemainderLaw
    have hsplit := LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p
    rw [← hsplit.measure_preimage hC.nullMeasurableSet]
    change (ContinuousLearningRows.timeControlLaw p) (e ⁻¹' Cset) = _
    have hpre : e ⁻¹' Cset = physicalProposalBit rate ⁻¹' Dset := by
      ext u
      simp only [Cset, Set.mem_preimage, MeasurableEquiv.symm_apply_apply]
    rw [hpre, ← Measure.map_apply (measurable_physicalProposalBit rate) hD,
      timeControl_map_physicalProposalBit]
  have h := installation_controlSplit_cylinder rate rewards C_star C_h control0 k t
    Set.univ MeasurableSet.univ Cset hC
  have hpre : {z | z ∈ installEvent k t ∧ z ∈ (Set.univ : Set (SourceInput p))} ∩
      (fun z => e (currentControl t z)) ⁻¹' Cset =
        {z | z ∈ installEvent k t ∧ physicalProposalBit rate (currentControl t z) ∈ Dset} := by
    ext z
    simp only [Cset, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_univ, and_true,
      Set.mem_preimage, MeasurableEquiv.symm_apply_apply]
  rw [hpre, hmass] at h
  simpa only [Set.mem_univ, and_true, Set.ofPred_mem_eq] using h

/-- The false atom is exactly the complement of the strict physical hazard. -/
theorem proposalBitLaw_false :
    proposalBitLaw rate {false} =
      ENNReal.ofReal (1 - FollowerCutoffScan.proposalHazard p rate.eta.val) := by
  have hfalse : ({false} : Set Bool) = {true}ᶜ := by
    ext b
    cases b <;> simp
  rw [hfalse, measure_compl (measurableSet_singleton true) (measure_ne_top _ _),
    measure_univ, proposalBitLaw_true, ENNReal.ofReal_sub 1
      (physicalProposalThreshold_bounds rate).1.le, ENNReal.ofReal_one]

/-- Both original E-restricted atoms have the physical hazard h = 4*m*eta.
Zero-mass installation events remain unnormalized. -/
theorem installationEvent_proposal_true_false
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
      {z | z ∈ installEvent k t ∧ physicalProposalBit rate (currentControl t z) = true} =
        BootstrapPrivateRoundStreams.sourceInputLaw p (installEvent k t) *
          ENNReal.ofReal (4 * (p.m : ℝ) * rate.eta.val) ∧
    BootstrapPrivateRoundStreams.sourceInputLaw p
      {z | z ∈ installEvent k t ∧ physicalProposalBit rate (currentControl t z) = false} =
        BootstrapPrivateRoundStreams.sourceInputLaw p (installEvent k t) *
          ENNReal.ofReal (1 - 4 * (p.m : ℝ) * rate.eta.val) := by
  constructor
  · simpa only [Set.mem_singleton_iff, proposalBitLaw_true,
      FollowerCutoffScan.proposalHazard] using
      (installationEvent_proposal_cylinder rate rewards C_star C_h control0 k t
        {true} (measurableSet_singleton true))
  · simpa only [Set.mem_singleton_iff, proposalBitLaw_false,
      FollowerCutoffScan.proposalHazard] using
      (installationEvent_proposal_cylinder rate rewards C_star C_h control0 k t
        {false} (measurableSet_singleton false))

end Bandits.Support.ReferenceRankInstallationPostUpdateProposalLaw

end
