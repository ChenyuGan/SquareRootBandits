/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteInstallationCollectionPrefixNumericalTruth

import Mathlib.Tactic

/-!
# Original-calendar continuing-live recorder law

The actual cell is read from the original source record at the selected
calendar date. Its outer absence, a present bottom marker, and a present arm
marker remain distinct.

Source evidence: ZIP4 `04_slow_fast_learner.tex:157-188,218-288`,
`06_interruptions.tex:355-426`, and `appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open ReferenceSourcePrefixHistoryFiltration (actualRecord sourcePrefix sourcePrefixFiltration)
open ReferenceFixedTimeSourceControlCoupling (replaceSourceControl)
open scoped Classical BigOperators

open ReferenceLaterLiveNumericalReadout (ordinaryData preparedOrdinary preparedStates preparedMemories
  prepared_configuration selection_choiceValid laterLiveReadout laterLiveReadout_some laterLiveReadout_numerical
  source_record_prefix laterLiveReadout_domain)
open ReferenceFirstWindowNumericalStream (sourceCell sourceCell_quantizedArrival sourceArm sourceWeights
  sourceWeights_pos sourceWeights_lower sourceWeights_upper ActualLiveSourceCell actualFirstLiveSeed)
open ReferenceFirstCollectionRenewalNextRecordingPriorView (dispatchTag dispatchTag_congr downView_congr
  configurationStatus preparedStatusCode_eq measurable_preparedStatusCode measurable_dispatchTag
  ordinary_preparation_congr LiveTag)
open ReferenceCalendarLaterSamplerOutputSections (actualRecord_fields)
open ReferenceActivePhysicalStep (Selection RoundInput prepare dispatch liveRegistersAt liveInput liveRecordingInput)

open ReferenceCoordinatorRecorderCallCorrespondence (selectionAt_eq selectionOfArm actual_call_frames)
open ReferenceContinuingRecordingFastPair (physicalMarkerOnRecord candidatePhysicalMarker candidatePhysicalFastPair)
open ReferenceContinuingDataCandidateLogging (candidateInput candidateRecord)
open ReferenceContinuingLiveSlicePreparation (inputAtControl inputAtControl_actual liveSliceWeights liveSliceSnapshot)
open ReferenceActiveDataOwnership (choiceSnapshot)
open ReferenceFirstCollectionOldRecorderFoundation (incomingPayload? incomingAmplitude? incomingRates?
  incomingAmplitudeValue_measurable roundedReward_bounds roundedReward)

namespace Bandits.Support.ReferenceOriginalCalendarContinuingLiveRecorderLaw

local instance optionMeasurableSpace {Y : Type*} [MeasurableSpace Y] :
    MeasurableSpace (Option Y) := LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance optionSingleton {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y] :
    MeasurableSingletonClass (Option Y) := by
  constructor
  intro o
  let e := Equiv.optionEquivSumPUnit Y
  have hset : e ⁻¹' {e o} = {o} := by
    ext x
    exact e.injective.eq_iff
  rw [← hset]
  apply comap_measurable e
  cases he : e o with
  | inl y => simpa only [Set.image_singleton] using (measurableSet_singleton y).inl_image (β := PUnit)
  | inr u => simpa only [Set.image_singleton] using (measurableSet_singleton u).inr_image (α := Y)

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "mu" => sourceInputLaw p
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
local notation "Cell" => RecordedQueueRun.RoundInput p.K

/-- The actual original-calendar record, retaining every absent branch. -/
def actualRecordAt (q : Fin p.T) (z : X) : Option Record := actualRecord rate rewards C_star C_h q z

/-- The continuing-live domain keeps actual incoming state and the literal
zero-start readout test together. A selected cell is retained only on this
domain; failed, absent, and cutoff selections remain outside it. -/
def actualDomain (q : Fin p.T) : Set X := {z | ∃ r : Record, actualRecordAt rate rewards C_star C_h q z = some r ∧
    (∃ regs owned base, r.input.state.coordinator = .live regs owned base) ∧ (laterLiveReadout 0 r).isSome = true}

/-- The optional cell is the same actual record's same readout-0 result. -/
def actualCell (q : Fin p.T) (z : X) : Option Cell := (actualRecordAt rate rewards C_star C_h q z).bind
    (laterLiveReadout 0)

/-- The actual marker preserves outer absence and a present bottom marker. -/
def actualMarker (q : Fin p.T) (z : X) : Option (Option (Fin p.K)) :=
  (actualCell rate rewards C_star C_h q z).map fun c => c.recordedArm

/-- The exact numerical parameters of the same present actual cell. -/
def actualParameters (q : Fin p.T) (z : X) : Option (Bool × (Fin p.K → ℝ)) :=
  (actualCell rate rewards C_star C_h q z).map fun c => (c.enabled, c.rate)

/-- The literal zero extension of the actual normalized integer arrival, gated
only by the actual readout domain. -/
def actualArrival (q : Fin p.T) (a : Fin p.K) : X → ℝ := (actualDomain rate rewards C_star C_h q).indicator (fun z =>
    match actualCell rate rewards C_star C_h q z with
    | none => 0
    | some c =>
        (RecordedQueueRun.quantizedArrival Q c a : ℝ) / (rate.n : ℝ))

/-- Indicator of the actual present marker atom on the continuing-live domain.
The outer domain gate is deliberately separate from marker bottom. -/
def markerTest (q : Fin p.T) (o : Option (Option (Fin p.K))) (z : X) : ℝ :=
  (actualDomain rate rewards C_star C_h q).indicator
    (fun z => if actualMarker rate rewards C_star C_h q z = o then 1 else 0) z

/-- The conditional marker coefficient computed from the rate vector of the
same actual enabled cell on the actual domain. -/
def markerCoefficient (q : Fin p.T) (o : Option (Option (Fin p.K))) (z : X) : ℝ :=
  if z ∈ actualDomain rate rewards C_star C_h q then
    match actualParameters rate rewards C_star C_h q z with
    | none => 0
    | some (enabled, xi) =>
        ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters o (some (enabled, xi))
  else 0

/-- Actual payload arm rate on D, extended by zero outside D. -/
def actualRate (q : Fin p.T) (a : Fin p.K) (z : X) : ℝ := if z ∈ actualDomain rate rewards C_star C_h q then
    match actualParameters rate rewards C_star C_h q z with
    | none => 0
    | some (_, xi) => xi a
  else 0

theorem markerTest_off_domain (q : Fin p.T) (o : Option (Option (Fin p.K))) (z : X)
    (hz : z ∉ actualDomain rate rewards C_star C_h q) :
    markerTest rate rewards C_star C_h q o z = 0 := by
  simp [markerTest, hz]

theorem actualCell_data (q : Fin p.T) (z : X) (hz : z ∈ actualDomain rate rewards C_star C_h q) :
    ∃ (r : Record) (regs : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters regs) (base : Fin (p.m - 1) → ℕ) (c : Cell)
      (selected : Selection r.input), actualRecordAt rate rewards C_star C_h q z = some r ∧
      r.input.state.coordinator = .live regs owned base ∧ laterLiveReadout 0 r = some c ∧
      actualCell rate rewards C_star C_h q z = some c ∧ c.enabled = true ∧
      r.output.preparation.coordinator.selection = some selected ∧ c.rate = selected.view.payload.rate ∧
      (c.reward = fun a => ((rewards q a).val : ℝ) / (D p : ℝ)) ∧
      (∀ a, RecordedQueueRun.quantizedArrival Q c a = if c.recordedArm = some a then
          Nat.floor ((D p : ℝ) * rate.eta.val * (((rewards q a).val : ℝ) / (D p : ℝ)) / selected.view.payload.rate a)
        else 0) := by
  rcases hz with ⟨r, hr, hlive, hsome⟩
  rcases hlive with ⟨regs, owned, base, hcoord⟩
  cases hread : laterLiveReadout 0 r with
  | none => simp [hread] at hsome
  | some c =>
      obtain ⟨henabled, selected, hselected, hreward, hrate, hfloor⟩ := laterLiveReadout_numerical 0 r c hread
      obtain ⟨hrows, hJ, htime, hwhole⟩ := actualRecord_fields rate rewards C_star C_h q z r hr
      refine ⟨r, regs, owned, base, c, selected, hr, hcoord, hread, ?_, henabled, hselected, ?_, ?_, ?_⟩
      · change (actualRecordAt rate rewards C_star C_h q z).bind (laterLiveReadout 0) = some c
        rw [hr]
        simp [hread]
      · exact hrate
      · simpa only [htime, hwhole] using hreward
      · intro a
        simpa only [htime, hwhole] using hfloor a

theorem actualArrival_eq_quantizedValue (q : Fin p.T) (a : Fin p.K) (z : X)
    (hz : z ∈ actualDomain rate rewards C_star C_h q)
    (hm : (actualCell rate rewards C_star C_h q z).bind (fun c => c.recordedArm) = some a) :
    actualArrival rate rewards C_star C_h q a z = QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
        (actualRate rate rewards C_star C_h q a z)
        ((rewards q a).val / (D p : ℝ)) := by
  obtain ⟨r, regs, owned, base, c, selected, hr, hcoord, hread, hcell,
    henabled, hselected, hrate, hreward, hfloor⟩ := actualCell_data rate rewards C_star C_h q z hz
  have hm' : c.recordedArm = some a := by simpa only [hcell, Option.bind_some] using hm
  simp only [actualArrival, Set.indicator_of_mem hz, hcell, actualRate, ite_eq_left hz,
    actualParameters, Option.map_some, hrate, hfloor a, hm', ite_true,
    QuantizedRecordingMoments.quantizedValue, QuantizedRecordingMoments.quantizedIndex, rate.n_scale]

theorem actualIncoming_replace (control0 : TimeControl p) (q : Fin p.T) (z : X) (c : TimeControl p) :
    ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q
        (replaceSourceControl p q (sourcePrefix control0 q.val z) c) := by
  rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 q z,
    ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 q
      (replaceSourceControl p q (sourcePrefix control0 q.val z) c),
    ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current,
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 q.val q.val le_rfl z]

theorem actualRecords_state_congr (q : Fin p.T) (z z' : X) (r r' : Record)
    (hr : actualRecordAt rate rewards C_star C_h q z = some r)
    (hr' : actualRecordAt rate rewards C_star C_h q z' = some r')
    (hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z') :
    r.input.state = r'.input.state := by
  have he : ReferenceActivePhysicalStepMeasurability.encodeState r.input.state =
      ReferenceActivePhysicalStepMeasurability.encodeState r'.input.state := by
    change (actualRecordAt rate rewards C_star C_h q z).map _ =
      (actualRecordAt rate rewards C_star C_h q z').map _ at hin
    rw [hr, hr'] at hin
    exact Option.some.inj hin
  simpa only [ReferenceActivePhysicalStepMeasurability.decodeState_encodeState]
    using congrArg ReferenceActivePhysicalStepMeasurability.decodeState he

theorem actualCell_recordingMap (q : Fin p.T) (z : X) (hz : z ∈ actualDomain rate rewards C_star C_h q) :
    ∃ (r : Record) (c : Cell) (selected : Selection r.input) (ho : preparedOrdinary r),
      actualRecordAt rate rewards C_star C_h q z = some r ∧ laterLiveReadout 0 r = some c ∧
      r.output.preparation.coordinator.selection = some selected ∧
      c = sourceCell r selected.view.payload selected.view.pendingAtChoice (preparedStates r ho)
        selected.view.complementWeights selected.view.cutoff
        (selection_choiceValid selected) ∧
      c.recordedArm = SnapshotRecordingKernel.recordingMap p (.live selected.view.payload.assignment
          { missing := selected.view.pendingAtChoice
            status := fun i =>
              (preparedStates r ho i).status })
        true rate.eta.val rate.eta.property rate.sourceCap selected.view.payload.anchor
        (sourceWeights selected.view.payload selected.view.complementWeights)
        selected.view.payload.anchor_pos
        (sourceWeights_pos selected.view.payload selected.view.complementWeights selected.view.cutoff r.input.time
          (selection_choiceValid selected))
        (sourceWeights_lower selected.view.payload selected.view.complementWeights selected.view.cutoff r.input.time
          (selection_choiceValid selected))
        (sourceWeights_upper selected.view.payload selected.view.complementWeights selected.view.cutoff r.input.time
          (selection_choiceValid selected))
        (r.input.row.2 r.input.time).1 := by
  obtain ⟨r, regs, owned, base, c, selected, hr, hcoord, hread, hcell,
    henabled, hselected, hrate, hreward, hfloor⟩ := actualCell_data rate rewards C_star C_h q z hz
  obtain ⟨selected', ho, hselection, hsigma, hlive, hsource⟩ := laterLiveReadout_some 0 r c hread
  have hselected' : selected' = selected := by
    exact Option.some.inj (hselection.symm.trans hselected)
  subst selected'
  refine ⟨r, c, selected, ho, hr, hread, hselection, hsource, ?_⟩
  have hmarker := congrArg (fun x : Cell => x.recordedArm) hsource
  simpa only [sourceCell, sourceArm] using hmarker

theorem actualRecord_suffix_index (q : Fin p.T) (z : X) (r : Record)
    (hr : actualRecordAt rate rewards C_star C_h q z = some r) :
    ∃ k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] = r := by
  change actualRecord rate rewards C_star C_h q z = some r at hr
  unfold actualRecord at hr
  split_ifs at hr with hs
  obtain ⟨hk, heq⟩ := List.getElem?_eq_some_iff.mp hr
  exact ⟨⟨_, hk⟩, heq⟩

theorem actualRecord_ordinary_prepare (q : Fin p.T) (z : X) (r : Record)
    (hr : actualRecordAt rate rewards C_star C_h q z = some r) (i : Fin (p.m - 1)) :
    ∃ state memory choice, r.input.state.followers i = .ordinary state memory ∧
      ActiveFollowerLifecycle.localStateDomainValid state ∧
      ActiveFollowerLifecycle.startRound rate.eta r.input.time state memory = .ok (choice, memory) ∧
      (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary choice memory ∧
      ActiveFollowerLifecycle.localStateDomainValid choice ∧
      ActiveFollowerDownAcceptance.operationInputDomain p rate choice := by
  obtain ⟨k, hk⟩ := actualRecord_suffix_index rate rewards C_star C_h q z r hr
  obtain ⟨state, memory, hinput, _⟩ := ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_input
      (rate := rate) rewards C_star C_h z k i
  obtain ⟨choice, hdomain, hstart, hchoice, hchoiceDomain, hoperation⟩ :=
    ReferenceCompleteFollowerPreparation.complete_ordinary_input_prepare
      (rate := rate) rewards C_star C_h z k i state memory hinput
  rw [hk] at hinput hstart hchoice
  exact ⟨state, memory, choice, hinput, hdomain, hstart, hchoice, hchoiceDomain, hoperation⟩

theorem actualRecord_preparedOrdinary (q : Fin p.T) (z : X) (r : Record)
    (hr : actualRecordAt rate rewards C_star C_h q z = some r) :
    preparedOrdinary r := by
  intro i
  obtain ⟨state, memory, choice, _, _, _, hchoice, _, _⟩ :=
    actualRecord_ordinary_prepare rate rewards C_star C_h q z r hr i
  change (ordinaryData (ReferenceFollowerFixedReply.actualChoice r i).configuration).isSome = true
  rw [hchoice]
  rfl

theorem actualPrepared_replace (control0 : TimeControl p) (q : Fin p.T) (z : X) (c : TimeControl p) (r r' : Record)
    (hr : actualRecordAt rate rewards C_star C_h q z = some r) (hr' : actualRecordAt rate rewards C_star C_h q
      (replaceSourceControl p q (sourcePrefix control0 q.val z) c) = some r') :
    ∃ (ho : preparedOrdinary r) (ho' : preparedOrdinary r'), preparedStates r ho = preparedStates r' ho' ∧
      preparedMemories r ho = preparedMemories r' ho' := by
  let ho := actualRecord_preparedOrdinary rate rewards C_star C_h q z r hr
  let ho' := actualRecord_preparedOrdinary rate rewards C_star C_h q _ r' hr'
  have hs := actualRecords_state_congr rate rewards C_star C_h q z _ r r' hr hr'
    (actualIncoming_replace rate rewards C_star C_h control0 q z c)
  have ht := (actualRecord_fields rate rewards C_star C_h q z r hr).2.2.1.trans (actualRecord_fields
      rate rewards C_star C_h q _ r' hr').2.2.1.symm
  have hp (i : Fin (p.m - 1)) := ordinary_preparation_congr r.input r'.input hs ht i (preparedStates r ho i)
      (preparedStates r' ho' i) (preparedMemories r ho i) (preparedMemories r' ho' i) (by
        have h := prepared_configuration r ho i
        rw [r.output_eq] at h
        exact h)
      (by
        have h := prepared_configuration r' ho' i
        rw [r'.output_eq] at h
        exact h)
  exact ⟨ho, ho', funext (fun i => (hp i).1), funext (fun i => (hp i).2)⟩

theorem actualReadout_downView_guard (q : Fin p.T) (z : X) (r : Record)
    (hr : actualRecordAt rate rewards C_star C_h q z = some r) :
    (laterLiveReadout 0 r).isSome = true ↔ ∃ v, (dispatch r.input).downView = some v ∧ 0 < v.payload.sigma.val ∧
        CoordinatorLocalArmChoice.assignmentIsLive v.payload v.cutoff r.input.time := by
  have ho := actualRecord_preparedOrdinary rate rewards C_star C_h q z r hr
  have hs : (dispatch r.input).selection = r.output.preparation.coordinator.selection := by
    rw [r.output_eq]
    rfl
  rw [ReferenceActivePhysicalStep.DispatchCut.downView, hs, laterLiveReadout_domain]
  unfold ReferenceLaterLiveNumericalReadout.laterLiveDomain
  cases hsel : r.output.preparation.coordinator.selection with
  | none => simp
  | some selected => simp [ho]

theorem actualDomain_of_incoming_eq (q : Fin p.T) (z z' : X)
    (hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z')
    (hz : z ∈ actualDomain rate rewards C_star C_h q) :
    z' ∈ actualDomain rate rewards C_star C_h q := by
  obtain ⟨r, hr, ⟨regs, owned, base, hlive⟩, hread⟩ := hz
  have hsome : (actualRecordAt rate rewards C_star C_h q z').isSome = true := by
    have hi := congrArg Option.isSome hin
    change ((actualRecordAt rate rewards C_star C_h q z).map _).isSome =
      ((actualRecordAt rate rewards C_star C_h q z').map _).isSome at hi
    simpa only [hr, Option.map_some, Option.isSome_some, Option.isSome_map] using hi.symm
  cases hr' : actualRecordAt rate rewards C_star C_h q z' with
  | none => simp only [hr', Option.isSome_none, Bool.false_eq_true] at hsome
  | some r' =>
    have hs := actualRecords_state_congr rate rewards C_star C_h q z z' r r' hr hr' hin
    have ht := (actualRecord_fields rate rewards C_star C_h q z r hr).2.2.1.trans (actualRecord_fields
        rate rewards C_star C_h q z' r' hr').2.2.1.symm
    have hv := downView_congr r.input r'.input hs ht (by rw [hlive]; trivial)
    refine ⟨r', hr', ⟨regs, owned, base, by rw [← hs]; exact hlive⟩, ?_⟩
    apply (actualReadout_downView_guard rate rewards C_star C_h q z' r' hr').mpr
    obtain ⟨v, hview, hsigma, hassign⟩ := (actualReadout_downView_guard rate rewards C_star C_h q z r hr).mp hread
    exact ⟨v, hv.symm.trans hview, hsigma, by rw [← ht]; exact hassign⟩

theorem actualDomain_replace (control0 : TimeControl p) (q : Fin p.T) (z : X) (c : TimeControl p) :
    replaceSourceControl p q (sourcePrefix control0 q.val z) c ∈ actualDomain rate rewards C_star C_h q ↔
      z ∈ actualDomain rate rewards C_star C_h q := by
  have hi := actualIncoming_replace rate rewards C_star C_h control0 q z c
  exact ⟨actualDomain_of_incoming_eq rate rewards C_star C_h q _ z hi.symm,
    actualDomain_of_incoming_eq rate rewards C_star C_h q z _ hi⟩

theorem mem_liveSet_iff (x : RoundInput p rate) : x ∈ ReferenceFirstLiveCoordinatorStepMeasurability.liveSet ↔
      ∃ regs owned base, x.state.coordinator = .live regs owned base := by
  cases h : x.state.coordinator <;>
    simp [ReferenceFirstLiveCoordinatorStepMeasurability.liveSet, ReferenceActivePhysicalStepMeasurability.encodeState,
      ReferenceActivePhysicalStepMeasurability.encodeCoordinator, h]

theorem actualRecord_none_iff (q : Fin p.T) (z : X) : actualRecordAt rate rewards C_star C_h q z = none ↔
      q.val < ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
  unfold actualRecordAt actualRecord
  split_ifs with hs
  · rw [List.getElem?_eq_none_iff, ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    have hq := q.isLt
    omega
  · simp only [true_iff]
    omega

theorem measurable_actualReadout {Y : Type*} [MeasurableSpace Y] (f : Record → Option Y)
    (hf : ∀ k : ℕ, Measurable (fun x :
      ReferenceCompleteSuffixInputMeasurability.IndexedSource rate rewards C_star C_h k =>
      f ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate x.val rewards C_star C_h).get ⟨k, x.property⟩))) (q : Fin p.T) :
    Measurable (fun z : X => (actualRecordAt rate rewards C_star C_h q z).bind f) := by
  intro B hB
  let E (k : ℕ) : Set (ReferenceCompleteSuffixInputMeasurability.IndexedSource
      rate rewards C_star C_h k) := {x |
    ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h ≤ q.val ∧
    q.val - ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h = k ∧
    f ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate x.val rewards C_star C_h).get ⟨k, x.property⟩) ∈ B}
  have hE (k : ℕ) : MeasurableSet (E k) := by
    have hs := (ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart rate rewards C_star C_h).comp
      (measurable_subtype_coe (p := fun z : X => k < (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).length))
    exact (measurableSet_le hs measurable_const).inter
      ((measurableSet_eq_fun (measurable_const.sub hs) measurable_const).inter (hf k hB))
  have hnone : MeasurableSet {z : X | actualRecordAt rate rewards C_star C_h q z = none} := by
    simp_rw [actualRecord_none_iff rate rewards C_star C_h]
    exact measurableSet_lt measurable_const
      (ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart rate rewards C_star C_h)
  have heq : {z : X | (actualRecordAt rate rewards C_star C_h q z).bind f ∈ B} =
      (if none ∈ B then {z | actualRecordAt rate rewards C_star C_h q z = none} else ∅) ∪
        ⋃ k : ℕ, Subtype.val '' E k := by
    ext z
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hz
      cases hr : actualRecordAt rate rewards C_star C_h q z with
      | none =>
        left
        have hb : none ∈ B := by simpa only [hr, Option.bind_none] using hz
        simp only [hb, ite_true, Set.mem_ofPred_eq, hr]
      | some r =>
        right
        have hb : f r ∈ B := by simpa only [hr, Option.bind_some] using hz
        change actualRecord rate rewards C_star C_h q z = some r at hr
        unfold actualRecord at hr
        split_ifs at hr with hs
        obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.mp hr
        refine Set.mem_iUnion.mpr ⟨_, ⟨⟨z, hk⟩, ⟨hs, rfl, ?_⟩, rfl⟩⟩
        simpa only [List.get_eq_getElem, he] using hb
    · rintro (hz | hz)
      · split_ifs at hz with hb
        · simp only [Set.mem_ofPred_eq] at hz
          simpa only [hz, Option.bind_none] using hb
        · exact False.elim hz
      · obtain ⟨k, x, ⟨hs, hi, hb⟩, rfl⟩ := Set.mem_iUnion.mp hz
        simpa only [actualRecordAt, actualRecord, ite_eq_left hs, hi,
          List.getElem?_eq_getElem x.property, Option.bind_some, List.get_eq_getElem] using hb
  change MeasurableSet {z : X | (actualRecordAt rate rewards C_star C_h q z).bind f ∈ B}
  rw [heq]
  have hleft : MeasurableSet
      (if none ∈ B then {z | actualRecordAt rate rewards C_star C_h q z = none} else ∅) := by
    by_cases hb : none ∈ B
    · rw [ite_eq_left hb]
      exact hnone
    · rw [ite_eq_right hb]
      exact MeasurableSet.empty
  exact hleft.union (MeasurableSet.iUnion fun k =>
      (ReferenceCompleteSuffixInputMeasurability.measurableSet_indexDomain
        rate rewards C_star C_h k).subtype_image (hE k))

theorem measurableSet_actualDomain (q : Fin p.T) :
    MeasurableSet (actualDomain rate rewards C_star C_h q) := by
  let f : Record → Option Unit := fun r =>
    if r.input ∈ ReferenceFirstLiveCoordinatorStepMeasurability.liveSet ∧
        (laterLiveReadout 0 r).isSome = true then some () else none
  have hf (k : ℕ) : Measurable (fun x :
      ReferenceCompleteSuffixInputMeasurability.IndexedSource rate rewards C_star C_h k =>
      f ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate x.val rewards C_star C_h).get ⟨k, x.property⟩)) :=
    Measurable.ite ((ReferenceFirstLiveCoordinatorStepMeasurability.measurableSet_liveSet.preimage
        (ReferenceCompleteSuffixInputMeasurability.measurable_actualRoundInputAt rate rewards C_star C_h k)).inter
        (ReferenceLaterLiveReadoutDomain.measurableSet_indexedReadoutDomain_fixed
          rate rewards C_star C_h 0 k)) measurable_const measurable_const
  have hm := measurable_actualReadout rate rewards C_star C_h f hf q
  have heq : actualDomain rate rewards C_star C_h q =
      {z | (actualRecordAt rate rewards C_star C_h q z).bind f = some ()} := by
    ext z
    cases hr : actualRecordAt rate rewards C_star C_h q z with
    | none => simp only [actualDomain, hr, reduceCtorEq, false_and, exists_false, Option.bind_none, Set.mem_ofPred_eq]
    | some r =>
      simp only [actualDomain, hr, Option.some.injEq, exists_eq_left', Option.bind_some,
        f, mem_liveSet_iff rate, Set.mem_ofPred_eq]
      split_ifs with h <;> simp_all
      exact h
  exact heq ▸ (measurableSet_singleton (some ())).preimage hm

theorem actualDomain_measurable (control0 : TimeControl p) (q : Fin p.T) :
    MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)] (actualDomain rate rewards C_star C_h q) := by
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
  have h := (measurableSet_actualDomain rate rewards C_star C_h q).preimage
    (comap_measurable (sourcePrefix control0 q.val))
  convert h using 1
  ext z
  have hi := ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 q z
  exact ⟨actualDomain_of_incoming_eq rate rewards C_star C_h q z _ hi,
    actualDomain_of_incoming_eq rate rewards C_star C_h q _ z hi.symm⟩

theorem actualViews_replace (control0 : TimeControl p) (q : Fin p.T) (z : X) (c : TimeControl p) (r r' : Record)
    (hr : actualRecordAt rate rewards C_star C_h q z = some r) (hr' : actualRecordAt rate rewards C_star C_h q
      (replaceSourceControl p q (sourcePrefix control0 q.val z) c) = some r')
    (hlive : ∃ regs owned base, r.input.state.coordinator = .live regs owned base) (selected : Selection r.input)
    (selected' : Selection r'.input) (hsel : r.output.preparation.coordinator.selection = some selected)
    (hsel' : r'.output.preparation.coordinator.selection = some selected') :
    selected'.view = selected.view := by
  have hs := actualRecords_state_congr rate rewards C_star C_h q z _ r r' hr hr'
    (actualIncoming_replace rate rewards C_star C_h control0 q z c)
  have ht := (actualRecord_fields rate rewards C_star C_h q z r hr).2.2.1.trans (actualRecord_fields
      rate rewards C_star C_h q _ r' hr').2.2.1.symm
  have hv := downView_congr r.input r'.input hs ht (by obtain ⟨_, _, _, h⟩ := hlive; rw [h]; trivial)
  have hl : (dispatch r.input).selection = some selected := by
    rw [r.output_eq] at hsel
    exact hsel
  have hr : (dispatch r'.input).selection = some selected' := by
    rw [r'.output_eq] at hsel'
    exact hsel'
  simpa only [ReferenceActivePhysicalStep.DispatchCut.downView, hl, hr,
    Option.map_some, Option.some.injEq] using hv.symm

theorem actualMarker_all_controls (control0 : TimeControl p) (q : Fin p.T)
    (z : X) (hz : z ∈ actualDomain rate rewards C_star C_h q) :
    ∃ (r : Record) (selected : Selection r.input) (ho : preparedOrdinary r),
      actualRecordAt rate rewards C_star C_h q z = some r ∧ r.output.preparation.coordinator.selection = some selected ∧
      actualParameters rate rewards C_star C_h q z = some (true, selected.view.payload.rate) ∧
      ∀ c : TimeControl p, actualMarker rate rewards C_star C_h q
          (replaceSourceControl p q (sourcePrefix control0 q.val z) c) =
          some (SnapshotRecordingKernel.recordingMap p (.live selected.view.payload.assignment
              { missing := selected.view.pendingAtChoice
                status := fun i =>
                  (preparedStates r ho i).status })
            true rate.eta.val rate.eta.property rate.sourceCap selected.view.payload.anchor
            (sourceWeights selected.view.payload selected.view.complementWeights)
            selected.view.payload.anchor_pos
            (sourceWeights_pos _ _ _ _ (selection_choiceValid selected))
            (sourceWeights_lower _ _ _ _ (selection_choiceValid selected))
            (sourceWeights_upper _ _ _ _ (selection_choiceValid selected)) c.1) ∧
        actualParameters rate rewards C_star C_h q (replaceSourceControl p q (sourcePrefix control0 q.val z) c) =
            some (true, selected.view.payload.rate) := by
  obtain ⟨r, cell, selected, ho, hr, hread, hsel, hsource, hmap⟩ :=
    actualCell_recordingMap rate rewards C_star C_h q z hz
  refine ⟨r, selected, ho, hr, hsel, ?_, ?_⟩
  · change ((actualRecordAt rate rewards C_star C_h q z).bind (laterLiveReadout 0)).map _ = _
    rw [hr]
    simp only [Option.bind_some, hread, Option.map_some]
    rw [hsource]
    rfl
  intro c
  let z' := replaceSourceControl p q (sourcePrefix control0 q.val z) c
  have hz' : z' ∈ actualDomain rate rewards C_star C_h q :=
    (actualDomain_replace rate rewards C_star C_h control0 q z c).mpr hz
  obtain ⟨r', cell', selected', ho', hr', hread', hsel', hsource', hmap'⟩ :=
    actualCell_recordingMap rate rewards C_star C_h q z' hz'
  have hlive : ∃ regs owned base, r.input.state.coordinator = .live regs owned base := by
    obtain ⟨r0, hr0, hl, _⟩ := hz
    have he : r0 = r := Option.some.inj (hr0.symm.trans hr)
    exact he ▸ hl
  have hv := actualViews_replace rate rewards C_star C_h control0 q z c r r' hr hr' hlive selected selected' hsel hsel'
  have hp : preparedStates r ho = preparedStates r' ho' := by
    obtain ⟨_, _, h, _⟩ := actualPrepared_replace rate rewards C_star C_h control0 q z c r r' hr hr'
    exact h
  have hslice : (r'.input.row.2 r'.input.time).1 = c.1 := by
    have hf := actualRecord_fields rate rewards C_star C_h q _ r' hr'
    simp only [RoundInput.row, hf.1, hf.2.1, hf.2.2.1, z', replaceSourceControl,
      ActualInitializationPhysicalStep.selectedRowIndex,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex, Function.update_self]
  have hcell' : actualCell rate rewards C_star C_h q z' = some cell' := by
    simp only [actualCell, hr', Option.bind_some, hread']
  constructor
  · change (actualCell rate rewards C_star C_h q z').map _ = _
    rw [hcell']
    simp only [Option.map_some]
    rw [hmap', hslice]
    rw [← hp]
    cases selected with
    | mk view started pending cutoff arm choice =>
      cases selected' with
      | mk view' started' pending' cutoff' arm' choice' =>
        dsimp only at hv ⊢
        cases hv
        rfl
  · have hn := laterLiveReadout_numerical 0 r' cell' hread'
    obtain ⟨hen, s, hs, _, hrate, _⟩ := hn
    have he : s = selected' := Option.some.inj (hs.symm.trans hsel')
    subst s
    change (actualCell rate rewards C_star C_h q z').map _ = _
    rw [hcell']
    simp only [Option.map_some, hen, hrate, hv]

theorem actualPrepared_payload_fields (q : Fin p.T) (z : X) (r : Record)
    (hr : actualRecordAt rate rewards C_star C_h q z = some r) (selected : Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some selected) (ho : preparedOrdinary r) :
    ∀ i, (preparedStates r ho i).status ≠ .unoccupied → (preparedStates r ho i).lastDown =
        some (selected.view.payload.downRecord i) := by
  obtain ⟨k, hk⟩ := actualRecord_suffix_index rate rewards C_star C_h q z r hr
  have hfields := ReferenceCompletePayloadChoiceChronology.complete_selected_payload_choice_fields
    (rate := rate) rewards C_star C_h z k
  rw [hk] at hfields
  obtain ⟨states, memories, hordinary, hf, _, _⟩ := hfields selected hsel
  intro i hi
  have he := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    ((prepared_configuration r ho i).symm.trans (hordinary i))
  rw [he.1] at hi ⊢
  exact hf i hi

theorem actualCell_checkedRecorder (q : Fin p.T) (z : X) (hz : z ∈ actualDomain rate rewards C_star C_h q) :
    ∃ (r : Record) (c : Cell) (selected : Selection r.input), actualRecordAt rate rewards C_star C_h q z = some r ∧
      laterLiveReadout 0 r = some c ∧ r.output.preparation.coordinator.selection = some selected ∧
      ∃ out, r.output.coordinator.recording = some out ∧
        out.gateArm = (if CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec
            (r.input.row.2 r.input.time).1) = ActiveRoundActions.coordinator p.two_le_m
          then c.recordedArm else none) ∧
        out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val selected.view.payload.anchor
          (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (r.input.rewards r.input.time j)) out.gateArm := by
  obtain ⟨r, c, selected, ho, hr, hread, hsel, hsource, _⟩ := actualCell_recordingMap rate rewards C_star C_h q z hz
  have hf := actualPrepared_payload_fields rate rewards C_star C_h q z r hr selected hsel ho
  let states := preparedStates r ho
  let memories := preparedMemories r ho
  have hordinary := prepared_configuration r ho
  have hp : r.output.preparation = prepare r.input := by
    rw [r.output_eq]
    rfl
  have hoi : ∀ i, ((prepare r.input).followers.followers i).configuration =
      .ordinary (states i) (memories i) := by rw [← hp]; exact hordinary
  have hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
      selected.view.cutoff r.input.time := by
    obtain ⟨s, _, hs, _, hl, _⟩ := laterLiveReadout_some 0 r c hread
    have he : s = selected := Option.some.inj (hs.symm.trans hsel)
    exact he ▸ hl
  obtain ⟨r0, hr0, ⟨regs, owned, base, hcoord⟩, _⟩ := hz
  have he : r0 = r := Option.some.inj (hr0.symm.trans hr)
  subst r0
  have hd : r.output.preparation.coordinator = .live regs owned base (CoordinatorRoundDispatch.dispatchLive
        (liveInput r.input regs owned base)) := by
    rw [hp]
    exact ReferenceLiveDispatchMeasurability.canonicalDispatch_live_reconstruction r.input regs owned base hcoord
  have hframes := actual_call_frames r
  rw [hd] at hsel hframes
  generalize houtcome : CoordinatorRoundDispatch.dispatchLive
    (liveInput r.input regs owned base) = outcome at hd hsel hframes
  cases outcome <;> try cases hsel
  case cutoffChosen dispatched hstart ledger hinit hledger hdomains hclock hpending hno arm =>
    change ReferenceActivePhysicalStep.selectionAt _ _ _ _ _ _ = some selected at hsel
    rw [selectionAt_eq r.input regs.payload dispatched.startResult r.input.time
      (liveRegistersAt regs r.input.time).complementWeights arm rfl] at hsel
    cases hsel
    exact False.elim (hframes.1 hlive)
  case continuingChosen dispatched hstart continuation arm =>
    change ReferenceActivePhysicalStep.selectionAt _ _ _ _ _ _ = some selected at hsel
    rw [selectionAt_eq r.input regs.payload dispatched.startResult r.input.time
      (liveRegistersAt regs r.input.time).complementWeights arm rfl] at hsel
    have hs : selected = selectionOfArm r.input regs.payload dispatched.startResult r.input.time
        (liveRegistersAt regs r.input.time).complementWeights arm rfl :=
      (Option.some.inj hsel).symm
    subst selected
    obtain ⟨out, _, hrecording, hgate, hraw⟩ :=
      ReferenceCoordinatorLiveRecording.continuing_recording_identification r.input regs owned base
        dispatched hstart continuation arm (by rw [← hp]; exact hd)
        states memories hoi hf hlive
    have henabled : decide (¬ CoordinatorRecorderComplementBridge.isFrozen (liveRecordingInput (prepare r.input)
          (liveRegistersAt regs r.input.time)
          dispatched.startResult)) = true := by
      apply decide_eq_true
      intro hfreeze
      exact (Nat.not_le_of_gt hframes.2) hfreeze.2
    have hgate0 := hgate
    rw [henabled] at hgate
    refine ⟨r, c, selectionOfArm r.input regs.payload dispatched.startResult r.input.time
      (liveRegistersAt regs r.input.time).complementWeights arm rfl, hr, hread, ?_, out, ?_, ?_, ?_⟩
    · rw [hd]
      exact selectionAt_eq r.input regs.payload dispatched.startResult r.input.time
        (liveRegistersAt regs r.input.time).complementWeights arm rfl
    · simpa only [r.output_eq] using hrecording
    · rw [hsource]
      exact hgate
    · rw [← hgate0] at hraw
      exact hraw

theorem measurable_actualNumerical (q : Fin p.T) : Measurable (fun z : X =>
    (actualCell rate rewards C_star C_h q z).map
      ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates) := by
  have h := measurable_actualReadout rate rewards C_star C_h (fun r => (laterLiveReadout 0 r).map
      ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates)
    (fun k => (ReferenceLaterLiveCalendarMeasurability.measurable_indexedNumericalReadout
      rate rewards C_star C_h k).comp (show Measurable (fun x : ReferenceCompleteSuffixInputMeasurability.IndexedSource
          rate rewards C_star C_h k => ((0 : ℕ), x)) from
          measurable_const.prodMk measurable_id)) q
  convert h using 1
  funext z
  unfold actualCell
  cases actualRecordAt rate rewards C_star C_h q z <;> rfl

theorem measurable_actualMarker (q : Fin p.T) : Measurable (actualMarker rate rewards C_star C_h q) := by
  have h := LaterAssignmentFullOutputMeasurability.measurable_optionMap
    (fun c : ReferenceLaterLiveCalendarMeasurability.NumericalCoordinates => c.2.1)
    (measurable_fst.comp measurable_snd) _ (measurable_actualNumerical rate rewards C_star C_h q)
  convert h using 1
  funext z
  simp only [Option.map_map, actualMarker]
  rfl

theorem markerTest_restore (control0 : TimeControl p) (q : Fin p.T) (o : Option (Option (Fin p.K))) (z : X) :
    markerTest rate rewards C_star C_h q o (replaceSourceControl p q (sourcePrefix control0 q.val z)
        (ReferenceSourceCurrentControlFreshness.u_t p q z)) =
      markerTest rate rewards C_star C_h q o z := by
  let c := ReferenceSourceCurrentControlFreshness.u_t p q z
  let z' := replaceSourceControl p q (sourcePrefix control0 q.val z) c
  have hd := actualDomain_replace rate rewards C_star C_h control0 q z c
  by_cases hz : z ∈ actualDomain rate rewards C_star C_h q
  · obtain ⟨r, selected, ho, hr, hsel, _, hk⟩ := actualMarker_all_controls rate rewards C_star C_h control0 q z hz
    obtain ⟨r0, cell, sel0, ho0, hr0, hread, hsel0, _, hmap⟩ := actualCell_recordingMap rate rewards C_star C_h q z hz
    have he : r0 = r := Option.some.inj (hr0.symm.trans hr)
    subst r0
    have he : sel0 = selected := Option.some.inj (hsel0.symm.trans hsel)
    subst sel0
    have hm : actualMarker rate rewards C_star C_h q z = some cell.recordedArm := by
      simp only [actualMarker, actualCell, hr, Option.bind_some, hread, Option.map_some]
    have hslice : (r.input.row.2 r.input.time).1 = c.1 := by
      have hf := actualRecord_fields rate rewards C_star C_h q z r hr
      simp only [c, ReferenceSourceCurrentControlFreshness.u_t, RoundInput.row, hf.1, hf.2.1, hf.2.2.1]
    have heq : actualMarker rate rewards C_star C_h q z' = actualMarker rate rewards C_star C_h q z := by
      rw [(hk c).1, hm, hmap, hslice]
    simp only [markerTest]
    change (actualDomain rate rewards C_star C_h q).indicator _ z' = _
    rw [Set.indicator_of_mem (hd.mpr hz), Set.indicator_of_mem hz, heq]
  · exact (markerTest_off_domain rate rewards C_star C_h q o z' (mt hd.mp hz)).trans
      (markerTest_off_domain rate rewards C_star C_h q o z hz).symm

theorem markerTest_control_integral (control0 : TimeControl p) (q : Fin p.T) (o : Option (Option (Fin p.K))) (z : X) :
    (∫ c, markerTest rate rewards C_star C_h q o (replaceSourceControl p q (sourcePrefix control0 q.val z) c)
        ∂ContinuousLearningRows.timeControlLaw p) =
      markerCoefficient rate rewards C_star C_h q o z := by
  by_cases hz : z ∈ actualDomain rate rewards C_star C_h q
  · obtain ⟨r, selected, ho, hr, hsel, hparams, hk⟩ := actualMarker_all_controls rate rewards C_star C_h control0 q z hz
    let v := selected.view
    let snapshot : ActiveRoundActions.Snapshot v.payload.assignment :=
      ⟨v.pendingAtChoice, fun i => (preparedStates r ho i).status⟩
    let f := SnapshotRecordingKernel.recordingMap p (.live v.payload.assignment snapshot) true
      rate.eta.val rate.eta.property rate.sourceCap v.payload.anchor
      (sourceWeights v.payload v.complementWeights)
      v.payload.anchor_pos
      (sourceWeights_pos _ _ _ _ (selection_choiceValid selected))
      (sourceWeights_lower _ _ _ _ (selection_choiceValid selected))
      (sourceWeights_upper _ _ _ _ (selection_choiceValid selected))
    have hf : Measurable f := SnapshotRecordingKernel.measurable_recordingMap p _ _ _ _ _ _ _ _ _ _ true
    let S : Set (TimeControl p) := {c | some (f c.1) = o}
    have hS : MeasurableSet S := (measurableSet_singleton o).preimage
      ((measurable_of_countable (some : Option (Fin p.K) → Option (Option (Fin p.K)))).comp (hf.comp measurable_fst))
    have htest : (fun c => markerTest rate rewards C_star C_h q o
        (replaceSourceControl p q (sourcePrefix control0 q.val z) c)) =
        S.indicator (fun _ => (1 : ℝ)) := by
      funext c
      rw [markerTest, Set.indicator_of_mem
        ((actualDomain_replace rate rewards C_star C_h control0 q z c).mpr hz), (hk c).1]
      simp only [S, f, v, snapshot, Set.indicator_apply, Set.mem_ofPred_eq]
    have hm (a : Option (Fin p.K)) : (ContinuousLearningRows.timeControlLaw p) {c | f c.1 = a} =
          (ContinuousControlSlice.sliceLaw p.m p.K) {x | f x = a} := by
      rw [← ContinuousLearningRows.map_slice p, Measure.map_apply measurable_fst
        (show MeasurableSet {x | f x = a} from (measurableSet_singleton a).preimage hf)]
      rfl
    rw [htest, integral_indicator_const (1 : ℝ) hS, smul_eq_mul, mul_one, markerCoefficient, ite_eq_left hz, hparams]
    cases o with
    | none => simp only [S, reduceCtorEq, Set.ofPred_false, measureReal_empty,
        ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
    | some a =>
      simp only [S, Option.some.injEq, measureReal_def, hm]
      cases a with
      | none =>
        simp only [ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
        simp_rw [selected.view.payload.rate_eq_canonical]
        change ((ContinuousControlSlice.sliceLaw p.m p.K) {x | _ = none}).toReal = _
        rw [SnapshotRecordingKernel.recordingMap_none_mass]
        exact ENNReal.toReal_ofReal (sub_nonneg.mpr
          (CanonicalRecordingRates.sum_xi_le_one p rate.eta.property rate.sourceCap
            v.payload.anchor v.payload.anchor_pos))
      | some a =>
        simp only [ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters,
          selected.view.payload.rate_eq_canonical]
        change ((ContinuousControlSlice.sliceLaw p.m p.K) {x | _ = some a}).toReal = _
        rw [SnapshotRecordingKernel.recordingMap_atom_mass]
        exact ENNReal.toReal_ofReal (CanonicalRecordingRates.xi_pos p rate.eta.property v.payload.anchor a).le
  · have hzero : (fun c => markerTest rate rewards C_star C_h q o
        (replaceSourceControl p q (sourcePrefix control0 q.val z) c)) = fun _ => 0 := by
      funext c
      exact markerTest_off_domain rate rewards C_star C_h q o _
        (mt (actualDomain_replace rate rewards C_star C_h control0 q z c).mp hz)
    rw [hzero, integral_zero, markerCoefficient, ite_eq_right hz]

/-- Original-source conditional arm and present-bottom law on the exact
continuing-live domain, in the exact strict-prefix filtration. -/
theorem markerTest_condExp (control0 : TimeControl p) (q : Fin p.T) (o : Option (Option (Fin p.K))) :
    mu[markerTest rate rewards C_star C_h q o | sourcePrefixFiltration control0 (q.val + 1)] =ᵐ[mu]
        markerCoefficient rate rewards C_star C_h q o := by
  let B : Set (X × TimeControl p) := {x | replaceSourceControl p q x.1 x.2 ∈ actualDomain rate rewards C_star C_h q ∧
      actualMarker rate rewards C_star C_h q (replaceSourceControl p q x.1 x.2) = o}
  have hB : MeasurableSet B := ((measurableSet_actualDomain rate rewards C_star C_h q).inter
      ((measurableSet_singleton o).preimage (measurable_actualMarker rate rewards C_star C_h q))).preimage
      (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p q)
  have htest (seed : X) (c : TimeControl p) : B.indicator (fun _ => (1 : ℝ)) (seed, c) =
        markerTest rate rewards C_star C_h q o (replaceSourceControl p q seed c) := by
    by_cases hz : replaceSourceControl p q seed c ∈ actualDomain rate rewards C_star C_h q <;>
      simp [B, markerTest, Set.indicator, hz]
  have hrestore : ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 q B =
      markerTest rate rewards C_star C_h q o := by
    funext z
    rw [ReferenceSourceCurrentControlFreshness.sourceControlTest, htest,
      ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
    exact markerTest_restore rate rewards C_star C_h control0 q o z
  have hce := ReferenceSourceCurrentControlFreshness.source_control_test_condExp control0 q B hB
  rw [hrestore] at hce
  simpa only [ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t,
    htest, ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix,
    markerTest_control_integral rate rewards C_star C_h control0 q o] using hce

/-- The arm coefficient is the actual payload rate, zero only outside D. -/
theorem marker_arm_condExp (control0 : TimeControl p) (q : Fin p.T) (a : Fin p.K) :
    mu[markerTest rate rewards C_star C_h q (some (some a)) |
      sourcePrefixFiltration control0 (q.val + 1)] =ᵐ[mu] actualRate rate rewards C_star C_h q a := by
  convert markerTest_condExp rate rewards C_star C_h control0 q (some (some a)) using 1
  funext z
  by_cases hz : z ∈ actualDomain rate rewards C_star C_h q
  · obtain ⟨r, regs, owned, base, c, selected, hr, hc, hread, hcell, hen, hs, hrate, hy, hf⟩ :=
      actualCell_data rate rewards C_star C_h q z hz
    simp only [markerCoefficient, actualRate, actualParameters, hz, ite_true, hcell, Option.map_some, hen,
      ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
  · simp only [markerCoefficient, actualRate, ite_eq_right hz]

/-- Present bottom has the complement of the entire K-arm actual rate vector. -/
theorem marker_bottom_condExp (control0 : TimeControl p) (q : Fin p.T) :
    mu[markerTest rate rewards C_star C_h q (some none) | sourcePrefixFiltration control0 (q.val + 1)] =ᵐ[mu]
      (actualDomain rate rewards C_star C_h q).indicator
        (fun z => 1 - ∑ a, actualRate rate rewards C_star C_h q a z) := by
  convert markerTest_condExp rate rewards C_star C_h control0 q (some none) using 1
  funext z
  by_cases hz : z ∈ actualDomain rate rewards C_star C_h q
  · rw [Set.indicator_of_mem hz]
    obtain ⟨r, regs, owned, base, c, selected, hr, hc, hread, hcell, hen, hs, hrate, hy, hf⟩ :=
      actualCell_data rate rewards C_star C_h q z hz
    simp only [markerCoefficient, actualRate, actualParameters, hz, ite_true, hcell, Option.map_some, hen,
      ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
  · simp only [Set.indicator_of_notMem hz, markerCoefficient, ite_eq_right hz]

theorem actualSelection_incomingPayload (q : Fin p.T) (z : X) (r : Record)
    (hr : actualRecordAt rate rewards C_star C_h q z = some r)
    (hlive : ∃ regs owned base, r.input.state.coordinator = .live regs owned base) (selected : Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some selected) :
    incomingPayload?
      rate rewards C_star C_h q z = some selected.view.payload := by
  change actualRecord rate rewards C_star C_h q z = some r at hr
  obtain ⟨regs, owned, base, hc⟩ := hlive
  have hd : r.output.preparation.coordinator = .live regs owned base (CoordinatorRoundDispatch.dispatchLive
        (liveInput r.input regs owned base)) := by
    rw [r.output_eq]
    exact ReferenceLiveDispatchMeasurability.canonicalDispatch_live_reconstruction r.input regs owned base hc
  rw [hd] at hsel
  generalize he : CoordinatorRoundDispatch.dispatchLive (liveInput r.input regs owned base) = out at hsel
  cases out <;> try cases hsel
  all_goals
    rename_i arm
    change ReferenceActivePhysicalStep.selectionAt r.input regs.payload _ r.input.time
      (liveRegistersAt regs r.input.time).complementWeights arm = some selected at hsel
    rw [selectionAt_eq r.input regs.payload _ r.input.time (liveRegistersAt regs r.input.time).complementWeights
      arm rfl] at hsel
    cases hsel
    simp only [incomingPayload?, hr, Option.bind_some, hc, ReferenceAssignmentPayloadPersistence.storedPayload,
      selectionOfArm]

theorem actualArrival_factor (q : Fin p.T) (a : Fin p.K) : actualArrival rate rewards C_star C_h q a =
      (fun z => (incomingAmplitude? rate rewards C_star C_h q a z).getD 0) *
      markerTest rate rewards C_star C_h q (some (some a)) := by
  funext z
  by_cases hz : z ∈ actualDomain rate rewards C_star C_h q
  · obtain ⟨r, regs, owned, base, c, selected, hr, hc, hread, hcell, hen, hs, hrate, hy, hf⟩ :=
      actualCell_data rate rewards C_star C_h q z hz
    have hp := actualSelection_incomingPayload rate rewards C_star C_h q z r hr ⟨regs, owned, base, hc⟩ selected hs
    have hm : actualMarker rate rewards C_star C_h q z = some c.recordedArm := by
      simp only [actualMarker, hcell, Option.map_some]
    change _ = _ * markerTest rate rewards C_star C_h q (some (some a)) z
    simp only [markerTest, Set.indicator_of_mem hz, hm]
    by_cases ha : c.recordedArm = some a
    · simp only [ha, ite_true, mul_one, incomingAmplitude?, hp, Option.map_some, Option.getD_some]
      rw [actualArrival_eq_quantizedValue rate rewards C_star C_h q a z hz (by simp only [hcell, Option.bind_some, ha])]
      congr 1
      simp only [actualRate, ite_eq_left hz, actualParameters, hcell, Option.map_some, hrate]
    · simp only [Option.some.injEq, ha, ite_false, mul_zero]
      have hf0 : RecordedQueueRun.quantizedArrival Q c a = 0 := by
        rw [hf a, ite_eq_right ha]
      simp only [actualArrival, Set.indicator_of_mem hz, hcell, hf0, Nat.cast_zero, zero_div]
  · simp only [Pi.mul_apply, markerTest_off_domain rate rewards C_star C_h q _ z hz,
      mul_zero, actualArrival, Set.indicator_of_notMem hz]

theorem markerTest_integrable (q : Fin p.T) (o : Option (Option (Fin p.K))) :
    Integrable (markerTest rate rewards C_star C_h q o) mu := by
  have ht : Measurable (markerTest rate rewards C_star C_h q o) := (Measurable.ite ((measurableSet_singleton o).preimage
      (measurable_actualMarker rate rewards C_star C_h q)) measurable_const measurable_const).indicator
      (measurableSet_actualDomain rate rewards C_star C_h q)
  apply (integrable_const (1 : ℝ)).mono' ht.aestronglyMeasurable
  filter_upwards [] with z
  by_cases hz : z ∈ actualDomain rate rewards C_star C_h q <;>
    by_cases hm : actualMarker rate rewards C_star C_h q z = o <;>
    simp [markerTest, Set.indicator, hz, hm]

theorem actualArrival_bounds (q : Fin p.T) (a : Fin p.K) (z : X) : 0 ≤ actualArrival rate rewards C_star C_h q a z ∧
      actualArrival rate rewards C_star C_h q a z ≤ 1 / beta := by
  have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
  by_cases hz : z ∈ actualDomain rate rewards C_star C_h q
  · obtain ⟨r, regs, owned, base, c, selected, hr, hc, hread, hcell, hen, hs, hrate, hy, hf⟩ :=
      actualCell_data rate rewards C_star C_h q z hz
    by_cases hm : c.recordedArm = some a
    · have hxi : actualRate rate rewards C_star C_h q a z = c.rate a := by
        simp only [actualRate, ite_eq_left hz, actualParameters, hcell, Option.map_some]
      rw [actualArrival_eq_quantizedValue rate rewards C_star C_h q a z hz
        (by simp only [hcell, Option.bind_some, hm]), hxi, ← congrFun hy a]
      exact ⟨QuantizedRecordingMoments.quantizedValue_nonneg (D p) rate.eta.val
          (c.rate a) (c.reward a) rate.eta.property,
        QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le (D p) rate.eta.val
          (c.rate a) (c.reward a) beta (D_pos p) rate.eta.property (c.rate_pos a)
          ⟨c.reward_nonneg a, c.reward_le_one a⟩ hb
          (by rw [hrate]; exact selected.view.payload.beta_le_rate a)⟩
    · have hf0 : RecordedQueueRun.quantizedArrival Q c a = 0 := by rw [hf a, ite_eq_right hm]
      simp only [actualArrival, Set.indicator_of_mem hz, hcell, hf0, Nat.cast_zero, zero_div]
      exact ⟨le_rfl, div_nonneg zero_le_one hb.le⟩
  · rw [actualArrival, Set.indicator_of_notMem hz]
    exact ⟨le_rfl, div_nonneg zero_le_one hb.le⟩

theorem actualArrival_integrable (control0 : TimeControl p) (q : Fin p.T) (a : Fin p.K) :
    Integrable (actualArrival rate rewards C_star C_h q a) mu := by
  have ha := incomingAmplitudeValue_measurable rate rewards C_star C_h control0 q a
  have ht := (markerTest_integrable rate rewards C_star C_h q (some (some a))).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (actualArrival rate rewards C_star C_h q a) mu := by
    rw [actualArrival_factor rate rewards C_star C_h q a]
    exact (ha.mono ((sourcePrefixFiltration control0).le' _) le_rfl).aestronglyMeasurable.mul ht
  apply (integrable_const (1 / beta)).mono' hmeas
  filter_upwards [] with z
  have h := actualArrival_bounds rate rewards C_star C_h q a z
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

theorem actualArrival_condExp (control0 : TimeControl p) (q : Fin p.T) (a : Fin p.K) :
    mu[actualArrival rate rewards C_star C_h q a | sourcePrefixFiltration control0 (q.val + 1)] =ᵐ[mu] fun z =>
        (incomingAmplitude?
          rate rewards C_star C_h q a z).getD 0 * actualRate rate rewards C_star C_h q a z := by
  have hp := condExp_mul_of_stronglyMeasurable_left (incomingAmplitudeValue_measurable
      rate rewards C_star C_h control0 q a).stronglyMeasurable
    (by rw [← actualArrival_factor rate rewards C_star C_h q a]
        exact actualArrival_integrable rate rewards C_star C_h control0 q a)
    (markerTest_integrable rate rewards C_star C_h q (some (some a)))
  rw [← actualArrival_factor rate rewards C_star C_h q a] at hp
  filter_upwards [hp, marker_arm_condExp rate rewards C_star C_h control0 q a] with z hz hm
  simpa only [Pi.mul_apply, hm] using hz

/-- The original conditional first moment has the source's floor loss and
unit-reward upper bound on D. -/
theorem actualArrival_condExp_bounds (control0 : TimeControl p) (q : Fin p.T) (a : Fin p.K) :
    ∀ᵐ z ∂mu, z ∈ actualDomain rate rewards C_star C_h q → ((rewards q a).val : ℝ) / (D p : ℝ) -
          actualRate rate rewards C_star C_h q a z / (rate.n : ℝ) ≤
        mu[actualArrival rate rewards C_star C_h q a | sourcePrefixFiltration control0 (q.val + 1)] z ∧
      mu[actualArrival rate rewards C_star C_h q a | sourcePrefixFiltration control0 (q.val + 1)] z ≤
        ((rewards q a).val : ℝ) / (D p : ℝ) := by
  filter_upwards [actualArrival_condExp rate rewards C_star C_h control0 q a] with z hm
  intro hz
  obtain ⟨r, regs, owned, base, c, selected, hr, hc, hread, hcell, hen, hs, hrate, hy, hf⟩ :=
    actualCell_data rate rewards C_star C_h q z hz
  have hp := actualSelection_incomingPayload rate rewards C_star C_h q z r hr ⟨regs, owned, base, hc⟩ selected hs
  have hxi : actualRate rate rewards C_star C_h q a z = selected.view.payload.rate a := by
    simp only [actualRate, ite_eq_left hz, actualParameters, hcell, Option.map_some, hrate]
  rw [hm, hxi]
  simp only [incomingAmplitude?, hp, Option.map_some, Option.getD_some]
  rw [mul_comm]
  have hreward : ((rewards q a).val : ℝ) / (D p : ℝ) ∈ Set.Icc (0 : ℝ) 1 := roundedReward_bounds rewards q a
  exact ⟨by simpa only [rate.n_scale, roundedReward] using
      (QuantizedRecordingMoments.quantizedValue_roundingError (D p) rate.eta.val
        (selected.view.payload.rate a) _ (D_pos p) rate.eta.property
        (CanonicalRecordingRates.xi_pos p rate.eta.property selected.view.payload.anchor a) hreward),
    QuantizedRecordingMoments.quantizedValue_firstMoment_le (D p) rate.eta.val
      (selected.view.payload.rate a) _ (D_pos p) rate.eta.property
      (CanonicalRecordingRates.xi_pos p rate.eta.property selected.view.payload.anchor a) hreward⟩

theorem actualRate_measurable (control0 : TimeControl p) (q : Fin p.T) (a : Fin p.K) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)] (actualRate rate rewards C_star C_h q a) := by
  let g : Option (Fin p.K → ℝ) → ℝ := fun o => match o with | none => 0 | some xi => xi a
  have hg : Measurable g := by
    convert ((measurable_pi_apply a).sumElim (measurable_const (a := (0 : ℝ)))).comp
      (comap_measurable (Equiv.optionEquivSumPUnit (Fin p.K → ℝ))) using 1
    funext o
    cases o <;> rfl
  have hm := (hg.comp (ReferenceFirstCollectionOldRecorderFoundation.incomingRates_measurable
    rate rewards C_star C_h control0 q)).indicator (actualDomain_measurable rate rewards C_star C_h control0 q)
  convert hm using 1
  funext z
  by_cases hz : z ∈ actualDomain rate rewards C_star C_h q
  · obtain ⟨r, regs, owned, base, c, selected, hr, hc, hread, hcell, hen, hs, hrate, hy, hf⟩ :=
      actualCell_data rate rewards C_star C_h q z hz
    have hp := actualSelection_incomingPayload rate rewards C_star C_h q z r hr ⟨regs, owned, base, hc⟩ selected hs
    simp only [actualRate, ite_eq_left hz, actualParameters, hcell, Option.map_some, hrate,
      Set.indicator_of_mem hz, Function.comp_apply, incomingRates?, hp, g]
  · simp only [actualRate, ite_eq_right hz, Set.indicator_of_notMem hz]

/-- The actual LIVE dispatch observation retains the full sender view and
all three prepared status codes; only the chosen arm is erased. -/
def liveObservation (x : RoundInput p rate) : Option (Option (LiveTag p) ×
      Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
      (Fin (p.m - 1) → Option (Fin 3))) :=
  if x ∈ ReferenceFirstLiveCoordinatorStepMeasurability.liveSet then
    some (dispatchTag x, (dispatch x).downView, fun i => configurationStatus rate
        ((prepare x).followers.followers i).configuration)
  else none

/-- The observer uses the actual incoming encoded state and actual local
PREPARE/dispatch projections, retaining continuous payloads and weights. -/
def actualObserver (q : Fin p.T) (z : X) :=
  (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z,
    (actualRecordAt rate rewards C_star C_h q z).bind fun r => liveObservation rate r.input)

theorem measurable_liveObservation : Measurable (liveObservation rate) := by
  have hs : Measurable (fun x : RoundInput p rate =>
      fun i => configurationStatus rate ((prepare x).followers.followers i).configuration) := by
    apply measurable_pi_iff.mpr
    intro i
    simp_rw [← preparedStatusCode_eq]
    exact (measurable_preparedStatusCode rate).comp
      (ReferenceActivePhysicalStepMeasurability.measurable_preparedFollowerCode i)
  exact Measurable.ite ReferenceFirstLiveCoordinatorStepMeasurability.measurableSet_liveSet
    (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ (measurable_dispatchTag.prodMk
        (ReferenceActiveStepCompositionMeasurability.measurable_downView.prodMk hs))) measurable_const

theorem actualObserver_of_incoming_eq (q : Fin p.T) (z z' : X)
    (hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z') :
    actualObserver rate rewards C_star C_h q z = actualObserver rate rewards C_star C_h q z' := by
  apply Prod.ext hin
  cases hr : actualRecordAt rate rewards C_star C_h q z with
  | none =>
    have hn : actualRecordAt rate rewards C_star C_h q z' = none := by
      change (actualRecordAt rate rewards C_star C_h q z).map _ =
        (actualRecordAt rate rewards C_star C_h q z').map _ at hin
      simpa only [hr, Option.map_none, eq_comm, Option.map_eq_none_iff] using hin
    simp only [actualObserver, hr, hn, Option.bind_none]
  | some r =>
    have hn : (actualRecordAt rate rewards C_star C_h q z').isSome = true := by
      change (actualRecordAt rate rewards C_star C_h q z).map _ =
        (actualRecordAt rate rewards C_star C_h q z').map _ at hin
      simpa only [hr, Option.map_some, Option.isSome_some, Option.isSome_map] using (congrArg Option.isSome hin).symm
    obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp hn
    have hs := actualRecords_state_congr rate rewards C_star C_h q z z' r r' hr hr' hin
    have ht := (actualRecord_fields rate rewards C_star C_h q z r hr).2.2.1.trans (actualRecord_fields
        rate rewards C_star C_h q z' r' hr').2.2.1.symm
    have hl : r.input ∈ ReferenceFirstLiveCoordinatorStepMeasurability.liveSet ↔
        r'.input ∈ ReferenceFirstLiveCoordinatorStepMeasurability.liveSet := by
      rw [mem_liveSet_iff, mem_liveSet_iff, hs]
    simp only [actualObserver, hr, hr', Option.bind_some, liveObservation]
    by_cases h : r.input ∈ ReferenceFirstLiveCoordinatorStepMeasurability.liveSet
    · rw [ite_eq_left h, ite_eq_left (hl.mp h)]
      have hp : (match r.input.state.coordinator with | .live .. => True | .dagger => True | _ => False) := by
        obtain ⟨_, _, _, hc⟩ := (mem_liveSet_iff rate r.input).mp h
        rw [hc]; trivial
      apply congrArg some
      apply Prod.ext
      · exact dispatchTag_congr _ _ hs ht hp
      · apply Prod.ext
        · exact downView_congr _ _ hs ht hp
        · funext i
          obtain ⟨s, m, u, hi, _, hstart, hu, _, _⟩ := actualRecord_ordinary_prepare rate rewards C_star C_h q z r hr i
          obtain ⟨s', m', u', hi', _, hstart', hu', _, _⟩ :=
            actualRecord_ordinary_prepare rate rewards C_star C_h q z' r' hr' i
          have he : s = s' ∧ m = m' := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
            (hi.symm.trans ((congrArg (fun st => st.followers i) hs).trans hi'))
          have he' : u = u' := by
            rw [← ht, ← he.1, ← he.2, hstart] at hstart'
            exact congrArg Prod.fst (Except.ok.inj hstart')
          change (r.output.preparation.followers.followers i).configuration = _ at hu
          change (r'.output.preparation.followers.followers i).configuration = _ at hu'
          rw [r.output_eq] at hu
          rw [r'.output_eq] at hu'
          change ((prepare r.input).followers.followers i).configuration = _ at hu
          change ((prepare r'.input).followers.followers i).configuration = _ at hu'
          dsimp only
          rw [hu, hu', he']
          rfl
    · rw [ite_eq_right h, ite_eq_right (mt hl.mpr h)]

theorem actualObserver_replace (control0 : TimeControl p) (q : Fin p.T) (z : X) (c : TimeControl p) :
    actualObserver rate rewards C_star C_h q z = actualObserver rate rewards C_star C_h q
      (replaceSourceControl p q (sourcePrefix control0 q.val z) c) :=
  actualObserver_of_incoming_eq rate rewards C_star C_h q z _
    (actualIncoming_replace rate rewards C_star C_h control0 q z c)

theorem actualObserver_measurable (control0 : TimeControl p) (q : Fin p.T) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)] (actualObserver rate rewards C_star C_h q) := by
  have hm : Measurable (actualObserver rate rewards C_star C_h q) :=
    (ReferenceSourcePrefixHistoryFiltration.measurable_incoming rate rewards C_star C_h q).prodMk
      (measurable_actualReadout rate rewards C_star C_h (fun r => liveObservation rate r.input)
        (fun k => measurable_liveObservation rate |>.comp
          (ReferenceCompleteSuffixInputMeasurability.measurable_actualRoundInputAt rate rewards C_star C_h k)) q)
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
  convert hm.comp (comap_measurable (sourcePrefix control0 q.val)) using 1
  funext z
  exact actualObserver_of_incoming_eq rate rewards C_star C_h q z _
    (ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 q z)

/-- The enabled increment includes zero arrivals; it vanishes only outside D. -/
def actualIncrement (q : Fin p.T) (a : Fin p.K) : X → ℝ := (actualDomain rate rewards C_star C_h q).indicator
    (fun z => actualArrival rate rewards C_star C_h q a z - 4)

theorem actualArrival_exp_integrable (control0 : TimeControl p) (q : Fin p.T) (a : Fin p.K) :
    Integrable (fun z => Real.exp (beta * actualArrival rate rewards C_star C_h q a z)) mu := by
  have hi := actualArrival_integrable rate rewards C_star C_h control0 q a
  apply (integrable_const (Real.exp 1)).mono' ((hi.aemeasurable.const_mul beta).exp.aestronglyMeasurable)
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_exp.mpr
  have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
  calc
    beta * actualArrival rate rewards C_star C_h q a z ≤ beta * (1 / beta) :=
      mul_le_mul_of_nonneg_left (actualArrival_bounds rate rewards C_star C_h q a z).2 hb.le
    _ = 1 := by field_simp

theorem actualArrival_exp_condExp_chord (control0 : TimeControl p) (q : Fin p.T) (a : Fin p.K) :
    mu[(fun z => Real.exp (beta * actualArrival rate rewards C_star C_h q a z)) |
      sourcePrefixFiltration control0 (q.val + 1)] ≤ᵐ[mu] fun z =>
        1 + (Real.exp 1 - 1) * beta * mu[actualArrival rate rewards C_star C_h q a |
            sourcePrefixFiltration control0 (q.val + 1)] z := by
  let A := actualArrival rate rewards C_star C_h q a
  let F := sourcePrefixFiltration control0 (q.val + 1)
  let k := (Real.exp 1 - 1) * beta
  have hA := actualArrival_integrable rate rewards C_star C_h control0 q a
  have hk : Integrable (fun z => k * A z) mu := hA.const_mul k
  have hm := condExp_mono (m := F) (actualArrival_exp_integrable rate rewards C_star C_h control0 q a)
    ((integrable_const (1 : ℝ)).add hk) (Filter.Eventually.of_forall fun z => by
      have h := actualArrival_bounds rate rewards C_star C_h q a z
      have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
      have hupper : beta * A z ≤ 1 := by
        calc
          beta * A z ≤ beta * (1 / beta) := mul_le_mul_of_nonneg_left h.2 hb.le
          _ = 1 := by field_simp
      simpa only [Pi.add_apply, A, k, mul_assoc] using
        RecordedRoundMoments.exp_le_unit_chord (mul_nonneg hb.le h.1) hupper)
  have hs := condExp_add (integrable_const (1 : ℝ)) hk F
  have hscale := condExp_smul (μ := mu) k A F
  have hc := condExp_const (μ := mu) ((sourcePrefixFiltration control0).le' (q.val + 1)) (1 : ℝ)
  filter_upwards [hm, hs, hscale] with z hm hs hscale
  have hscale' : mu[(fun z => k * A z) | F] z = k * mu[A | F] z := by
    change mu[(fun z => k * A z) | F] z = k * mu[A | F] z at hscale
    exact hscale
  have hce : mu[(fun z => Real.exp (beta * A z)) | F] z ≤ 1 + k * mu[A | F] z := by
    calc
      _ ≤ _ := hm.trans_eq hs
      _ = _ := by rw [Pi.add_apply, hc, hscale']
  exact hce

/-- Finite exponential moment of the actual enabled arrival minus four,
with the exact predictable domain gate and the original private source law. -/
theorem actualIncrement_exponential_condExp (control0 : TimeControl p) (q : Fin p.T) (a : Fin p.K) :
    Integrable (fun z => Real.exp (beta * actualIncrement rate rewards C_star C_h q a z)) mu ∧
    mu[(fun z => Real.exp (beta * actualIncrement rate rewards C_star C_h q a z)) |
      sourcePrefixFiltration control0 (q.val + 1)] ≤ᵐ[mu] fun _ => (1 : ℝ) := by
  let E := actualDomain rate rewards C_star C_h q
  let F := sourcePrefixFiltration control0 (q.val + 1)
  let f := fun z => Real.exp (beta * actualArrival rate rewards C_star C_h q a z)
  let penalty := Real.exp (-4 * beta)
  have hE := actualDomain_measurable rate rewards C_star C_h control0 q
  have hEa := measurableSet_actualDomain rate rewards C_star C_h q
  have hf := actualArrival_exp_integrable rate rewards C_star C_h control0 q a
  have hg := hf.indicator hEa
  have hh := (integrable_const (1 : ℝ) (μ := mu)).indicator hEa.compl
  have heq : (fun z => Real.exp (beta * actualIncrement rate rewards C_star C_h q a z)) =
      fun z => penalty * E.indicator f z + Eᶜ.indicator (fun _ => (1 : ℝ)) z := by
    funext z
    change Real.exp (beta * E.indicator (fun z => actualArrival rate rewards C_star C_h q a z - 4) z) = _
    by_cases hz : z ∈ E
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz,
        Set.indicator_of_notMem (show z ∉ Eᶜ from Set.notMem_compl_iff.mpr hz), add_zero]
      change Real.exp (beta * (actualArrival rate rewards C_star C_h q a z - 4)) =
        Real.exp (-4 * beta) * Real.exp (beta * actualArrival rate rewards C_star C_h q a z)
      rw [← Real.exp_add]
      congr 1
      ring
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, Set.indicator_of_mem (show z ∈ Eᶜ from hz)]
      simp only [mul_zero, Real.exp_zero, zero_add]
  have hint : Integrable (fun z => Real.exp (beta * actualIncrement rate rewards C_star C_h q a z)) mu := by
    rw [heq]
    exact (hg.const_mul penalty).add hh
  refine ⟨hint, ?_⟩
  have hs := condExp_add (hg.const_mul penalty) hh F
  have hp := condExp_smul (μ := mu) penalty (E.indicator f) F
  have hm := condExp_indicator (μ := mu) hf hE
  have hn := condExp_indicator (μ := mu) (integrable_const (1 : ℝ)) hE.compl
  have hc := condExp_const (μ := mu) ((sourcePrefixFiltration control0).le' (q.val + 1)) (1 : ℝ)
  have hd := actualArrival_exp_condExp_chord rate rewards C_star C_h control0 q a
  have hb := actualArrival_condExp_bounds rate rewards C_star C_h control0 q a
  have hscalar := ReferenceFirstCollectionCurrentExponentialIncrement.exp_neg_four_beta_chord_le_one rate
  have hk : 0 ≤ (Real.exp 1 - 1) * beta := mul_nonneg
    (by linarith [Real.exp_one_gt_two]) (CanonicalRecordingRates.beta_pos p rate.eta.property).le
  rw [heq]
  filter_upwards [hs, hp, hm, hn, hd, hb] with z hs hp hm hn hd hb
  change mu[(fun z => penalty * E.indicator f z) | F] z = penalty * mu[E.indicator f | F] z at hp
  change mu[((fun z => penalty * E.indicator f z) + Eᶜ.indicator (fun _ => (1 : ℝ))) | F] z ≤ 1
  rw [hs, Pi.add_apply, hp, hm, hn, hc]
  change penalty * E.indicator (mu[f | F]) z + Eᶜ.indicator (fun _ : X => (1 : ℝ)) z ≤ 1
  by_cases hz : z ∈ E
  · simp only [Set.indicator_of_mem hz, Set.indicator_of_notMem (show z ∉ Eᶜ from Set.notMem_compl_iff.mpr hz), add_zero]
    have hmean := (hb hz).2.trans (roundedReward_bounds rewards q a).2
    calc
      penalty * mu[f | F] z ≤ penalty *
          (1 + (Real.exp 1 - 1) * beta * mu[actualArrival rate rewards C_star C_h q a | F] z) :=
        mul_le_mul_of_nonneg_left hd (Real.exp_nonneg _)
      _ ≤ penalty * (1 + (Real.exp 1 - 1) * beta) := by
        have hmul := mul_le_mul_of_nonneg_left hmean hk
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg (-4 * beta))
        linarith only [hmul]
      _ ≤ 1 := hscalar
  · simp only [Set.indicator_of_notMem hz, Set.indicator_of_mem (show z ∈ Eᶜ from hz), mul_zero, zero_add]
    exact le_rfl

section PhysicalRaw
open ReferenceActivePhysicalHorizon ReferenceActivePhysicalStep ActiveRoundActions
open PublicDiscreteDraws ContinuousControlSlice CanonicalRecordingSlice SnapshotRecordingKernel

private theorem occupiedArrival {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : RoundRecord (p := p) (rate := rate)) (cell : ActualLiveSourceCell record)
    (i : Fin (p.m - 1)) (hu : (cell.states i).status ≠ .unoccupied) :
    (cell.input.recordedArm = some (cell.selected.view.payload.assignment.assigned i) ↔
      ActiveFollowerQueueOperation.recorderGate rate.eta i record.input.row record.input.time
        (cell.selected.view.payload.downRecord i)) ∧
    ActiveFollowerQueueOperation.rawArrival rate.eta i record.input.row record.input.time
        (cell.selected.view.payload.downRecord i) (record.output.ownEntries (followerPlayer p.two_le_m i)).2 =
      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        cell.input (cell.selected.view.payload.assignment.assigned i) := by
  classical
  let P := cell.selected.view.payload
  let snapshot := choiceSnapshot cell.selected cell.states
  let W := sourceWeights P cell.selected.view.complementWeights
  have hp := sourceWeights_pos P cell.selected.view.complementWeights
    cell.selected.view.cutoff record.input.time cell.choiceInputsValid
  have hl := sourceWeights_lower P cell.selected.view.complementWeights
    cell.selected.view.cutoff record.input.time cell.choiceInputsValid
  have hh := sourceWeights_upper P cell.selected.view.complementWeights
    cell.selected.view.cutoff record.input.time cell.choiceInputsValid
  have hn := ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i
  have hi := ActiveRoundActions.followerIndex_followerPlayer p.two_le_m i hn
  have hstatus : snapshot.status i ≠ .unoccupied := hu
  have howns : owns p (.live P.assignment snapshot) (followerPlayer p.two_le_m i) (P.assignment.assigned i) := by
    simp only [owns, dite_eq_right hn, hi]
  have hanchorUpper : ∀ j, P.anchor j ≤ 2 * P.anchor j := by
    intro j
    rw [two_mul]
    exact le_add_of_nonneg_right (le_of_lt (P.anchor_pos j))
  have hW := recordingMap_fixed_event_eq p (.live P.assignment snapshot) rate.eta.val rate.eta.property
    rate.sourceCap P.anchor W P.anchor_pos hp hl hh (followerPlayer p.two_le_m i)
    (P.assignment.assigned i) howns (by intro z; simp [dataAction, hn, hi, hstatus])
    (by simp [actionProbability, hn, hi, hstatus])
  have hA := recordingMap_fixed_event_eq p (.live P.assignment snapshot) rate.eta.val rate.eta.property
    rate.sourceCap P.anchor P.anchor P.anchor_pos P.anchor_pos (fun _ => le_rfl) hanchorUpper
    (followerPlayer p.two_le_m i) (P.assignment.assigned i) howns (by intro z; simp [dataAction, hn, hi, hstatus])
    (by simp [actionProbability, hn, hi, hstatus])
  have hsame := Set.ext_iff.mp (hW.trans hA.symm) (record.input.row.2 record.input.time).1
  have hoccupied : (cell.states i).status.occupied := by
    cases h : (cell.states i).status <;> simp_all [FollowerStatus.occupied]
  have hv := ReferenceFollowerOccupiedRecorderEvent.occupiedGate_eq_canonicalRecordingMap
    P snapshot i record.input.row record.input.time (cell.states i) rfl hoccupied
  have hmap : cell.input.recordedArm = some (P.assignment.assigned i) ↔
      ActiveFollowerQueueOperation.recorderGate rate.eta i record.input.row record.input.time (P.downRecord i) := by
    rw [cell.recordedArm_eq]
    simpa only [sourceArm, snapshot,
      choiceSnapshot, cell.selected.pending_eq, W, P, Set.mem_ofPred_eq] using hsame.trans hv.symm
  refine ⟨hmap, ?_⟩
  rw [ActiveFollowerQueueOperation.rawArrival_eq_sourceFormula, cell.quantizedArrival_eq]
  by_cases hg : ActiveFollowerQueueOperation.recorderGate rate.eta i record.input.row record.input.time (P.downRecord i)
  · have hm := hmap.mpr hg
    rw [cell.recordedArm_eq] at hm
    rw [ite_eq_left hg, ite_eq_left hm]
    have hmask := hg.2.2.1
    rw [ReferenceActiveDataOwnership.downRecord_arm] at hmask
    have hy := ((cell.followerDataClaim i hg.1).2 hu hmask).2
    change (record.output.ownEntries (followerPlayer p.two_le_m i)).2.val.val = _ at hy
    unfold ActiveFollowerQueueOperation.sourceArrivalFloor
    rw [cell.selected.view.payload.downRecord_rate i, hy, rate.n_scale, cell.selected.view.payload.rate_eq_canonical]
    congr 1
    ring
  · have hm : sourceArm record P cell.selected.view.pendingAtChoice
        cell.states cell.selected.view.complementWeights cell.selected.view.cutoff cell.choiceInputsValid ≠
        some (P.assignment.assigned i) := by
      intro hm
      exact hg (hmap.mp (cell.recordedArm_eq.trans hm))
    rw [ite_eq_right hg, ite_eq_right hm]

private theorem coordinatorArrival {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : RoundRecord (p := p) (rate := rate)) (cell : ActualLiveSourceCell record)
    (out : CoordinatorRecordingOperation.Output p) (hgate : out.gateArm = if recorderSourceFromScalar p.two_le_m
        (coordinate Label.rec (record.input.row.2 record.input.time).1) = coordinator p.two_le_m then
      cell.input.recordedArm else none)
    (hraw : out.rawArrival = recordedIncrement p rate.eta.val cell.selected.view.payload.anchor
      (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        (record.input.rewards record.input.time j)) out.gateArm)
    (a : Fin p.K) (ha : a ∉ cell.selected.view.payload.slowSet.1) :
    (if out.gateArm = some a then out.rawArrival else 0) =
      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a := by
  classical
  rw [cell.quantizedArrival_eq]
  by_cases hm : cell.input.recordedArm = some a
  · have hsource : recorderSourceFromScalar p.two_le_m
        (coordinate Label.rec (record.input.row.2 record.input.time).1) = coordinator p.two_le_m := by
      by_contra hn
      have hmap := hm
      rw [cell.recordedArm_eq] at hmap
      rcases (recordingMap_some_iff p _ _ _ _ _ _ _ _ _ _ _ a).mp hmap with ⟨_, _, ho, _, _⟩
      simp only [owns, dite_eq_right hn] at ho
      apply ha
      rw [← cell.selected.view.payload.assignment_image, ho]
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    have hg : out.gateArm = some a := by simp only [hgate, ite_eq_left hsource, hm]
    have hmap := cell.recordedArm_eq.symm.trans hm
    rw [ite_eq_left hg, ite_eq_left hmap, hraw, hg]
    simp only [recordedIncrement, RealRewardGridCount.realRewardGridValue,
      cell.selected.view.payload.rate_eq_canonical, rate.n_scale]
    congr 1
    ring
  · have hg : out.gateArm ≠ some a := by
      rw [hgate]
      split_ifs <;> simp_all
    rw [ite_eq_right hg, ite_eq_right (fun h => hm (cell.recordedArm_eq.trans h))]

/-- Same-source physical marker, original owner feedback, and all-arm integer
raw arrivals, including current follower logs and every failed later tail. -/
theorem actualCell_physical {p : ConstructorDimensions.Parameters} (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin p.T) : ∀ z : BootstrapPrivateRoundStreams.SourceInput p,
    z ∈ actualDomain rate rewards C_star C_h q →
    ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (c : RecordedQueueRun.RoundInput p.K) (cell : ActualLiveSourceCell r), actualRecordAt rate rewards C_star C_h q z = some r ∧
      laterLiveReadout 0 r = some c ∧ cell.input = c ∧
      c.recordedArm = physicalMarkerOnRecord r cell.selected.view.payload true ∧
      (∀ a, c.recordedArm = some a → ∃ owner : Fin p.m,
        SnapshotRecordingKernel.owns p (.live cell.selected.view.payload.assignment
          (choiceSnapshot cell.selected cell.states)) owner a ∧
        r.output.preparation.arms.actions owner = a ∧ r.gridFeedback owner = rewards r.input.time a ∧
        (r.output.ownEntries owner).2.val.val = ((rewards r.input.time a).val : ℝ) / (D p : ℝ)) ∧
      (∀ i, (cell.states i).status ≠ .unoccupied →
        (cell.states i).lastDown = some (cell.selected.view.payload.downRecord i)) ∧
      (∀ i, (cell.states i).status = .unoccupied →
        ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution
          r cell.selected.view.payload i = RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
            (cell.selected.view.payload.assignment.assigned i)) ∧
      ∀ a, (∃! owner : Fin p.m, owns p (.live cell.selected.view.payload.assignment
          (choiceSnapshot cell.selected cell.states)) owner a) ∧
        ((a ∉ cell.selected.view.payload.slowSet.1 ∧ ∃ out, r.output.coordinator.recording = some out ∧
            ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
              (ReferenceActiveHorizonMeasurability.roundRecordCode r) a =
              some (RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)) ∨
        ∃ i : Fin (p.m - 1), cell.selected.view.payload.assignment.assigned i = a ∧
          (∀ j, cell.selected.view.payload.assignment.assigned j = a → j = i) ∧
          (if (cell.states i).status = .unoccupied then
            ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution r cell.selected.view.payload i
          else ActiveFollowerQueueOperation.rawArrival rate.eta i r.input.row r.input.time
            (cell.selected.view.payload.downRecord i) (r.output.ownEntries (followerPlayer p.two_le_m i)).2) =
            RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) := by
  intro z hz
  obtain ⟨r, c, selected, ho, hr, hread, hsel, hsource, _⟩ := actualCell_recordingMap rate rewards C_star C_h q z hz
  let states := preparedStates r ho
  let memories := preparedMemories r ho
  have hordinary := prepared_configuration r ho
  have hf := actualPrepared_payload_fields rate rewards C_star C_h q z r hr selected hsel ho
  obtain ⟨selected', _, hs', _, hlive, _⟩ := laterLiveReadout_some 0 r c hread
  have he : selected' = selected := Option.some.inj (hs'.symm.trans hsel)
  subst selected'
  obtain ⟨k, hk⟩ := actualRecord_suffix_index rate rewards C_star C_h q z r hr
  obtain ⟨hcross, span, hpref⟩ := source_record_prefix rate rewards C_star C_h z k
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hcross
  let seed := actualFirstLiveSeed rate z rewards C_star C_h hcross
  let start := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have heq : r = ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start k.val span seed.activeAtStart :=
    hk.symm.trans hpref
  have hm : r ∈ (ReferenceActivePhysicalHorizon.run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start (k.val + 1)
      span seed.activeAtStart).records := by
    rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start k.val span seed.activeAtStart, heq]
    exact List.mem_append_right _ (by simp)
  have hdata := ReferenceFirstWindowRecordingTruth.actual_window_follower_data_truth initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start (k.val + 1) span
    seed.activeAtStart r hm selected hsel states memories hordinary hf hlive
  obtain ⟨r', c', selected', hr', hread', hsel', out, hout, hgate, hraw⟩ :=
    actualCell_checkedRecorder rate rewards C_star C_h q z hz
  have he : r' = r := Option.some.inj (hr'.symm.trans hr)
  subst r'
  have he : c' = c := Option.some.inj (hread'.symm.trans hread)
  subst c'
  have he : selected' = selected := Option.some.inj (hsel'.symm.trans hsel)
  subst selected'
  let cell : ActualLiveSourceCell r :=
    { states := states, memories := memories, ordinary := hordinary
      selected := selected, selection_actual := hsel, assignment_live := hlive
      choiceInputsValid := selection_choiceValid selected
      input := sourceCell r selected.view.payload
        selected.view.pendingAtChoice states selected.view.complementWeights selected.view.cutoff
        (selection_choiceValid selected)
      input_eq := rfl, enabled := rfl, recordedArm_eq := rfl
      quantizedArrival_eq := sourceCell_quantizedArrival _ _ _ _ _ _ _
      coordinatorProjection := ⟨out, out.gateArm, hout, rfl, hraw, fun a => by
        unfold ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
        rw [ReferenceCoordinatorRecorderCallTrace.recording_eq_actualDiagnostics]
        change (r.output.coordinator.recording).map _ = _
        simp only [hout, Option.map_some]⟩
      followerDataClaim := by
        rw [(actualRecord_fields rate rewards C_star C_h q z r hr).2.2.2]
        exact hdata
      followerRawArrivalGate := fun i h => ActiveFollowerQueueOperation.rawArrival_eq_floor_of_gate
        rate.eta i r.input.row r.input.time (selected.view.payload.downRecord i) _ h
      followerRawArrivalNoGate := fun i h => by simp only [ActiveFollowerQueueOperation.rawArrival, ite_eq_right h] }
  have hinput : cell.input = c := hsource.symm
  obtain ⟨r0, hr0, hlive, _⟩ := hz
  have he : r0 = r := Option.some.inj (hr0.symm.trans hr)
  subst r0
  obtain ⟨regs, owned, base, hcoord⟩ := hlive
  let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start k.val span seed.activeAtStart
  change r = record at heq
  clear hk hpref
  subst r
  have hp : record.output.preparation = prepare record.input := by
    rw [record.output_eq]; rfl
  have hordinary : ∀ i, ((prepare record.input).followers.followers i).configuration =
      .ordinary (cell.states i) (cell.memories i) := by rw [← hp]; exact cell.ordinary
  have hsel := cell.selection_actual
  have hd : record.output.preparation.coordinator = .live regs owned base
      (CoordinatorRoundDispatch.dispatchLive (liveInput record.input regs owned base)) := by
    rw [hp]
    exact ReferenceLiveDispatchMeasurability.canonicalDispatch_live_reconstruction _ _ _ _ hcoord
  have hframes := actual_call_frames record
  rw [hd] at hsel hframes
  generalize houtcome : CoordinatorRoundDispatch.dispatchLive
    (liveInput record.input regs owned base) = outcome at hd hsel hframes
  cases outcome <;> try cases hsel
  case cutoffChosen dispatched hstart ledger hinit hledger hdomains hclock hpending hno arm =>
    change ReferenceActivePhysicalStep.selectionAt _ _ _ _ _ _ = some cell.selected at hsel
    rw [selectionAt_eq record.input regs.payload dispatched.startResult record.input.time
      (liveRegistersAt regs record.input.time).complementWeights arm rfl] at hsel
    have he := (Option.some.inj hsel).symm
    have hl := cell.assignment_live
    rw [he] at hl
    exact False.elim (hframes.1 hl)
  case continuingChosen dispatched hstart continuation arm =>
    change ReferenceActivePhysicalStep.selectionAt _ _ _ _ _ _ = some cell.selected at hsel
    rw [selectionAt_eq record.input regs.payload dispatched.startResult record.input.time
      (liveRegistersAt regs record.input.time).complementWeights arm rfl] at hsel
    have he := (Option.some.inj hsel).symm
    have hq := ReferenceContinuingRecordingPhysicalReward.prefix_continuing_recording_physical_reward
      initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start k.val
      span seed.activeAtStart seed.followers seed.memory seed.coordinatorFirst seed.configuration
      seed.unoccupied seed.bufferValid seed.chronologicalBuffer seed.bufferStamps
      regs owned base dispatched hstart continuation arm (by
        change (prepare record.input).coordinator = _
        rw [← hp]; exact hd)
      cell.states cell.memories hordinary hframes.2
    have hcand : candidateRecord initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start k.val span
        seed.activeAtStart (record.input.row.2 record.input.time) = record :=
      congrArg (fun x : RoundInput p rate =>
        (⟨x, ReferenceActivePhysicalStep.step x, rfl⟩ : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
        (inputAtControl_actual _)
    have hpair := congrArg Prod.fst (hq.1 (record.input.row.2 record.input.time))
    simp only [candidatePhysicalFastPair, candidatePhysicalMarker, hcand,
      FastRewardSliceLaw.liveRecordingFastPair] at hpair
    have hmarker : c.recordedArm = physicalMarkerOnRecord
        record cell.selected.view.payload true := by
      rw [← hinput, cell.recordedArm_eq]
      have ht := congrArg (fun selected : Selection record.input =>
        sourceArm record selected.view.payload
          selected.view.pendingAtChoice cell.states selected.view.complementWeights selected.view.cutoff
          (selection_choiceValid selected) =
        physicalMarkerOnRecord record selected.view.payload true) he
      apply Eq.mpr ht
      have hW : sourceWeights regs.payload (liveRegistersAt regs record.input.time).complementWeights =
          liveSliceWeights regs record.input.time := by
        funext j
        rfl
      have htime : (candidateInput initial z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start k.val span
          seed.activeAtStart).time = record.input.time := rfl
      simpa only [selectionOfArm, sourceArm, hW, liveSliceSnapshot, htime] using hpair.symm
    have hu : ∀ i, (cell.states i).status = .unoccupied →
        ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution record cell.selected.view.payload i =
          RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c (cell.selected.view.payload.assignment.assigned i) := by
      intro i hi
      rw [ReferenceFirstLiveUnoccupiedEmission.actualCurrentSavedContribution_eq_emissionContribution, ← hinput]
      exact ReferenceFirstLiveUnoccupiedEmission.emissionContribution_eq_quantizedArrival record cell hf i hi
    refine ⟨record, c, cell, hr, hread, hinput, hmarker, ?_, hf, hu, ?_⟩
    · intro a ha
      have hphys := (hq.2 (record.input.row.2 record.input.time)).1 a
      simp only [candidatePhysicalMarker] at hphys
      rw [hcand] at hphys
      have hrestore : inputAtControl (candidateInput initial z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start k.val span seed.activeAtStart)
          (record.input.row.2 record.input.time) = record.input :=
        inputAtControl_actual _
      rw [hrestore] at hphys
      rw [he] at hmarker
      rw [hmarker] at ha
      obtain ⟨selected, hs, hpay, hstart, ho, hdata, howns, haction, hfeedback, hobs, _⟩ := hphys ha
      let owner := CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec (record.input.row.2 record.input.time).1)
      refine ⟨owner, ?_, ?_, ?_, ?_⟩
      · rw [he]
        exact howns
      · exact haction
      · exact hfeedback
      · have hown : (record.output.ownEntries owner).2.val.val =
            (record.output.preparation.feedback.observations owner).val.val := by
          rw [record.output_eq, ReferenceActivePhysicalStep.step_own_entry]
          rfl
        exact hown.trans hobs
    · have hgate' : out.gateArm = if CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec
            (record.input.row.2 record.input.time).1) = ActiveRoundActions.coordinator p.two_le_m
          then cell.input.recordedArm else none := by rw [hinput]; exact hgate
      intro a
      constructor
      · obtain ⟨owner, ho⟩ := exists_ownerSource p (.live cell.selected.view.payload.assignment
          (choiceSnapshot cell.selected cell.states)) a
        exact ⟨owner, ho, fun other hother => owns_unique p _ a other owner hother ho⟩
      · by_cases ha : a ∈ cell.selected.view.payload.slowSet.1
        · rw [← cell.selected.view.payload.assignment_image] at ha
          obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
          refine Or.inr ⟨i, hi, fun j hj => cell.selected.view.payload.assignment.injective (hj.trans hi.symm), ?_⟩
          split_ifs with hstatus
          · simpa only [hi] using hu i hstatus
          · rw [← hinput]
            simpa only [hi] using (occupiedArrival record cell i hstatus).2
        · refine Or.inl ⟨ha, out, hout, ?_⟩
          unfold ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
          rw [ReferenceCoordinatorRecorderCallTrace.recording_eq_actualDiagnostics]
          change (record.output.coordinator.recording).map _ = _
          simp only [hout, Option.map_some]
          rw [← hinput]
          exact congrArg some (coordinatorArrival record cell out hgate' hraw a ha)

end PhysicalRaw

end Bandits.Support.ReferenceOriginalCalendarContinuingLiveRecorderLaw

end
