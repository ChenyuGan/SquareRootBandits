/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalExponentialQueueStep

/-!
# Original-source first-renewal exponential transport

This module projects the actual first-renewal coordinator recording and its
numerical update onto the original renewal source.  It keeps the incoming
queue, the whole reward table, and the unnormalized source measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.RecordedQueueRun

namespace Bandits.Support.ReferenceFirstCollectionRenewalSourceExponentialTransport

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl
variable {p : Parameters}

abbrev Source (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
    rate rewards C_star C_h u t
abbrev Pair (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalInstallationCoupling.RenewalBase
      rate rewards C_star C_h u t ×
    ReferenceFirstCollectionRenewalInstallationCoupling.Source
      rate rewards C_star C_h u t
abbrev Readout (p : Parameters) :=
  (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ)))

variable (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

local instance sourceInputMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local notation "Z" => Source rate rewards C_star C_h u t
local notation "B" => Pair rate rewards C_star C_h u t
local notation "mu" => ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
  rate rewards C_star C_h u t
local instance pairLawIsFinite : IsFiniteMeasure mu :=
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_finite
    rate rewards C_star C_h u t
local notation "nu" => ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
  rate rewards C_star C_h u t
local notation "incoming" => ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
  rate rewards C_star C_h u t
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "qp" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "F_R" control0 => MeasurableSpace.comap
  (ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates
    rate rewards C_star C_h u t control0)
  (inferInstance : MeasurableSpace
    (ReferenceFirstCollectionRenewalControlFactor.RetainedCoordinates p))

/-- The literal coordinator recording option in the actual renewal record. -/
def recOption (z : Z) : Option (CoordinatorRecordingOperation.Output p) :=
  (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
    rate rewards C_star C_h u t z).output.coordinator.recording

private theorem actual_source_recording
    (z : Z) :
    ∃ d : ReferenceFirstCollectionRenewalAuxiliaryLaw.ActualRenewalCall
        rate rewards C_star C_h u t z,
      ∃ recording : CoordinatorRecordingOperation.Output p,
        d.record = ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
          rate rewards C_star C_h u t z ∧
        d.record.output.coordinator.recording = some recording ∧
        recording.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
          (AssignmentScoreReconstruction.currentWeight d.out)
          (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (rewards t j)) recording.gateArm ∧
        (∀ j, recording.gateArm = some j →
          d.record.output.preparation.feedback.feedback
            (ActiveRoundActions.coordinator p.two_le_m) = rewards t j ∧
          d.record.output.preparation.coordinatorObservation = rewards t j ∧
          (d.record.output.preparation.feedback.observations
            (ActiveRoundActions.coordinator p.two_le_m)).val.val =
              RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
                (rewards t j)) := by
  classical
  obtain ⟨d, hw⟩ :=
    ReferenceFirstCollectionRenewalSampleInstallation.actual_renewal_call_installation
      rate rewards C_star C_h u t z
  dsimp only at hw
  rcases hw with ⟨consistent, output, hlocal, hlater, hvector, hreconstruction,
    hsample, hslow, hpayloadSlow, hregisters, hinstalledVector,
    hinstalledReconstruction, hanchor, hqueues, selection, hselection,
    hdispatch, hpreparation, hpreparationCoordinator, hremaining⟩
  let x := ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
    rate u d.record.input d.old d.ledger d.saved
  let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence
      output := {
    priorClock := x.clock
    pending := x.ledger.pending
    proposalParameterValid := d.core.clock_parameter_valid
    priorClockValid := d.core.clock_registers_valid
    startTimeValid := by
      simpa only [x, ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
        ReferenceActivePhysicalStep.collectionInput, d.instruction_time] using
        d.core.clock_start_time_valid
    result := d.started
    startRound_eq := by
      simpa only [x, ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
        ReferenceActivePhysicalStep.collectionInput,
        ReferenceActivePhysicalStep.collectionClock, d.instruction_time] using
        d.clock_eq
    assignmentStart_eq := d.instruction_eq
    priorSigma_eq := d.core.clock_sigma_eq
    priorGrid_eq_freezeAt := by
      calc
        x.clock.g = x.ledger.freezeAt := d.core.ledger_freeze_eq.symm
        _ = consistent.oldFreezeAt := consistent.oldFreezeAt_eq.symm
        _ = output.localConsistency.oldFreezeAt := by rw [hlocal]
  }
  let installed := CoordinatorAssignmentRegisterInstall.installLater output clockData
  have hcut :
      (ReferenceActivePhysicalStep.prepare d.record.input).coordinator =
        .collection d.old d.ledger
          (ReferenceActivePhysicalStep.collectionClock d.old d.ledger d.saved u) u
          (.laterChosen d.core consistent d.started d.clock_eq d.instruction
            d.instruction_eq output hlocal clockData installed selection) := by
    have h := hpreparationCoordinator
    rw [hpreparation] at h
    rw [hdispatch] at h
    simpa [x, ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView] using h
  obtain ⟨hinstalled, _hrows, _hselected, _hrewards, states, memories, hstates⟩ :=
    ReferenceFirstCollectionRenewalRecordingFeedback.actual_call_prepared_followers
      rate rewards C_star C_h u t z d consistent output hlocal clockData installed
      selection hcut
  have hordinary : ∀ i,
      ((ReferenceActivePhysicalStep.prepare d.record.input).followers.followers i).configuration =
        .ordinary (states i) (memories i) := fun i => (hstates i).2.2
  have hfields : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (installed.registers.payload.downRecord i) := by
    intro i hi
    exact (hi (hstates i).2.1).elim
  have hcompat :=
    CoordinatorAssignmentRegisterInstall.later_start_round_compatibility output clockData
  have hresult : clockData.result = d.started := rfl
  rw [hresult] at hcompat
  obtain ⟨_hkind, _hsigma, huNone, _hgrid, _hproposal, _hpending, _hledger,
    _hclass, _hexpected⟩ := hcompat
  have hpayload : installed.registers.payload = output.payload := by
    rw [hinstalled]
    rfl
  have hnew : installed.registers.payload.sigma = d.record.input.time :=
    (congrArg AssignmentStartPayload.Input.sigma hpayload).trans
      (output.payload_start.trans d.instruction_time)
  have hlive : CoordinatorLocalArmChoice.assignmentIsLive installed.registers.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u)
      d.record.input.time := by
    rw [huNone]
    change installed.registers.payload.sigma.val + 1 ≤ d.record.input.time.val + 1 ∧
      d.record.input.time.val + 1 < p.T + 1
    rw [hnew]
    exact ⟨le_rfl, Nat.add_lt_add_right d.record.input.time.isLt 1⟩
  obtain ⟨recording, hrun, _hstep, _hgate, _hraw⟩ :=
    ReferenceCoordinatorLiveRecording.later_recording_identification
      d.record.input d.old d.ledger
      (ReferenceActivePhysicalStep.collectionClock d.old d.ledger d.saved u) u
      d.core consistent d.started d.clock_eq d.instruction d.instruction_eq
      output hlocal clockData installed selection hcut states memories hordinary hfields hlive
  obtain ⟨_hinstalled', _states', _memories', _hstates', _hlive', _hpending',
    _hu', _hsigma', _hnotFrozen, hrecording, hraw, hgateFacts⟩ :=
    ReferenceFirstCollectionRenewalRecordingFeedback.actual_call_recording_feedback
      rate rewards C_star C_h u t z d consistent output hlocal clockData installed
      selection hcut hresult recording hrun
  have hrecord := ReferenceFirstCollectionRenewalIncomingQueuePrefix.actual_call_record_eq
    rate rewards C_star C_h u t z d
  refine ⟨d, recording, hrecord, hrecording, hraw, ?_⟩
  intro j hj
  rcases hgateFacts j hj with ⟨_hslot, _hsource, _haction, _hunoccupied,
    _hmask, _hcollision, hfeedback, hcoordinatorObservation, hgrid⟩
  exact ⟨hfeedback, hcoordinatorObservation, hgrid⟩

/-- Every original renewal source has the literal successful coordinator
recording in its source-selected record. -/
theorem recorder_present (z : Z) : (recOption rate rewards C_star C_h u t z).isSome := by
  obtain ⟨d, recording, hrecord, hrecording, _hraw, _hfeedback⟩ :=
    actual_source_recording rate rewards C_star C_h u t z
  rw [recOption, ← hrecord, hrecording]
  rfl

/-- The source recording is the value of the actual present option. -/
def sourceRecording (z : Z) : CoordinatorRecordingOperation.Output p :=
  (recOption rate rewards C_star C_h u t z).get
    (recorder_present rate rewards C_star C_h u t z)

/-- The option is exactly `some` of the unique actual recording value. -/
theorem recOption_eq_some_sourceRecording (z : Z) :
    recOption rate rewards C_star C_h u t z = some (sourceRecording rate rewards C_star C_h u t z) :=
  (Option.some_get (recorder_present rate rewards C_star C_h u t z)).symm

/-- The source getter returns the very recorder output in the same actual
successful call, with its physical feedback and raw quantized arrival. -/
theorem recorder_spec (z : Z) :
    ∃ d : ReferenceFirstCollectionRenewalAuxiliaryLaw.ActualRenewalCall
        rate rewards C_star C_h u t z,
      ∃ recording : CoordinatorRecordingOperation.Output p,
        d.record = ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
          rate rewards C_star C_h u t z ∧
        d.record.output.coordinator.recording = some recording ∧
        sourceRecording rate rewards C_star C_h u t z = recording ∧
        recording.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
          (AssignmentScoreReconstruction.currentWeight d.out)
          (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (rewards t j)) recording.gateArm ∧
        (∀ j, recording.gateArm = some j →
          d.record.output.preparation.feedback.feedback
            (ActiveRoundActions.coordinator p.two_le_m) = rewards t j ∧
          d.record.output.preparation.coordinatorObservation = rewards t j ∧
          (d.record.output.preparation.feedback.observations
            (ActiveRoundActions.coordinator p.two_le_m)).val.val =
              RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
                (rewards t j)) := by
  obtain ⟨d, recording, hrecord, hrecording, hraw, hfeedback⟩ :=
    actual_source_recording rate rewards C_star C_h u t z
  have hoption : recOption rate rewards C_star C_h u t z = some recording := by
    rw [recOption, ← hrecord, hrecording]
  have hsource : sourceRecording rate rewards C_star C_h u t z = recording := by
    simp [sourceRecording, hoption]
  exact ⟨d, recording, hrecord, hrecording, hsource, hraw, hfeedback⟩

/-- The original renewal call's literal selected sampler parameter. -/
def vSource (z : Z) : AssignmentParameterFibreKernel.Anchor p :=
  (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
    rate rewards C_star C_h u t z).2

/-- The actual coordinator-gated current input to the existing queue machine. -/
def coordinatorCell (z : Z) : RecordedQueueRun.RoundInput p.K where
  enabled := true
  recordedArm := (sourceRecording rate rewards C_star C_h u t z).gateArm
  reward := fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t j)
  rate := fun j => CanonicalRecordingRates.xi p rate.eta.val
    (vSource rate rewards C_star C_h u t z) j
  reward_nonneg := by
    intro j
    exact (RealRewardGridCount.realRewardGridValue_mem_Icc (D p) (D_pos p)
      (rewards t j)).1
  reward_le_one := by
    intro j
    exact (RealRewardGridCount.realRewardGridValue_mem_Icc (D p) (D_pos p)
      (rewards t j)).2
  rate_pos := by
    intro j
    exact CanonicalRecordingRates.xi_pos p rate.eta.property
      (vSource rate rewards C_star C_h u t z) j

/-- The actual source cell is the current coordinator gate, the whole reward
row, and the canonical recording-rate vector of this renewal call. Its raw
arrival and feedback are witnessed by the same actual record. -/
theorem source_cell_spec (z : Z) :
    ∃ d : ReferenceFirstCollectionRenewalAuxiliaryLaw.ActualRenewalCall
        rate rewards C_star C_h u t z,
      ∃ recording : CoordinatorRecordingOperation.Output p,
        d.record = ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
          rate rewards C_star C_h u t z ∧
        sourceRecording rate rewards C_star C_h u t z = recording ∧
        (coordinatorCell rate rewards C_star C_h u t z).enabled = true ∧
        (coordinatorCell rate rewards C_star C_h u t z).recordedArm = recording.gateArm ∧
        (coordinatorCell rate rewards C_star C_h u t z).reward =
          (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t j)) ∧
        (coordinatorCell rate rewards C_star C_h u t z).rate =
          (fun j => CanonicalRecordingRates.xi p rate.eta.val
            (vSource rate rewards C_star C_h u t z) j) ∧
        vSource rate rewards C_star C_h u t z =
          AssignmentScoreReconstruction.currentWeight d.out ∧
        recording.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
          (vSource rate rewards C_star C_h u t z)
          (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (rewards t j)) recording.gateArm ∧
        (∀ j, recording.gateArm = some j →
          d.record.output.preparation.feedback.feedback
            (ActiveRoundActions.coordinator p.two_le_m) = rewards t j ∧
          d.record.output.preparation.coordinatorObservation = rewards t j ∧
          (d.record.output.preparation.feedback.observations
            (ActiveRoundActions.coordinator p.two_le_m)).val.val =
              RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
                (rewards t j)) := by
  obtain ⟨d, recording, hrecord, hrecording, hsource, hraw, hfeedback⟩ :=
    recorder_spec rate rewards C_star C_h u t z
  let x := ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
    rate u d.record.input d.old d.ledger d.saved
  let ell := CoordinatorRoundDispatch.collectionOperationLedger x d.core.payload_n_eq
  have hselected := LaterAssignmentStartMeasurability.selectedSamplerParameters_renewal
    d.old ell d.instruction d.out d.reconstruction_eq d.renewal
  have hv : vSource rate rewards C_star C_h u t z =
      AssignmentScoreReconstruction.currentWeight d.out := by
    change (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
      rate rewards C_star C_h u t z).2 = _
    rw [d.parameter_eq]
    exact hselected.1
  have hraw' : recording.rawArrival = SnapshotRecordingKernel.recordedIncrement
      p rate.eta.val (vSource rate rewards C_star C_h u t z)
      (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t j))
      recording.gateArm := by
    rw [hv]
    exact hraw
  refine ⟨d, recording, hrecord, hsource, rfl, ?_, rfl, rfl, hv, hraw', hfeedback⟩
  exact congrArg (fun value : CoordinatorRecordingOperation.Output p => value.gateArm) hsource

/-- Readout after one actual coordinator-gated service step from the incoming
renewal queue; the current update and all historical fields are retained. -/
def coordinatorPostReadout (z : Z) :=
  ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
    (RecordedQueueRun.step qp (incoming z) (coordinatorCell rate rewards C_star C_h u t z))

/-- Incoming exponential on the original renewal source. -/
def sourceXMinus (j : Fin p.K) (z : Z) : ℝ :=
  Real.exp (beta *
    ((((incoming z).registers j).2 : ℝ) / (rate.n : ℝ)))

/-- Coordinator-post-update exponential on the original renewal source. -/
def sourceXPlus (j : Fin p.K) (z : Z) : ℝ :=
  Real.exp (beta *
    ((((coordinatorPostReadout rate rewards C_star C_h u t z).1 j).2 : ℝ) /
      (rate.n : ℝ)))

/-- No overflow in the complete incoming renewal prefix. -/
def noPastOverflow : Set Z := {z | (incoming z).overflow = false}

/-- Literal incoming no-overflow indicator on the original source. -/
def sourceIndicator (z : Z) : ℝ :=
  Set.indicator (noPastOverflow rate rewards C_star C_h u t)
    (fun _ : Z => (1 : ℝ)) z

private def callRecordCodeTag (z : Z) :
    Unit ⊕ ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) :=
  ReferenceActiveHorizonMeasurability.listObservationAt
    (ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
      (rate := rate) rewards C_star C_h z.val)
    (t.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
      rate rewards C_star C_h u t z)

private theorem measurable_variableListObservationAt
    {α : Type*} [MeasurableSpace α] :
    Measurable (fun v : ℕ × List α =>
      ReferenceActiveHorizonMeasurability.listObservationAt v.2 v.1) := by
  exact measurable_from_prod_countable_right
    (f := fun v : ℕ × List α =>
      ReferenceActiveHorizonMeasurability.listObservationAt v.2 v.1)
    (fun n => (measurable_pi_apply n).comp
      (measurable_snd.comp
        (ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
          (α := α))))

private def recordingFromRecordCode (r : RateInput p)
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := r)) :
    Option (CoordinatorRecordingOperation.Output p) :=
  ReferenceCoordinatorRecorderCallTrace.recording (p := p) (rate := r) code

private def recordingOptionFromTag (r : RateInput p) :
    Unit ⊕ ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := r) → Option (CoordinatorRecordingOperation.Output p)
  | .inl _ => none
  | .inr code => recordingFromRecordCode r code

private theorem callRecordCodeTag_eq (z : Z) :
    callRecordCodeTag rate rewards C_star C_h u t z =
      Sum.inr (ReferenceActiveHorizonMeasurability.roundRecordCode
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
          rate rewards C_star C_h u t z)) := by
  have hindex : t.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z <
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords
        rate rewards C_star C_h u t z).length :=
    ReferenceFirstCollectionRenewalIncomingQueuePrefix.call_index_lt
      rate rewards C_star C_h u t z
  have hindex' : t.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z <
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards
        C_star C_h).length := by
    simpa [ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords] using hindex
  simp only [callRecordCodeTag,
    ReferenceActiveHorizonMeasurability.listObservationAt,
    ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode,
    ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord,
    ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords]
  rw [List.getElem?_map, List.getElem?_eq_getElem hindex']
  rfl

private theorem recOption_eq_recordingOptionFromTag (z : Z) :
    recOption rate rewards C_star C_h u t z =
      recordingOptionFromTag rate
        (callRecordCodeTag rate rewards C_star C_h u t z) := by
  rw [callRecordCodeTag_eq, recordingOptionFromTag, recOption]
  have hdecode := (ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs
    (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
      rate rewards C_star C_h u t z)).2.1
  change ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation
      ((ReferenceActiveHorizonMeasurability.roundRecordCode
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
          rate rewards C_star C_h u t z)).2.2.1.2.2.2.2) =
    (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
      rate rewards C_star C_h u t z).output.coordinator at hdecode
  rw [← hdecode]
  rfl

private theorem measurable_recordingFromRecordCode (r : RateInput p) :
    Measurable (recordingFromRecordCode r) := by
  have htail : Measurable
      (ReferenceCoordinatorRecorderCallTrace.tail (p := p) (rate := r)) := by
    exact measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp
        (measurable_snd.comp (measurable_snd.comp measurable_id))))))
  have hrecording : Measurable
      (ReferenceCoordinatorRecorderCallTrace.recording (p := p) (rate := r)) := by
    exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp htail)))
  change Measurable
    (ReferenceCoordinatorRecorderCallTrace.recording (p := p) (rate := r))
  exact hrecording

private theorem measurable_recordingOptionFromTag (r : RateInput p) :
    Measurable (recordingOptionFromTag r) := by
  exact Measurable.sumElim measurable_const
    (measurable_recordingFromRecordCode r)

/-- The complete-suffix code of the actual call makes its original recorder
output a Borel source function, including the successful option tag. -/
theorem measurable_sourceRecording : Measurable
    (sourceRecording rate rewards C_star C_h u t) := by
  have hstart : Measurable (fun z : Z =>
      ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z) :=
    (ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
      rate rewards C_star C_h).comp measurable_subtype_coe
  have hindex : Measurable (fun z : Z =>
      t.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z) :=
    (measurable_from_nat (f := fun s : ℕ => t.val - s)).comp hstart
  have hcodes : Measurable (fun z : Z =>
      ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
        (rate := rate) rewards C_star C_h z.val) :=
    (ReferenceGeneratedCompleteCalendarObservation.measurable_completeSuffixCode
      (rate := rate) rewards C_star C_h).comp measurable_subtype_coe
  have htag : Measurable (callRecordCodeTag rate rewards C_star C_h u t) := by
    change Measurable (fun z : Z =>
      ReferenceActiveHorizonMeasurability.listObservationAt
        (ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
          (rate := rate) rewards C_star C_h z.val)
        (t.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
          rate rewards C_star C_h u t z))
    exact measurable_variableListObservationAt.comp (hindex.prodMk hcodes)
  have hoption : Measurable (recOption rate rewards C_star C_h u t) := by
    rw [show recOption rate rewards C_star C_h u t =
      fun z => recordingOptionFromTag rate
        (callRecordCodeTag rate rewards C_star C_h u t z)
        from funext (recOption_eq_recordingOptionFromTag rate rewards C_star C_h u t)]
    exact (measurable_recordingOptionFromTag rate).comp htag
  have heq : (fun z : Z =>
      some (sourceRecording rate rewards C_star C_h u t z)) =
        recOption rate rewards C_star C_h u t :=
    funext fun z => (recOption_eq_some_sourceRecording rate rewards C_star C_h u t z).symm
  have hsome : Measurable (fun z : Z =>
      some (sourceRecording rate rewards C_star C_h u t z)) := by
    rw [heq]
    exact hoption
  have hencode : Measurable
      (Equiv.optionEquivSumPUnit (CoordinatorRecordingOperation.Output p)) :=
    measurable_of_countable _
  have hsum : Measurable (fun z : Z =>
      (Sum.inl (sourceRecording rate rewards C_star C_h u t z) :
        CoordinatorRecordingOperation.Output p ⊕ PUnit.{1})) := hencode.comp hsome
  have hinj : MeasurableEmbedding
      (@Sum.inl (CoordinatorRecordingOperation.Output p) PUnit.{1}) :=
    ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩
  exact hinj.measurable_comp_iff.mp hsum

/-- The renewal-selected current weight is Borel on the original renewal
source, with its original full-vector measurable structure. -/
theorem measurable_vSource : Measurable (vSource rate rewards C_star C_h u t) := by
  exact measurable_snd.comp
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurable_renewalCallParameter
      rate rewards C_star C_h u t)

private theorem measurable_sourceRateScalar (j : Fin p.K) :
    Measurable (fun z : Z => CanonicalRecordingRates.xi p rate.eta.val
      (vSource rate rewards C_star C_h u t z) j) := by
  have hsetWeight (S : Finset (Fin p.K)) :
      Measurable (fun v : Fin p.K → ℝ => ProductSetLaw.setWeight v S) := by
    unfold ProductSetLaw.setWeight
    exact Finset.measurable_fun_prod S (fun i _ => measurable_pi_apply i)
  have htotal : Measurable (fun v : Fin p.K → ℝ =>
      FiniteNormalization.totalMass (ProductSetLaw.support p.K p.m)
        (ProductSetLaw.setWeight v)) := by
    unfold FiniteNormalization.totalMass
    exact Finset.measurable_fun_sum _ (fun S _ => hsetWeight S)
  have htheta : Measurable (fun v : Fin p.K → ℝ =>
      ProductSetLaw.theta p.m v j) := by
    unfold ProductSetLaw.theta FiniteNormalization.mass
    apply Finset.measurable_fun_sum
    intro S _
    unfold FiniteNormalization.normalizedWeight
    exact (hsetWeight S).div htotal
  have hf : Measurable (fun v : Fin p.K → ℝ =>
      CanonicalRecordingRates.f p v j) := by
    unfold CanonicalRecordingRates.f
    fun_prop
  have hxi : Measurable (fun v : Fin p.K → ℝ =>
      CanonicalRecordingRates.xi p rate.eta.val v j) := by
    unfold CanonicalRecordingRates.xi
    exact AssignmentPayloadDerivedMeasurability.measurable_dyadicCeiling.comp
      ((measurable_const : Measurable fun _ : Fin p.K → ℝ =>
        CanonicalRecordingRates.beta p rate.eta.val).max hf)
  exact hxi.comp (measurable_vSource rate rewards C_star C_h u t)

private def coordinatorCellNumericalCoordinates (z : Z) :=
  ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates
    (coordinatorCell rate rewards C_star C_h u t z)

/-- The original enabled gate, whole reward row and renewal-selected rate
vector are Borel numerical coordinates on the renewal source. -/
theorem measurable_coordinatorCellNumericalCoordinates :
    Measurable (fun z : Z =>
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates
        (coordinatorCell rate rewards C_star C_h u t z)) := by
  have hrecording := measurable_sourceRecording rate rewards C_star C_h u t
  have hgate0 : Measurable
      (fun x : CoordinatorRecordingOperation.Output p => x.gateArm) := measurable_of_countable _
  have hgate : Measurable (fun z : Z =>
      (sourceRecording rate rewards C_star C_h u t z).gateArm) := hgate0.comp hrecording
  have hreward : Measurable (fun z : Z =>
      fun j : Fin p.K =>
        RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t j)) := by
    apply Measurable.of_eval
    intro j
    exact measurable_const
  have hrate : Measurable (fun z : Z =>
      fun j : Fin p.K => CanonicalRecordingRates.xi p rate.eta.val
        (vSource rate rewards C_star C_h u t z) j) := by
    apply Measurable.of_eval
    intro j
    exact measurable_sourceRateScalar rate rewards C_star C_h u t j
  change Measurable (fun z : Z =>
    (true, ((sourceRecording rate rewards C_star C_h u t z).gateArm,
      ((fun j : Fin p.K =>
        RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t j)),
       (fun j : Fin p.K => CanonicalRecordingRates.xi p rate.eta.val
         (vSource rate rewards C_star C_h u t z) j)))))
  exact measurable_const.prodMk (hgate.prodMk (hreward.prodMk hrate))

private instance sourceRecordListMeasurableSingleton :
    MeasurableSingletonClass (List (Bool × ℕ)) where
  measurableSet_singleton l := by
    let : MeasurableSingletonClass (Unit ⊕ (Bool × ℕ)) := ⟨fun x => by
      cases x with
      | inl a => simpa only [Set.image_singleton] using
          (MeasurableSet.singleton a).inl_image
      | inr a => simpa only [Set.image_singleton] using
          (MeasurableSet.singleton a).inr_image⟩
    have hinj : Function.Injective
        (ReferenceActiveHorizonMeasurability.listObservationCoordinates
          (α := Bool × ℕ)) := by
      intro a b h
      have hlen : a.length = b.length := congrArg Prod.fst h
      apply List.ext_getElem hlen
      intro i hi hj
      have he := congrFun (congrArg Prod.snd h) i
      simpa only [ReferenceActiveHorizonMeasurability.listObservationCoordinates,
        ReferenceActiveHorizonMeasurability.listObservationAt,
        List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
        Sum.inr.injEq] using he
    have hm := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
      (α := Bool × ℕ)
    have hh := hm (MeasurableSet.singleton
      (ReferenceActiveHorizonMeasurability.listObservationCoordinates l))
    convert hh using 1
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, hinj.eq_iff]

private theorem measurable_sourceStepReadout {X : Type*} [MeasurableSpace X]
    (state : X → RecordedQueueRun.RunState p.K)
    (cell : X → RecordedQueueRun.RoundInput p.K)
    (hs : Measurable (fun x =>
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout (state x)))
    (hc : Measurable (fun x =>
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates (cell x))) :
    Measurable (fun x =>
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.step qp (state x) (cell x))) := by
  classical
  have hreg := measurable_fst.comp hs
  have hflag := measurable_fst.comp (measurable_snd.comp hs)
  have hrecords := measurable_snd.comp (measurable_snd.comp hs)
  have henabled := measurable_fst.comp hc
  have harrivals := measurable_snd.comp
    ((ReferenceLaterCollectionSourceReadoutMeasurability.measurable_arrivalsFromNumerical
      rate).comp hc)
  have hrecs : Measurable (fun x => fun j : Fin p.K =>
      RecordedQueueRun.acceptedRecord qp (state x) (cell x) j) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_of_countable (fun v : Bool × (Bool × ℕ) =>
      if v.1 then (false, 0) else if v.2.1 then (true, v.2.2) else (false, 0))).comp
        (hflag.prodMk (henabled.prodMk ((measurable_pi_apply j).comp harrivals)))
  have hnext : Measurable (fun x => fun j : Fin p.K =>
      QueueReplay.transition (4 * rate.n) ((state x).registers j)
        (RecordedQueueRun.acceptedRecord qp (state x) (cell x) j)) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_of_countable (fun v : (ℕ × ℕ) × (Bool × ℕ) =>
      QueueReplay.transition (4 * rate.n) v.1 v.2)).comp
        (((measurable_pi_apply j).comp hreg).prodMk ((measurable_pi_apply j).comp hrecs))
  have hover : Measurable (fun x => (state x).overflow ||
      decide (∃ j : Fin p.K, 32 *
        (QueueReplay.transition (4 * rate.n) ((state x).registers j)
          (RecordedQueueRun.acceptedRecord qp (state x) (cell x) j)).2 > D p)) :=
    (measurable_of_countable (fun v : Bool × (Fin p.K → ℕ × ℕ) =>
      v.1 || decide (∃ j, 32 * (v.2 j).2 > D p))).comp (hflag.prodMk hnext)
  have hhistory : Measurable (fun x => fun j : Fin p.K =>
      (state x).records j ++
        [RecordedQueueRun.acceptedRecord qp (state x) (cell x) j]) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_of_countable (fun v : List (Bool × ℕ) × (Bool × ℕ) =>
      v.1 ++ [v.2])).comp
        (((measurable_pi_apply j).comp hrecords).prodMk ((measurable_pi_apply j).comp hrecs))
  change Measurable (fun x =>
    (fun j : Fin p.K => QueueReplay.transition (4 * rate.n) ((state x).registers j)
      (RecordedQueueRun.acceptedRecord qp (state x) (cell x) j),
     ((state x).overflow || decide (∃ j : Fin p.K, 32 *
        (QueueReplay.transition (4 * rate.n) ((state x).registers j)
          (RecordedQueueRun.acceptedRecord qp (state x) (cell x) j)).2 > D p),
      fun j : Fin p.K => (state x).records j ++
        [RecordedQueueRun.acceptedRecord qp (state x) (cell x) j])))
  exact hnext.prodMk (hover.prodMk hhistory)

/-- The entire physical queue readout after the existing gated queue step is
Borel on the original renewal source. -/
theorem measurable_coordinatorPostReadout :
    Measurable (coordinatorPostReadout rate rewards C_star C_h u t) := by
  exact measurable_sourceStepReadout rate incoming
    (coordinatorCell rate rewards C_star C_h u t)
    (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_incomingReadout
      rate rewards C_star C_h u t)
    (measurable_coordinatorCellNumericalCoordinates rate rewards C_star C_h u t)

/-- Incoming exponentials retain the original incoming queue registers. -/
theorem measurable_sourceXMinus (j : Fin p.K) :
    Measurable (sourceXMinus rate rewards C_star C_h u t j) := by
  have hreadout :=
    ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_incomingReadout
      rate rewards C_star C_h u t
  have hvalue : Measurable (fun z : Z =>
      (((incoming z).registers j).2 : ℝ)) := by
    exact (measurable_of_countable fun a : ℕ × ℕ => (a.2 : ℝ)).comp
      ((measurable_pi_apply j).comp
        (measurable_fst.comp hreadout))
  change Measurable (fun z : Z =>
    Real.exp (beta * ((((incoming z).registers j).2 : ℝ) / (rate.n : ℝ))))
  exact Real.measurable_exp.comp
    (measurable_const.mul (hvalue.div_const (rate.n : ℝ)))

/-- The actual one-step post-update exponential is Borel. -/
theorem measurable_sourceXPlus (j : Fin p.K) :
    Measurable (sourceXPlus rate rewards C_star C_h u t j) := by
  have hreadout := measurable_coordinatorPostReadout rate rewards C_star C_h u t
  have hvalue : Measurable (fun z : Z =>
      (((coordinatorPostReadout rate rewards C_star C_h u t z).1 j).2 : ℝ)) := by
    exact (measurable_of_countable fun a : ℕ × ℕ => (a.2 : ℝ)).comp
      ((measurable_pi_apply j).comp (measurable_fst.comp hreadout))
  change Measurable (fun z : Z =>
    Real.exp (beta * ((((coordinatorPostReadout rate rewards C_star C_h u t z).1 j).2 : ℝ) /
      (rate.n : ℝ))))
  exact Real.measurable_exp.comp
    (measurable_const.mul (hvalue.div_const (rate.n : ℝ)))

/-- The complete incoming-prefix no-overflow event is Borel on the renewal
source. -/
theorem measurableSet_noPastOverflow :
    MeasurableSet (noPastOverflow rate rewards C_star C_h u t) := by
  have hreadout :=
    ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_incomingReadout
      rate rewards C_star C_h u t
  let flag : Z → Bool := fun z =>
      (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (incoming z)).2.1
  have hflag : Measurable flag := measurable_fst.comp (measurable_snd.comp hreadout)
  change MeasurableSet (flag ⁻¹' ({false} : Set Bool))
  exact hflag (MeasurableSet.singleton false)

/-- The literal no-past-overflow indicator is Borel. -/
theorem measurable_sourceIndicator :
    Measurable (sourceIndicator rate rewards C_star C_h u t) := by
  classical
  change Measurable (fun z : Z =>
    if z ∈ noPastOverflow rate rewards C_star C_h u t then (1 : ℝ) else 0)
  exact Measurable.ite
    (measurableSet_noPastOverflow rate rewards C_star C_h u t)
    measurable_const measurable_const

abbrev ActualPostReadoutIdentity (control0 : TimeControl p) (b : B)
    (d : ReferenceFirstCollectionRenewalAuxiliaryLaw.ActualRenewalCall
      rate rewards C_star C_h u t b.2)
    (recording : CoordinatorRecordingOperation.Output p) : Prop :=
  d.record = ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
      rate rewards C_star C_h u t b.2 ∧
    d.record.output.coordinator.recording = some recording ∧
    ReferenceFirstCollectionRenewalComplementMoments.v
        rate rewards C_star C_h u t b =
      AssignmentScoreReconstruction.currentWeight d.out ∧
    (∀ j : Fin p.K, recording.gateArm = some j ↔
      b ∈ ReferenceFirstCollectionRenewalGateCoefficient.gateEvent
        rate rewards C_star C_h u t j) ∧
    (∀ j : Fin p.K, recording.gateArm = some j →
      PublicDiscreteDraws.slotDraw (d.record.input.row.2 d.record.input.time).1 =
          PublicDiscreteDraws.dataSlot ∧
      PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
          (d.record.input.row.2 d.record.input.time).1 =
        ActiveRoundActions.coordinator p.two_le_m ∧
      d.record.output.preparation.feedback.feedback
          (ActiveRoundActions.coordinator p.two_le_m) = rewards t j ∧
      d.record.output.preparation.coordinatorObservation = rewards t j ∧
      (d.record.output.preparation.feedback.observations
          (ActiveRoundActions.coordinator p.two_le_m)).val.val =
        RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t j)) ∧
    ((incoming b.2).overflow = false ↔
      ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastLength
          rate rewards C_star C_h u t b.2 <
        UnstoppedRecordedQueueComparison.firstOverflowPrefix qp
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
            rate rewards C_star C_h u t b.2)) ∧
    (∀ j : Fin p.K,
      ReferenceFirstCollectionRenewalAcceptedComplementMoments.acceptedA
          rate rewards C_star C_h u t j b =
        if (incoming b.2).overflow then 0
        else if recording.gateArm = some j then
          (recording.rawArrival : ℝ) / (rate.eta.val * (D p : ℝ))
        else 0) ∧
    (∀ j : Fin p.K, b ∈
        ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
          rate rewards C_star C_h u t control0 →
      (AssignmentScoreReconstruction.sourceScore d.out j,
        AssignmentScoreReconstruction.initialQueue d.out j) =
          (incoming b.2).registers j) ∧
    (∀ j : Fin p.K,
      ReferenceFirstCollectionRenewalAcceptedComplementMoments.acceptedA
          rate rewards C_star C_h u t j b =
        ((RecordedQueueRun.acceptedRecord qp (incoming b.2)
          (ReferenceFirstCollectionRenewalAcceptedComplementMoments.actualNumericalCell
            rate rewards C_star C_h u t b d recording) j).2 : ℝ) /
          (rate.eta.val * (D p : ℝ))) ∧
    (∀ j : Fin p.K,
      ReferenceFirstCollectionRenewalQueuePostReadout.queueRecord
          rate rewards C_star C_h u t b j =
        RecordedQueueRun.acceptedRecord qp (incoming b.2)
          (ReferenceFirstCollectionRenewalAcceptedComplementMoments.actualNumericalCell
            rate rewards C_star C_h u t b d recording) j) ∧
    ReferenceFirstCollectionRenewalQueuePostReadout.postReadout
        rate rewards C_star C_h u t b =
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.step qp (incoming b.2)
          (ReferenceFirstCollectionRenewalAcceptedComplementMoments.actualNumericalCell
            rate rewards C_star C_h u t b d recording))

private theorem sourceRecording_eq_actual
    (z : Z) (d : ReferenceFirstCollectionRenewalAuxiliaryLaw.ActualRenewalCall
      rate rewards C_star C_h u t z)
    (recording : CoordinatorRecordingOperation.Output p)
    (hrecord : d.record = ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
      rate rewards C_star C_h u t z)
    (hrecording : d.record.output.coordinator.recording = some recording) :
    sourceRecording rate rewards C_star C_h u t z = recording := by
  have hoption : recOption rate rewards C_star C_h u t z = some recording := by
    rw [recOption, ← hrecord, hrecording]
  simp [sourceRecording, hoption]

private theorem vSource_eq_actual
    (z : Z) (d : ReferenceFirstCollectionRenewalAuxiliaryLaw.ActualRenewalCall
      rate rewards C_star C_h u t z) :
    vSource rate rewards C_star C_h u t z =
      AssignmentScoreReconstruction.currentWeight d.out := by
  let x := ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
    rate u d.record.input d.old d.ledger d.saved
  let ell := CoordinatorRoundDispatch.collectionOperationLedger x d.core.payload_n_eq
  have hselected := LaterAssignmentStartMeasurability.selectedSamplerParameters_renewal
    d.old ell d.instruction d.out d.reconstruction_eq d.renewal
  change (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
    rate rewards C_star C_h u t z).2 = _
  rw [d.parameter_eq]
  exact hselected.1

private theorem coordinatorCell_eq_actual
    (b : B) (d : ReferenceFirstCollectionRenewalAuxiliaryLaw.ActualRenewalCall
      rate rewards C_star C_h u t b.2)
    (recording : CoordinatorRecordingOperation.Output p)
    (hsource : sourceRecording rate rewards C_star C_h u t b.2 = recording) :
    coordinatorCell rate rewards C_star C_h u t b.2 =
      ReferenceFirstCollectionRenewalAcceptedComplementMoments.actualNumericalCell
        rate rewards C_star C_h u t b d recording := by
  have hv := vSource_eq_actual rate rewards C_star C_h u t b.2 d
  simp [coordinatorCell,
    ReferenceFirstCollectionRenewalAcceptedComplementMoments.actualNumericalCell,
    ReferenceFirstCollectionRenewalComplementMoments.r, hsource, hv]

/-- The original source projections agree with the accepted queue producer on
the same AE witness, retaining every field of that producer's identity. -/
theorem ae_actual_source_alignment (control0 : TimeControl p) :
    ∀ᵐ b : B ∂mu,
      ∃ d : ReferenceFirstCollectionRenewalAuxiliaryLaw.ActualRenewalCall
          rate rewards C_star C_h u t b.2,
        ∃ recording : CoordinatorRecordingOperation.Output p,
          ActualPostReadoutIdentity rate rewards C_star C_h u t control0 b d recording ∧
          sourceRecording rate rewards C_star C_h u t b.2 = recording ∧
          coordinatorCell rate rewards C_star C_h u t b.2 =
            ReferenceFirstCollectionRenewalAcceptedComplementMoments.actualNumericalCell
              rate rewards C_star C_h u t b d recording ∧
          coordinatorPostReadout rate rewards C_star C_h u t b.2 =
            ReferenceFirstCollectionRenewalQueuePostReadout.postReadout
              rate rewards C_star C_h u t b := by
  filter_upwards [ReferenceFirstCollectionRenewalQueuePostReadout.ae_actual_postReadout_identity
    rate rewards C_star C_h u t control0] with b hb
  rcases hb with ⟨d, recording, hrecord, hrecording, hweight, hgate, hfeedback,
    hstrict, harrival, hscore, haccepted, hrec, hpost⟩
  have hsource := sourceRecording_eq_actual rate rewards C_star C_h u t b.2 d
    recording hrecord hrecording
  have hcell := coordinatorCell_eq_actual rate rewards C_star C_h u t b d recording hsource
  have hidentity : ActualPostReadoutIdentity rate rewards C_star C_h u t control0 b d recording :=
    ⟨hrecord, hrecording, hweight, hgate, hfeedback, hstrict, harrival, hscore,
      haccepted, hrec, hpost⟩
  have hreadout : coordinatorPostReadout rate rewards C_star C_h u t b.2 =
      ReferenceFirstCollectionRenewalQueuePostReadout.postReadout
        rate rewards C_star C_h u t b := by
    change ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
      (RecordedQueueRun.step qp (incoming b.2)
        (coordinatorCell rate rewards C_star C_h u t b.2)) = _
    rw [hcell, ← hpost]
  exact ⟨d, recording, hidentity, hsource, hcell, hreadout⟩

/-- The incoming source exponential is the pair exponential after projection. -/
theorem sourceXMinus_eq_XMinus_comp_snd (control0 : TimeControl p)
    (j : Fin p.K) :
    (fun b : B => sourceXMinus rate rewards C_star C_h u t j b.2) =
      (fun b : B =>
        ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
          rate rewards C_star C_h u t control0 j b) := by
  funext b
  rfl

/-- The source post-update exponential uses the same full readout AE. -/
theorem ae_sourceXPlus_eq_XPlus (control0 : TimeControl p) (j : Fin p.K) :
    ∀ᵐ b : B ∂mu,
      sourceXPlus rate rewards C_star C_h u t j b.2 =
        ReferenceFirstCollectionRenewalExponentialQueueStep.XPlus
          rate rewards C_star C_h u t j b := by
  filter_upwards [ae_actual_source_alignment rate rewards C_star C_h u t control0]
    with b hb
  rcases hb with ⟨d, recording, _hidentity, _hsource, _hcell, hreadout⟩
  have hcount :
      ((coordinatorPostReadout rate rewards C_star C_h u t b.2).1 j).2 =
        (ReferenceFirstCollectionRenewalQueuePostReadout.postRegisters
          rate rewards C_star C_h u t b j).2 := by
    rw [hreadout]
    rfl
  have hback :
      (((coordinatorPostReadout rate rewards C_star C_h u t b.2).1 j).2 : ℝ) /
          (rate.n : ℝ) =
        ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
          rate rewards C_star C_h u t b j := by
    change (((coordinatorPostReadout rate rewards C_star C_h u t b.2).1 j).2 : ℝ) /
        (rate.n : ℝ) =
      (ReferenceFirstCollectionRenewalQueuePostReadout.postRegisters
        rate rewards C_star C_h u t b j).2 / (rate.n : ℝ)
    rw [hcount]
  simpa [sourceXPlus, ReferenceFirstCollectionRenewalExponentialQueueStep.XPlus,
    ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter,
    ReferenceFirstCollectionRenewalQueuePostReadout.postRegisters] using
      congrArg (fun x : ℝ => Real.exp (beta * x)) hback

/-- The source no-overflow marker is the pair retained-field marker AE. -/
theorem ae_sourceIndicator_eq_indicatorG (control0 : TimeControl p) :
    (fun b : B => sourceIndicator rate rewards C_star C_h u t b.2) =ᵐ[mu]
      (fun b : B =>
        ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
          rate rewards C_star C_h u t control0 b) := by
  classical
  filter_upwards [ReferenceFirstCollectionRenewalExponentialQueueStep.ae_G_iff_incoming_noOverflow
    rate rewards C_star C_h u t control0] with b hG
  change (if b.2 ∈ noPastOverflow rate rewards C_star C_h u t then (1 : ℝ) else 0) =
    if b ∈ ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
      rate rewards C_star C_h u t control0 then 1 else 0
  have hevent : b.2 ∈ noPastOverflow rate rewards C_star C_h u t ↔
      b ∈ ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
        rate rewards C_star C_h u t control0 := by
    change (incoming b.2).overflow = false ↔ _
    exact hG.symm
  rw [hevent]

/-- Integrability on the original renewal law follows from the pair law's
second marginal, without conditioning or normalizing its mass. -/
theorem integrable_sourceXMinus (control0 : TimeControl p) (j : Fin p.K) :
    Integrable (sourceXMinus rate rewards C_star C_h u t j) nu := by
  rw [← ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_map_snd
    rate rewards C_star C_h u t]
  have hcomp : Integrable
      ((sourceXMinus rate rewards C_star C_h u t j) ∘ Prod.snd) mu := by
    convert ReferenceFirstCollectionRenewalExponentialQueueStep.integrable_XMinus
      rate rewards C_star C_h u t control0 j using 1
    funext b
    rfl
  exact (integrable_map_measure
    (measurable_sourceXMinus rate rewards C_star C_h u t j).aestronglyMeasurable
    measurable_snd.aemeasurable).mpr hcomp

/-- The post-update source exponential is integrable by transport of the
existing pair-law result along the same-witness AE identity. -/
theorem integrable_sourceXPlus (control0 : TimeControl p) (j : Fin p.K) :
    Integrable (sourceXPlus rate rewards C_star C_h u t j) nu := by
  rw [← ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_map_snd
    rate rewards C_star C_h u t]
  have hcomp : Integrable
      ((sourceXPlus rate rewards C_star C_h u t j) ∘ Prod.snd) mu := by
    have hroot := ReferenceFirstCollectionRenewalExponentialQueueStep.integrable_XPlus
      rate rewards C_star C_h u t control0 j
    apply hroot.congr
    filter_upwards [ae_sourceXPlus_eq_XPlus rate rewards C_star C_h u t control0 j]
      with b hb
    exact hb.symm
  exact (integrable_map_measure
    (measurable_sourceXPlus rate rewards C_star C_h u t j).aestronglyMeasurable
    measurable_snd.aemeasurable).mpr hcomp

/-- Integrating a source function equals integrating its second-coordinate
pair representative. -/
theorem integral_sourceXMinus_eq_integral_XMinus
    (control0 : TimeControl p) (j : Fin p.K) :
    (∫ z : Z, sourceXMinus rate rewards C_star C_h u t j z ∂nu) =
      ∫ b : B,
        ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
          rate rewards C_star C_h u t control0 j b ∂mu := by
  rw [← ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_map_snd
    rate rewards C_star C_h u t]
  rw [integral_map measurable_snd.aemeasurable
    (measurable_sourceXMinus rate rewards C_star C_h u t j).aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ fun b => by
    rw [sourceXMinus_eq_XMinus_comp_snd rate rewards C_star C_h u t control0 j])

/-- The post-update source integral equals the existing pair-law integral. -/
theorem integral_sourceXPlus_eq_integral_XPlus
    (control0 : TimeControl p) (j : Fin p.K) :
    (∫ z : Z, sourceXPlus rate rewards C_star C_h u t j z ∂nu) =
      ∫ b : B,
        ReferenceFirstCollectionRenewalExponentialQueueStep.XPlus
          rate rewards C_star C_h u t j b ∂mu := by
  rw [← ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_map_snd
    rate rewards C_star C_h u t]
  rw [integral_map measurable_snd.aemeasurable
    (measurable_sourceXPlus rate rewards C_star C_h u t j).aestronglyMeasurable]
  exact integral_congr_ae
    (ae_sourceXPlus_eq_XPlus rate rewards C_star C_h u t control0 j)

/-- The source indicator has exactly its unnormalized no-past-overflow mass. -/
theorem integral_sourceIndicator_eq_mass :
    (∫ z : Z, sourceIndicator rate rewards C_star C_h u t z ∂nu) =
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t).real
        (noPastOverflow rate rewards C_star C_h u t) := by
  change (∫ z : Z,
    Set.indicator (noPastOverflow rate rewards C_star C_h u t)
      (fun _ : Z => (1 : ℝ)) z ∂nu) = _
  rw [integral_indicator_const (1 : ℝ)
    (measurableSet_noPastOverflow rate rewards C_star C_h u t)]
  simp

/-- Original-source, unweighted exponential transport with the literal
incoming-prefix no-overflow cost. -/
theorem integral_sourceXPlus_le_sourceXMinus_add_noPastOverflow
    (control0 : TimeControl p) (j : Fin p.K) :
    (∫ z : Z, sourceXPlus rate rewards C_star C_h u t j z ∂nu) ≤
      (∫ z : Z, sourceXMinus rate rewards C_star C_h u t j z ∂nu) +
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t).real
          (noPastOverflow rate rewards C_star C_h u t) := by
  have hpair :=
    ReferenceFirstCollectionRenewalExponentialQueueStep.integral_XPlus_le_integral_XMinus_add_G
      rate rewards C_star C_h u t control0 j
  have hGmeas : MeasurableSet
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
        rate rewards C_star C_h u t control0) := by
    have hfield :=
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurableSet_G_R
        rate rewards C_star C_h u t control0
    have hdom := ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
      rate rewards C_star C_h u t control0
    rcases hfield with ⟨S, hS, hpre⟩
    have hR : Measurable
        (ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates
          rate rewards C_star C_h u t control0) :=
      (comap_measurable _).mono hdom le_rfl
    rw [← hpre]
    exact hS.preimage hR
  have hcost :
      (∫ b : B,
        ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
          rate rewards C_star C_h u t control0 b ∂mu) =
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t).real
          (noPastOverflow rate rewards C_star C_h u t) := by
    calc
      _ = ∫ z : Z, sourceIndicator rate rewards C_star C_h u t z ∂nu := by
        rw [← ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_map_snd
          rate rewards C_star C_h u t]
        rw [integral_map measurable_snd.aemeasurable
          (measurable_sourceIndicator rate rewards C_star C_h u t).aestronglyMeasurable]
        exact integral_congr_ae
          (ae_sourceIndicator_eq_indicatorG rate rewards C_star C_h u t control0).symm
      _ = _ := integral_sourceIndicator_eq_mass rate rewards C_star C_h u t
  have hmass :
      (ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
        rate rewards C_star C_h u t).real
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
            rate rewards C_star C_h u t control0) =
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t).real
          (noPastOverflow rate rewards C_star C_h u t) := by
    calc
      _ = ∫ b : B,
          ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
            rate rewards C_star C_h u t control0 b ∂mu := by
        symm
        change (∫ b : B,
          Set.indicator
            (ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
              rate rewards C_star C_h u t control0)
            (fun _ : B => (1 : ℝ)) b ∂mu) = _
        rw [integral_indicator_const (1 : ℝ) hGmeas]
        simp
      _ = _ := hcost
  rw [← integral_sourceXPlus_eq_integral_XPlus rate rewards C_star C_h u t control0 j,
    ← integral_sourceXMinus_eq_integral_XMinus rate rewards C_star C_h u t control0 j,
    hmass] at hpair
  exact hpair

private theorem integrable_bounded_pair {f : B → ℝ} {C : ℝ}
    (hf : Measurable f) (_hC : 0 ≤ C) (hbound : ∀ b, ‖f b‖ ≤ C) :
    Integrable f mu := by
  have hconst : Integrable (fun _ : B => C) mu := integrable_const C
  refine hconst.mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with b
  simpa [Real.norm_eq_abs, abs_of_nonneg _hC] using hbound b

/-- Weighted source transport for every nonnegative bounded Borel function of
the incoming physical readout. Its pair representative is the exact retained
source used by the existing conditional-expectation producer. -/
theorem integral_weighted_sourceXPlus_le
    (control0 : TimeControl p) (j : Fin p.K)
    (psi : Readout p → ℝ) (Mbound : ℝ)
    (hpsiMeas : Measurable psi) (hMbound : 0 ≤ Mbound)
    (hpsiNonneg : ∀ x, 0 ≤ psi x) (hpsiBound : ∀ x, psi x ≤ Mbound) :
    (∫ z : Z, psi (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
        rate rewards C_star C_h u t z) * sourceXPlus rate rewards C_star C_h u t j z ∂nu) ≤
      (∫ z : Z, psi (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
        rate rewards C_star C_h u t z) * sourceXMinus rate rewards C_star C_h u t j z ∂nu) +
        ∫ z : Z, psi (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
          rate rewards C_star C_h u t z) * sourceIndicator rate rewards C_star C_h u t z ∂nu := by
  let Hret : B → ℝ := fun b =>
    psi (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
      rate rewards C_star C_h u t
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.erasedSource
        rate rewards C_star C_h u t control0 b.1.1))
  let testSource : Z → ℝ := fun z =>
    psi (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
      rate rewards C_star C_h u t z)
  have hHmeasField : Measurable[
      F_R control0] Hret := by
    change Measurable[F_R control0] (fun b : B =>
      psi (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
        rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.erasedSource
          rate rewards C_star C_h u t control0 b.1.1)))
    exact hpsiMeas.comp
      (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_retainedIncomingReadout
        rate rewards C_star C_h u t control0)
  have hHmeas : AEStronglyMeasurable[
      F_R control0] Hret mu :=
    hHmeasField.aestronglyMeasurable
  have hHnonneg : 0 ≤ᵐ[mu] Hret :=
    Filter.Eventually.of_forall (fun b => hpsiNonneg _)
  have hHbound : ∀ b : B, ‖Hret b‖ ≤ Mbound := by
    intro b
    rw [Real.norm_eq_abs, abs_of_nonneg (hpsiNonneg _)]
    exact hpsiBound _
  have hHint : Integrable Hret mu := by
    have hHambient : Measurable Hret := hHmeasField.mono
      (ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
        rate rewards C_star C_h u t control0) le_rfl
    exact integrable_bounded_pair rate rewards C_star C_h u t
      hHambient hMbound hHbound
  have hreadout : Hret =ᵐ[mu] fun b : B => testSource b.2 := by
    filter_upwards [ReferenceFirstCollectionRenewalIncomingQueueMeasurability.ae_incomingReadout_eq_retained
      rate rewards C_star C_h u t control0] with b hb
    dsimp [Hret, testSource]
    exact congrArg psi hb.symm
  have hplusPair :
      (fun b : B => Hret b *
        ReferenceFirstCollectionRenewalExponentialQueueStep.XPlus
          rate rewards C_star C_h u t j b) =ᵐ[mu]
      (fun b : B => testSource b.2 * sourceXPlus rate rewards C_star C_h u t j b.2) := by
    filter_upwards [hreadout,
      ae_sourceXPlus_eq_XPlus rate rewards C_star C_h u t control0 j] with b htest hplus
    rw [htest, ← hplus]
  have hminusPair :
      (fun b : B => Hret b *
        ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
          rate rewards C_star C_h u t control0 j b) =ᵐ[mu]
      (fun b : B => testSource b.2 * sourceXMinus rate rewards C_star C_h u t j b.2) := by
    filter_upwards [hreadout] with b htest
    rw [htest, ← congrFun (sourceXMinus_eq_XMinus_comp_snd
      rate rewards C_star C_h u t control0 j) b]
  have hcostPair :
      (fun b : B => Hret b *
        ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
          rate rewards C_star C_h u t control0 b) =ᵐ[mu]
      (fun b : B => testSource b.2 * sourceIndicator rate rewards C_star C_h u t b.2) := by
    filter_upwards [hreadout,
      ae_sourceIndicator_eq_indicatorG rate rewards C_star C_h u t control0] with
      b htest hind
    rw [htest, ← hind]
  have htestSourceMeas : Measurable testSource := by
    change Measurable (fun z : Z => psi
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
        rate rewards C_star C_h u t z))
    exact hpsiMeas.comp
      (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_incomingReadout
        rate rewards C_star C_h u t)
  have hplusMeas : Measurable
      (fun z : Z => testSource z * sourceXPlus rate rewards C_star C_h u t j z) :=
    htestSourceMeas.mul (measurable_sourceXPlus rate rewards C_star C_h u t j)
  have hminusMeas : Measurable
      (fun z : Z => testSource z * sourceXMinus rate rewards C_star C_h u t j z) :=
    htestSourceMeas.mul (measurable_sourceXMinus rate rewards C_star C_h u t j)
  have hcostMeas : Measurable
      (fun z : Z => testSource z * sourceIndicator rate rewards C_star C_h u t z) :=
    htestSourceMeas.mul (measurable_sourceIndicator rate rewards C_star C_h u t)
  have hplusIntegral :
      (∫ b : B, Hret b *
        ReferenceFirstCollectionRenewalExponentialQueueStep.XPlus
          rate rewards C_star C_h u t j b ∂mu) =
      ∫ z : Z, testSource z * sourceXPlus rate rewards C_star C_h u t j z ∂nu := by
    calc
      _ = ∫ b : B, testSource b.2 * sourceXPlus rate rewards C_star C_h u t j b.2 ∂mu :=
        integral_congr_ae hplusPair
      _ = _ := by
        symm
        rw [← ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_map_snd
          rate rewards C_star C_h u t]
        rw [integral_map measurable_snd.aemeasurable hplusMeas.aestronglyMeasurable]
  have hminusIntegral :
      (∫ b : B, Hret b *
        ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
          rate rewards C_star C_h u t control0 j b ∂mu) =
      ∫ z : Z, testSource z * sourceXMinus rate rewards C_star C_h u t j z ∂nu := by
    calc
      _ = ∫ b : B, testSource b.2 * sourceXMinus rate rewards C_star C_h u t j b.2 ∂mu :=
        integral_congr_ae hminusPair
      _ = _ := by
        symm
        rw [← ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_map_snd
          rate rewards C_star C_h u t]
        rw [integral_map measurable_snd.aemeasurable hminusMeas.aestronglyMeasurable]
  have hcostIntegral :
      (∫ b : B, Hret b *
        ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
          rate rewards C_star C_h u t control0 b ∂mu) =
      ∫ z : Z, testSource z * sourceIndicator rate rewards C_star C_h u t z ∂nu := by
    calc
      _ = ∫ b : B, testSource b.2 * sourceIndicator rate rewards C_star C_h u t b.2 ∂mu :=
        integral_congr_ae hcostPair
      _ = _ := by
        symm
        rw [← ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_map_snd
          rate rewards C_star C_h u t]
        rw [integral_map measurable_snd.aemeasurable hcostMeas.aestronglyMeasurable]
  have hpair :=
    ReferenceFirstCollectionRenewalExponentialQueueStep.integral_mul_XPlus_le
      rate rewards C_star C_h u t control0 j hHmeas hHnonneg hHint
  rw [hplusIntegral, hminusIntegral, hcostIntegral] at hpair
  exact hpair

/-- Borel-set specialization of weighted transport. The cost is the source
mass of the physical readout set intersected with no past overflow. -/
theorem integral_readoutSet_sourceXPlus_le
    (control0 : TimeControl p) (j : Fin p.K) (Dtest : Set (Readout p))
    (hDtest : MeasurableSet Dtest) :
    (∫ z : Z,
      (Dtest.indicator (fun _ : Readout p => (1 : ℝ)))
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
          rate rewards C_star C_h u t z) * sourceXPlus rate rewards C_star C_h u t j z ∂nu) ≤
      (∫ z : Z,
        (Dtest.indicator (fun _ : Readout p => (1 : ℝ)))
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
            rate rewards C_star C_h u t z) * sourceXMinus rate rewards C_star C_h u t j z ∂nu) +
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t).real
          ({z | ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
              rate rewards C_star C_h u t z ∈ Dtest} ∩
            noPastOverflow rate rewards C_star C_h u t) := by
  let psi : Readout p → ℝ := Dtest.indicator (fun _ => (1 : ℝ))
  let ER : Z → Readout p :=
    ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
      rate rewards C_star C_h u t
  have hpsiMeas : Measurable psi := by
    change Measurable (Dtest.indicator (fun _ : Readout p => (1 : ℝ)))
    exact Measurable.indicator measurable_const hDtest
  have hcost :
      (∫ z : Z, psi (ER z) * sourceIndicator rate rewards C_star C_h u t z ∂nu) =
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t).real
          (ER ⁻¹' Dtest ∩ noPastOverflow rate rewards C_star C_h u t) := by
    classical
    have hset : MeasurableSet
        (ER ⁻¹' Dtest ∩ noPastOverflow rate rewards C_star C_h u t) :=
      (hDtest.preimage
        (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_incomingReadout
          rate rewards C_star C_h u t)).inter
        (measurableSet_noPastOverflow rate rewards C_star C_h u t)
    have hpoint :
        (fun z : Z => psi (ER z) * sourceIndicator rate rewards C_star C_h u t z) =
          Set.indicator (ER ⁻¹' Dtest ∩ noPastOverflow rate rewards C_star C_h u t)
            (fun _ : Z => (1 : ℝ)) := by
      funext z
      by_cases hd : ER z ∈ Dtest <;>
        by_cases ho : (incoming z).overflow = false <;>
        simp [psi, ER, sourceIndicator, noPastOverflow, Set.indicator,
          Set.mem_inter_iff, Set.mem_preimage, hd, ho]
    calc
      _ = ∫ z : Z,
          Set.indicator (ER ⁻¹' Dtest ∩ noPastOverflow rate rewards C_star C_h u t)
            (fun _ : Z => (1 : ℝ)) z ∂nu := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z => congrFun hpoint z)
      _ = _ := by
        rw [integral_indicator_const (1 : ℝ) hset]
        simp
  have hweighted := integral_weighted_sourceXPlus_le
    rate rewards C_star C_h u t control0 j psi 1 hpsiMeas (by norm_num)
    (by intro x; by_cases hx : x ∈ Dtest <;> simp [psi, hx])
    (by intro x; by_cases hx : x ∈ Dtest <;> simp [psi, hx])
  rw [hcost] at hweighted
  change _ ≤ _ + (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
    rate rewards C_star C_h u t).real (ER ⁻¹' Dtest ∩
      noPastOverflow rate rewards C_star C_h u t)
  exact hweighted

end Bandits.Support.ReferenceFirstCollectionRenewalSourceExponentialTransport

end
