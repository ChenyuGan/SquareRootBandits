/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalCallFirstEmptyBoundary

/-!
# Actual first-renewal installation and live service tail

Sources: `sources/zip4/manuscript/06_interruptions.tex:40-69,399-423`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-215`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`, and
`sources/zip4/manuscript/07_public_setup.tex:121-164`.

On the existing renewal installation coupling's pair law, this module keeps
the same actual renewal call and proves that its literal coordinator recorder,
complement service, confirmation, and phase-clock finish all succeed. The
joint stored score/queue bound includes the arrival of this round, including
the first overflow update. This is an internal coordinator tail, not a claim
about all-arm physical replay or manuscript theorem closure.
-/

@[expose] public section

namespace Bandits.Support.ReferenceFirstCollectionRenewalInstalledServiceTail

private theorem recorder_run_some_of_local_inputs_valid
    {p : ConstructorDimensions.Parameters}
    {eta : ReferencePrelaunchFollower.LearningRate}
    {s : AssignmentStartPayload.Input p eta}
    (input : CoordinatorRecorderComplementBridge.Input s)
    (hvalid : CoordinatorRecorderComplementBridge.LocalInputsValid input) :
    ∃ recording : CoordinatorRecordingOperation.Output p,
      CoordinatorRecorderComplementBridge.run input = some recording := by
  classical
  let operationInput := CoordinatorRecorderComplementBridge.recorderInput input
  have operationValid := CoordinatorRecorderComplementBridge.recorderInput_inputsValid
    input hvalid
  have lift {recording : CoordinatorRecordingOperation.Output p}
      (h : CoordinatorRecordingOperation.executeValid operationInput operationValid =
        some recording) :
      CoordinatorRecorderComplementBridge.run input = some recording := by
    rw [CoordinatorRecorderComplementBridge.run_eq_executeValid input hvalid]
    exact h
  by_cases hdata : CoordinatorRecordingOperation.selectedSlot operationInput =
      PublicDiscreteDraws.dataSlot
  · by_cases hsource : CoordinatorRecordingOperation.selectedRecorder operationInput =
        ActiveRoundActions.coordinator p.two_le_m
    · by_cases hfrozen : CoordinatorRecordingOperation.isFrozen operationInput
      · exact ⟨CoordinatorRecordingOperation.zeroOutput p,
          lift (CoordinatorRecordingOperation.executeValid_zero_of_frozen
            operationInput operationValid hdata hsource hfrozen)⟩
      · by_cases howned : CoordinatorRecordingOperation.ownsArm
            operationInput.mode operationInput.ownArm
        · by_cases hmask : CoordinatorRecordingOperation.ownMaskPasses operationInput
          · by_cases hthin : (ContinuousControlSlice.coordinate
                ContinuousControlSlice.Label.thin
                (ContinuousLearningRows.sliceAt operationInput.time
                  operationInput.row.2)).val ≤
                CoordinatorRecordingOperation.coordinatorThreshold operationInput
                  operationValid
            · refine ⟨⟨some operationInput.ownArm,
                  CoordinatorRecordingOperation.floorArrival operationInput,
                  CoordinatorRecordingOperation.floorArrival_le_D operationInput
                    operationValid⟩, ?_⟩
              exact lift (CoordinatorRecordingOperation.executeValid_recorded_of_gate
                operationInput operationValid hdata hsource hfrozen howned hmask hthin)
            · exact ⟨CoordinatorRecordingOperation.zeroOutput p,
                lift (CoordinatorRecordingOperation.executeValid_zero_of_thinning_rejected
                  operationInput operationValid hdata hsource hfrozen howned hmask hthin)⟩
          · exact ⟨CoordinatorRecordingOperation.zeroOutput p,
              lift (CoordinatorRecordingOperation.executeValid_zero_of_mask_rejected
                operationInput operationValid hdata hsource hfrozen howned hmask)⟩
        · exact ⟨CoordinatorRecordingOperation.zeroOutput p,
            lift (CoordinatorRecordingOperation.executeValid_zero_of_unowned
              operationInput operationValid hdata hsource hfrozen howned)⟩
    · exact ⟨CoordinatorRecordingOperation.zeroOutput p,
        lift (CoordinatorRecordingOperation.executeValid_zero_of_other_source
          operationInput operationValid hdata hsource)⟩
  · exact ⟨CoordinatorRecordingOperation.zeroOutput p,
      lift (CoordinatorRecordingOperation.executeValid_zero_of_not_data
        operationInput operationValid hdata)⟩

/-- The actual installed first renewal start performs its literal recorder,
complement service, confirmation update, and `FinishRound` on the same
pair-law witness supplied by the installation coupling. The service budget
uses the joint score-plus-queue estimate and includes this round's arrival. -/
theorem ae_pairLaw_actual_service_tail
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    ∀ᵐ b : ReferenceFirstCollectionRenewalInstallationCoupling.RenewalBase
        rate rewards C_star C_h u t ×
      ReferenceFirstCollectionRenewalInstallationCoupling.Source
        rate rewards C_star C_h u t ∂
        ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
          rate rewards C_star C_h u t,
    let z := b.1.1
    let a := b.1.2
    let z' := b.2
    let U := ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
      rate rewards C_star C_h u t z a
    ∃ d : ReferenceFirstCollectionRenewalAuxiliaryLaw.ActualRenewalCall
        rate rewards C_star C_h u t z',
      let x := ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
        rate u d.record.input d.old d.ledger d.saved
      let ell : LaterAssignmentStartOperation.LocalLedger x.payload :=
        CoordinatorRoundDispatch.collectionOperationLedger x d.core.payload_n_eq
      let par := LaterAssignmentStartMeasurability.selectedSamplerParameters
        x.payload ell d.instruction d.out d.reconstruction_eq
      let v := LaterAssignmentStartOperation.ownAssignmentVector
        d.record.input.row d.instruction.time
      let clock := ReferenceActivePhysicalStep.collectionClock d.old d.ledger d.saved u
      ∃ consistent : LaterAssignmentStartOperation.LocalConsistency x.payload ell,
        ∃ output : LaterAssignmentStartOperation.SuccessfulStart
          x.payload ell d.instruction x.row,
          ∃ hlocal : output.localConsistency = consistent,
            LaterAssignmentStartOperation.laterAssignmentStart
                x.payload ell d.instruction x.row consistent =
              .success output hlocal ∧
            v = output.assignmentVector ∧
            output.reconstruction = d.out ∧
            AssignmentParameterFibreKernel.successfulSlowSet p par v =
              some output.slowSet ∧
            output.slowSet = U ∧
            output.payload.slowSet = U ∧
            let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence
                output := {
              priorClock := x.clock
              pending := x.ledger.pending
              proposalParameterValid := d.core.clock_parameter_valid
              priorClockValid := d.core.clock_registers_valid
              startTimeValid := by
                simpa only [x,
                  ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
                  ReferenceActivePhysicalStep.collectionInput,
                  d.instruction_time] using d.core.clock_start_time_valid
              result := d.started
              startRound_eq := by
                simpa only [x,
                  ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
                  ReferenceActivePhysicalStep.collectionInput,
                  ReferenceActivePhysicalStep.collectionClock,
                  d.instruction_time] using d.clock_eq
              assignmentStart_eq := d.instruction_eq
              priorSigma_eq := d.core.clock_sigma_eq
              priorGrid_eq_freezeAt := by
                calc
                  x.clock.g = x.ledger.freezeAt := d.core.ledger_freeze_eq.symm
                  _ = consistent.oldFreezeAt := consistent.oldFreezeAt_eq.symm
                  _ = output.localConsistency.oldFreezeAt := by rw [hlocal] }
            let installed := CoordinatorAssignmentRegisterInstall.installLater
              output clockData
            installed.registers.payload = output.payload ∧
            output.assignmentVector = installed.assignmentVector ∧
            installed.reconstruction = d.out ∧
            installed.registers.payload.anchor =
              AssignmentScoreReconstruction.currentWeight d.out ∧
            (∀ arm, installed.registers.payload.queues arm =
              AssignmentScoreReconstruction.initialQueue d.out arm) ∧
            (∀ i, installed.retainedBaseScore i =
              AssignmentScoreReconstruction.sourceScore d.out
                (output.payload.assignment.assigned i)) ∧
            installed.registers.payload.slowSet = U ∧
            ∃ selection : CoordinatorRoundDispatch.ArmSelection
                installed.registers.payload d.started d.instruction.time
                installed.registers.complementWeights d.record.input.row,
              CoordinatorLocalArmChoice.coordinatorArmChoice
                  installed.registers.payload d.started.pending
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u)
                  d.instruction.time installed.registers.complementWeights d.record.input.row =
                some selection.arm ∧
              CoordinatorRoundDispatch.dispatchCollection x =
                .laterChosen d.core consistent d.started d.clock_eq d.instruction
                  d.instruction_eq output hlocal clockData installed selection ∧
              d.record.output.preparation =
                ReferenceActivePhysicalStep.prepare d.record.input ∧
              d.record.output.preparation.coordinator =
                .collection d.old d.ledger clock u
                  (CoordinatorRoundDispatch.dispatchCollection x) ∧
              d.record.output.preparation.coordinator.arm = selection.arm ∧
              d.record.output.coordinator =
                ReferenceActivePhysicalStep.livePostChoice
                  (ReferenceActivePhysicalStep.prepare d.record.input)
                  installed.registers installed.ownedRegisters installed.retainedBaseScore
                  d.started ∧
              d.record.output.next.coordinator =
                (ReferenceActivePhysicalStep.livePostChoice
                  (ReferenceActivePhysicalStep.prepare d.record.input)
                  installed.registers installed.ownedRegisters installed.retainedBaseScore
                  d.started).configuration ∧
              let r := installed.registers
              let q := installed.ownedRegisters
              let base := installed.retainedBaseScore
              let P := ReferenceActivePhysicalStep.prepare d.record.input
              ∃ recording : CoordinatorRecordingOperation.Output p,
              ∃ serviced : CoordinatorLiveServiceFinish.ServicedRegisters
                  r q,
              ∃ pending : Finset (Fin (p.m - 1)),
              ∃ finished : CoordinatorPhaseClock.FinishRoundResult p,
                CoordinatorRecorderComplementBridge.run
                    (ReferenceActivePhysicalStep.liveRecordingInput
                      P r d.started) = some recording ∧
                CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced ∧
                CoordinatorLocalArmChoice.confirmationUpdate
                  r.payload d.started.pending
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u)
                  d.record.input.time d.record.input.row
                  P.coordinatorObservation = some pending ∧
                CoordinatorPhaseClock.finishRound p rate.eta.val d.record.input.time
                  d.started.clock pending d.record.input.row = .ok finished ∧
                d.record.output.coordinator =
                  ReferenceActivePhysicalStep.livePostChoice P r q base d.started ∧
                d.record.output.coordinator.failure = none ∧
                d.record.output.coordinator.recording = some recording ∧
                d.record.output.coordinator.up = none ∧
                d.record.output.coordinator.configuration =
                  .live { payload := r.payload
                          priorClock := finished.clock
                          pendingAtChoice := finished.pending
                          time := d.record.input.time
                          gridBoundary := finished.clock.g
                          complementScores := serviced.score }
                    { queue := serviced.queue
                      previousService := serviced.previousService }
                    base ∧
                d.record.output.next.coordinator =
                  .live { payload := r.payload
                          priorClock := finished.clock
                          pendingAtChoice := finished.pending
                          time := d.record.input.time
                          gridBoundary := finished.clock.g
                          complementScores := serviced.score }
                    { queue := serviced.queue
                      previousService := serviced.previousService }
                    base ∧
                (∀ j : CanonicalFastSampling.FastArm
                    r.payload.slowSet,
                  serviced.score j + serviced.queue j ≤
                    (t.val - ReferenceFirstCollectionReadyStream.startTime
                      (rate := rate) b.2.val rewards C_star C_h + 1) *
                      ConstructorDimensions.D p) ∧
                (t.val - ReferenceFirstCollectionReadyStream.startTime
                    (rate := rate) b.2.val rewards C_star C_h + 1) *
                    ConstructorDimensions.D p ≤ p.T * ConstructorDimensions.D p := by
  classical
  filter_upwards
    [ReferenceFirstCollectionRenewalInstallationCoupling.ae_pairLaw_actual_installation
      rate rewards C_star C_h u t] with b hb
  dsimp only at hb
  rcases hb with ⟨d, consistent, output, hlocal, hstart, hv, hreconstruction,
    hsample, hslow, hpayloadSlow, htail⟩
  let x := ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
    rate u d.record.input d.old d.ledger d.saved
  let ell : LaterAssignmentStartOperation.LocalLedger x.payload :=
    CoordinatorRoundDispatch.collectionOperationLedger x d.core.payload_n_eq
  let par := LaterAssignmentStartMeasurability.selectedSamplerParameters
    x.payload ell d.instruction d.out d.reconstruction_eq
  let v := LaterAssignmentStartOperation.ownAssignmentVector
    d.record.input.row d.instruction.time
  let clock := ReferenceActivePhysicalStep.collectionClock d.old d.ledger d.saved u
  let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output := {
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
        ReferenceActivePhysicalStep.collectionClock, d.instruction_time] using d.clock_eq
    assignmentStart_eq := d.instruction_eq
    priorSigma_eq := d.core.clock_sigma_eq
    priorGrid_eq_freezeAt := by
      calc
        x.clock.g = x.ledger.freezeAt := d.core.ledger_freeze_eq.symm
        _ = consistent.oldFreezeAt := consistent.oldFreezeAt_eq.symm
        _ = output.localConsistency.oldFreezeAt := by rw [hlocal] }
  let installed := CoordinatorAssignmentRegisterInstall.installLater output clockData
  rcases htail with ⟨hinstalledPayload, hinstalledVector, hinstalledReconstruction,
    hanchor, hqueues, hbase, hinstalledSlow, selection, hselection, hdispatch,
    hpreparation, hpreparationCoordinator, hselectedArm, hpostChoice, hnextChoice⟩
  let P : ReferenceActivePhysicalStep.PreparedRound d.record.input :=
    ReferenceActivePhysicalStep.prepare d.record.input
  let r := installed.registers
  let q := installed.ownedRegisters
  let base := installed.retainedBaseScore
  let s := ReferenceFirstCollectionReadyStream.startTime
    (rate := rate) b.2.val rewards C_star C_h
  have hbudget :=
    ReferenceFirstCollectionRenewalCallFirstEmptyBoundary.actual_renewal_call_joint_budget
      rate rewards C_star C_h u t b.2 d
  have hbudgetAll : ∀ arm : Fin p.K,
      AssignmentScoreReconstruction.sourceScore d.out arm +
        AssignmentScoreReconstruction.initialQueue d.out arm ≤
          (t.val - s) * ConstructorDimensions.D p := by
    simpa only [s] using hbudget
  have hsourceScore : ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      r.complementScores j = AssignmentScoreReconstruction.sourceScore d.out j.1 := by
    intro j
    change (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.complementScores j = _
    rw [CoordinatorAssignmentRegisterInstall.later_complement_score_eq_source_score
      output clockData j, hreconstruction]
  have hinitialQueue : ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      q.queue j = AssignmentScoreReconstruction.initialQueue d.out j.1 := by
    intro j
    change (CoordinatorAssignmentRegisterInstall.installLater output clockData).ownedRegisters.queue j = _
    rw [CoordinatorAssignmentRegisterInstall.later_owned_queue_eq_initial_queue
      output clockData j, hreconstruction]
  have hmass : ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      r.complementScores j + q.queue j ≤ (t.val - s) * ConstructorDimensions.D p := by
    intro j
    simpa only [hsourceScore j, hinitialQueue j] using hbudgetAll j.1
  have hweight : ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      r.complementWeights j = r.payload.anchor j.1 := by
    intro j
    change ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
      (r.complementScores j) = (installed.registers.payload.anchor) j.1
    rw [hsourceScore j]
    exact (congrArg (fun weights : Fin p.K → ℝ => weights j.1) hanchor).symm
  have henvelope : r.complementEnvelopeValid := by
    intro j
    rw [hweight j]
    exact ⟨le_rfl, by linarith [r.payload.anchor_pos j.1]⟩
  have hrecorderInputs : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.liveRecordingInput P r d.started) := by
    constructor
    · change d.started.clock.g ≤ p.T + 1
      exact CoordinatorPhaseClock.startRoundResult_grid_upper_bound p d.started
    · exact henvelope
  obtain ⟨recording, hrecord⟩ := recorder_run_some_of_local_inputs_valid
    (ReferenceActivePhysicalStep.liveRecordingInput P r d.started) hrecorderInputs
  have hregisterDomains :=
    CoordinatorAssignmentRegisterInstall.later_register_domains output clockData
  have hqueueInput : q.queueDomainValid := hregisterDomains.2.1
  have hpreviousInput : q.previousServiceDomainValid := hregisterDomains.2.2
  let arrival : CanonicalFastSampling.FastArm r.payload.slowSet → ℕ := fun j =>
    CoordinatorLiveServiceFinish.complementArrival r.payload recording j
  let service : CanonicalFastSampling.FastArm r.payload.slowSet → ℕ := fun j =>
    CappedService.service (4 * r.payload.n) (q.queue j) (arrival j)
  let queue : CanonicalFastSampling.FastArm r.payload.slowSet → ℕ := fun j =>
    CappedService.residual (4 * r.payload.n) (q.queue j) (arrival j)
  let score : CanonicalFastSampling.FastArm r.payload.slowSet → ℕ := fun j =>
    r.complementScores j + service j
  have harrival : ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      arrival j ≤ ConstructorDimensions.D p := by
    intro j
    by_cases hgate : recording.gateArm = some j.1
    · simp [arrival, CoordinatorLiveServiceFinish.complementArrival, hgate,
        recording.rawArrival_le_D]
    · simp [arrival, CoordinatorLiveServiceFinish.complementArrival, hgate]
  have hcapacity : 4 * r.payload.n ≤ ConstructorDimensions.D p := by
    rw [ReferenceActivePhysicalStep.payload_n_eq r.payload]
    exact ActiveFollowerDownAcceptance.four_n_le_D p rate
  have hserviceDomain : ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      service j ≤ ConstructorDimensions.D p := by
    intro j
    exact (CappedService.service_le_capacity (4 * r.payload.n) (q.queue j)
      (arrival j)).trans hcapacity
  have hconservation : ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      score j + queue j = r.complementScores j + q.queue j + arrival j := by
    intro j
    calc
      score j + queue j = r.complementScores j +
          (queue j + service j) := by dsimp [score]; omega
      _ = r.complementScores j + (q.queue j + arrival j) := by
        dsimp [queue, service, arrival]
        rw [CappedService.residual_add_service]
      _ = r.complementScores j + q.queue j + arrival j := by omega
  have hstepScale :
      (t.val - s) * ConstructorDimensions.D p + ConstructorDimensions.D p =
        (t.val - s + 1) * ConstructorDimensions.D p := by
    rw [Nat.add_mul, one_mul]
  have htotal : ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      score j + queue j ≤ (t.val - s + 1) * ConstructorDimensions.D p := by
    intro j
    calc
      score j + queue j = r.complementScores j + q.queue j + arrival j :=
        hconservation j
      _ ≤ (t.val - s) * ConstructorDimensions.D p + ConstructorDimensions.D p :=
        Nat.add_le_add (hmass j) (harrival j)
      _ = (t.val - s + 1) * ConstructorDimensions.D p := hstepScale
  have hroundCount : t.val - s + 1 ≤ p.T := by omega
  have htotalHorizon :
      (t.val - s + 1) * ConstructorDimensions.D p ≤
        p.T * ConstructorDimensions.D p :=
    Nat.mul_le_mul_right _ hroundCount
  have hscoreOutput : ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      score j ≤ p.T * ConstructorDimensions.D p := by
    intro j
    have h := (htotal j).trans htotalHorizon
    dsimp [score, queue] at h ⊢
    omega
  have hqueueOutput : ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      queue j ≤ p.T * ConstructorDimensions.D p := by
    intro j
    have h := (htotal j).trans htotalHorizon
    dsimp [score, queue] at h ⊢
    omega
  let serviced : CoordinatorLiveServiceFinish.ServicedRegisters r q := {
    recording := recording
    arrival := arrival
    service := service
    queue := queue
    score := score
    previousService := service
    arrivalDomain := harrival
    serviceDomain := hserviceDomain
    queueDomain := hqueueOutput
    scoreDomain := hscoreOutput
    previousServiceDomain := hserviceDomain
    arrival_eq := by intro j; rfl
    service_eq := by intro j; rfl
    queue_eq := by intro j; rfl
    score_eq := by intro j; rfl
    previousService_eq := by intro j; rfl }
  have hservice : CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced := by
    unfold CoordinatorLiveServiceFinish.servicePass
    dsimp only [arrival, service, queue, score] at harrival hserviceDomain hscoreOutput hqueueOutput
    simp only [dite_eq_left hqueueInput, dite_eq_left hpreviousInput,
      dite_eq_left harrival, dite_eq_left hserviceDomain,
      dite_eq_left hscoreOutput, dite_eq_left hqueueOutput]
    apply congrArg Except.ok
    rfl
  have hpayloadStart : r.payload.sigma = d.record.input.time := by
    calc
      r.payload.sigma = output.payload.sigma := rfl
      _ = d.instruction.time := output.payload_start
      _ = d.record.input.time := d.instruction_time
  have hlaterFrame :=
    CoordinatorAssignmentRegisterInstall.later_start_round_compatibility output clockData
  rcases hlaterFrame with ⟨_, hsigma, hu, hgrid, _, hpending, _, _, _⟩
  have hsigma' : d.started.clock.sigma = some d.instruction.time := by
    change clockData.result.clock.sigma = some d.instruction.time
    exact hsigma
  have hu' : d.started.clock.u = none := by
    change clockData.result.clock.u = none
    exact hu
  have hstartedTime : CoordinatorLocalArmChoice.assignmentStart r.payload ≤
      CoordinatorLocalArmChoice.sourceRound d.record.input.time := by
    simp [CoordinatorLocalArmChoice.assignmentStart,
      CoordinatorLocalArmChoice.sourceRound, hpayloadStart]
  have hcutoffTime : CoordinatorLocalArmChoice.assignmentStart r.payload ≤
      CoordinatorLocalArmChoice.cutoffRound
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u) := by
    rw [CoordinatorLocalArmChoice.assignmentStart, hpayloadStart,
      CoordinatorLiveChoiceRecorderStep.cutoffRoundFromClock]
    rw [hu']
    simp
  have hconfirmationInputs := CoordinatorLocalArmChoice.confirmationInputsValid_mk
    r.payload (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u)
    d.record.input.time hstartedTime hcutoffTime
  let timeControl := d.record.input.row.2 d.record.input.time
  let pending : Finset (Fin (p.m - 1)) :=
    if CoordinatorLocalArmChoice.downConfirmationEvent r.payload d.started.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u)
        d.record.input.time timeControl P.coordinatorObservation then
      d.started.pending.erase (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m
        p.m_lt_K timeControl.1)
    else d.started.pending
  have hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate r.payload
      d.started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u)
      d.record.input.time d.record.input.row P.coordinatorObservation = some pending := by
    change CoordinatorLocalArmChoice.confirmationUpdateCore r.payload d.started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u)
      d.record.input.time (d.record.input.row.2 d.record.input.time)
      P.coordinatorObservation = some pending
    simp only [CoordinatorLocalArmChoice.confirmationUpdateCore,
      dite_eq_left hconfirmationInputs, pending, timeControl]
    rfl
  have hgridDomain :
      d.instruction.time.val + 1 < d.started.clock.g ∧
        d.started.clock.g ≤ p.T + 1 := by
    have hgd := d.started.gridDomain
    simp only [CoordinatorPhaseClock.clockGridDomain, hsigma'] at hgd
    exact hgd
  have hclockDomain : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val
      d.started.clock := by
    unfold CoordinatorPhaseClock.clockRegistersValid
    constructor
    · rw [hsigma', CoordinatorPhaseClock.boundaryFromSigma]
      exact hgrid
    · rw [hsigma']
      exact ⟨hgridDomain.1, hgridDomain.2, by simp [hu']⟩
  have hfinishTime : CoordinatorPhaseClock.finishRoundTimeValid
      d.record.input.time d.started.clock := by
    simp only [CoordinatorPhaseClock.finishRoundTimeValid, hsigma', hu',
      d.instruction_time, FollowerCutoffScan.calendarRound]
    refine ⟨by omega, ?_⟩
    rw [← d.instruction_time]
    exact Nat.le_of_lt hgridDomain.1
  have hsigmaNe : d.started.clock.sigma ≠ none := by
    rw [hsigma']
    simp
  obtain ⟨finished, hfinish, _, _, _⟩ :=
    CoordinatorPhaseClock.finishRound_live_savedProposal p rate.eta.val
      d.record.input.time d.started.clock pending d.record.input.row hclockDomain
      hfinishTime hsigmaNe hu clockData.proposalParameterValid
  have hpost := ReferenceActivePhysicalStep.livePostChoice_success P r q base d.started
    recording serviced pending finished hrecord hservice hconfirmation hfinish
  have hcoordinator : d.record.output.coordinator =
      ReferenceActivePhysicalStep.livePostChoice P r q base d.started := by
    simpa [P, r, q, base] using hpostChoice
  have hfailure : d.record.output.coordinator.failure = none := by
    rw [hcoordinator, hpost]
  have hrecordingField : d.record.output.coordinator.recording = some recording := by
    rw [hcoordinator, hpost]
  have hupField : d.record.output.coordinator.up = none := by
    rw [hcoordinator, hpost]
  have hconfiguration : d.record.output.coordinator.configuration =
      .live { payload := r.payload
              priorClock := finished.clock
              pendingAtChoice := finished.pending
              time := d.record.input.time
              gridBoundary := finished.clock.g
              complementScores := serviced.score }
        { queue := serviced.queue, previousService := serviced.previousService } base := by
    rw [hcoordinator, hpost]
  have hnextConfiguration : d.record.output.next.coordinator =
      .live { payload := r.payload
              priorClock := finished.clock
              pendingAtChoice := finished.pending
              time := d.record.input.time
              gridBoundary := finished.clock.g
              complementScores := serviced.score }
        { queue := serviced.queue, previousService := serviced.previousService } base := by
    calc
      d.record.output.next.coordinator =
          (ReferenceActivePhysicalStep.livePostChoice P r q base d.started).configuration :=
        hnextChoice
      _ = .live { payload := r.payload
                  priorClock := finished.clock
                  pendingAtChoice := finished.pending
                  time := d.record.input.time
                  gridBoundary := finished.clock.g
                  complementScores := serviced.score }
            { queue := serviced.queue, previousService := serviced.previousService } base := by
        rw [hpost]
  have hserviceBudget : ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      serviced.score j + serviced.queue j ≤
        (t.val - s + 1) * ConstructorDimensions.D p := by
    intro j
    exact htotal j
  refine ⟨d, consistent, output, hlocal, hstart, hv, hreconstruction, hsample,
    hslow, hpayloadSlow, ?_⟩
  refine ⟨hinstalledPayload, hinstalledVector, hinstalledReconstruction, hanchor,
    hqueues, hbase, hinstalledSlow, selection, hselection, hdispatch, hpreparation,
    hpreparationCoordinator, hselectedArm, hpostChoice, hnextChoice,
    recording, serviced, pending, finished, hrecord, hservice, hconfirmation, hfinish,
    hcoordinator, hfailure, hrecordingField, hupField, hconfiguration, hnextConfiguration,
    hserviceBudget, htotalHorizon⟩

end Bandits.Support.ReferenceFirstCollectionRenewalInstalledServiceTail

end
