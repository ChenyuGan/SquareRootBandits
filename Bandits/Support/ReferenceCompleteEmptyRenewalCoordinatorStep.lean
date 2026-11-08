/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteEmptyCollectionRenewalChoiceDomains
public import Bandits.Support.ReferenceCompleteSelectedLiveCoordinatorServiceFinish

/-!
# Empty-pending renewal coordinator step

Compose the actual empty-pending collection renewal with the selected-live
coordinator service step at the same complete-suffix record. The output
telescope preserves the full renewal choice, installed score/queue seed,
normalized assignment sample, and physical selection, then extends that exact
prepared output with the recorder, complement service, confirmation, finish,
live-state, and decoder-bank result.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188`,
`sources/zip4/manuscript/05_binary_transport.tex:354-429`,
`sources/zip4/manuscript/06_interruptions.tex:9-100,246-299`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-84`.
-/

@[expose] public section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorAssignmentRegisterInstall
open Bandits.Support.LaterAssignmentStartOperation
open Bandits.Support.AssignmentScoreReconstruction
open Bandits.Support.PrefixSetSampler
open Bandits.Support.OrientedAssignmentLaw
open Bandits.Support.CheckedAssignmentSample
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.CoordinatorLiveServiceFinish
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.ReferenceCoordinatorRecorderCallTrace
open Bandits.Support.ReferenceLiveDispatchOutputMeasurability
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ActiveRoundActions
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ReferenceActiveHorizonMeasurability

namespace Bandits.Support.ReferenceCompleteEmptyRenewalCoordinatorStep

noncomputable section

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {p : ConstructorDimensions.Parameters}

/--
For each actual complete-suffix record, retain the complete empty-pending
renewal result and produce the selected-live coordinator service result from
the very selection installed by that renewal in the prepared physical output.
The only branch localizers are the collection state, empty pending set, and
the source freeze boundary, including equality at the old clipped grid.
-/
theorem complete_empty_renewal_coordinator_step
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ (k : Fin records.length),
      let record := records[k.val]'k.isLt
      let x := record.input
      ∀ (payload : ReferenceActivePhysicalStep.Payload rate)
        (ledger : ReferenceActivePhysicalStep.Ledger rate)
        (saved : Option (Fin p.T × Bool)),
        x.state.coordinator = .collection payload ledger saved →
        ledger.pending = ∅ →
        ledger.freezeAt ≤ x.time.val + 1 →
        ∃ u : Fin p.T, u.val + 1 = ledger.cutoff ∧
          let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved u
          let input := ReferenceActivePhysicalStep.collectionInput x payload ledger clock u
          ∃ (core : CoordinatorRoundDispatch.CollectionCoreValid input),
            CoordinatorRoundDispatch.collectionCurrentScoresCheck input = true ∧
            ∃ (started : CoordinatorPhaseClock.StartRoundResult p),
              ∃ (hstart : CoordinatorPhaseClock.startRound p rate.eta.val x.time
                input.clock ledger.pending = .ok started),
              ∃ (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p),
                ∃ (hassignment : started.assignmentStart = some instruction),
                  ∃ (hinstructionTime : instruction.time = x.time),
                    ∃ (_hrenewal : instruction.kind = .renewal),
                      let operationLedger := CoordinatorRoundDispatch.collectionOperationLedger
                        input core.payload_n_eq
                      let consistent : LaterAssignmentStartOperation.LocalConsistency
                          input.payload operationLedger := {
                        oldStart_eq := by
                          simpa [CoordinatorRecorderComplementBridge.sourceStart,
                            operationLedger, CoordinatorRoundDispatch.collectionOperationLedger] using
                            core.ledger_sigma_eq.symm
                        oldAssignment_eq := by
                          intro i
                          simpa [operationLedger,
                            CoordinatorRoundDispatch.collectionOperationLedger] using
                            (core.assignment_eq i).symm
                        oldFreezeAt := ledger.freezeAt
                        oldFreezeAt_eq := rfl }
                      ∃ (output : LaterAssignmentStartOperation.SuccessfulStart
                          input.payload operationLedger instruction input.row)
                        (hlocal : output.localConsistency = consistent),
                        LaterAssignmentStartOperation.laterAssignmentStart input.payload
                          operationLedger instruction input.row consistent = .success output hlocal ∧
                        let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence
                            output := {
                          priorClock := input.clock
                          pending := ledger.pending
                          proposalParameterValid := core.clock_parameter_valid
                          priorClockValid := core.clock_registers_valid
                          startTimeValid := by rw [hinstructionTime]; exact core.clock_start_time_valid
                          result := started
                          startRound_eq := by rw [hinstructionTime]; exact hstart
                          assignmentStart_eq := hassignment
                          priorSigma_eq := core.clock_sigma_eq
                          priorGrid_eq_freezeAt := by
                            calc
                              input.clock.g = ledger.freezeAt := core.ledger_freeze_eq.symm
                              _ = consistent.oldFreezeAt := consistent.oldFreezeAt_eq.symm
                              _ = output.localConsistency.oldFreezeAt := by rw [hlocal] }
                        let installation :=
                          CoordinatorAssignmentRegisterInstall.installLater output clockData
                        (∀ a, AssignmentScoreReconstruction.sourceScore output.reconstruction a =
                          (output.reconstruction.registers.cutoff a).score + operationLedger.increment a) ∧
                        (∀ a, AssignmentScoreReconstruction.initialQueue output.reconstruction a =
                          (output.reconstruction.registers.current a).queue) ∧
                        (∀ a, AssignmentScoreReconstruction.currentWeight output.reconstruction a =
                          (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
                            AssignmentScoreReconstruction.sourceScore output.reconstruction a) ∧
                        installation.registers.payload.anchor =
                          AssignmentScoreReconstruction.currentWeight output.reconstruction ∧
                        (∀ a, installation.registers.payload.queues a =
                          AssignmentScoreReconstruction.initialQueue output.reconstruction a) ∧
                        (installation.registers.scoreDomainValid ∧
                          installation.ownedRegisters.queueDomainValid ∧
                          installation.ownedRegisters.previousServiceDomainValid) ∧
                        (∀ i, installation.retainedBaseScore i ≤ p.T * D p) ∧
                        (instruction.kind = CoordinatorPhaseClock.classifyAssignmentStart
                            input.clock.sigma instruction.time input.clock.g ∧
                          started.clock.sigma = some x.time ∧ started.clock.u = none ∧
                          started.clock.g = FollowerCutoffScan.gridBoundary p rate.eta.val x.time ∧
                          started.pending = Finset.univ ∧ started.ledgerCommand = none) ∧
                        ∃ (mass : PrefixSetSampler.NormalizedMass p.K p.m
                            (Nat.le_of_lt p.m_lt_K))
                          (sampled : OrientedAssignmentLaw.AssignmentOutcome p.K p.m),
                          (∀ S : PrefixSetSampler.SetCarrier p.K p.m,
                            mass.weight S = output.law.mass S) ∧
                          CheckedAssignmentSample.checkedAssignmentSample p mass.weight
                            output.law.anchor
                            (LaterAssignmentStartOperation.ownAssignmentVector x.row instruction.time) =
                              .sampled sampled ∧
                          output.assignmentVector =
                            LaterAssignmentStartOperation.ownAssignmentVector x.row instruction.time ∧
                          ∃ (selection : CoordinatorRoundDispatch.ArmSelection
                              installation.registers.payload started instruction.time
                              installation.registers.complementWeights input.row),
                            CoordinatorRoundDispatch.dispatchCollection input =
                              .laterChosen core consistent started
                                hstart instruction hassignment
                                output hlocal clockData installation selection ∧
                            let preparation := ReferenceActivePhysicalStep.prepare x
                            preparation.coordinator =
                              .collection payload ledger clock u
                                (CoordinatorRoundDispatch.dispatchCollection input) ∧
                            ∃ (physicalSelection : ReferenceActivePhysicalStep.Selection x),
                              ReferenceActivePhysicalStep.DispatchCut.selection
                                  preparation.coordinator = some physicalSelection ∧
                              physicalSelection.view.payload = installation.registers.payload ∧
                              physicalSelection.view.cutoff =
                                CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u ∧
                              CoordinatorLocalArmChoice.assignmentIsLive
                                physicalSelection.view.payload physicalSelection.view.cutoff x.time ∧
                              record.output.preparation.coordinator.selection =
                                some physicalSelection ∧
                              ∃ (a : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                                  (q : CoordinatorLiveServiceFinish.OwnedRegisters a)
                                  (base : Fin (p.m - 1) → ℕ)
                                  (started : CoordinatorPhaseClock.StartRoundResult p),
                                  (match record.output.preparation.coordinator with
                                    | .first (.chosen installed _) =>
                                        a = installed.registers ∧ HEq q installed.ownedRegisters ∧
                                          base = installed.followerBaseScore ∧
                                          started = installed.startRoundResult
                                    | .live registers owned oldBase (.continuingChosen dispatched _ _ _) =>
                                        a = ReferenceActivePhysicalStep.liveRegistersAt registers x.time ∧
                                          HEq q (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) ∧
                                          base = oldBase ∧ started = dispatched.startResult
                                    | .collection _ _ _ _
                                        (.laterChosen _ _ roundStart _ _ _ _ _ _ installation _) =>
                                        a = installation.registers ∧ HEq q installation.ownedRegisters ∧
                                          base = installation.retainedBaseScore ∧ started = roundStart
                                    | _ => False) ∧
                                  ∃ (valid : CoordinatorRecordingOperation.InputsValid
                                      (ReferenceCoordinatorRecorderCallTrace.inputFromSelection record
                                        (ReferenceLiveDispatchOutputMeasurability.encodeSelection
                                          physicalSelection)))
                                    (o : CoordinatorRecordingOperation.Output p)
                                    (serviced : CoordinatorLiveServiceFinish.ServicedRegisters a q)
                                    (pending : Finset (Fin (p.m - 1)))
                                    (finished : CoordinatorPhaseClock.FinishRoundResult p),
                                    let call := ReferenceCoordinatorRecorderCallTrace.inputFromSelection
                                      record
                                      (ReferenceLiveDispatchOutputMeasurability.encodeSelection
                                        physicalSelection)
                                    let F0 := Nat.floor ((D p : ℝ) * rate.eta.val *
                                      (((rewards x.time physicalSelection.arm).val : ℝ) / (D p : ℝ)) /
                                      CanonicalRecordingRates.xi p rate.eta.val
                                        physicalSelection.view.payload.anchor physicalSelection.arm)
                                    let G0 : Prop :=
                                      CoordinatorRecordingOperation.selectedSlot call =
                                        PublicDiscreteDraws.dataSlot ∧
                                      CoordinatorRecordingOperation.selectedRecorder call =
                                        ActiveRoundActions.coordinator p.two_le_m ∧
                                      ¬ CoordinatorRecordingOperation.isFrozen call ∧
                                      CoordinatorRecordingOperation.ownsArm call.mode call.ownArm ∧
                                      CoordinatorRecordingOperation.ownMaskPasses call ∧
                                      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
                                        ((x.row.2 x.time).1)).val ≤
                                        CoordinatorRecordingOperation.coordinatorThreshold call valid
                                    CoordinatorRecordingOperation.run call = some o ∧
                                    record.output.coordinator.recording = some o ∧
                                    o.gateArm = (if G0 then some physicalSelection.arm else none) ∧
                                    o.rawArrival = (if G0 then F0 else 0) ∧
                                    ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
                                      (ReferenceActiveHorizonMeasurability.roundRecordCode record)
                                      physicalSelection.arm = some (if G0 then F0 else 0) ∧
                                    ReferenceCoordinatorRecorderCallTrace.inputFromSelection record
                                      (ReferenceLiveDispatchOutputMeasurability.encodeSelection
                                        physicalSelection) =
                                      CoordinatorRecorderComplementBridge.recorderInput
                                        (ReferenceActivePhysicalStep.liveRecordingInput
                                          record.output.preparation a started) ∧
                                    CoordinatorRecorderComplementBridge.run
                                      (ReferenceActivePhysicalStep.liveRecordingInput
                                        record.output.preparation a started) = some o ∧
                                    q.queueDomainValid ∧ q.previousServiceDomainValid ∧
                                    serviced.recording = o ∧
                                    (∀ j, serviced.arrival j =
                                      CoordinatorLiveServiceFinish.complementArrival
                                        a.payload o j) ∧
                                    (∀ j, serviced.service j =
                                      CappedService.service (4 * a.payload.n) (q.queue j)
                                        (serviced.arrival j)) ∧
                                    (∀ j, serviced.queue j =
                                      CappedService.residual (4 * a.payload.n) (q.queue j)
                                        (serviced.arrival j)) ∧
                                    (∀ j, serviced.score j =
                                      a.complementScores j + serviced.service j) ∧
                                    (∀ j, serviced.previousService j = serviced.service j) ∧
                                    CoordinatorLocalArmChoice.confirmationUpdate a.payload
                                      started.pending
                                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                                      x.time x.row record.output.preparation.coordinatorObservation =
                                      some pending ∧
                                    pending =
                                      (if CoordinatorLocalArmChoice.downConfirmationEvent a.payload
                                          started.pending
                                          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                                          x.time (x.row.2 x.time)
                                          record.output.preparation.coordinatorObservation then
                                        started.pending.erase
                                          (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m
                                            p.m_lt_K (x.row.2 x.time).1)
                                      else started.pending) ∧
                                    CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                                      started.clock pending x.row = .ok finished ∧
                                    ReferenceActivePhysicalStep.livePostChoice
                                      record.output.preparation a q base started =
                                      ⟨.live {
                                          payload := a.payload
                                          priorClock := finished.clock
                                          pendingAtChoice := finished.pending
                                          time := x.time
                                          gridBoundary := finished.clock.g
                                          complementScores := serviced.score }
                                        { queue := serviced.queue
                                          previousService := serviced.previousService } base,
                                        x.state.upDecoderBank, none, some o, none⟩ ∧
                                    record.output.coordinator =
                                      ⟨.live {
                                          payload := a.payload
                                          priorClock := finished.clock
                                          pendingAtChoice := finished.pending
                                          time := x.time
                                          gridBoundary := finished.clock.g
                                          complementScores := serviced.score }
                                        { queue := serviced.queue
                                          previousService := serviced.previousService } base,
                                        x.state.upDecoderBank, none, some o, none⟩ ∧
                                    record.output.next.coordinator =
                                      (ReferenceActivePhysicalStep.livePostChoice
                                        record.output.preparation a q base started).configuration ∧
                                    record.output.next.upDecoderBank =
                                      (ReferenceActivePhysicalStep.livePostChoice
                                        record.output.preparation a q base started).upDecoderBank := by
  have hchoice :=
    _root_.Bandits.Support.ReferenceCompleteEmptyCollectionRenewalChoiceDomains.complete_empty_collection_renewal_choice_domains
      rate rewards C_star C_h source
  dsimp only
  intro k
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let record := R[k.val]'k.isLt
  let x := record.input
  intro payload ledger saved hstate hpending hfreeze
  have hcase := hchoice k payload ledger saved hstate hpending hfreeze
  dsimp only at hcase
  rcases hcase with
    ⟨u, hu, core, hscoreCheck, started, hstart, instruction, hassignment,
      hinstructionTime, hrenewal, output, hlocal, hlater, hsourceScore,
      hinitialQueue, hcurrentWeight, hanchor, hqueues, hdomains, hbaseBound,
      hclockFacts, mass, sampled, hmassEq, hsampled, hvectorEq, selection,
      hdispatch, hpreparedCoordinator, physicalSelection, hphysicalSelection,
      hpayload, hcutoff, hlive⟩
  have hprepare : record.output.preparation = ReferenceActivePhysicalStep.prepare x := by
    rw [record.output_eq]
    rfl
  have hselectionAtOutput :
      record.output.preparation.coordinator.selection = some physicalSelection := by
    rw [hprepare]
    exact hphysicalSelection
  exact ⟨u, hu, core, hscoreCheck, started, hstart, instruction, hassignment,
    hinstructionTime, hrenewal, output, hlocal, hlater, hsourceScore,
    hinitialQueue, hcurrentWeight, hanchor, hqueues, hdomains, hbaseBound,
    hclockFacts, mass, sampled, hmassEq, hsampled, hvectorEq, selection,
    hdispatch, hpreparedCoordinator, physicalSelection, hphysicalSelection,
    hpayload, hcutoff, hlive, hselectionAtOutput,
    _root_.Bandits.Support.ReferenceCompleteSelectedLiveCoordinatorServiceFinish.complete_selected_live_coordinator_service_finish
      (rate := rate) rewards C_star C_h source k physicalSelection
      hselectionAtOutput hlive⟩

end
end Bandits.Support.ReferenceCompleteEmptyRenewalCoordinatorStep
