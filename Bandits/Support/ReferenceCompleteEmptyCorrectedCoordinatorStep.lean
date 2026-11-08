/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteEmptyCollectionCorrectedChoiceDomains
public import Bandits.Support.ReferenceCompleteSelectedLiveCoordinatorServiceFinish

/-!
# Complete empty-corrected coordinator step

Compose the actual empty-pending corrected collection assignment with its
selected live recorder, complement service, confirmation, and finish.
Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188`,
`sources/zip4/manuscript/05_binary_transport.tex:354-429`,
`sources/zip4/manuscript/06_interruptions.tex:9-100,246-299`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-84`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.CoordinatorLiveServiceFinish
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.ReferenceCoordinatorRecorderCallTrace
open Bandits.Support.ReferenceLiveDispatchOutputMeasurability
open Bandits.Support.ReferenceActiveHorizonMeasurability
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.CappedService
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.ActiveRoundActions
open Bandits.Support.ScoreWeights
open Bandits.Support.AssignmentScoreReconstruction
open Bandits.Support.LaterAssignmentStartOperation
open Bandits.Support.CoordinatorAssignmentRegisterInstall
open Bandits.Support.CheckedAssignmentSample

namespace Bandits.Support.ReferenceCompleteEmptyCorrectedCoordinatorStep

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

/-- On an actual complete-suffix row in an empty-pending corrected collection,
the very installation and assignment chosen by the collection dispatcher
supplies the selected live arm and its complete physical coordinator step.
The collection choice conditions are exactly the empty-pending and strict
pre-boundary localizers; all recorder and service outcomes are constructed
inside the result. -/
theorem complete_empty_corrected_coordinator_step
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ (k : Fin R.length),
      let r := R[k.val]'k.isLt
      let x := r.input
      ∀ (P : ReferenceActivePhysicalStep.Payload rate)
        (l : ReferenceActivePhysicalStep.Ledger rate)
        (saved : Option (Fin p.T × Bool)),
        x.state.coordinator = .collection P l saved →
        l.pending = ∅ → x.time.val + 1 < l.freezeAt →
        ∃ (u : Fin p.T), u.val + 1 = l.cutoff ∧
        let clock := ReferenceActivePhysicalStep.collectionClock P l saved u
        let input := ReferenceActivePhysicalStep.collectionInput x P l clock u
        ∃ (core : CoordinatorRoundDispatch.CollectionCoreValid input)
          (started : CoordinatorPhaseClock.StartRoundResult p)
          (hstart : startRound p rate.eta.val x.time input.clock l.pending = .ok started)
          (instruction : AssignmentStartInstruction p)
          (hassignment : started.assignmentStart = some instruction),
          instruction.time = x.time ∧ instruction.kind = .corrected ∧
          started.clock.sigma = some x.time ∧ started.clock.u = none ∧
          let operation := CoordinatorRoundDispatch.collectionOperationLedger input
            core.payload_n_eq
          ∃ (consistent : LaterAssignmentStartOperation.LocalConsistency P operation)
            (output : LaterAssignmentStartOperation.SuccessfulStart P operation instruction x.row)
            (hlocal : output.localConsistency = consistent),
            LaterAssignmentStartOperation.laterAssignmentStart P operation instruction x.row
              consistent = .success output hlocal ∧
            ∃ (clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output)
              (installation : CoordinatorAssignmentRegisterInstall.LaterInstallation output clockData)
              (selected : CoordinatorRoundDispatch.ArmSelection installation.registers.payload
                started instruction.time installation.registers.complementWeights x.row),
              clockData.priorClock = clock ∧ clockData.result = started ∧
              clockData.pending = l.pending ∧
              installation = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
              CoordinatorRoundDispatch.dispatchCollection input =
                .laterChosen core consistent started hstart instruction hassignment
                  output hlocal clockData installation selected ∧
              installation.registers.scoreDomainValid ∧
              installation.ownedRegisters.queueDomainValid ∧
              installation.ownedRegisters.previousServiceDomainValid ∧
              (∀ i, installation.retainedBaseScore i ≤ p.T * D p) ∧
              installation.registers.complementEnvelopeValid ∧
              installation.registers.payload = output.payload ∧
              output.payload.anchor = P.anchor ∧ output.law.anchor = P.anchor ∧
              (∀ a, l.cutoffRegisters a = some (output.reconstruction.registers.cutoff a)) ∧
              (∀ a, l.currentRegisters a = some (output.reconstruction.registers.current a)) ∧
              (∀ a, AssignmentScoreReconstruction.sourceScore output.reconstruction a =
                (output.reconstruction.registers.cutoff a).score + l.increment a) ∧
              (∀ a, AssignmentScoreReconstruction.initialQueue output.reconstruction a =
                (output.reconstruction.registers.current a).queue) ∧
              (∀ a, output.payload.queues a =
                (output.reconstruction.registers.current a).queue) ∧
              output.assignmentVector =
                LaterAssignmentStartOperation.ownAssignmentVector x.row x.time ∧
              ∃ v : ReferenceActivePhysicalStep.Selection x,
                (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some v ∧
                r.output.preparation.coordinator.selection = some v ∧
                v.view.payload = installation.registers.payload ∧
                v.started = started ∧ v.view.cutoff = none ∧ v.arm = selected.arm ∧
                CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff x.time ∧
                r.output.preparation.coordinator =
                  .collection P l clock u
                    (.laterChosen core consistent started hstart instruction hassignment
                      output hlocal clockData installation selected) ∧
                ∃ (a : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                  (owned : CoordinatorLiveServiceFinish.OwnedRegisters a)
                  (followerBase : Fin (p.m - 1) → ℕ)
                  (liveStarted : CoordinatorPhaseClock.StartRoundResult p),
                  a = installation.registers ∧
                  HEq owned installation.ownedRegisters ∧
                  followerBase = installation.retainedBaseScore ∧
                  liveStarted = started ∧
                  ∃ (valid : CoordinatorRecordingOperation.InputsValid
                      (ReferenceCoordinatorRecorderCallTrace.inputFromSelection r
                        (ReferenceLiveDispatchOutputMeasurability.encodeSelection v)))
                    (o : CoordinatorRecordingOperation.Output p)
                    (serviced : CoordinatorLiveServiceFinish.ServicedRegisters a owned)
                    (pending : Finset (Fin (p.m - 1)))
                    (finished : CoordinatorPhaseClock.FinishRoundResult p),
                    let call := ReferenceCoordinatorRecorderCallTrace.inputFromSelection r
                      (ReferenceLiveDispatchOutputMeasurability.encodeSelection v)
                    let F0 := Nat.floor ((D p : ℝ) * rate.eta.val *
                      (((rewards x.time v.arm).val : ℝ) / (D p : ℝ)) /
                      CanonicalRecordingRates.xi p rate.eta.val v.view.payload.anchor v.arm)
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
                    r.output.coordinator.recording = some o ∧
                    o.gateArm = (if G0 then some v.arm else none) ∧
                    o.rawArrival = (if G0 then F0 else 0) ∧
                    ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
                      (ReferenceActiveHorizonMeasurability.roundRecordCode r) v.arm =
                        some (if G0 then F0 else 0) ∧
                    ReferenceCoordinatorRecorderCallTrace.inputFromSelection r
                      (ReferenceLiveDispatchOutputMeasurability.encodeSelection v) =
                        CoordinatorRecorderComplementBridge.recorderInput
                          (ReferenceActivePhysicalStep.liveRecordingInput
                            r.output.preparation a liveStarted) ∧
                    CoordinatorRecorderComplementBridge.run
                      (ReferenceActivePhysicalStep.liveRecordingInput
                        r.output.preparation a liveStarted) = some o ∧
                    owned.queueDomainValid ∧ owned.previousServiceDomainValid ∧
                    serviced.recording = o ∧
                    (∀ j, serviced.arrival j =
                      CoordinatorLiveServiceFinish.complementArrival a.payload o j) ∧
                    (∀ j, serviced.service j =
                      CappedService.service (4 * a.payload.n) (owned.queue j)
                        (serviced.arrival j)) ∧
                    (∀ j, serviced.queue j =
                      CappedService.residual (4 * a.payload.n) (owned.queue j)
                        (serviced.arrival j)) ∧
                    (∀ j, serviced.score j = a.complementScores j + serviced.service j) ∧
                    (∀ j, serviced.previousService j = serviced.service j) ∧
                    CoordinatorLocalArmChoice.confirmationUpdate a.payload liveStarted.pending
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p liveStarted.clock.u)
                      x.time x.row r.output.preparation.coordinatorObservation = some pending ∧
                    pending =
                      (if CoordinatorLocalArmChoice.downConfirmationEvent a.payload
                          liveStarted.pending
                          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p liveStarted.clock.u)
                          x.time (x.row.2 x.time)
                          r.output.preparation.coordinatorObservation then
                        liveStarted.pending.erase (PublicDiscreteDraws.selectedFollowerDraw
                          p.two_le_m p.m_lt_K (x.row.2 x.time).1)
                      else liveStarted.pending) ∧
                    CoordinatorPhaseClock.finishRound p rate.eta.val x.time liveStarted.clock
                      pending x.row = .ok finished ∧
                    ReferenceActivePhysicalStep.livePostChoice r.output.preparation a owned
                      followerBase liveStarted =
                        ⟨.live {
                            payload := a.payload
                            priorClock := finished.clock
                            pendingAtChoice := finished.pending
                            time := x.time
                            gridBoundary := finished.clock.g
                            complementScores := serviced.score }
                          { queue := serviced.queue
                            previousService := serviced.previousService } followerBase,
                          x.state.upDecoderBank, none, some o, none⟩ ∧
                    r.output.coordinator =
                      ⟨.live {
                          payload := a.payload
                          priorClock := finished.clock
                          pendingAtChoice := finished.pending
                          time := x.time
                          gridBoundary := finished.clock.g
                          complementScores := serviced.score }
                        { queue := serviced.queue
                          previousService := serviced.previousService } followerBase,
                        x.state.upDecoderBank, none, some o, none⟩ ∧
                    r.output.next.coordinator =
                      (ReferenceActivePhysicalStep.livePostChoice r.output.preparation a owned
                        followerBase liveStarted).configuration ∧
                    r.output.next.upDecoderBank =
                      (ReferenceActivePhysicalStep.livePostChoice r.output.preparation a owned
                        followerBase liveStarted).upDecoderBank := by
  classical
  dsimp only
  intro k P l saved hstate hempty hbefore
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let r := R[k.val]'k.isLt
  let x := r.input
  obtain ⟨u, hu, core, started, hstart, instruction, hassignment, htime, hkind,
    hclockSigma, hclockU, consistent, output, hlocal, hlater, clockData, installation,
    selected, hprior, hresult,
    hpending, hininstallation, hdispatch, hscoreDomain, hqueueDomain,
    hpreviousDomain, hbase, hEnvelope, hpayload, hanchor, hlawAnchor,
    hcutoffRegisters, hcurrentRegisters, hsourceScore, hinitialQueue,
    hpayloadQueues, _hcurrentWeight, _hcutoffWeight, _henvelope, _hprevious,
    _hlaw, _hnonneg, _hsum, _hsample, hvector, v, hprepareSelection,
    hrecordSelection, hvpayload, hvstarted, hvcutoff, hvarm, hlive⟩ :=
    _root_.Bandits.Support.ReferenceCompleteEmptyCollectionCorrectedChoiceDomains.complete_empty_corrected_choice_domains
      (rate := rate) rewards C_star C_h source k
      P l saved hstate hempty hbefore
  let clock := ReferenceActivePhysicalStep.collectionClock P l saved u
  let input := ReferenceActivePhysicalStep.collectionInput x P l clock u
  have hstate' : x.state.coordinator = .collection P l saved := hstate
  have hprepared : r.output.preparation = ReferenceActivePhysicalStep.prepare x := by
    rw [r.output_eq]
    rfl
  have hprepare : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .collection P l clock u
        (.laterChosen core consistent started hstart instruction hassignment output hlocal
          clockData installation selected) := by
    have hrange : 1 ≤ l.cutoff ∧ l.cutoff ≤ p.T := by
      constructor <;> have := u.isLt <;> omega
    have hval : l.cutoff - 1 = u.val := by omega
    let cutoff : Fin p.T := ⟨l.cutoff - 1, by omega⟩
    have hcut : cutoff = u := Fin.ext hval
    simp only [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
      hstate', dite_eq_left hrange, CoordinatorRoundDispatch.dispatch]
    change ReferenceActivePhysicalStep.DispatchCut.collection P l
      (ReferenceActivePhysicalStep.collectionClock P l saved cutoff) cutoff
      (CoordinatorRoundDispatch.dispatchCollection
        (ReferenceActivePhysicalStep.collectionInput x P l
          (ReferenceActivePhysicalStep.collectionClock P l saved cutoff) cutoff)) = _
    rw [hcut]
    exact congrArg (ReferenceActivePhysicalStep.DispatchCut.collection P l clock u) hdispatch
  have hprepareOutput : r.output.preparation.coordinator =
      .collection P l clock u
        (.laterChosen core consistent started hstart instruction hassignment output hlocal
          clockData installation selected) := by
    rw [hprepared]
    exact hprepare
  have hchoiceOutput : r.output.preparation.coordinator.selection = some v := hrecordSelection
  have hprepareOutput' :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].output.preparation.coordinator =
        .collection P l clock u
          (.laterChosen core consistent started hstart instruction hassignment output hlocal
            clockData installation selected) := by
    simpa [R, r] using hprepareOutput
  obtain ⟨a, owned, followerBase, liveStarted, hmatch,
    valid, o, serviced, pending, finished, hrun, hrecording, hgate, hraw,
    hdiagnostic, hinput, hbridge, hqueueValid, hpreviousValid,
    hservicedRecording, harrival, hservice, hqueue, hscore, hpreviousService,
    hconfirmation, hpendingFormula, hfinish, hpost, houtput, hnext, hup⟩ :=
    _root_.Bandits.Support.ReferenceCompleteSelectedLiveCoordinatorServiceFinish.complete_selected_live_coordinator_service_finish
      (rate := rate) rewards C_star C_h
      source k v hchoiceOutput hlive
  have halignment : a = installation.registers ∧
      HEq owned installation.ownedRegisters ∧
      followerBase = installation.retainedBaseScore ∧ liveStarted = started := by
    rw [hprepareOutput'] at hmatch
    exact hmatch
  refine ⟨u, hu, core, started, hstart, instruction, hassignment, htime, hkind,
    hclockSigma, hclockU, consistent, output, hlocal, hlater, clockData,
    installation, selected, hprior, hresult, hpending, hininstallation, hdispatch, hscoreDomain,
    hqueueDomain, hpreviousDomain, hbase, hEnvelope, hpayload, hanchor,
    hlawAnchor, hcutoffRegisters, hcurrentRegisters, hsourceScore,
    hinitialQueue, hpayloadQueues, hvector, v, hprepareSelection,
    hrecordSelection, hvpayload, hvstarted, hvcutoff, hvarm, hlive,
    hprepareOutput, a, owned, followerBase, liveStarted,
    halignment.1, halignment.2.1, halignment.2.2.1, halignment.2.2.2,
    valid, o, serviced, pending, finished, ?_⟩
  exact ⟨hrun, hrecording, hgate, hraw, hdiagnostic, hinput, hbridge,
    hqueueValid, hpreviousValid, hservicedRecording, harrival, hservice,
    hqueue, hscore, hpreviousService, hconfirmation, hpendingFormula, hfinish,
    hpost, houtput, hnext, hup⟩

end Bandits.Support.ReferenceCompleteEmptyCorrectedCoordinatorStep

end
