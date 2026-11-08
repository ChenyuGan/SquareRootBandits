/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteLiveChoiceDomains
public import Bandits.Support.ReferenceCompleteSelectedLiveCoordinatorServiceFinish

/-!
# Complete-source continuing-live coordinator step

Compose the actual complete-suffix live arm-choice producer with the accepted
selected-live recorder, complement service, confirmation, and clock finish.
The cutoff dispatch remains an explicit boundary case.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,219-278`,
`sources/zip4/manuscript/06_interruptions.tex:9-100,192-233`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-84`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.ReferenceCompleteLiveChoiceDomains
open Bandits.Support.ReferenceCompleteSelectedLiveCoordinatorServiceFinish
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.CoordinatorLiveServiceFinish
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.ActiveRoundActions
open Bandits.Support.ReferenceCoordinatorRecorderCallTrace
open Bandits.Support.ReferenceLiveDispatchOutputMeasurability
open Bandits.Support.ReferenceActiveHorizonMeasurability
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.CappedService
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.CanonicalFastSampling

namespace Bandits.Support.ReferenceCompleteContinuingLiveCoordinatorStep

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

/-- At an actual complete-suffix row with a live incoming coordinator, retain
the original live dispatch. A continuing choice has its actual physical
selection, recorder call, enabled complement service, confirmation, finish,
and output equations. A cutoff choice is explicitly excluded from this
post-choice conclusion; every other dispatch branch is impossible by the
complete-source choice producer. -/
theorem complete_live_continuing_coordinator_step
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator =
        .live registers q base) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    let r := R[k.val]'k.isLt
    let x := r.input
    let current := ReferenceActivePhysicalStep.liveInput x registers q base
    let preparation := ReferenceActivePhysicalStep.prepare x
    let chosen := CoordinatorRoundDispatch.dispatchLive current
    preparation.coordinator = .live registers q base chosen ∧
    (show Prop from match chosen with
    | .continuingChosen dispatched _ _ selection =>
        ∃ (v : ReferenceActivePhysicalStep.Selection x),
          preparation.coordinator.selection = some v ∧
          v.view.payload = registers.payload ∧
          v.view.cutoff = CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
            dispatched.startResult.clock.u ∧
          v.started = dispatched.startResult ∧
          v.arm = selection.arm ∧
          CoordinatorLocalArmChoice.assignmentIsLive v.view.payload
            v.view.cutoff x.time ∧
          r.output.preparation.coordinator.selection = some v ∧
          ∃ (a : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
            (owned : CoordinatorLiveServiceFinish.OwnedRegisters a)
            (followerBase : Fin (p.m - 1) → ℕ)
            (started : CoordinatorPhaseClock.StartRoundResult p),
            HEq a (ReferenceActivePhysicalStep.liveRegistersAt registers x.time) ∧
            HEq owned (ReferenceActivePhysicalStep.liveOwnedAt registers q x.time) ∧
            followerBase = base ∧ started = dispatched.startResult ∧
          ∃ (valid : CoordinatorRecordingOperation.InputsValid
              (ReferenceCoordinatorRecorderCallTrace.inputFromSelection r
                (ReferenceLiveDispatchOutputMeasurability.encodeSelection v)) )
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
              CoordinatorRecordingOperation.selectedSlot call = PublicDiscreteDraws.dataSlot ∧
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
                    r.output.preparation a started) ∧
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput
                r.output.preparation a started) = some o ∧
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
            CoordinatorLocalArmChoice.confirmationUpdate a.payload
              (started.pending : Finset (ActiveRoundActions.Follower p.m))
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row (r.output.preparation.coordinatorObservation) =
                some pending ∧
            pending =
              (if CoordinatorLocalArmChoice.downConfirmationEvent a.payload started.pending
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                  x.time (x.row.2 x.time)
                  r.output.preparation.coordinatorObservation then
                started.pending.erase (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m
                  p.m_lt_K (x.row.2 x.time).1)
              else started.pending) ∧
            CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
              pending x.row = .ok finished ∧
            ReferenceActivePhysicalStep.livePostChoice r.output.preparation a owned followerBase
              started =
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
              (ReferenceActivePhysicalStep.livePostChoice
                r.output.preparation a owned followerBase started).configuration ∧
            r.output.next.upDecoderBank =
              (ReferenceActivePhysicalStep.livePostChoice
                r.output.preparation a owned followerBase started).upDecoderBank
    | .cutoffChosen .. => True
    | _ => False) := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let r := R[k.val]'k.isLt
  let x := r.input
  let current := ReferenceActivePhysicalStep.liveInput x registers q base
  let preparation := ReferenceActivePhysicalStep.prepare x
  let chosen := CoordinatorRoundDispatch.dispatchLive current
  change preparation.coordinator = .live registers q base chosen ∧ _
  have hchoice :=
    ReferenceCompleteLiveChoiceDomains.complete_live_dispatch_choice_exists
      rate rewards C_star C_h source k registers q base hstate
  change preparation.coordinator = .live registers q base chosen ∧ _ at hchoice
  rcases hchoice with ⟨hpreparedCoordinator, hbranches⟩
  refine ⟨hpreparedCoordinator, ?_⟩
  cases hc : CoordinatorRoundDispatch.dispatchLive current with
  | continuingChosen dispatched hstartEq continuation selection =>
      rw [hc] at hbranches
      rcases hbranches with
        ⟨_hframe, hnoCutoff, hchoiceValid, _hboundary, _harmChoice,
          ⟨v, hselected, hpayload, _hstartPending, hcutoff, hstarted, harm, _hviewPending,
            _hviewCutoff, _hphysicalChoice⟩⟩
      have hprepared : r.output.preparation =
          ReferenceActivePhysicalStep.prepare x := by
        rw [r.output_eq]
        rfl
      have hselectedOutput : r.output.preparation.coordinator.selection = some v := by
        calc
          r.output.preparation.coordinator.selection =
              (ReferenceActivePhysicalStep.prepare x).coordinator.selection := by
            rw [hprepared]
          _ = some v := hselected
      have htime : CoordinatorLocalArmChoice.SourceTimeValid v.view.payload
          v.view.cutoff x.time := by
        simpa only [hpayload, hcutoff, hnoCutoff] using hchoiceValid.time
      have hlive : CoordinatorLocalArmChoice.assignmentIsLive v.view.payload
          v.view.cutoff x.time := by
        change CoordinatorLocalArmChoice.assignmentStart v.view.payload ≤
            CoordinatorLocalArmChoice.sourceRound x.time ∧
          CoordinatorLocalArmChoice.sourceRound x.time <
            CoordinatorLocalArmChoice.cutoffRound v.view.cutoff
        refine ⟨htime.assignment_started, ?_⟩
        have hterminal : CoordinatorLocalArmChoice.cutoffRound v.view.cutoff =
            p.T + 1 := by
          rw [hcutoff, hnoCutoff]
          simp [CoordinatorLiveChoiceRecorderStep.cutoffFromClock,
            CoordinatorLocalArmChoice.cutoffRound]
        rw [hterminal]
        exact Nat.lt_succ_of_le htime.source_round_le_horizon
      have hfinish :=
        _root_.Bandits.Support.ReferenceCompleteSelectedLiveCoordinatorServiceFinish.complete_selected_live_coordinator_service_finish
          (rate := rate) rewards C_star C_h source k v hselectedOutput hlive
      refine ⟨v, hselected, hpayload, hcutoff, hstarted, harm, hlive,
        hselectedOutput, ?_⟩
      rcases hfinish with ⟨a, owned, followerBase, started, hmatch, hpost⟩
      have hcoord : r.output.preparation.coordinator =
          .live registers q base
            (.continuingChosen dispatched hstartEq continuation selection) := by
        calc
          r.output.preparation.coordinator = preparation.coordinator := by
            rw [hprepared]
          _ = .live registers q base chosen := hpreparedCoordinator
          _ = .live registers q base
              (.continuingChosen dispatched hstartEq continuation selection) := by
            simp only [chosen, hc]
      rw [hcoord] at hmatch
      rcases hmatch with ⟨ha, howned, hbase, hstartedEq⟩
      refine ⟨a, owned, followerBase, started, ?_, howned, hbase, hstartedEq, hpost⟩
      cases ha
      exact HEq.rfl
  | cutoffChosen dispatched hstart ledger hinitialization hledger hdomain hclock
      hpending hassignment selection =>
      rw [hc] at hbranches
      exact True.intro
  | clockFailure failure hdispatch =>
      rw [hc] at hbranches
      change False
      exact False.elim hbranches
  | initializerFailure dispatched hstart checked hchecked =>
      rw [hc] at hbranches
      change False
      exact False.elim hbranches
  | localFailure dispatched hstart reason =>
      rw [hc] at hbranches
      change False
      exact False.elim hbranches

end Bandits.Support.ReferenceCompleteContinuingLiveCoordinatorStep

end
