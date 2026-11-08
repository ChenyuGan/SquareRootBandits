/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteContinuingLiveCoordinatorStep

/-!
# Actual later-live complement service on the canonical calendar

Bind one genuine later continuing LIVE round of the complete source execution
to its canonical numerical input and to the very same serviced output.
Enabled zero arrivals retain the service update on every physical slot.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188`,
`sources/zip4/manuscript/05_binary_transport.tex:354-429`,
`sources/zip4/manuscript/06_interruptions.tex:192-233,246-299`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-84`.

This is an internal one-round producer for the later complete-source calendar
splice and renewed-window overflow coverage. It does not assert a whole-window
replay, seed truth, a recording law, or a manuscript regret theorem.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.CanonicalFastSampling

namespace Bandits.Support.ReferenceCompleteLaterLiveCalendarService

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

/-- The actual dispatch supplies every physical witness. Only the strict
later-assignment comparison restricts the continuing branch. The numerical
cell uses the actual selected payload and prepared follower family, and its
arrivals drive the same complement service retained in the actual output. -/
theorem complete_later_live_calendar_service
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
    let s := ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h
    let current := ReferenceActivePhysicalStep.liveInput x registers q base
    let preparation := ReferenceActivePhysicalStep.prepare x
    let chosen := CoordinatorRoundDispatch.dispatchLive current
    preparation.coordinator = .live registers q base chosen ∧
    (show Prop from match chosen with
    | .continuingChosen dispatched _ _ selection =>
        s < registers.payload.sigma.val →
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
                r.output.preparation a owned followerBase started).upDecoderBank ∧
            ∃ (c : RecordedQueueRun.RoundInput p.K)
              (ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary r),
              ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some c ∧
              c.enabled = true ∧
              c = ReferenceFirstWindowNumericalStream.sourceCell r v.view.payload
                v.view.pendingAtChoice
                (ReferenceLaterLiveNumericalReadout.preparedStates r ho)
                v.view.complementWeights v.view.cutoff
                (ReferenceLaterLiveNumericalReadout.selection_choiceValid v) ∧
              (∀ i, (r.output.preparation.followers.followers i).configuration =
                .ordinary (ReferenceLaterLiveNumericalReadout.preparedStates r ho i)
                  (ReferenceLaterLiveNumericalReadout.preparedMemories r ho i)) ∧
              r.input.rows = source.1.2 ∧
              r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
              r.input.rewards = rewards ∧
              c.reward = (fun arm => ((rewards x.time arm).val : ℝ) / (D p : ℝ)) ∧
              c.rate = registers.payload.rate ∧
              a.payload = registers.payload ∧
              (∀ arm, RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) c arm =
                if c.recordedArm = some arm then
                  Nat.floor ((D p : ℝ) * rate.eta.val *
                    (((rewards x.time arm).val : ℝ) / (D p : ℝ)) /
                      registers.payload.rate arm) else 0) ∧
              (∀ j, serviced.arrival j = RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val ∧
                QueueReplay.transition (4 * rate.n)
                  (a.complementScores j, owned.queue j)
                  (c.enabled, RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val) =
                    (serviced.score j, serviced.queue j) ∧
                serviced.previousService j = serviced.service j ∧
                serviced.previousService j = serviced.score j - a.complementScores j) ∧
              r.output.coordinator.failure = none ∧
              r.output.next.coordinator =
                .live {
                  payload := a.payload
                  priorClock := finished.clock
                  pendingAtChoice := finished.pending
                  time := x.time
                  gridBoundary := finished.clock.g
                  complementScores := serviced.score }
                { queue := serviced.queue
                  previousService := serviced.previousService } followerBase
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
  have hstep :=
    ReferenceCompleteContinuingLiveCoordinatorStep.complete_live_continuing_coordinator_step
      (rate := rate) rewards C_star C_h source k registers q base hstate
  change preparation.coordinator = .live registers q base chosen ∧ _ at hstep
  rcases hstep with ⟨hpreparedCoordinator, hbranches⟩
  refine ⟨hpreparedCoordinator, ?_⟩
  cases hc : CoordinatorRoundDispatch.dispatchLive current with
  | continuingChosen dispatched hstartEq continuation selection =>
      rw [hc] at hbranches
      intro hlater
      rcases hbranches with
        ⟨v, hselected, hpayload, hcutoff, hstarted, harm, hlive, hselectedOutput,
          a, owned, followerBase, started, ha, howned, hbase, hstartedEq,
          valid, o, serviced, pending, finished, hpost⟩
      rcases hpost with
        ⟨hrun, hrecord, hgate, hraw, hdiag, hcall, hbridge, hqueue, hprevious,
          hserviceRecord, harrival, hservice, hresidual, hscore, hlast,
          hconfirm, hpending, hfinish, hpostChoice, hout, hnext, hup⟩
      refine ⟨v, hselected, hpayload, hcutoff, hstarted, harm, hlive,
        hselectedOutput, a, owned, followerBase, started, ha, howned, hbase,
        hstartedEq, valid, o, serviced, pending, finished, hrun, hrecord,
        hgate, hraw, hdiag, hcall, hbridge, hqueue, hprevious, hserviceRecord,
        harrival, hservice, hresidual, hscore, hlast, hconfirm, hpending,
        hfinish, hpostChoice, hout, hnext, hup, ?_⟩
      have ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary r := by
        intro i
        obtain ⟨_, memory, choice, _, _, _, hactual, _, _⟩ :=
          ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
            (rate := rate) rewards C_star C_h source k i
        change (r.output.preparation.followers.followers i).configuration =
          .ordinary choice memory at hactual
        rw [hactual]
        rfl
      have hdomain : ReferenceLaterLiveNumericalReadout.laterLiveDomain
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) r :=
        ⟨v, hselectedOutput, by simpa only [hpayload] using hlater, hlive, ho⟩
      obtain ⟨c, hreadout⟩ := Option.isSome_iff_exists.mp
        ((ReferenceLaterLiveNumericalReadout.laterLiveReadout_domain _ r).mpr hdomain)
      obtain ⟨selected, ordinary, hs, _, _, hcell⟩ :=
        ReferenceLaterLiveNumericalReadout.laterLiveReadout_some _ r c hreadout
      have hselectedEq : selected = v := Option.some.inj (hs.symm.trans hselectedOutput)
      subst selected
      have hcellCanonical : c = ReferenceFirstWindowNumericalStream.sourceCell r v.view.payload
          v.view.pendingAtChoice (ReferenceLaterLiveNumericalReadout.preparedStates r ho)
          v.view.complementWeights v.view.cutoff
          (ReferenceLaterLiveNumericalReadout.selection_choiceValid v) := hcell
      obtain ⟨henabled, selected, hs, hreward, hrate, hfloor⟩ :=
        ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical _ r c hreadout
      have hselectedEq : selected = v := Option.some.inj (hs.symm.trans hselectedOutput)
      subst selected
      have hphysical := ReferenceLaterLiveNumericalReadout.laterLiveReadout_physical
        rate rewards C_star C_h source k c hreadout
      simp only [List.get_eq_getElem] at hphysical
      obtain ⟨cell, _hcellInput, _, _, _, hrows, hrowIndex, hrewards,
        _, _, _, _, _, _, hphysicalRaw, _⟩ := hphysical
      have hphysicalSelected : cell.selected = v :=
        Option.some.inj (cell.selection_actual.symm.trans hselectedOutput)
      have hstates : cell.states = ReferenceLaterLiveNumericalReadout.preparedStates r ho := by
        funext i
        have hconfig := (cell.ordinary i).symm.trans
          (ReferenceLaterLiveNumericalReadout.prepared_configuration r ho i)
        exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hconfig).1
      have hmemories : cell.memories = ReferenceLaterLiveNumericalReadout.preparedMemories r ho := by
        funext i
        have hconfig := (cell.ordinary i).symm.trans
          (ReferenceLaterLiveNumericalReadout.prepared_configuration r ho i)
        exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hconfig).2
      have hpreparedFamily : ∀ i,
          (r.output.preparation.followers.followers i).configuration =
            .ordinary (ReferenceLaterLiveNumericalReadout.preparedStates r ho i)
              (ReferenceLaterLiveNumericalReadout.preparedMemories r ho i) := by
        simpa only [hstates, hmemories] using cell.ordinary
      have hapayload : a.payload = registers.payload := by
        have heq : a = ReferenceActivePhysicalStep.liveRegistersAt registers x.time := eq_of_heq ha
        calc
          a.payload = (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).payload :=
            congrArg (fun b : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta => b.payload) heq
          _ = registers.payload := rfl
      obtain ⟨physicalRecording, _hphysicalRecording, hrawAll⟩ := hphysicalRaw
      have harrivals : ∀ j, serviced.arrival j = RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val := by
        intro j
        have hfast : j.val ∉ cell.selected.view.payload.slowSet.val := by
          rw [hphysicalSelected, hpayload, ← hapayload]
          exact (Finset.mem_sdiff.mp j.property).2
        have hrawCanonical := hrawAll j.val hfast
        have hrecording : ReferenceCoordinatorRecorderCallTrace.recording
            (ReferenceActiveHorizonMeasurability.roundRecordCode r) = some o := by
          rw [ReferenceCoordinatorRecorderCallTrace.recording_eq_actualDiagnostics]
          exact hrecord
        unfold ReferenceCoordinatorRecorderCallTrace.coordinatorRaw at hrawCanonical
        rw [hrecording, Option.map_some] at hrawCanonical
        have hvalue := Option.some.inj hrawCanonical
        rw [harrival j, CoordinatorLiveServiceFinish.complementArrival]
        exact hvalue
      change r.input.rewards = rewards at hrewards
      rw [hrewards] at hreward hfloor
      refine ⟨c, ho, hreadout, henabled, hcellCanonical, hpreparedFamily,
        hrows, hrowIndex, hrewards, ?_, ?_, hapayload, ?_, ?_, ?_, ?_⟩
      · exact hreward
      · simpa only [hpayload] using hrate
      · simpa only [hpayload] using hfloor
      · intro j
        refine ⟨harrivals j, ?_, hlast j, ?_⟩
        · rw [henabled, ← harrivals j, ← ReferenceActivePhysicalStep.payload_n_eq a.payload]
          exact CoordinatorLiveServiceFinish.serviced_queueReplay_transition a owned serviced j
        · rw [hscore j, hlast j]
          exact (Nat.add_sub_cancel_left (a.complementScores j) (serviced.service j)).symm
      · rw [hout]
      · rw [hnext, hpostChoice]
  | cutoffChosen dispatched hstart ledger hinitialization hledger hdomain hclock
      hpending hassignment selection =>
      trivial
  | clockFailure failure hdispatch =>
      rw [hc] at hbranches
      exact False.elim hbranches
  | initializerFailure dispatched hstart checked hchecked =>
      rw [hc] at hbranches
      exact False.elim hbranches
  | localFailure dispatched hstart reason =>
      rw [hc] at hbranches
      exact False.elim hbranches

end Bandits.Support.ReferenceCompleteLaterLiveCalendarService

end
