/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveConfirmedOccupancy

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeWhile

/-!
# Actual first-live missing-confirmation provenance

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-88,293-318`,
`sources/zip4/manuscript/06_interruptions.tex:246-295`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

This module follows the coordinator's actual missing-confirmation register
from the original first installation through the first live window. It records
only positive DOWN confirmation events evaluated on each original row and the
coordinator's own prepared feedback. It proves provenance for a follower
outside the current pre-choice missing set; it makes no follower-persistence,
release, service, queue-truth, or regret-closure claim.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstLiveMissingSetProvenance

open ConstructorDimensions
open ReferenceActivePhysicalStep

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev Selection := ReferenceActivePhysicalStep.Selection (p := p) (rate := rate)
abbrev Registers := CoordinatorLiveChoiceRecorderStep.Registers p rate.eta

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

/-- The actual positive DOWN confirmation predicate on one retained physical
record, using its original row and the coordinator's own prepared feedback. -/
def actualDownConfirmationEvent
    (record : Record (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection (p := p) (rate := rate)
      record.input) : Prop :=
  CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
    selected.view.pendingAtChoice selected.view.cutoff record.input.time
    (record.input.row.2 record.input.time)
    record.output.preparation.coordinatorObservation

private theorem livePostChoice_pending_update
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound (p := p) (rate := rate) x)
    (r : Registers) (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base nextBase : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hpending : started.pending = r.clockPending)
    (next : Registers) (nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters next)
    (hnext : (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).configuration =
      .live next nextOwned nextBase) :
    next.payload = r.payload ∧
      next.pendingAtChoice =
        if CoordinatorLocalArmChoice.downConfirmationEvent r.payload r.pendingAtChoice
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time
          (x.row.2 x.time) prepared.coordinatorObservation then
          r.pendingAtChoice.erase (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m
            p.m_lt_K (x.row.2 x.time).1)
        else r.pendingAtChoice := by
  classical
  let recorderInput := ReferenceActivePhysicalStep.liveRecordingInput prepared r started
  cases hrecord : CoordinatorRecorderComplementBridge.run recorderInput with
  | none =>
      simp [ReferenceActivePhysicalStep.livePostChoice, recorderInput, hrecord] at hnext
      change CoordinatorConfiguration.dagger = .live next nextOwned nextBase at hnext
      cases hnext
  | some recording =>
      cases hservice : CoordinatorLiveServiceFinish.servicePass r q recording with
      | error failure =>
          simp [ReferenceActivePhysicalStep.livePostChoice, recorderInput, hrecord,
            hservice] at hnext
          change CoordinatorConfiguration.dagger = .live next nextOwned nextBase at hnext
          cases hnext
      | ok serviced =>
          cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate r.payload
              started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row prepared.coordinatorObservation with
          | none =>
              simp [ReferenceActivePhysicalStep.livePostChoice, recorderInput, hrecord,
                hservice, hconfirmation] at hnext
              change CoordinatorConfiguration.dagger = .live next nextOwned nextBase at hnext
              cases hnext
          | some pendingAfter =>
              cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock pendingAfter x.row with
              | error failure =>
                  simp [ReferenceActivePhysicalStep.livePostChoice, recorderInput,
                    hrecord, hservice, hconfirmation, hfinish] at hnext
                  change CoordinatorConfiguration.dagger = .live next nextOwned nextBase at hnext
                  cases hnext
              | ok finished =>
                  have hconfig : CoordinatorConfiguration.live {
                      payload := r.payload
                      priorClock := finished.clock
                      pendingAtChoice := finished.pending
                      time := x.time
                      gridBoundary := finished.clock.g
                      complementScores := serviced.score } {
                        queue := serviced.queue, previousService := serviced.previousService } base =
                      .live next nextOwned nextBase := by
                    simpa [ReferenceActivePhysicalStep.livePostChoice, recorderInput,
                      hrecord, hservice, hconfirmation, hfinish] using hnext
                  have hfields : next = {
                      payload := r.payload
                      priorClock := finished.clock
                      pendingAtChoice := finished.pending
                      time := x.time
                      gridBoundary := finished.clock.g
                      complementScores := serviced.score } :=
                    ((CoordinatorConfiguration.live.inj hconfig).1).symm
                  have hvalid : CoordinatorLocalArmChoice.ConfirmationInputsValid r.payload
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time := by
                    by_contra hinvalid
                    have hnone : CoordinatorLocalArmChoice.confirmationUpdateCore r.payload
                        started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                          started.clock.u) x.time (x.row.2 x.time)
                        prepared.coordinatorObservation = none := by
                      simp [CoordinatorLocalArmChoice.confirmationUpdateCore, hinvalid]
                    have hcore : CoordinatorLocalArmChoice.confirmationUpdateCore r.payload
                        started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                          started.clock.u) x.time (x.row.2 x.time)
                        prepared.coordinatorObservation = some pendingAfter := by
                      simpa only [CoordinatorLocalArmChoice.confirmationUpdate] using hconfirmation
                    rw [hnone] at hcore
                    cases hcore
                  have hcore : CoordinatorLocalArmChoice.confirmationUpdateCore r.payload
                      started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                        started.clock.u) x.time (x.row.2 x.time)
                      prepared.coordinatorObservation = some pendingAfter := by
                    simpa only [CoordinatorLocalArmChoice.confirmationUpdate] using hconfirmation
                  have hstartReg : started.pending = r.pendingAtChoice :=
                    hpending.trans (CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq r)
                  have hcoreRegisters : CoordinatorLocalArmChoice.confirmationUpdateCore r.payload
                      r.pendingAtChoice (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                        started.clock.u) x.time (x.row.2 x.time)
                      prepared.coordinatorObservation = some pendingAfter := by
                    simpa only [hstartReg] using hcore
                  have htransition : pendingAfter =
                      if CoordinatorLocalArmChoice.downConfirmationEvent r.payload
                          r.pendingAtChoice (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                            started.clock.u) x.time (x.row.2 x.time)
                          prepared.coordinatorObservation then
                        r.pendingAtChoice.erase (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m
                          p.m_lt_K (x.row.2 x.time).1)
                      else r.pendingAtChoice := by
                    by_cases hevent : CoordinatorLocalArmChoice.downConfirmationEvent r.payload
                        r.pendingAtChoice (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                          started.clock.u) x.time (x.row.2 x.time)
                        prepared.coordinatorObservation
                    · have hremove := CoordinatorLocalArmChoice.confirmationUpdateCore_removes
                        r.payload r.pendingAtChoice (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                          started.clock.u) x.time (x.row.2 x.time)
                        prepared.coordinatorObservation hvalid hevent
                      have hvalue : pendingAfter = r.pendingAtChoice.erase
                          (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                            (x.row.2 x.time).1) :=
                        Option.some.inj (hcoreRegisters.symm.trans hremove)
                      simp only [ite_eq_left hevent]
                      exact hvalue
                    · have hpreserve := CoordinatorLocalArmChoice.confirmationUpdateCore_preserves
                        r.payload r.pendingAtChoice (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                          started.clock.u) x.time (x.row.2 x.time)
                        prepared.coordinatorObservation hvalid hevent
                      have hvalue : pendingAfter = r.pendingAtChoice :=
                        Option.some.inj (hcoreRegisters.symm.trans hpreserve)
                      simp only [ite_eq_right hevent]
                      exact hvalue
                  have hfinishPending := CoordinatorPhaseClock.finishRound_pending_frame p
                    rate.eta.val x.time started.clock pendingAfter x.row finished hfinish
                  rw [hfields]
                  constructor
                  · rfl
                  · simp only [hfinishPending, htransition]

/-- The actual first dispatch installs every follower into the missing set.
The same literal installation yields the selected pre-choice view and the
next live register, whose pending set erases the selected follower exactly on
the positive event computed from this row and prepared feedback. -/
theorem first_live_actual_installation_pending_frame
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hfirst : x.state.coordinator = .first)
    (next : Registers) (nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters next)
    (base : Fin (p.m - 1) → ℕ)
    (hnext : (ReferenceActivePhysicalStep.step x).next.coordinator = .live next nextOwned base) :
    ∃ installed arm selected,
      CoordinatorRoundDispatch.dispatchFirst (ReferenceActivePhysicalStep.firstInput x) =
        .chosen installed arm ∧
      (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected ∧
      installed = CoordinatorAssignmentRegisterInstall.installFirst
        (CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput x)) ∧
      installed.registers.pendingAtChoice = Finset.univ ∧
      installed.startRoundResult.pending = Finset.univ ∧
      selected.view.payload = installed.registers.payload ∧
      selected.view.pendingAtChoice = Finset.univ ∧
      next.payload = selected.view.payload ∧
      next.pendingAtChoice =
        if actualDownConfirmationEvent
            ({ input := x, output := ReferenceActivePhysicalStep.step x, output_eq := rfl } : Record)
            selected then
          Finset.univ.erase (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (x.row.2 x.time).1)
        else Finset.univ := by
  classical
  have hdispatch := ReferenceActivePhysicalStep.dispatch_first x hfirst
  have hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .first (CoordinatorRoundDispatch.dispatchFirst (ReferenceActivePhysicalStep.firstInput x)) :=
    (ReferenceActivePhysicalStep.prepare x).coordinator_eq.trans hdispatch
  cases houtcome : CoordinatorRoundDispatch.dispatchFirst
      (ReferenceActivePhysicalStep.firstInput x) with
  | choiceDomainFailure installed =>
      have hobs := ReferenceActivePhysicalStep.observeCoordinator_first_equation
        (ReferenceActivePhysicalStep.prepare x)
        (.choiceDomainFailure installed) (by simp [hprepared, houtcome])
      have hconfig := (ReferenceActivePhysicalStep.step_next_fields x).1
      rw [hconfig] at hnext
      rw [hobs] at hnext
      simp [DispatchCut.selection, ReferenceActivePhysicalStep.coordinatorFailure] at hnext
  | recorderBoundaryFailure installed =>
      have hobs := ReferenceActivePhysicalStep.observeCoordinator_first_equation
        (ReferenceActivePhysicalStep.prepare x)
        (.recorderBoundaryFailure installed) (by simp [hprepared, houtcome])
      have hconfig := (ReferenceActivePhysicalStep.step_next_fields x).1
      rw [hconfig] at hnext
      rw [hobs] at hnext
      simp [DispatchCut.selection, ReferenceActivePhysicalStep.coordinatorFailure] at hnext
  | choiceRejected installed =>
      have hobs := ReferenceActivePhysicalStep.observeCoordinator_first_equation
        (ReferenceActivePhysicalStep.prepare x)
        (.choiceRejected installed) (by simp [hprepared, houtcome])
      have hconfig := (ReferenceActivePhysicalStep.step_next_fields x).1
      rw [hconfig] at hnext
      rw [hobs] at hnext
      simp [DispatchCut.selection, ReferenceActivePhysicalStep.coordinatorFailure] at hnext
  | chosen installed arm =>
      have hchosen := ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
        x installed arm houtcome
      have htime := ReferenceActivePhysicalStep.dispatchFirst_chosen_time x installed arm houtcome
      let selected : Selection x := {
        view := {
          payload := installed.registers.payload
          pendingAtChoice := installed.startRoundResult.pending
          cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
            installed.startRoundResult.clock.u
          complementWeights := installed.registers.complementWeights }
        started := installed.startRoundResult
        pending_eq := rfl
        cutoff_eq := rfl
        arm := arm.arm
        choice_eq := by
          simpa [ReferenceActivePhysicalStep.firstInput,
            ReferenceActivePhysicalStep.RoundInput.row, htime] using arm.armChoice_eq }
      have hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection =
          some selected := by
        rw [hprepared, houtcome]
        simp [DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt, htime, selected]
      have hselectedCut : (DispatchCut.first (.chosen installed arm)).selection =
          some selected := by
        simpa [hprepared, houtcome] using hselected
      have hregisterPending : installed.registers.pendingAtChoice = Finset.univ := by
        rw [hchosen]
        exact CoordinatorAssignmentRegisterInstall.first_registers_pending _
      have hstartedPending : installed.startRoundResult.pending = Finset.univ := by
        rw [hchosen]
        rfl
      have hregisterClockPending : installed.registers.clockPending = Finset.univ := by
        rw [CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq,
          hregisterPending]
        rfl
      have hpending : installed.startRoundResult.pending = installed.registers.clockPending :=
        hstartedPending.trans hregisterClockPending.symm
      have hobs := ReferenceActivePhysicalStep.observeCoordinator_first_equation
        (ReferenceActivePhysicalStep.prepare x) (.chosen installed arm)
        (by simp [hprepared, houtcome])
      have hobs' : (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
          ReferenceActivePhysicalStep.livePostChoice
            (ReferenceActivePhysicalStep.prepare x) installed.registers installed.ownedRegisters
            installed.followerBaseScore installed.startRoundResult := by
        simpa [hselectedCut] using hobs
      have hnextLive :
          (ReferenceActivePhysicalStep.livePostChoice
            (ReferenceActivePhysicalStep.prepare x) installed.registers installed.ownedRegisters
            installed.followerBaseScore installed.startRoundResult).configuration =
            .live next nextOwned base := by
        calc
          _ = (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration :=
            (congrArg CoordinatorObservation.configuration hobs').symm
          _ = .live next nextOwned base :=
            (ReferenceActivePhysicalStep.step_next_fields x).1.symm.trans hnext
      have htail := livePostChoice_pending_update (ReferenceActivePhysicalStep.prepare x)
        installed.registers installed.ownedRegisters installed.followerBaseScore base
        installed.startRoundResult hpending next nextOwned hnextLive
      refine ⟨installed, arm, selected, rfl, hselected, hchosen, hregisterPending,
        hstartedPending, rfl, selected.pending_eq.trans hstartedPending, ?_⟩
      constructor
      · simpa [selected] using htail.1
      · change next.pendingAtChoice =
          if CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
              selected.view.pendingAtChoice selected.view.cutoff x.time (x.row.2 x.time)
              (ReferenceActivePhysicalStep.prepare x).coordinatorObservation then
            Finset.univ.erase (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (x.row.2 x.time).1)
          else Finset.univ
        have hselectedPending : selected.view.pendingAtChoice = installed.registers.pendingAtChoice :=
          selected.pending_eq.trans (hstartedPending.trans hregisterPending.symm)
        have heventEq :
            CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
                selected.view.pendingAtChoice selected.view.cutoff x.time (x.row.2 x.time)
                (ReferenceActivePhysicalStep.prepare x).coordinatorObservation =
              CoordinatorLocalArmChoice.downConfirmationEvent installed.registers.payload
                installed.registers.pendingAtChoice
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                  installed.startRoundResult.clock.u) x.time (x.row.2 x.time)
                (ReferenceActivePhysicalStep.prepare x).coordinatorObservation := by
          change CoordinatorLocalArmChoice.downConfirmationEvent installed.registers.payload
              selected.view.pendingAtChoice
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                installed.startRoundResult.clock.u) x.time (x.row.2 x.time)
              (ReferenceActivePhysicalStep.prepare x).coordinatorObservation = _
          rw [hselectedPending]
        rw [heventEq]
        calc
          next.pendingAtChoice =
              if CoordinatorLocalArmChoice.downConfirmationEvent installed.registers.payload
                  installed.registers.pendingAtChoice
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                    installed.startRoundResult.clock.u) x.time (x.row.2 x.time)
                  (ReferenceActivePhysicalStep.prepare x).coordinatorObservation then
                installed.registers.pendingAtChoice.erase
                  (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                    (x.row.2 x.time).1)
              else installed.registers.pendingAtChoice := htail.2
          _ = if CoordinatorLocalArmChoice.downConfirmationEvent installed.registers.payload
                  installed.registers.pendingAtChoice
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                    installed.startRoundResult.clock.u) x.time (x.row.2 x.time)
                  (ReferenceActivePhysicalStep.prepare x).coordinatorObservation then
                Finset.univ.erase (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                  (x.row.2 x.time).1)
              else Finset.univ := by
            by_cases hevent : CoordinatorLocalArmChoice.downConfirmationEvent
                installed.registers.payload installed.registers.pendingAtChoice
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                  installed.startRoundResult.clock.u) x.time (x.row.2 x.time)
                (ReferenceActivePhysicalStep.prepare x).coordinatorObservation
            · simp [hregisterPending]
            · simp [hregisterPending]

private theorem actualDispatchLiveContinuingPending
    (input : CoordinatorRoundDispatch.LiveInput p)
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      input.registers input.ownedRegisters input.followerBaseScore)
    (hstart : CoordinatorPhaseClock.startRound p input.eta.val input.registers.time
      input.registers.priorClock input.registers.clockPending = .ok dispatched.startResult)
    (continuation : CoordinatorLiveChoiceRecorderStep.Continuation input.registers input.row)
    (selection : CoordinatorRoundDispatch.ArmSelection input.registers.payload
      dispatched.startResult input.registers.time input.registers.complementWeights input.row)
    (heq : CoordinatorRoundDispatch.dispatchLive input =
      .continuingChosen dispatched hstart continuation selection) :
    dispatched.startResult.pending = input.registers.pendingAtChoice := by
  unfold CoordinatorRoundDispatch.dispatchLive at heq
  dsimp only at heq
  split at heq
  · cases heq
  · rename_i actual hactual
    split at heq
    · cases heq
    · cases heq
    · by_cases hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
          input.registers actual.startResult
      · rw [dite_eq_left hframe] at heq
        have hp := hframe.2.1.trans
          (CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq input.registers)
        repeat' split at heq
        all_goals first
          | (cases heq; exact hp)
          | cases heq
          | (rename_i hchoice hboundary henvelope hselected
             exact ((CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
               input.registers.payload actual.startResult.pending
               (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p actual.startResult.clock.u)
               input.registers.time input.registers.complementWeights input.row hchoice) hselected).elim)
      · rw [dite_eq_right hframe] at heq
        cases heq
    · repeat' split at heq
      all_goals first
        | cases heq
        | (rename_i hchoice hboundary henvelope hselected
           exact ((CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
             input.registers.payload actual.startResult.pending
             (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p actual.startResult.clock.u)
             input.registers.time input.registers.complementWeights input.row hchoice) hselected).elim)

/-- A continuing live dispatch preserves its incoming pending set through the
actual StartRound clock frame, selects from that same set and payload, and
updates the next live register by the exact actual DOWN event on this row. -/
theorem first_live_actual_continuing_pending_frame
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : Registers) (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hlive : x.state.coordinator = .live r q base)
    (hnocut : ReferenceCollectionPhaseHistory.cutoffChosen x = false)
    (next : Registers) (nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters next)
    (nextBase : Fin (p.m - 1) → ℕ)
    (hnext : (ReferenceActivePhysicalStep.step x).next.coordinator =
      .live next nextOwned nextBase) :
    ∃ selected : Selection x,
      (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected ∧
      selected.view.payload = r.payload ∧
      selected.view.pendingAtChoice = r.pendingAtChoice ∧
      selected.started.pending = r.pendingAtChoice ∧
      next.payload = selected.view.payload ∧
      next.pendingAtChoice =
        if actualDownConfirmationEvent
            ({ input := x, output := ReferenceActivePhysicalStep.step x, output_eq := rfl } : Record)
            selected then
          r.pendingAtChoice.erase (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m
            p.m_lt_K (x.row.2 x.time).1)
        else r.pendingAtChoice := by
  classical
  have hdispatch : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live r q base (CoordinatorRoundDispatch.dispatchLive
        (ReferenceActivePhysicalStep.liveInput x r q base)) := by
    change ReferenceActivePhysicalStep.dispatch x = _
    simp only [ReferenceActivePhysicalStep.dispatch, hlive,
      CoordinatorRoundDispatch.dispatch]
    rfl
  have hprepared := (ReferenceActivePhysicalStep.prepare x).coordinator_eq.trans hdispatch
  cases houtcome : CoordinatorRoundDispatch.dispatchLive
      (ReferenceActivePhysicalStep.liveInput x r q base) with
  | clockFailure failure hfailure =>
      rw [houtcome] at hprepared
      have hobs := ReferenceActivePhysicalStep.observeCoordinator_live_equation
        (ReferenceActivePhysicalStep.prepare x) r q base (.clockFailure failure hfailure) hprepared
      have hconfig := ReferenceActivePhysicalStep.step_next_fields x
      rw [hconfig.1] at hnext
      rw [hobs] at hnext
      simp [DispatchCut.selection, ReferenceActivePhysicalStep.coordinatorFailure] at hnext
  | initializerFailure dispatched hstart checked hchecked =>
      rw [houtcome] at hprepared
      have hobs := ReferenceActivePhysicalStep.observeCoordinator_live_equation
        (ReferenceActivePhysicalStep.prepare x) r q base
        (.initializerFailure dispatched hstart checked hchecked) hprepared
      have hconfig := ReferenceActivePhysicalStep.step_next_fields x
      rw [hconfig.1] at hnext
      rw [hobs] at hnext
      simp [DispatchCut.selection, ReferenceActivePhysicalStep.coordinatorFailure] at hnext
  | localFailure dispatched hstart failure =>
      rw [houtcome] at hprepared
      have hobs := ReferenceActivePhysicalStep.observeCoordinator_live_equation
        (ReferenceActivePhysicalStep.prepare x) r q base
        (.localFailure dispatched hstart failure) hprepared
      have hconfig := ReferenceActivePhysicalStep.step_next_fields x
      rw [hconfig.1] at hnext
      rw [hobs] at hnext
      simp [DispatchCut.selection, ReferenceActivePhysicalStep.coordinatorFailure] at hnext
  | cutoffChosen dispatched hstart ledger hinitial hledger hvalid hclock hpending hno arm =>
      rw [houtcome] at hprepared
      have hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen x = true := by
        simp [ReferenceCollectionPhaseHistory.cutoffChosen, hprepared]
      simp [hnocut] at hcutoff
  | continuingChosen dispatched hstart continuation arm =>
      rw [houtcome] at hprepared
      let selected : Selection x := {
        view := {
          payload := r.payload
          pendingAtChoice := dispatched.startResult.pending
          cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
            dispatched.startResult.clock.u
          complementWeights := (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights }
        started := dispatched.startResult
        pending_eq := rfl
        cutoff_eq := rfl
        arm := arm.arm
        choice_eq := by
          simpa [ReferenceActivePhysicalStep.liveInput,
            ReferenceActivePhysicalStep.liveRegistersAt] using arm.armChoice_eq }
      have hselectedCut :
          (DispatchCut.live r q base (.continuingChosen dispatched hstart continuation arm)).selection =
            some selected := by
        simp [DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt, selected]
      have hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection =
          some selected := by
        rw [hprepared]
        exact hselectedCut
      have hpendingInput := actualDispatchLiveContinuingPending
        (ReferenceActivePhysicalStep.liveInput x r q base) dispatched hstart continuation arm houtcome
      have hpending : dispatched.startResult.pending = r.pendingAtChoice := by
        simpa only [ReferenceActivePhysicalStep.liveInput,
          ReferenceActivePhysicalStep.liveRegistersAt] using hpendingInput
      have hclockPending : dispatched.startResult.pending =
          (ReferenceActivePhysicalStep.liveRegistersAt r x.time).clockPending := by
        have hp := hpendingInput.trans
          (CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq
            (ReferenceActivePhysicalStep.liveInput x r q base).registers).symm
        simpa only [ReferenceActivePhysicalStep.liveInput,
          ReferenceActivePhysicalStep.liveRegistersAt] using hp
      have hobs := ReferenceActivePhysicalStep.observeCoordinator_live_equation
        (ReferenceActivePhysicalStep.prepare x) r q base
        (.continuingChosen dispatched hstart continuation arm) hprepared
      have hobs' : (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
          ReferenceActivePhysicalStep.livePostChoice
            (ReferenceActivePhysicalStep.prepare x)
            (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
            (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base dispatched.startResult := by
        simpa [hselectedCut] using hobs
      have hnextLive :
          (ReferenceActivePhysicalStep.livePostChoice
            (ReferenceActivePhysicalStep.prepare x)
            (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
            (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base dispatched.startResult).configuration =
            .live next nextOwned nextBase := by
        calc
          _ = (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration :=
            (congrArg CoordinatorObservation.configuration hobs').symm
          _ = .live next nextOwned nextBase :=
            (ReferenceActivePhysicalStep.step_next_fields x).1.symm.trans hnext
      have htail := livePostChoice_pending_update
        (ReferenceActivePhysicalStep.prepare x)
        (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
        (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base nextBase
        dispatched.startResult hclockPending next nextOwned hnextLive
      refine ⟨selected, hselected, rfl, hpending,
        selected.pending_eq.symm.trans hpending, htail.1, ?_⟩
      change next.pendingAtChoice =
        if CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
            selected.view.pendingAtChoice selected.view.cutoff x.time (x.row.2 x.time)
            (ReferenceActivePhysicalStep.prepare x).coordinatorObservation then
          r.pendingAtChoice.erase (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m
            p.m_lt_K (x.row.2 x.time).1)
        else r.pendingAtChoice
      have heventEq :
          CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
              selected.view.pendingAtChoice selected.view.cutoff x.time (x.row.2 x.time)
              (ReferenceActivePhysicalStep.prepare x).coordinatorObservation =
            CoordinatorLocalArmChoice.downConfirmationEvent r.payload r.pendingAtChoice
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                dispatched.startResult.clock.u) x.time (x.row.2 x.time)
              (ReferenceActivePhysicalStep.prepare x).coordinatorObservation := by
        simp only [selected, hpending]
      rw [heventEq]
      calc
        next.pendingAtChoice =
            if CoordinatorLocalArmChoice.downConfirmationEvent r.payload r.pendingAtChoice
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                  dispatched.startResult.clock.u) x.time (x.row.2 x.time)
                (ReferenceActivePhysicalStep.prepare x).coordinatorObservation then
              r.pendingAtChoice.erase (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m
                p.m_lt_K (x.row.2 x.time).1)
            else r.pendingAtChoice := by
          exact htail.2
        _ = if CoordinatorLocalArmChoice.downConfirmationEvent r.payload r.pendingAtChoice
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                  dispatched.startResult.clock.u) x.time (x.row.2 x.time)
                (ReferenceActivePhysicalStep.prepare x).coordinatorObservation then
              r.pendingAtChoice.erase (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m
                p.m_lt_K (x.row.2 x.time).1)
            else r.pendingAtChoice := rfl

private def ActualFirstLiveRecordFrame
    (record : Record (p := p) (rate := rate)) : Prop :=
  ∃ selected : Selection (p := p) (rate := rate) record.input,
    record.output.preparation.coordinator.selection = some selected ∧
    ∃ payload : ReferenceActivePhysicalStep.Payload rate,
      selected.view.payload = payload ∧
      (match record.input.state.coordinator with
        | .first => selected.view.pendingAtChoice = Finset.univ ∧
            selected.started.pending = Finset.univ
        | .live incoming _ _ =>
            selected.view.payload = incoming.payload ∧
              selected.view.pendingAtChoice = incoming.pendingAtChoice ∧
              selected.started.pending = incoming.pendingAtChoice
        | _ => False) ∧
      (match record.input.state.coordinator with
        | .first =>
            ∃ installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
                (CoordinatorRoundDispatch.firstLaunchInput
                  (ReferenceActivePhysicalStep.firstInput record.input)),
              ∃ arm : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
                  installed.startRoundResult installed.registers.time
                  installed.registers.complementWeights record.input.row,
                CoordinatorRoundDispatch.dispatchFirst
                    (ReferenceActivePhysicalStep.firstInput record.input) = .chosen installed arm ∧
                installed = CoordinatorAssignmentRegisterInstall.installFirst
                  (CoordinatorRoundDispatch.firstLaunchInput
                    (ReferenceActivePhysicalStep.firstInput record.input)) ∧
                installed.registers.pendingAtChoice = Finset.univ ∧
                installed.startRoundResult.pending = Finset.univ ∧
                installed.registers.payload = payload
        | .live _ _ _ => True
        | _ => False) ∧
      ∃ next : Registers, ∃ nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters next,
        ∃ nextBase : Fin (p.m - 1) → ℕ,
          record.output.next.coordinator = .live next nextOwned nextBase ∧
          next.payload = selected.view.payload ∧
          next.pendingAtChoice =
            if actualDownConfirmationEvent record selected then
              selected.view.pendingAtChoice.erase
                (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                  (record.input.row.2 record.input.time).1)
            else selected.view.pendingAtChoice

private theorem actualFirstLiveRecordFrames
    (records : List (Record (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalHorizon.State p rate)
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (phase : initial.coordinator = .first ∨
      ∃ registers owned base, initial.coordinator = .live registers owned base)
    (safe : ∀ record ∈ records,
      ∃ next owned base, record.output.next.coordinator = .live next owned base)
    (noCut : ∀ record ∈ records,
      ReferenceCollectionPhaseHistory.cutoffChosen record.input = false) :
    ∀ record ∈ records, ActualFirstLiveRecordFrame record := by
  induction records generalizing initial final with
  | nil =>
      intro record hmem
      simp at hmem
  | cons head tail ih =>
      intro record hmem
      obtain ⟨hinput, htailChain⟩ := chain
      obtain ⟨next, nextOwned, nextBase, hnext⟩ := safe head List.mem_cons_self
      have hphaseHead :
          head.input.state.coordinator = .first ∨
            ∃ registers owned base, head.input.state.coordinator = .live registers owned base := by
        rcases phase with hfirst | ⟨registers, owned, base, hlive⟩
        · exact Or.inl ((congrArg (fun s : ReferenceActivePhysicalStep.State p rate =>
            s.coordinator) hinput).trans hfirst)
        · exact Or.inr ⟨registers, owned, base,
            (congrArg (fun s : ReferenceActivePhysicalStep.State p rate =>
              s.coordinator) hinput).trans hlive⟩
      have hheadFrame : ActualFirstLiveRecordFrame head := by
        rcases hphaseHead with hfirst | ⟨registers, owned, base, hlive⟩
        · have hnextStep :
              (ReferenceActivePhysicalStep.step head.input).next.coordinator =
                .live next nextOwned nextBase := by
            simpa only [head.output_eq] using hnext
          obtain ⟨installed, arm, selected, hdispatch, hselected, hinstalled,
            hregisterPending, hstartPending, hpayload, hselectedPending,
            hnextPayload, hnextPending⟩ :=
            first_live_actual_installation_pending_frame head.input hfirst
              next nextOwned nextBase hnextStep
          have hnextPending' :
              next.pendingAtChoice =
                if actualDownConfirmationEvent head selected then
                  selected.view.pendingAtChoice.erase
                    (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                      (head.input.row.2 head.input.time).1)
                else selected.view.pendingAtChoice := by
            have hnextPendingSelect :
                next.pendingAtChoice =
                  if CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
                      selected.view.pendingAtChoice selected.view.cutoff head.input.time
                      (head.input.row.2 head.input.time)
                      (ReferenceActivePhysicalStep.step head.input).preparation.coordinatorObservation then
                    selected.view.pendingAtChoice.erase
                      (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                        (head.input.row.2 head.input.time).1)
                  else selected.view.pendingAtChoice := by
              change next.pendingAtChoice =
                if CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
                    selected.view.pendingAtChoice selected.view.cutoff head.input.time
                    (head.input.row.2 head.input.time)
                    (ReferenceActivePhysicalStep.step head.input).preparation.coordinatorObservation then
                  Finset.univ.erase
                    (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                      (head.input.row.2 head.input.time).1)
                else Finset.univ at hnextPending
              by_cases hevent : CoordinatorLocalArmChoice.downConfirmationEvent
                  selected.view.payload selected.view.pendingAtChoice selected.view.cutoff
                  head.input.time (head.input.row.2 head.input.time)
                  (ReferenceActivePhysicalStep.step head.input).preparation.coordinatorObservation
              · rw [ite_eq_left hevent] at hnextPending ⊢
                simpa only [hselectedPending] using hnextPending
              · rw [ite_eq_right hevent] at hnextPending ⊢
                simpa only [hselectedPending] using hnextPending
            have hEventEq :
                CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
                    selected.view.pendingAtChoice selected.view.cutoff head.input.time
                    (head.input.row.2 head.input.time)
                    (ReferenceActivePhysicalStep.step head.input).preparation.coordinatorObservation =
                  actualDownConfirmationEvent head selected := by
              change CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
                  selected.view.pendingAtChoice selected.view.cutoff head.input.time
                  (head.input.row.2 head.input.time)
                  (ReferenceActivePhysicalStep.step head.input).preparation.coordinatorObservation =
                CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
                  selected.view.pendingAtChoice selected.view.cutoff head.input.time
                  (head.input.row.2 head.input.time) head.output.preparation.coordinatorObservation
              rw [head.output_eq]
            rw [hEventEq] at hnextPendingSelect
            exact hnextPendingSelect
          simp only [ActualFirstLiveRecordFrame, hfirst]
          have hselectedStartedPending : selected.started.pending = Finset.univ := by
            exact selected.pending_eq.symm.trans hselectedPending
          refine ⟨selected, ?_, installed.registers.payload, hpayload,
            ⟨hselectedPending, hselectedStartedPending⟩,
            ⟨installed, arm, hdispatch, hinstalled, hregisterPending, hstartPending, rfl⟩,
            next, nextOwned, nextBase, hnext, hnextPayload, hnextPending'⟩
          simpa only [head.output_eq, ReferenceActivePhysicalStep.step] using hselected
        · have hnextStep :
              (ReferenceActivePhysicalStep.step head.input).next.coordinator =
                .live next nextOwned nextBase := by
            simpa only [head.output_eq] using hnext
          have hnoCutHead := noCut head List.mem_cons_self
          obtain ⟨selected, hselected, hpayload, hpending, hstartedPending,
            hnextPayload, hnextPending⟩ :=
            first_live_actual_continuing_pending_frame head.input registers owned base
              hlive hnoCutHead next nextOwned nextBase hnextStep
          have hnextPending' :
              next.pendingAtChoice =
                if actualDownConfirmationEvent head selected then
                  selected.view.pendingAtChoice.erase
                    (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                      (head.input.row.2 head.input.time).1)
                else selected.view.pendingAtChoice := by
            have hnextPendingSelect :
                next.pendingAtChoice =
                  if CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
                      selected.view.pendingAtChoice selected.view.cutoff head.input.time
                      (head.input.row.2 head.input.time)
                      (ReferenceActivePhysicalStep.step head.input).preparation.coordinatorObservation then
                    selected.view.pendingAtChoice.erase
                      (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                        (head.input.row.2 head.input.time).1)
                  else selected.view.pendingAtChoice := by
              change next.pendingAtChoice =
                if CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
                    selected.view.pendingAtChoice selected.view.cutoff head.input.time
                    (head.input.row.2 head.input.time)
                    (ReferenceActivePhysicalStep.step head.input).preparation.coordinatorObservation then
                  registers.pendingAtChoice.erase
                    (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                      (head.input.row.2 head.input.time).1)
                else registers.pendingAtChoice at hnextPending
              by_cases hevent : CoordinatorLocalArmChoice.downConfirmationEvent
                  selected.view.payload selected.view.pendingAtChoice selected.view.cutoff
                  head.input.time (head.input.row.2 head.input.time)
                  (ReferenceActivePhysicalStep.step head.input).preparation.coordinatorObservation
              · rw [ite_eq_left hevent] at hnextPending ⊢
                simpa only [hpending] using hnextPending
              · rw [ite_eq_right hevent] at hnextPending ⊢
                simpa only [hpending] using hnextPending
            have hEventEq :
                CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
                    selected.view.pendingAtChoice selected.view.cutoff head.input.time
                    (head.input.row.2 head.input.time)
                    (ReferenceActivePhysicalStep.step head.input).preparation.coordinatorObservation =
                  actualDownConfirmationEvent head selected := by
              change CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
                  selected.view.pendingAtChoice selected.view.cutoff head.input.time
                  (head.input.row.2 head.input.time)
                  (ReferenceActivePhysicalStep.step head.input).preparation.coordinatorObservation =
                CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
                  selected.view.pendingAtChoice selected.view.cutoff head.input.time
                  (head.input.row.2 head.input.time) head.output.preparation.coordinatorObservation
              rw [head.output_eq]
            rw [hEventEq] at hnextPendingSelect
            exact hnextPendingSelect
          simp only [ActualFirstLiveRecordFrame, hlive]
          refine ⟨selected, ?_, registers.payload, hpayload,
            ⟨hpayload, hpending, hstartedPending⟩, trivial,
            next, nextOwned, nextBase, hnext, hnextPayload, hnextPending'⟩
          simpa only [head.output_eq, ReferenceActivePhysicalStep.step] using hselected
      have htailFrames : ∀ record ∈ tail, ActualFirstLiveRecordFrame record := by
        exact ih (head.output.next) final htailChain
          (Or.inr ⟨next, nextOwned, nextBase, hnext⟩)
          (fun record hrecord => safe record (List.mem_cons_of_mem _ hrecord))
          (fun record hrecord => noCut record (List.mem_cons_of_mem _ hrecord))
      rcases List.mem_cons.mp hmem with heq | htailMem
      · subst record
        exact hheadFrame
      · exact htailFrames record htailMem

private def ActualConfirmationIn
    (records : List (Record (p := p) (rate := rate)))
    (payload : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1)) : Prop :=
  ∃ record, record ∈ records ∧
    ∃ selected : Selection (p := p) (rate := rate) record.input,
      record.output.preparation.coordinator.selection = some selected ∧
      selected.view.payload = payload ∧
      actualDownConfirmationEvent record selected ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (record.input.row.2 record.input.time).1 = i

private theorem actualConfirmationIn_append_left
    (records : List (Record (p := p) (rate := rate)))
    (record : Record (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1))
    (h : ActualConfirmationIn records payload i) :
    ActualConfirmationIn (records ++ [record]) payload i := by
  rcases h with ⟨prior, hprior, selected, hselected, hpayload, hevent, hdraw⟩
  exact ⟨prior, List.mem_append_left _ hprior, selected, hselected, hpayload, hevent, hdraw⟩

private theorem actualConfirmationIn_take_index
    (window historyPrefix : List (Record (p := p) (rate := rate)))
    (k : ℕ) (hbound : k ≤ window.length)
    (payload : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1))
    (hprefix : historyPrefix = window.take k)
    (h : ActualConfirmationIn historyPrefix payload i) :
    ∃ ell, ∃ hell : ell < k, ∃ selected :
      Selection (p := p) (rate := rate) (window[ell]'(by omega)).input,
        (window[ell]'(by omega)).output.preparation.coordinator.selection = some selected ∧
        selected.view.payload = payload ∧
        actualDownConfirmationEvent (window[ell]'(by omega)) selected ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          ((window[ell]'(by omega)).input.row.2 (window[ell]'(by omega)).input.time).1 = i := by
  rcases h with ⟨prior, hprior, selected, hselected, hpayload, hevent, hdraw⟩
  have hpriorTake : prior ∈ window.take k := by simpa only [hprefix] using hprior
  obtain ⟨ell, hellMin, hget⟩ := List.mem_take_iff_getElem.mp hpriorTake
  have hmin := Nat.lt_min.mp hellMin
  have hget' : window[ell]'hmin.2 = prior := by
    simpa only [List.getElem_take] using hget
  have hell : ell < k := hmin.1
  cases hget'
  exact ⟨ell, hell, selected, hselected, hpayload, hevent, hdraw⟩

private theorem liveFirstWindow_actual_confirmation_provenance
    (records : List (Record (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalHorizon.State p rate)
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (frames : ∀ record ∈ records, ActualFirstLiveRecordFrame record)
    (phase : ∃ registers owned base,
      initial.coordinator = .live registers owned base)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (historyPrefix : List (Record (p := p) (rate := rate)))
    (payloadInitial : ∀ registers owned base,
      initial.coordinator = .live registers owned base → registers.payload = payload)
    (coverage : ∀ i, ∀ registers owned base,
      initial.coordinator = .live registers owned base →
      i ∉ registers.pendingAtChoice → ActualConfirmationIn historyPrefix payload i) :
    (∀ k (hk : k < records.length),
      ∃ selected : Selection (p := p) (rate := rate) records[k].input,
        records[k].output.preparation.coordinator.selection = some selected ∧
        selected.view.payload = payload ∧
        ∀ i, i ∉ selected.view.pendingAtChoice →
          ActualConfirmationIn (historyPrefix ++ records.take k) payload i) ∧
    ∃ registers owned base,
      final.coordinator = .live registers owned base ∧
      ∀ i, i ∉ registers.pendingAtChoice →
        ActualConfirmationIn (historyPrefix ++ records) payload i := by
  induction records generalizing initial final phase historyPrefix payloadInitial coverage with
  | nil =>
      constructor
      · intro k hk
        simp at hk
      · obtain ⟨registers, owned, base, hphase⟩ := phase
        subst final
        refine ⟨registers, owned, base, hphase, ?_⟩
        intro i hi
        simpa only [List.append_nil] using coverage i registers owned base hphase hi
  | cons head tail ih =>
      obtain ⟨hinput, htailChain⟩ := chain
      obtain ⟨registers, owned, base, hphase⟩ := phase
      have hheadPhase : head.input.state.coordinator = .live registers owned base := by
        exact (congrArg (fun s : ReferenceActivePhysicalHorizon.State p rate =>
          s.coordinator) hinput).trans hphase
      obtain ⟨selected, hselected, _framePayload, _hpayload, hphaseFrame,
        _hfirstInstall, next, nextOwned, nextBase, hnext, hnextPayload, hupdate⟩ :=
        frames head List.mem_cons_self
      have hselectedFrame : selected.view.payload = registers.payload ∧
          selected.view.pendingAtChoice = registers.pendingAtChoice := by
        rcases (by simpa only [hheadPhase] using hphaseFrame) with
          ⟨hpay, hpending, _hstarted⟩
        exact ⟨hpay, hpending⟩
      have hselectedPayload : selected.view.payload = payload :=
        hselectedFrame.1.trans (payloadInitial registers owned base hphase)
      have hheadTargets :
          ∃ selected : Selection (p := p) (rate := rate) ((head :: tail)[0]).input,
            (head :: tail)[0].output.preparation.coordinator.selection = some selected ∧
            selected.view.payload = payload ∧
            ∀ i, i ∉ selected.view.pendingAtChoice →
              ActualConfirmationIn (historyPrefix ++ (head :: tail).take 0) payload i := by
        refine ⟨selected, ?_, hselectedPayload, ?_⟩
        · simpa only [List.getElem_cons_zero] using hselected
        · intro i hi
          have hincoming : i ∉ registers.pendingAtChoice := by
            simpa only [hselectedFrame.2] using hi
          simpa only [List.take_zero, List.append_nil] using
            coverage i registers owned base hphase hincoming
      have hcoverageNext : ∀ i, i ∉ next.pendingAtChoice →
          ActualConfirmationIn (historyPrefix ++ [head]) payload i := by
        intro i hi
        by_cases hevent : actualDownConfirmationEvent head selected
        · by_cases hincoming : i ∈ selected.view.pendingAtChoice
          · by_cases heq : i = PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                (head.input.row.2 head.input.time).1
            · exact ⟨head, List.mem_append_right _ (by simp), selected,
                hselected, hselectedPayload, hevent, heq.symm⟩
            · have hmemNext : i ∈ next.pendingAtChoice := by
                rw [hupdate, ite_eq_left hevent]
                exact Finset.mem_erase.mpr ⟨heq, hincoming⟩
              exact (hi hmemNext).elim
          · have hprior := coverage i registers owned base hphase (by
              simpa only [hselectedFrame.2] using hincoming)
            exact actualConfirmationIn_append_left historyPrefix head payload i hprior
        · have hincoming : i ∉ registers.pendingAtChoice := by
            have hnot : i ∉ selected.view.pendingAtChoice := by
              simpa only [hupdate, ite_eq_right hevent] using hi
            simpa only [hselectedFrame.2] using hnot
          exact actualConfirmationIn_append_left historyPrefix head payload i
            (coverage i registers owned base hphase hincoming)
      have htailFrames : ∀ record ∈ tail, ActualFirstLiveRecordFrame record := by
        intro record hrecord
        exact frames record (List.mem_cons_of_mem _ hrecord)
      have htailPayload : ∀ r q b,
          head.output.next.coordinator = .live r q b → r.payload = payload := by
        intro r q b hlive
        have hr : r = next := by
          have hcoord : CoordinatorConfiguration.live next nextOwned nextBase =
              CoordinatorConfiguration.live r q b := hnext.symm.trans hlive
          exact ((CoordinatorConfiguration.live.inj hcoord).1).symm
        subst r
        exact hnextPayload.trans hselectedPayload
      have htailCoverage : ∀ i, ∀ r q b,
          head.output.next.coordinator = .live r q b →
          i ∉ r.pendingAtChoice → ActualConfirmationIn (historyPrefix ++ [head]) payload i := by
        intro i r q b hlive hi
        have hregs : r = next := by
          have hcoord : CoordinatorConfiguration.live next nextOwned nextBase =
              CoordinatorConfiguration.live r q b := hnext.symm.trans hlive
          exact ((CoordinatorConfiguration.live.inj hcoord).1).symm
        subst r
        exact hcoverageNext i hi
      have htailResult := ih head.output.next final htailChain htailFrames
        ⟨next, nextOwned, nextBase, hnext⟩ (historyPrefix ++ [head])
        htailPayload htailCoverage
      rcases htailResult with ⟨htailTargets, hfinal⟩
      constructor
      · intro k hk
        cases k with
        | zero =>
            simpa only [List.getElem_cons_zero, List.take_zero] using hheadTargets
        | succ k =>
            have hk' : k < tail.length := by
              simp only [List.length_cons] at hk
              omega
            obtain ⟨selected', hselected', hpayload', hprior'⟩ := htailTargets k hk'
            refine ⟨selected', ?_, hpayload', ?_⟩
            · simpa only [List.getElem_cons_succ] using hselected'
            · intro i hi
              have hprior := hprior' i hi
              simpa [List.take, List.append_assoc] using hprior
      · rcases hfinal with ⟨finalRegisters, finalOwned, finalBase, hfinalLive, hfinalCoverage⟩
        refine ⟨finalRegisters, finalOwned, finalBase, hfinalLive, ?_⟩
        intro i hi
        simpa [List.append_assoc] using hfinalCoverage i hi

private theorem connected_firstLiveWindow
    (records : List (Record (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalHorizon.State p rate)
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final) :
    ∃ windowFinal,
      ReferenceActivePhysicalHorizon.Connected initial
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records) windowFinal := by
  induction records generalizing initial final with
  | nil => exact ⟨initial, by simp [ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
      ReferenceActivePhysicalHorizon.Connected]⟩
  | cons head tail ih =>
      obtain ⟨hinput, htail⟩ := chain
      cases hcut : ReferenceCollectionPhaseHistory.cutoffChosen head.input with
      | true =>
          refine ⟨initial, ?_⟩
          simp [ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hcut,
            ReferenceActivePhysicalHorizon.Connected]
      | false =>
          obtain ⟨windowFinal, hwindowTail⟩ := ih head.output.next final htail
          refine ⟨windowFinal, ?_⟩
          have hwindow :
              ReferenceFirstLiveConfirmationHistory.firstLiveWindow (head :: tail) =
                head :: ReferenceFirstLiveConfirmationHistory.firstLiveWindow tail := by
            simp [ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hcut]
          rw [hwindow]
          exact ⟨hinput, hwindowTail⟩

/-- Actual coordinator missing-set provenance on the original first-live
window. Every selected follower already outside the pre-choice set has a
strictly earlier positive DOWN confirmation in this same retained prefix, on
the earlier row and coordinator-prepared observation. The first row exposes
the literal first installation, and each row exposes the actual next-register
erase/preserve equation. -/
theorem run_first_live_missing_set_provenance
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards
      start count hspan active
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    W.length = 0 ∨
      ∃ hW : 0 < W.length,
        ∃ firstSelected : Selection (p := p) (rate := rate)
            (W[0]'(by omega)).input,
          ∃ firstInstalled : CoordinatorAssignmentRegisterInstall.FirstInstallation
              (CoordinatorRoundDispatch.firstLaunchInput
                (ReferenceActivePhysicalStep.firstInput (W[0]'(by omega)).input)),
            ∃ firstArm : CoordinatorRoundDispatch.ArmSelection firstInstalled.registers.payload
                firstInstalled.startRoundResult firstInstalled.registers.time
                firstInstalled.registers.complementWeights (W[0]'(by omega)).input.row,
              (W[0]'(by omega)).input.state.coordinator = .first ∧
              CoordinatorRoundDispatch.dispatchFirst
                (ReferenceActivePhysicalStep.firstInput (W[0]'(by omega)).input) =
                  .chosen firstInstalled firstArm ∧
              firstInstalled = CoordinatorAssignmentRegisterInstall.installFirst
                (CoordinatorRoundDispatch.firstLaunchInput
                  (ReferenceActivePhysicalStep.firstInput (W[0]'(by omega)).input)) ∧
              firstInstalled.registers.pendingAtChoice = Finset.univ ∧
              firstInstalled.startRoundResult.pending = Finset.univ ∧
              (W[0]'(by omega)).output.preparation.coordinator.selection = some firstSelected ∧
              firstSelected.view.payload = firstInstalled.registers.payload ∧
              firstSelected.view.pendingAtChoice = Finset.univ ∧
              firstSelected.started.pending = Finset.univ ∧
              ∀ k : Fin W.length,
                ∃ record : Record (p := p) (rate := rate),
                  record = W[k.val] ∧
                  ∃ selected : Selection (p := p) (rate := rate) record.input,
                  record.output.preparation.coordinator.selection = some selected ∧
                  selected.view.payload = firstInstalled.registers.payload ∧
                  (match record.input.state.coordinator with
                    | .first => selected.view.pendingAtChoice = Finset.univ ∧
                        selected.started.pending = Finset.univ
                    | .live incoming _ _ =>
                        selected.view.payload = incoming.payload ∧
                          selected.view.pendingAtChoice = incoming.pendingAtChoice ∧
                          selected.started.pending = incoming.pendingAtChoice
                    | _ => False) ∧
                  ∃ next : Registers,
                    ∃ nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters next,
                      ∃ nextBase : Fin (p.m - 1) → ℕ,
                        record.output.next.coordinator = .live next nextOwned nextBase ∧
                        next.payload = selected.view.payload ∧
                        (next.pendingAtChoice =
                          if actualDownConfirmationEvent record selected then
                            selected.view.pendingAtChoice.erase
                              (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                                (record.input.row.2 record.input.time).1)
                          else selected.view.pendingAtChoice) ∧
                        ∀ i, i ∉ selected.view.pendingAtChoice →
                          ∃ ell, ∃ hell : ell < k.val,
                            ∃ priorRecord : Record (p := p) (rate := rate),
                              priorRecord = W[ell]'(by omega) ∧
                              ∃ priorSelected : Selection (p := p) (rate := rate)
                                  priorRecord.input,
                              priorRecord.output.preparation.coordinator.selection = some priorSelected ∧
                              priorSelected.view.payload = selected.view.payload ∧
                              actualDownConfirmationEvent priorRecord priorSelected ∧
                              PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                                (priorRecord.input.row.2 priorRecord.input.time).1 = i := by
  intro E W
  by_cases hzero : W.length = 0
  · exact Or.inl hzero
  · right
    have hnonempty : 0 < W.length := by omega
    have hroot := ReferenceFirstLiveCoordinatorSafety.run_first_live_coordinator_safety
      initial rows J rewards start count hspan active hfirst
    have hsafe : ∀ k : Fin W.length,
        let record := W[k.val]
        record.output.coordinator.failure = none ∧
          ∃ recording, record.output.coordinator.recording = some recording ∧
            ∃ next nextOwned nextBase,
              record.output.next.coordinator = .live next nextOwned nextBase := by
      dsimp only [E, W]
      exact hroot.1
    have hrunChain :
        ReferenceActivePhysicalHorizon.Connected initial E.records E.finalState := by
      simpa only [E] using ReferenceActivePhysicalHorizon.run_connected
        initial rows J rewards start count hspan active
    obtain ⟨windowFinal, hwindowChain⟩ :=
      connected_firstLiveWindow E.records initial E.finalState hrunChain
    have hsafeRows : ∀ record ∈ W,
        ∃ next nextOwned nextBase,
          record.output.next.coordinator = .live next nextOwned nextBase := by
      intro record hmem
      obtain ⟨n, hn, hget⟩ := List.mem_iff_getElem.mp hmem
      have hs := hsafe ⟨n, hn⟩
      dsimp only at hs
      rw [hget] at hs
      have hs' : record.output.coordinator.failure = none ∧
          ∃ recording, record.output.coordinator.recording = some recording ∧
            ∃ next nextOwned nextBase,
              record.output.next.coordinator = .live next nextOwned nextBase := by
        exact hs
      rcases hs' with ⟨_, recording, _, next, nextOwned, nextBase, hnext⟩
      exact ⟨next, nextOwned, nextBase, hnext⟩
    have hnoCutRows : ∀ record ∈ W,
        ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
      intro record hmem
      have hwindowMem : record ∈
          ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records := by
        simpa only [W] using hmem
      have hpredicate := List.mem_takeWhile_imp hwindowMem
      simpa only [ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
        Bool.not_eq_true'] using hpredicate
    have hframes := actualFirstLiveRecordFrames W initial windowFinal hwindowChain
      (Or.inl hfirst) hsafeRows hnoCutRows
    let head : Record (p := p) (rate := rate) := W[0]'hnonempty
    let tail : List (Record (p := p) (rate := rate)) := W.drop 1
    have hwindowSplit : W = head :: tail := by
      have hdrop := List.cons_getElem_drop_succ (l := W) (n := 0) (h := hnonempty)
      simpa only [head, tail, Nat.zero_add, List.drop_zero] using hdrop.symm
    have hchainW :
        ReferenceActivePhysicalHorizon.Connected initial W windowFinal := by
      change ReferenceActivePhysicalHorizon.Connected initial
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records) windowFinal
      exact hwindowChain
    have hheadChain :
        ReferenceActivePhysicalHorizon.Connected initial (head :: tail) windowFinal := by
      rw [← hwindowSplit]
      exact hchainW
    rcases hheadChain with ⟨hheadInput, htailChain⟩
    have hheadMem : head ∈ W := by
      dsimp only [head]
      exact List.getElem_mem hnonempty
    have hheadFirst : head.input.state.coordinator = .first := by
      exact (congrArg (fun s : ReferenceActivePhysicalHorizon.State p rate =>
        s.coordinator) hheadInput).trans hfirst
    obtain ⟨firstSelected, hfirstSelected, firstPayload, hfirstPayload,
      hfirstPhase, hfirstInstallData, firstNext, firstNextOwned, firstNextBase,
      hfirstNext, hfirstNextPayload, hfirstUpdate⟩ :=
      hframes head hheadMem
    have hfirstPending :
        firstSelected.view.pendingAtChoice = Finset.univ ∧
          firstSelected.started.pending = Finset.univ := by
      simpa only [hheadFirst] using hfirstPhase
    have hfirstInstall' := hfirstInstallData
    simp only [hheadFirst] at hfirstInstall'
    rcases hfirstInstall' with
      ⟨firstInstalled, firstArm, hdispatchFirst, hinstalled, hregPending,
        hstartPending, hinstalledPayload⟩
    have hfirstSelectionPayload :
        firstSelected.view.payload = firstInstalled.registers.payload :=
      hfirstPayload.trans hinstalledPayload.symm
    have hframesTail : ∀ record ∈ tail, ActualFirstLiveRecordFrame record := by
      intro record hmem
      have hmemW : record ∈ W := by
        rw [hwindowSplit]
        exact List.mem_cons_of_mem head hmem
      exact hframes record hmemW
    have htailPayload : ∀ registers owned base,
        head.output.next.coordinator = .live registers owned base →
          registers.payload = firstInstalled.registers.payload := by
      intro registers owned base hlive
      have hregs : registers = firstNext := by
        have hcoord : CoordinatorConfiguration.live firstNext firstNextOwned firstNextBase =
            CoordinatorConfiguration.live registers owned base :=
          hfirstNext.symm.trans hlive
        exact ((CoordinatorConfiguration.live.inj hcoord).1).symm
      subst registers
      exact hfirstNextPayload.trans hfirstSelectionPayload
    have hfirstCoverage : ∀ i, i ∉ firstNext.pendingAtChoice →
        ActualConfirmationIn [head] firstInstalled.registers.payload i := by
      intro i hi
      by_cases hevent : actualDownConfirmationEvent head firstSelected
      · by_cases hincoming : i ∈ firstSelected.view.pendingAtChoice
        · by_cases heq : i = PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (head.input.row.2 head.input.time).1
          · exact ⟨head, by simp, firstSelected, hfirstSelected,
              hfirstSelectionPayload, hevent, heq.symm⟩
          · have hmemNext : i ∈ firstNext.pendingAtChoice := by
              rw [hfirstUpdate, ite_eq_left hevent]
              exact Finset.mem_erase.mpr ⟨heq, hincoming⟩
            exact (hi hmemNext).elim
        · have hin : i ∈ firstSelected.view.pendingAtChoice := by
            simpa only [hfirstPending.1] using Finset.mem_univ i
          exact (hincoming hin).elim
      · have hmemNext : i ∈ firstNext.pendingAtChoice := by
          rw [hfirstUpdate, ite_eq_right hevent]
          simpa only [hfirstPending.1] using Finset.mem_univ i
        exact (hi hmemNext).elim
    have htailCoverage : ∀ i, ∀ registers owned base,
        head.output.next.coordinator = .live registers owned base →
        i ∉ registers.pendingAtChoice →
          ActualConfirmationIn [head] firstInstalled.registers.payload i := by
      intro i registers owned base hlive hi
      have hregs : registers = firstNext := by
        have hcoord : CoordinatorConfiguration.live firstNext firstNextOwned firstNextBase =
            CoordinatorConfiguration.live registers owned base :=
          hfirstNext.symm.trans hlive
        exact ((CoordinatorConfiguration.live.inj hcoord).1).symm
      subst registers
      exact hfirstCoverage i hi
    have htailResult := liveFirstWindow_actual_confirmation_provenance tail
      head.output.next windowFinal htailChain hframesTail
      ⟨firstNext, firstNextOwned, firstNextBase, hfirstNext⟩
      firstInstalled.registers.payload [head] htailPayload htailCoverage
    rcases htailResult with ⟨htailTargets, _hfinalCoverage⟩
    refine ⟨hnonempty, firstSelected, firstInstalled, firstArm,
      hheadFirst, hdispatchFirst, hinstalled, hregPending, hstartPending,
      hfirstSelected, hfirstSelectionPayload, hfirstPending.1, hfirstPending.2, ?_⟩
    intro k
    rcases k with ⟨index, hindex⟩
    cases index with
    | zero =>
        have hrowFrame := hframes head hheadMem
        rcases hrowFrame with
          ⟨selected, hselected, payload, hpayload, hphaseFrame, hinstallFrame,
            next, nextOwned, nextBase, hnext, hnextPayload, hupdate⟩
        have hselectedEq : selected = firstSelected :=
          Option.some.inj (hselected.symm.trans hfirstSelected)
        subst selected
        refine ⟨head, rfl, firstSelected, hfirstSelected, hfirstSelectionPayload,
          hfirstPhase,
          firstNext, firstNextOwned, firstNextBase,
          hfirstNext, hfirstNextPayload, hfirstUpdate, ?_⟩
        intro i hi
        exact (hi (by simpa only [hfirstPending.1] using Finset.mem_univ i)).elim
    | succ index =>
        have hindexTail : index < tail.length := by
          rw [hwindowSplit, List.length_cons] at hindex
          omega
        have hsucc : index + 1 < W.length := by omega
        obtain ⟨selected, hselected, hselectedPayload, hprior⟩ :=
          htailTargets index hindexTail
        let record := tail[index]
        have hrecordMem : record ∈ W := by
          rw [hwindowSplit]
          simp only [record]
          exact List.mem_cons_of_mem _ (List.getElem_mem hindexTail)
        have hrowEq : W[index + 1]'hsucc = record := by
          rw [List.getElem_of_eq hwindowSplit hsucc]
          simp only [List.getElem_cons_succ, record]
        obtain ⟨selectedFrame, hselectedFrame, framePayload, hpayloadFrame,
          hphaseFrame, _hinstallFrame, next, nextOwned, nextBase,
          hnext, hnextPayload, hupdate⟩ := hframes record hrecordMem
        have hselectedEq : selectedFrame = selected :=
          Option.some.inj (hselectedFrame.symm.trans hselected)
        subst selectedFrame
        have hprefixEq : [head] ++ tail.take index =
            (head :: tail).take (index + 1) := by
          simp [List.take]
        refine ⟨record, hrowEq.symm, selected, hselected, hselectedPayload, hphaseFrame,
          next, nextOwned, nextBase, hnext, hnextPayload, hupdate, ?_⟩
        intro i hi
        obtain ⟨ell, hell, priorSelected, hpriorSelected, hpriorPayload,
          hevent, hdraw⟩ := actualConfirmationIn_take_index
            (head :: tail) ([head] ++ tail.take index) (index + 1)
            (by simp only [List.length_cons]; omega)
            firstInstalled.registers.payload i hprefixEq (hprior i hi)
        have hellWindow : ell < W.length := by omega
        have hellCons : ell < (head :: tail).length := by
          simpa only [hwindowSplit] using hellWindow
        have hpriorRowEq : (head :: tail)[ell]'hellCons = W[ell]'hellWindow := by
          exact (List.getElem_of_eq hwindowSplit hellWindow).symm
        refine ⟨ell, hell, (head :: tail)[ell]'hellCons, hpriorRowEq, priorSelected,
          hpriorSelected, ?_, hevent, ?_⟩
        · exact hpriorPayload.trans hselectedPayload.symm
        · exact hdraw


end Bandits.Support.ReferenceFirstLiveMissingSetProvenance

end
