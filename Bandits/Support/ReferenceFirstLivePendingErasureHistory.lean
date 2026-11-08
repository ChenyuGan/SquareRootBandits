/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveConfirmationHistory

import Mathlib.Data.List.TakeWhile
import Lean.Elab.Tactic.Omega

/-!
# Actual first-live pending-erasure history

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-88`,
`sources/zip4/manuscript/06_interruptions.tex:246-295`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:100-106`.

This file follows the literal first-live prefix of the original physical run.
It recovers an actual successful DOWN confirmation when a currently selected
follower is absent from the pending set, then composes that event with the
accepted DOWN history for the current payload record. Failed records remain in
the prefix. The result is an internal history lemma for the retained-assignment
case of AppA:102; it asserts no general assignment lineage or manuscript
closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep

namespace Bandits.Support.ReferenceFirstLivePendingErasureHistory

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {p : Parameters} {rate : RateInput p}

/-- The exact actual horizon record used by this history producer. -/
abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
/-- The checked same-round selected coordinator view from an actual input. -/
abbrev Selection (x : RoundInput p rate) :=
  ReferenceActivePhysicalStep.Selection (p := p) (rate := rate) x

private theorem selectionAt_fields (x : RoundInput p rate) (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (arm : CoordinatorRoundDispatch.ArmSelection payload started time weights x.row)
    (selected : Selection x)
    (h : ReferenceActivePhysicalStep.selectionAt x payload started time weights arm =
      some selected) :
    selected.view.payload = payload ∧ selected.view.pendingAtChoice = started.pending ∧
      selected.view.cutoff = CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u := by
  unfold ReferenceActivePhysicalStep.selectionAt at h
  split at h
  · cases h
    exact ⟨rfl, rfl, rfl⟩
  · cases h

private theorem dispatchLive_continuing_pending
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

private def HasActualErasure
    (records : List (Record (p := p) (rate := rate)))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1)) : Prop :=
  ∃ record, record ∈ records ∧ ∃ selected : Selection record.input,
    (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = some selected ∧
    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (record.input.row.2 record.input.time).1 = i ∧
    CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
      selected.view.pendingAtChoice selected.view.cutoff record.input.time
      (record.input.row.2 record.input.time)
      (ReferenceActivePhysicalStep.prepare record.input).coordinatorObservation ∧
    selected.view.payload = payload ∧
    ∃ next owned base,
      record.output.next.coordinator = .live next owned base ∧
      next.pendingAtChoice = selected.view.pendingAtChoice.erase i ∧
      next.payload = payload

private def HasMissingHistory
    (records : List (Record (p := p) (rate := rate)))
    (state : ReferenceActivePhysicalStep.State p rate) : Prop :=
  match state.coordinator with
  | .live registers _ _ =>
      ∀ i, i ∉ registers.pendingAtChoice → HasActualErasure records registers.payload i
  | _ => True

private theorem livePostChoice_live_success
    (x : RoundInput p rate) (prepared : PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters next)
    (h : (livePostChoice prepared r q base started).configuration = .live next owned base) :
    ∃ recording serviced pending finished,
      CoordinatorRecorderComplementBridge.run (liveRecordingInput prepared r started) =
        some recording ∧
      CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced ∧
      CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
        x.time x.row prepared.coordinatorObservation = some pending ∧
      CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock pending x.row =
        .ok finished ∧
      next.payload = r.payload ∧ next.pendingAtChoice = finished.pending := by
  unfold livePostChoice at h
  split at h
  · cases h
  · rename_i recording hrecord
    split at h
    · cases h
    · rename_i serviced hservice
      split at h
      · cases h
      · rename_i pending hpending
        split at h
        · cases h
        · rename_i finished hfinish
          cases h
          exact ⟨recording, serviced, pending, finished,
            hrecord, hservice, hpending, hfinish, rfl, rfl⟩

private theorem confirmation_erases_absent
    (x : RoundInput p rate) (started : CoordinatorPhaseClock.StartRoundResult p)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (observation : Fin (D p + 1))
    (pendingAfter : Finset (Fin (p.m - 1))) (finished : CoordinatorPhaseClock.FinishRoundResult p)
    (hupdate : CoordinatorLocalArmChoice.confirmationUpdate payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time x.row observation = some pendingAfter)
    (hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
      pendingAfter x.row = .ok finished)
    (i : Fin (p.m - 1)) (hmem : i ∈ started.pending)
    (habsent : i ∉ finished.pending) :
    CoordinatorLocalArmChoice.downConfirmationEvent payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time (x.row.2 x.time) observation ∧
    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (x.row.2 x.time).1 = i ∧
    pendingAfter = started.pending.erase
      (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 x.time).1) := by
  have hcore : CoordinatorLocalArmChoice.confirmationUpdateCore payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time (x.row.2 x.time) observation = some pendingAfter := hupdate
  have hvalid : CoordinatorLocalArmChoice.ConfirmationInputsValid payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time := by
    by_contra hnot
    simp [CoordinatorLocalArmChoice.confirmationUpdateCore, hnot] at hcore
  have hfinishPending := CoordinatorPhaseClock.finishRound_pending_frame p rate.eta.val
    x.time started.clock pendingAfter x.row finished hfinish
  have hnotAfter : i ∉ pendingAfter := by
    simpa only [hfinishPending] using habsent
  by_cases hevent : CoordinatorLocalArmChoice.downConfirmationEvent payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time (x.row.2 x.time) observation
  · have hremove := CoordinatorLocalArmChoice.confirmationUpdateCore_removes payload
      started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time (x.row.2 x.time) observation hvalid hevent
    have hout : pendingAfter = started.pending.erase
        (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 x.time).1) := by
      exact Option.some.inj (hcore.symm.trans hremove)
    have hdraw := Finset.eq_of_mem_of_notMem_erase hmem (by simpa only [hout] using hnotAfter)
    exact ⟨hevent, hdraw.symm, hout⟩
  · have hpreserve := CoordinatorLocalArmChoice.confirmationUpdateCore_preserves payload
      started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time (x.row.2 x.time) observation hvalid hevent
    have hout : pendingAfter = started.pending :=
      Option.some.inj (hcore.symm.trans hpreserve)
    have : i ∈ pendingAfter := by simpa only [hout] using hmem
    exact (hnotAfter this).elim

private theorem append_live_tail_history
    (x : RoundInput p rate) (records : List (Record (p := p) (rate := rate)))
    (selected : Selection x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p)
    (hselected : (prepare x).coordinator.selection = some selected)
    (hviewPayload : selected.view.payload = r.payload)
    (hviewPending : selected.view.pendingAtChoice = started.pending)
    (hviewCutoff : selected.view.cutoff =
      CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
    (hprior : ∀ i, i ∉ started.pending → HasActualErasure records r.payload i)
    (hcoord : (step x).next.coordinator =
      (livePostChoice (prepare x) r q base started).configuration) :
    HasMissingHistory (records ++ [⟨x, step x, rfl⟩]) (step x).next := by
  cases hnextcoord : (step x).next.coordinator with
  | live next owned' base' =>
      have htail : (livePostChoice (prepare x) r q base started).configuration =
          .live next owned' base' := hcoord.symm.trans hnextcoord
      rcases ReferenceFirstLiveConfirmationHistory.livePostChoice_frame x (prepare x)
          r q base started with hdagger | ⟨next0, owned0, hpost, _, _⟩
      · rw [hdagger] at htail
        cases htail
      · have hsame : CoordinatorConfiguration.live next0 owned0 base =
              CoordinatorConfiguration.live next owned' base' :=
          hpost.symm.trans htail
        have hbaseEq : base' = base := by
          have hproject := congrArg
            (fun c : CoordinatorConfiguration p rate =>
              match c with
              | .live _ _ scores => scores
              | _ => base') hsame
          simpa using hproject.symm
        subst base'
        obtain ⟨_, _, pendingAfter, finished,
          _, _, hupdate, hfinish, hnextPayload, hnextPending⟩ :=
          livePostChoice_live_success x (prepare x) r q base started next owned' htail
        simp only [HasMissingHistory, hnextcoord]
        intro i hi
        have hnotFinished : i ∉ finished.pending := by
          intro hmem
          apply hi
          rw [← hnextPending] at hmem
          exact hmem
        by_cases hmem : i ∈ started.pending
        · obtain ⟨hevent, hdraw, hout⟩ := confirmation_erases_absent x started r.payload
            (prepare x).coordinatorObservation pendingAfter finished hupdate hfinish i hmem
            hnotFinished
          have hviewPayloadNext : selected.view.payload = next.payload :=
            hviewPayload.trans hnextPayload.symm
          have hevent' : CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
              selected.view.pendingAtChoice selected.view.cutoff x.time (x.row.2 x.time)
              (prepare x).coordinatorObservation := by
            simpa only [hviewPayload, hviewPending, hviewCutoff] using hevent
          refine ⟨⟨x, step x, rfl⟩,
            List.mem_append_right records (by simp), selected, hselected, hdraw, hevent',
            hviewPayloadNext, next, owned', base, ?_, ?_, ?_⟩
          · change (step x).next.coordinator = .live next owned' base
            exact hnextcoord
          · have hfinishedPending : finished.pending = pendingAfter :=
              CoordinatorPhaseClock.finishRound_pending_frame p rate.eta.val x.time
                started.clock pendingAfter x.row finished hfinish
            have hselectedErase : started.pending.erase
                (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                  (x.row.2 x.time).1) = selected.view.pendingAtChoice.erase i := by
              simp only [← hviewPending, hdraw]
              rfl
            exact hnextPending.trans (hfinishedPending.trans (hout.trans hselectedErase))
          · rfl
        · have hold := hprior i hmem
          rw [hnextPayload]
          rcases hold with ⟨oldRecord, holdRecord, oldSelected, holdSelected, holdDraw,
            holdEvent, holdEventPayload, oldNext, oldOwned, oldBase, holdLive, holdPending,
            holdPayload⟩
          exact ⟨oldRecord, List.mem_append_left _ holdRecord, oldSelected, holdSelected,
            holdDraw, holdEvent, holdEventPayload, oldNext, oldOwned, oldBase, holdLive,
            holdPending, holdPayload⟩
  | _ =>
      simp [HasMissingHistory, hnextcoord]

private theorem no_live_next_of_dagger (x : RoundInput p rate)
    (records : List (Record (p := p) (rate := rate)))
    (hdagger : (step x).next.coordinator = .dagger) :
    HasMissingHistory (records ++ [⟨x, step x, rfl⟩]) (step x).next := by
  simp [HasMissingHistory, hdagger]

private theorem selected_view_first_or_live
    (x : RoundInput p rate) (hs : ReferenceFirstLiveConfirmationHistory.FirstLiveState x.state)
    (hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen x = false)
    (selected : Selection x)
    (hselected : (prepare x).coordinator.selection = some selected) :
    (∃ r q base, x.state.coordinator = .live r q base ∧
      selected.view.payload = r.payload ∧
      selected.view.pendingAtChoice = r.pendingAtChoice) ∨
    (x.state.coordinator = .first ∧ selected.view.pendingAtChoice = Finset.univ) := by
  cases hstate : x.state.coordinator with
  | first =>
      have hdispatch : dispatch x = .first (CoordinatorRoundDispatch.dispatchFirst (firstInput x)) :=
        dispatch_first x hstate
      have hselection : (DispatchCut.first
          (CoordinatorRoundDispatch.dispatchFirst (firstInput x))).selection = some selected := by
        simpa only [prepare, hdispatch] using hselected
      cases houtcome : CoordinatorRoundDispatch.dispatchFirst (firstInput x) with
      | choiceDomainFailure installed =>
          simp only [DispatchCut.selection, houtcome] at hselection
          cases hselection
      | recorderBoundaryFailure installed =>
          simp only [DispatchCut.selection, houtcome] at hselection
          cases hselection
      | choiceRejected installed =>
          simp only [DispatchCut.selection, houtcome] at hselection
          cases hselection
      | chosen installed arm =>
          have hselectionAt : selectionAt x installed.registers.payload
              installed.startRoundResult installed.registers.time
              installed.registers.complementWeights arm = some selected := by
            simpa only [DispatchCut.selection, houtcome] using hselection
          have hfields := selectionAt_fields x installed.registers.payload
            installed.startRoundResult installed.registers.time
            installed.registers.complementWeights arm selected hselectionAt
          have hinstalled := dispatchFirst_chosen_installation x installed arm houtcome
          have huniv : installed.startRoundResult.pending = Finset.univ := by
            rw [hinstalled]
            rfl
          exact Or.inr ⟨rfl, hfields.2.1.trans huniv⟩
  | live r q base =>
      have hdispatch : dispatch x = .live r q base
          (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
        simp only [dispatch, hstate, CoordinatorRoundDispatch.dispatch]
        rfl
      have hselection : (DispatchCut.live r q base
          (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base))).selection = some selected := by
        simpa only [prepare, hdispatch] using hselected
      cases houtcome : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base) with
      | clockFailure failure hfailure =>
          simp only [DispatchCut.selection, houtcome] at hselection
          cases hselection
      | initializerFailure dispatched hstart checked hchecked =>
          simp only [DispatchCut.selection, houtcome] at hselection
          cases hselection
      | localFailure dispatched hstart reason =>
          simp only [DispatchCut.selection, houtcome] at hselection
          cases hselection
      | cutoffChosen dispatched hstart ledger hinitialized hledger hdomain hclock
          hpending hnoAssignment arm =>
          simp [ReferenceCollectionPhaseHistory.cutoffChosen, prepare, hdispatch, houtcome]
            at hcutoff
      | continuingChosen dispatched hstart continuation arm =>
          have hselectionAt : selectionAt x r.payload dispatched.startResult x.time
              (liveRegistersAt r x.time).complementWeights arm = some selected := by
            simpa only [DispatchCut.selection, houtcome] using hselection
          have hfields := selectionAt_fields x r.payload dispatched.startResult x.time
            (liveRegistersAt r x.time).complementWeights arm selected hselectionAt
          have hpending := dispatchLive_continuing_pending (liveInput x r q base)
            dispatched hstart continuation arm houtcome
          have hpending' : dispatched.startResult.pending = r.pendingAtChoice := by
            simpa [liveInput, liveRegistersAt] using hpending
          exact Or.inl ⟨r, q, base, rfl, hfields.1, hfields.2.1.trans hpending'⟩
  | collection payload ledger proposal =>
      simp only [ReferenceFirstLiveConfirmationHistory.FirstLiveState, hstate] at hs
  | dagger =>
      have hdispatch : dispatch x = .dagger := dispatch_dagger x hstate
      simp [prepare, hdispatch, DispatchCut.selection] at hselected

private theorem append_missing_history_step
    (x : RoundInput p rate) (records : List (Record (p := p) (rate := rate)))
    (hs : ReferenceFirstLiveConfirmationHistory.FirstLiveState x.state)
    (hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen x = false)
    (hprior : HasMissingHistory records x.state) :
    HasMissingHistory (records ++ [⟨x, step x, rfl⟩]) (step x).next := by
  cases hstate : x.state.coordinator with
  | dagger =>
      have hdagger : (step x).next.coordinator = .dagger :=
        (step_coordinator_dagger x hstate).1
      exact no_live_next_of_dagger x records hdagger
  | collection payload ledger proposal =>
      simp only [ReferenceFirstLiveConfirmationHistory.FirstLiveState, hstate] at hs
  | first =>
      have hdispatch : dispatch x = .first (CoordinatorRoundDispatch.dispatchFirst (firstInput x)) :=
        dispatch_first x hstate
      have hprepared : (prepare x).coordinator =
          .first (CoordinatorRoundDispatch.dispatchFirst (firstInput x)) := by
        change dispatch x = _
        exact hdispatch
      have he := observeCoordinator_first_equation (prepare x)
        (CoordinatorRoundDispatch.dispatchFirst (firstInput x)) hprepared
      cases houtcome : CoordinatorRoundDispatch.dispatchFirst (firstInput x) with
      | choiceDomainFailure installed =>
          apply no_live_next_of_dagger x records
          rw [(step_next_fields x).1]
          rw [he, houtcome]
          simp [DispatchCut.selection, coordinatorFailure]
      | recorderBoundaryFailure installed =>
          apply no_live_next_of_dagger x records
          rw [(step_next_fields x).1]
          rw [he, houtcome]
          simp [DispatchCut.selection, coordinatorFailure]
      | choiceRejected installed =>
          apply no_live_next_of_dagger x records
          rw [(step_next_fields x).1]
          rw [he, houtcome]
          simp [DispatchCut.selection, coordinatorFailure]
      | chosen installed arm =>
          cases hselection :
              (DispatchCut.first (.chosen installed arm)).selection with
          | none =>
              apply no_live_next_of_dagger x records
              rw [(step_next_fields x).1]
              rw [he, houtcome]
              have hselNone : selectionAt x installed.registers.payload
                  installed.startRoundResult installed.registers.time
                  installed.registers.complementWeights arm = none := by
                simpa only [DispatchCut.selection] using hselection
              simp [DispatchCut.selection, hselNone, coordinatorFailure]
          | some selected =>
              have hselected : (prepare x).coordinator.selection = some selected := by
                change (dispatch x).selection = some selected
                rw [hdispatch, houtcome]
                exact hselection
              have hselectionAt : selectionAt x installed.registers.payload
                  installed.startRoundResult installed.registers.time
                  installed.registers.complementWeights arm = some selected := by
                simpa only [DispatchCut.selection] using hselection
              have hfields := selectionAt_fields x installed.registers.payload
                installed.startRoundResult installed.registers.time
                installed.registers.complementWeights arm selected hselectionAt
              have hinstalled := dispatchFirst_chosen_installation x installed arm houtcome
              have huniv : installed.startRoundResult.pending = Finset.univ := by
                rw [hinstalled]
                rfl
              have hpriorPending : ∀ i, i ∉ installed.startRoundResult.pending →
                  HasActualErasure records installed.registers.payload i := by
                intro i hi
                rw [huniv] at hi
                exact (hi (Finset.mem_univ i)).elim
              have hcoord : (step x).next.coordinator =
                  (livePostChoice (prepare x) installed.registers installed.ownedRegisters
                    installed.followerBaseScore installed.startRoundResult).configuration := by
                rw [(step_next_fields x).1]
                rw [he, houtcome, hselection]
                rfl
              exact append_live_tail_history x records selected installed.registers
                installed.ownedRegisters installed.followerBaseScore installed.startRoundResult
                hselected hfields.1 hfields.2.1 hfields.2.2 hpriorPending hcoord
  | live r q base =>
      have hdispatch : dispatch x = .live r q base
          (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
        simp only [dispatch, hstate, CoordinatorRoundDispatch.dispatch]
        rfl
      have hprepared : (prepare x).coordinator = .live r q base
          (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
        change dispatch x = _
        exact hdispatch
      have he := observeCoordinator_live_equation (prepare x) r q base
        (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) hprepared
      have hpriorLive : ∀ i, i ∉ r.pendingAtChoice → HasActualErasure records r.payload i := by
        simpa only [HasMissingHistory, hstate] using hprior
      cases houtcome : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base) with
      | clockFailure failure hfailure =>
          apply no_live_next_of_dagger x records
          rw [(step_next_fields x).1]
          rw [he, houtcome]
          simp [DispatchCut.selection, coordinatorFailure]
      | initializerFailure dispatched hstart checked hchecked =>
          apply no_live_next_of_dagger x records
          rw [(step_next_fields x).1]
          rw [he, houtcome]
          simp [DispatchCut.selection, coordinatorFailure]
      | localFailure dispatched hstart reason =>
          apply no_live_next_of_dagger x records
          rw [(step_next_fields x).1]
          rw [he, houtcome]
          simp [DispatchCut.selection, coordinatorFailure]
      | cutoffChosen dispatched hstart ledger hinitialized hledger hdomain hclock
          hpending hnoAssignment arm =>
          have hfalse := hcutoff
          simp [ReferenceCollectionPhaseHistory.cutoffChosen, prepare, hdispatch, houtcome]
            at hfalse
      | continuingChosen dispatched hstart continuation arm =>
          cases hselection :
              (DispatchCut.live r q base
                (.continuingChosen dispatched hstart continuation arm)).selection with
          | none =>
              apply no_live_next_of_dagger x records
              rw [(step_next_fields x).1]
              rw [he, houtcome, hselection]
              simp [coordinatorFailure]
          | some selected =>
              have hselected : (prepare x).coordinator.selection = some selected := by
                change (dispatch x).selection = some selected
                rw [hdispatch, houtcome]
                exact hselection
              have hselectionAt : selectionAt x r.payload dispatched.startResult x.time
                  (liveRegistersAt r x.time).complementWeights arm = some selected := by
                simpa only [DispatchCut.selection] using hselection
              have hfields := selectionAt_fields x r.payload dispatched.startResult x.time
                (liveRegistersAt r x.time).complementWeights arm selected hselectionAt
              have hstartPending := dispatchLive_continuing_pending (liveInput x r q base)
                dispatched hstart continuation arm houtcome
              have hstartPending' : dispatched.startResult.pending = r.pendingAtChoice := by
                simpa [liveInput, liveRegistersAt] using hstartPending
              have hpriorPending : ∀ i, i ∉ dispatched.startResult.pending →
                  HasActualErasure records r.payload i := by
                intro i hi
                apply hpriorLive i
                rw [hstartPending'] at hi
                exact hi
              have hcoord : (step x).next.coordinator =
                  (livePostChoice (prepare x) (liveRegistersAt r x.time)
                    (liveOwnedAt r q x.time) base dispatched.startResult).configuration := by
                rw [(step_next_fields x).1]
                rw [he, houtcome, hselection]
                rfl
              exact append_live_tail_history x records selected (liveRegistersAt r x.time)
                (liveOwnedAt r q x.time) base dispatched.startResult hselected hfields.1
                hfields.2.1 hfields.2.2 hpriorPending hcoord

private theorem connected_missing_history_final
    {initial final : ReferenceActivePhysicalStep.State p rate}
    (records : List (Record (p := p) (rate := rate)))
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hs : ReferenceFirstLiveConfirmationHistory.FirstLiveState initial)
    (hno : ∀ record ∈ records,
      ReferenceCollectionPhaseHistory.cutoffChosen record.input = false)
    (historyPrefix : List (Record (p := p) (rate := rate)))
    (hprefix : HasMissingHistory historyPrefix initial) :
    HasMissingHistory (historyPrefix ++ records) final := by
  induction records generalizing initial final historyPrefix with
  | nil =>
      change final = initial at chain
      subst final
      simpa only [List.append_nil] using hprefix
  | cons record rest ih =>
      obtain ⟨hpre, hrest⟩ := chain
      have hinputState : ReferenceFirstLiveConfirmationHistory.FirstLiveState record.input.state :=
        hpre ▸ hs
      have hprefixInput : HasMissingHistory historyPrefix record.input.state := by
        rw [hpre]
        exact hprefix
      have hcutoff := hno record List.mem_cons_self
      have hheadStep := append_missing_history_step record.input historyPrefix hinputState
        hcutoff hprefixInput
      have hrecordEq : record = ⟨record.input, step record.input, rfl⟩ := by
        cases record with
        | mk input output output_eq =>
            cases output_eq
            rfl
      have hhead : HasMissingHistory (historyPrefix ++ [record]) record.output.next := by
        rw [hrecordEq]
        exact hheadStep
      have hnext : ReferenceFirstLiveConfirmationHistory.FirstLiveState record.output.next := by
        rw [record.output_eq]
        exact ReferenceFirstLiveConfirmationHistory.firstLive_step record.input
          (hpre ▸ hs) hcutoff
      have hnoTail : ∀ r ∈ rest,
          ReferenceCollectionPhaseHistory.cutoffChosen r.input = false := by
        intro r hr
        exact hno r (List.mem_cons_of_mem record hr)
      have htail := ih hrest hnext hnoTail (historyPrefix ++ [record]) hhead
      simpa [List.append_assoc] using htail

private theorem window_no_cutoff
    (records : List (Record (p := p) (rate := rate)))
    (record : Record (p := p) (rate := rate))
    (hrecord : record ∈ ReferenceFirstLiveConfirmationHistory.firstLiveWindow records) :
    ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
  have h := List.mem_takeWhile_imp hrecord
  simpa only [Bool.not_eq_true'] using h

private theorem actual_erasure_mem_take
    (W : List (Record (p := p) (rate := rate))) (a : ℕ)
    (ha : a ≤ W.length) (payload : Payload rate) (i : Fin (p.m - 1))
    (eventRecord : Record (p := p) (rate := rate))
    (heventMem : eventRecord ∈ W.take a)
    (w : Selection eventRecord.input)
    (hselected : (prepare eventRecord.input).coordinator.selection = some w)
    (hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (eventRecord.input.row.2 eventRecord.input.time).1 = i)
    (hevent : CoordinatorLocalArmChoice.downConfirmationEvent w.view.payload
      w.view.pendingAtChoice w.view.cutoff eventRecord.input.time
      (eventRecord.input.row.2 eventRecord.input.time)
      (prepare eventRecord.input).coordinatorObservation)
    (hpayload : w.view.payload = payload)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters next)
    (base : Fin (p.m - 1) → ℕ)
    (hlive : eventRecord.output.next.coordinator = .live next owned base)
    (hpending : next.pendingAtChoice = w.view.pendingAtChoice.erase i)
    (hnextPayload : next.payload = payload) :
    ∃ b : Fin W.length, b.val < a ∧
      ∃ selected : Selection W[b.val].input,
        (prepare W[b.val].input).coordinator.selection = some selected ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (W[b.val].input.row.2 W[b.val].input.time).1 = i ∧
        CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
          selected.view.pendingAtChoice selected.view.cutoff W[b.val].input.time
          (W[b.val].input.row.2 W[b.val].input.time)
          (prepare W[b.val].input).coordinatorObservation ∧
        selected.view.payload = payload ∧
        ∃ next' owned' base',
          W[b.val].output.next.coordinator = .live next' owned' base' ∧
          next'.pendingAtChoice = selected.view.pendingAtChoice.erase i ∧
          next'.payload = payload := by
  obtain ⟨bval, hbTake, heqRecord⟩ := List.mem_iff_getElem.mp heventMem
  have htakeLength : (W.take a).length = a := by
    simp only [List.length_take, Nat.min_eq_left ha]
  have hb : bval < a := by
    rw [htakeLength] at hbTake
    exact hbTake
  have hbW : bval < W.length := lt_of_lt_of_le hb ha
  have hget : (W.take a)[bval] = W[bval] := by
    simp only [List.getElem_take]
  rw [hget] at heqRecord
  let b : Fin W.length := ⟨bval, hbW⟩
  have hinput : W[b.val].input = eventRecord.input :=
    congrArg (fun record : Record => record.input) heqRecord
  have htransport :
      ∃ selected : Selection W[b.val].input,
        (prepare W[b.val].input).coordinator.selection = some selected ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (W[b.val].input.row.2 W[b.val].input.time).1 = i ∧
        CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
          selected.view.pendingAtChoice selected.view.cutoff W[b.val].input.time
          (W[b.val].input.row.2 W[b.val].input.time)
          (prepare W[b.val].input).coordinatorObservation ∧
        selected.view.payload = payload ∧
        next.pendingAtChoice = selected.view.pendingAtChoice.erase i := by
    exact hinput.symm ▸ ⟨w, hselected, hdraw, hevent, hpayload, hpending⟩
  rcases htransport with ⟨selected, hselected', hdraw', hevent', hpayload', hpending'⟩
  have hnextEq := congrArg (fun record : Record => record.output.next.coordinator) heqRecord
  exact ⟨b, hb, selected, hselected', hdraw', hevent', hpayload',
    next, owned, base, hnextEq.trans hlive, hpending', hnextPayload⟩

/-- In the literal original run, a selected follower missing from the live
pending set has an earlier actual successful DOWN confirmation whose live
successor erased exactly that follower. The event and whole payload are
carried through the actual connected first-live prefix.
-/
theorem run_firstLive_missing_pending_confirmation (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hseed : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial) :
    let R := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan hmode
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records
    ∀ (a : Fin W.length) (v : Selection W[a.val].input),
      (prepare W[a.val].input).coordinator.selection = some v →
      ∀ (i : Fin (p.m - 1)), i ∉ v.view.pendingAtChoice →
        ∃ b : Fin W.length, b.val < a.val ∧
          ∃ w : Selection W[b.val].input,
            (prepare W[b.val].input).coordinator.selection = some w ∧
            PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (W[b.val].input.row.2 W[b.val].input.time).1 = i ∧
            CoordinatorLocalArmChoice.downConfirmationEvent w.view.payload
              w.view.pendingAtChoice w.view.cutoff W[b.val].input.time
              (W[b.val].input.row.2 W[b.val].input.time)
              (prepare W[b.val].input).coordinatorObservation ∧
            w.view.payload = v.view.payload ∧
            ∃ r_b q_b base_b,
              W[b.val].output.next.coordinator = .live r_b q_b base_b ∧
              r_b.pendingAtChoice = w.view.pendingAtChoice.erase i := by
  intro R W a v hselected i hi
  have hwindowPrefix : W.IsPrefix R.records := List.takeWhile_prefix _
  have hwindowLen := hwindowPrefix.length_le
  have hrecordAt : W[a.val] = R.records[a.val] := hwindowPrefix.getElem a.isLt
  have haR : a.val < R.records.length := lt_of_lt_of_le a.isLt hwindowLen
  obtain ⟨windowSuffix, hwindowEq⟩ := hwindowPrefix
  have hwindowTake : W.take a.val = R.records.take a.val := by
    rw [← hwindowEq, List.take_append_of_le_length (Nat.le_of_lt a.isLt)]
  have hchainR := ReferenceFollowerReplyChronology.connected_take_to_input
    R.connected a.val haR
  have hchainWindow : ReferenceActivePhysicalHorizon.Connected initial
      (W.take a.val) W[a.val].input.state := by
    rw [hwindowTake, hrecordAt]
    exact hchainR
  have hseedState : ReferenceFirstLiveConfirmationHistory.FirstLiveState initial := by
    simpa only [ReferenceFirstLiveConfirmationHistory.FirstLiveState, hfirst] using hseed
  have hinitialHistory : HasMissingHistory [] initial := by
    simp [HasMissingHistory, hfirst]
  have hno : ∀ record ∈ W.take a.val,
      ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
    intro record hmem
    exact window_no_cutoff R.records record (List.mem_of_mem_take hmem)
  have hhistory := connected_missing_history_final (W.take a.val) hchainWindow hseedState
    hno [] hinitialHistory
  have hhistory' : HasMissingHistory (W.take a.val) W[a.val].input.state := by
    simpa only [List.nil_append] using hhistory
  have hcurrentCutoff : ReferenceCollectionPhaseHistory.cutoffChosen W[a.val].input = false :=
    window_no_cutoff R.records W[a.val]
      (List.getElem_mem a.isLt)
  have hcarried := ReferenceFirstLiveConfirmationHistory.run_firstLive_carried
    initial rows J rewards start count hspan hmode hfirst hseed a
  rcases selected_view_first_or_live W[a.val].input hcarried hcurrentCutoff v hselected with
    hLive | ⟨_, hpendingUniv⟩
  · rcases hLive with ⟨r, q, base, hstate, hpayload, hpending⟩
    have hhistoryLive : ∀ j, j ∉ r.pendingAtChoice →
        HasActualErasure (W.take a.val) r.payload j := by
      simpa only [HasMissingHistory, hstate] using hhistory'
    have hiState : i ∉ r.pendingAtChoice := by
      simpa only [hpending] using hi
    rcases hhistoryLive i hiState with
      ⟨eventRecord, heventMem, w, hselectedEvent, hdraw, hevent, hpayloadEvent,
        r_b, q_b, base_b, hliveEvent, hpendingEvent, hnextPayload⟩
    rcases actual_erasure_mem_take W a.val (Nat.le_of_lt a.isLt) v.view.payload i
        eventRecord heventMem w hselectedEvent hdraw hevent
        (hpayloadEvent.trans hpayload.symm) r_b q_b base_b hliveEvent hpendingEvent
        (hnextPayload.trans hpayload.symm) with
      ⟨b, hb, w', hselectedEvent', hdraw', hevent', hpayload',
        r_b', q_b', base_b', hliveEvent', hpendingEvent', _⟩
    exact ⟨b, hb, w', hselectedEvent', hdraw', hevent', hpayload',
      r_b', q_b', base_b', hliveEvent', hpendingEvent'⟩
  · rw [hpendingUniv] at hi
    exact (hi (Finset.mem_univ i)).elim

/-- The current ordinary drawn follower has the same retained assignment in
an earlier accepted DOWN, by tracing its actual ordinary output back to the
confirmation round and then applying the actual first-live event history.
-/
theorem run_firstLive_missing_pending_prior_down (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hseed : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial) :
    let R := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan hmode
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records
    ∀ (a : Fin W.length) (v : Selection W[a.val].input),
      (prepare W[a.val].input).coordinator.selection = some v →
      ∀ (i : Fin (p.m - 1)) (s : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        ((prepare W[a.val].input).followers.followers i).configuration = .ordinary s memory →
        i ∉ v.view.pendingAtChoice →
          ∃ b : Fin W.length, b.val < a.val ∧
            ∃ w : Selection W[b.val].input,
              (prepare W[b.val].input).coordinator.selection = some w ∧
              PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                (W[b.val].input.row.2 W[b.val].input.time).1 = i ∧
              CoordinatorLocalArmChoice.downConfirmationEvent w.view.payload
                w.view.pendingAtChoice w.view.cutoff W[b.val].input.time
                (W[b.val].input.row.2 W[b.val].input.time)
                (prepare W[b.val].input).coordinatorObservation ∧
              w.view.payload = v.view.payload ∧
              ∃ r_b q_b base_b,
                W[b.val].output.next.coordinator = .live r_b q_b base_b ∧
                r_b.pendingAtChoice = w.view.pendingAtChoice.erase i ∧
              ∃ j : Fin W.length, j.val < b.val ∧
                ReferenceFirstLiveConfirmationHistory.AcceptedDown W[j.val] i
                  (v.view.payload.downRecord i) := by
  intro R W a v hselected i s memory hc hi
  obtain ⟨b, hb, w, hselectedEvent, hdraw, hevent, hpayload, r_b, q_b, base_b,
      hliveEvent, hpendingEvent⟩ :=
    run_firstLive_missing_pending_confirmation initial rows J rewards start count hspan
      hmode hfirst hseed a v hselected i hi
  have hwindowPrefix : W.IsPrefix R.records := List.takeWhile_prefix _
  have hwindowLen := hwindowPrefix.length_le
  have hrecordAt : W[a.val] = R.records[a.val] := hwindowPrefix.getElem a.isLt
  have haR : a.val < R.records.length := lt_of_lt_of_le a.isLt hwindowLen
  obtain ⟨windowSuffix, hwindowEq⟩ := hwindowPrefix
  have hwindowTake : W.take a.val = R.records.take a.val := by
    rw [← hwindowEq, List.take_append_of_le_length (Nat.le_of_lt a.isLt)]
  have hchainR := ReferenceFollowerReplyChronology.connected_take_to_input
    R.connected a.val haR
  have hchainWindow : ReferenceActivePhysicalHorizon.Connected initial
      (W.take a.val) W[a.val].input.state := by
    rw [hwindowTake, hrecordAt]
    exact hchainR
  have hcurrentChoice :
      (ReferenceFollowerFixedReply.actualChoice W[a.val] i).configuration = .ordinary s memory := by
    change (W[a.val].output.preparation.followers.followers i).configuration = .ordinary s memory
    rw [W[a.val].output_eq]
    exact hc
  obtain ⟨before, beforeMemory, hbefore, _, _⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice W[a.val] i s memory hcurrentChoice
  have htakeLength : (W.take a.val).length = a.val := by
    simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt a.isLt)]
  have hbTake : b.val < (W.take a.val).length := by
    rw [htakeLength]
    exact hb
  obtain ⟨next, nextMemory, hnext, _⟩ :=
    ReferenceFollowerReplyChronology.connected_output_chronology hchainWindow i before
      beforeMemory hbefore b.val hbTake
  have hnextWindow : W[b.val].output.next.followers i = .ordinary next nextMemory := by
    have hget : (W.take a.val)[b.val] = W[b.val] := by
      simp only [List.getElem_take]
    rw [← hget]
    exact hnext
  obtain ⟨choiceAtB, memoryAtB, hchoiceAtB, _, _, _⟩ :=
    ReferenceFollowerReplyChronology.record_choice_chronology W[b.val] i next nextMemory
      hnextWindow
  have hdrawChoice : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (W[b.val].input.row.2 W[b.val].input.time).1 = i := hdraw
  have hchoiceAtB' : ((prepare W[b.val].input).followers.followers
      (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (W[b.val].input.row.2 W[b.val].input.time).1)).configuration =
        .ordinary choiceAtB memoryAtB := by
    have hchoiceAtB'' : ((prepare W[b.val].input).followers.followers i).configuration =
        .ordinary choiceAtB memoryAtB := by
      have hprepEq : W[b.val].output.preparation = prepare W[b.val].input := by
        rw [W[b.val].output_eq]
        rfl
      rw [← hprepEq]
      change (ReferenceFollowerFixedReply.actualChoice W[b.val] i).configuration = _
      exact hchoiceAtB
    rw [hdrawChoice]
    exact hchoiceAtB''
  obtain ⟨jval, hjval, haccepted⟩ :=
    ReferenceFirstLiveConfirmationHistory.run_firstLive_confirmation_prior_down initial rows J
      rewards start count hspan hmode hfirst hseed b w hselectedEvent choiceAtB memoryAtB
      hchoiceAtB' hevent
  have hjWindow : jval < W.length := lt_trans hjval b.isLt
  let j : Fin W.length := ⟨jval, hjWindow⟩
  have haccepted' : ReferenceFirstLiveConfirmationHistory.AcceptedDown W[j.val] i
      (v.view.payload.downRecord i) := by
    have hrewritten : ReferenceFirstLiveConfirmationHistory.AcceptedDown W[j.val]
        (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (W[b.val].input.row.2 W[b.val].input.time).1)
        (w.view.payload.downRecord
          (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (W[b.val].input.row.2 W[b.val].input.time).1)) := by
      simpa only [j] using haccepted
    rw [hdrawChoice, hpayload] at hrewritten
    exact hrewritten
  exact ⟨b, hb, w, hselectedEvent, hdraw, hevent, hpayload, r_b, q_b, base_b,
    hliveEvent, hpendingEvent, j, hjval, haccepted'⟩

section ActualLaunch

variable
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : ReferenceActivePhysicalStep.RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)

/-- Specialize the first-live retained-assignment history result to the actual
launched boundary, preserving its whole source, private row index, rewards,
buffers, batches, proposal memory, and all initialization conditions.
-/
theorem ofActualLaunchedBoundary_missing_pending_prior_down (count : ℕ)
    (hspan : BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) +
      count ≤ p.T) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start :=
      fun i => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
    let R := ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records
    ∀ (a : Fin W.length) (v : Selection W[a.val].input),
      (prepare W[a.val].input).coordinator.selection = some v →
      ∀ (i : Fin (p.m - 1)) (s : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        ((prepare W[a.val].input).followers.followers i).configuration = .ordinary s memory →
        i ∉ v.view.pendingAtChoice →
          ∃ b : Fin W.length, b.val < a.val ∧
            ∃ w : Selection W[b.val].input,
              (prepare W[b.val].input).coordinator.selection = some w ∧
              PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                (W[b.val].input.row.2 W[b.val].input.time).1 = i ∧
              CoordinatorLocalArmChoice.downConfirmationEvent w.view.payload
                w.view.pendingAtChoice w.view.cutoff W[b.val].input.time
                (W[b.val].input.row.2 W[b.val].input.time)
                (prepare W[b.val].input).coordinatorObservation ∧
              w.view.payload = v.view.payload ∧
              ∃ r_b q_b base_b,
                W[b.val].output.next.coordinator = .live r_b q_b base_b ∧
                r_b.pendingAtChoice = w.view.pendingAtChoice.erase i ∧
              ∃ j : Fin W.length, j.val < b.val ∧
                ReferenceFirstLiveConfirmationHistory.AcceptedDown W[j.val] i
                  (v.view.payload.downRecord i) := by
  dsimp only
  exact run_firstLive_missing_pending_prior_down _ _ _ _ _ count hspan _
    (ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
    (ReferenceFirstLiveConfirmationHistory.ofActualLaunchedBoundary_initialFollowers
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)

end ActualLaunch

end Bandits.Support.ReferenceFirstLivePendingErasureHistory

end
