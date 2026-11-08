/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceSelectedPayloadChronology
public import Bandits.Support.ReferenceDownPhysicalHashRule
public import Bandits.Support.ReferenceFirstLiveConfirmationHistory

import Mathlib.Data.List.TakeWhile

/-!
# Sender and local acceptance before the first DOWN acceptance

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-124`,
`sources/zip4/manuscript/06_interruptions.tex:164-177,246-295,327-348`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,151-157`.

The endpoint conditions select a live, ordinary, still-unaccepted branch of
the original physical run. They do not assert that a run reaches that branch.
All banks, buffers, rows, private indices and rewards remain the original ones.
These are internal deterministic results; batch uniqueness, service, delivery,
collection, later assignments and manuscript closure are separate obligations.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstUnacceptedDownEpoch

open ConstructorDimensions ReferenceActivePhysicalStep
open ReferencePrelaunchFollower (acceptedStart)


variable {p : Parameters} {rate : RateInput p}

private theorem lastDown_none_of_start_zero
    (s : ReferencePrelaunchFollower.State p rate.eta)
    (h : acceptedStart s = 0) : s.lastDown = none := by
  cases hd : s.lastDown with
  | none => rfl
  | some M =>
      have hp : 1 ≤ M.val.sigma := M.property.1
      simp only [acceptedStart, hd] at h
      omega

private theorem connected_unaccepted_record
    {initial final : State p rate} {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final) (seed : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial)
    (i : Fin (p.m - 1)) (sB : ReferencePrelaunchFollower.State p rate.eta)
    (memoryB : ActiveFollowerLifecycle.LocalMemory p)
    (hout : final.followers i = .ordinary sB memoryB) (hnone : sB.lastDown = none)
    (a : ℕ) (ha : a < records.length) :
    ∃ before beforeMemory choice choiceMemory next nextMemory,
      records[a].input.state.followers i = .ordinary before beforeMemory ∧
      (ReferenceFollowerFixedReply.actualChoice records[a] i).configuration = .ordinary choice choiceMemory ∧
      records[a].output.next.followers i = .ordinary next nextMemory ∧
      before.lastDown = none ∧ choice.lastDown = none ∧ next.lastDown = none ∧
      before.status = .unoccupied ∧ choice.status = .unoccupied ∧ next.status = .unoccupied := by
  have hz : acceptedStart sB = 0 := by simp only [acceptedStart, hnone]
  obtain ⟨next, nextMemory, hn, hbound⟩ :=
    ReferenceFollowerReplyChronology.connected_output_chronology chain i sB memoryB hout a ha
  have hnz : acceptedStart next = 0 := by omega
  obtain ⟨choice, choiceMemory, hc, hcn, hkeep, _⟩ :=
    ReferenceFollowerReplyChronology.record_choice_chronology records[a] i next nextMemory hn
  have hcz : acceptedStart choice = 0 := by omega
  obtain ⟨before, beforeMemory, hb, hreply, hstatus⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice records[a] i choice choiceMemory hc
  have hbz : acceptedStart before = 0 := (ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply).symm.trans hcz
  have prefixChain := ReferenceFollowerReplyChronology.connected_take_to_input chain a ha
  obtain ⟨first, firstMemory, hf, hmono, hframe, _⟩ :=
    ReferenceFollowerReplyChronology.connected_ordinary_chronology prefixChain i before beforeMemory hb
  have hseed := seed i first firstMemory hf
  have hfz : acceptedStart first = 0 := by simp only [acceptedStart, hseed.2]
  have hbu := (hframe hseed.1 (hfz.trans hbz.symm)).1
  have hcu := hstatus hbu
  exact ⟨before, beforeMemory, choice, choiceMemory, next, nextMemory, hb, hc, hn,
    lastDown_none_of_start_zero before hbz, lastDown_none_of_start_zero choice hcz,
    lastDown_none_of_start_zero next hnz, hbu, hcu, (hkeep hcu (hcz.trans hnz.symm)).1⟩

private theorem no_acceptedDown_of_output_none
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : record.output.next.followers i = .ordinary next memory)
    (hnone : next.lastDown = none) (M : ReferenceFirstLiveConfirmationHistory.DownRecord (p := p) (rate := rate)) :
    ¬ ReferenceFirstLiveConfirmationHistory.AcceptedDown record i M := by
  intro haccepted
  obtain ⟨logged, cut, after, raw, scan, registers, lastService, hi, hd, ho⟩ := haccepted
  have applied : ReferenceFollowerReplyChronology.appliedDown record i M.val.sigma :=
    ⟨logged, cut, after, raw, M, scan, registers, lastService, hi, hd, ho, rfl⟩
  obtain ⟨choice, choiceMemory, _, hlt, he⟩ :=
    ReferenceFollowerReplyChronology.record_appliedDown_strict record i M.val.sigma applied next memory hout
  have hz : acceptedStart next = 0 := by simp only [acceptedStart, hnone]
  omega

private theorem continuing_pending
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

private theorem selection_fields (x : RoundInput p rate) (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (arm : CoordinatorRoundDispatch.ArmSelection payload started time weights x.row)
    (selected : Selection x) (h : selectionAt x payload started time weights arm = some selected) :
    selected.view.payload = payload ∧ selected.view.pendingAtChoice = started.pending ∧
      selected.view.cutoff = CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u := by
  unfold selectionAt at h
  split at h
  · cases h; exact ⟨rfl, rfl, rfl⟩
  · cases h

private theorem live_tail_pending
    (x : RoundInput p rate) (prepared : PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hnot : (livePostChoice prepared r q base started).configuration ≠ .dagger) :
    ∃ next owned,
      (livePostChoice prepared r q base started).configuration = .live next owned base ∧
      next.payload = r.payload ∧
      CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
        x.time x.row prepared.coordinatorObservation = some next.pendingAtChoice := by
  unfold livePostChoice at hnot
  split at hnot
  · exact (hnot rfl).elim
  · rename_i recording hrecord
    split at hnot
    · exact (hnot rfl).elim
    · rename_i serviced hservice
      split at hnot
      · exact (hnot rfl).elim
      · rename_i pending hpending
        split at hnot
        · exact (hnot rfl).elim
        · rename_i finished hfinish
          let next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta := {
            payload := r.payload
            priorClock := finished.clock
            pendingAtChoice := finished.pending
            time := x.time
            gridBoundary := finished.clock.g
            complementScores := serviced.score }
          let owned : CoordinatorLiveServiceFinish.OwnedRegisters next := {
            queue := serviced.queue, previousService := serviced.previousService }
          refine ⟨next, owned, ?_, rfl, ?_⟩
          · simp only [livePostChoice, hrecord, hservice, hpending, hfinish]
            rfl
          · change _ = some finished.pending
            rw [CoordinatorPhaseClock.finishRound_pending_frame p rate.eta.val x.time
              started.clock pending x.row finished hfinish]
            exact hpending

private theorem firstLive_selection
    (x : RoundInput p rate) (hs : ReferenceFirstLiveConfirmationHistory.FirstLiveState x.state)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen x = false)
    (hnot : (step x).next.coordinator ≠ .dagger) :
    ∃ (selected : Selection x) (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters next) (base : Fin (p.m - 1) → ℕ),
      (prepare x).coordinator.selection = some selected ∧
      (step x).next.coordinator = .live next owned base ∧
      selected.view.payload = next.payload ∧
      (match x.state.coordinator with
       | .first => selected.view.pendingAtChoice = Finset.univ
       | .live old _ _ => selected.view.pendingAtChoice = old.pendingAtChoice ∧
           selected.view.payload = old.payload
       | _ => False) ∧
      CoordinatorLocalArmChoice.confirmationUpdate selected.view.payload selected.view.pendingAtChoice selected.view.cutoff
        x.time x.row (prepare x).coordinatorObservation = some next.pendingAtChoice := by
  cases hc : x.state.coordinator with
  | dagger => exact (hnot (step_coordinator_dagger x hc).1).elim
  | collection payload ledger proposal => simp only [ReferenceFirstLiveConfirmationHistory.FirstLiveState, hc] at hs
  | first =>
      have hd : (prepare x).coordinator = .first
          (CoordinatorRoundDispatch.dispatchFirst (firstInput x)) := dispatch_first x hc
      have he := observeCoordinator_first_equation (prepare x) _ hd
      cases ho : CoordinatorRoundDispatch.dispatchFirst (firstInput x) with
      | choiceDomainFailure installed =>
          simp only [step, he, ho, DispatchCut.selection, ite_true, coordinatorFailure] at hnot
          exact (hnot rfl).elim
      | recorderBoundaryFailure installed =>
          simp only [step, he, ho, DispatchCut.selection, ite_true, coordinatorFailure] at hnot
          exact (hnot rfl).elim
      | choiceRejected installed =>
          simp only [step, he, ho, DispatchCut.selection, ite_true, coordinatorFailure] at hnot
          exact (hnot rfl).elim
      | chosen installed arm =>
          cases hsel : (DispatchCut.first (.chosen installed arm)).selection with
          | none =>
              simp only [step, he, ho, hsel, ite_true, coordinatorFailure] at hnot
              exact (hnot rfl).elim
          | some selected =>
              have hselected : (prepare x).coordinator.selection = some selected := by
                rw [hd, ho]; exact hsel
              have hout : (step x).next.coordinator =
                  (livePostChoice (prepare x) installed.registers installed.ownedRegisters
                    installed.followerBaseScore installed.startRoundResult).configuration := by
                change (prepare x).observeCoordinator.configuration = _
                rw [he, ho, hsel]
                rfl
              obtain ⟨next, owned, hn, hp, hupdate⟩ := live_tail_pending x (prepare x)
                installed.registers installed.ownedRegisters installed.followerBaseScore
                installed.startRoundResult (by rw [← hout]; exact hnot)
              obtain ⟨hpayload, hpending, hclock⟩ := selection_fields x _ _ _ _ arm selected hsel
              refine ⟨selected, next, owned, installed.followerBaseScore, hselected,
                hout.trans hn, hpayload.trans hp.symm, ?_, ?_⟩
              · change selected.view.pendingAtChoice = Finset.univ
                rw [hpending, dispatchFirst_chosen_installation x installed arm ho]
                rfl
              · rw [hpayload, hpending, hclock]
                exact hupdate
  | live r q base =>
      have hd : (prepare x).coordinator = .live r q base
          (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
        change dispatch x = _
        simp only [dispatch, hc, CoordinatorRoundDispatch.dispatch]
        rfl
      have he := observeCoordinator_live_equation (prepare x) r q base _ hd
      cases ho : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base) with
      | clockFailure failure hfailure =>
          simp only [step, he, ho, DispatchCut.selection, ite_true, coordinatorFailure] at hnot
          exact (hnot rfl).elim
      | initializerFailure dispatched hstart checked hchecked =>
          simp only [step, he, ho, DispatchCut.selection, ite_true, coordinatorFailure] at hnot
          exact (hnot rfl).elim
      | localFailure dispatched hstart reason =>
          simp only [step, he, ho, DispatchCut.selection, ite_true, coordinatorFailure] at hnot
          exact (hnot rfl).elim
      | cutoffChosen =>
          simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hd, ho,
            Bool.true_eq_false] at hcut
      | continuingChosen dispatched hstart continuation arm =>
          cases hsel : (DispatchCut.live r q base
              (.continuingChosen dispatched hstart continuation arm)).selection with
          | none =>
              simp only [step, he, ho, hsel, ite_true, coordinatorFailure] at hnot
              exact (hnot rfl).elim
          | some selected =>
              have hselected : (prepare x).coordinator.selection = some selected := by
                rw [hd, ho]; exact hsel
              have hout : (step x).next.coordinator =
                  (livePostChoice (prepare x) (liveRegistersAt r x.time)
                    (liveOwnedAt r q x.time) base dispatched.startResult).configuration := by
                change (prepare x).observeCoordinator.configuration = _
                rw [he, ho, hsel]
                rfl
              obtain ⟨next, owned, hn, hp, hupdate⟩ := live_tail_pending x (prepare x)
                (liveRegistersAt r x.time) (liveOwnedAt r q x.time) base
                dispatched.startResult (by rw [← hout]; exact hnot)
              obtain ⟨hpayload, hpending, hclock⟩ := selection_fields x _ _ _ _ arm selected hsel
              have hpend := continuing_pending (liveInput x r q base)
                dispatched hstart continuation arm ho
              refine ⟨selected, next, owned, base, hselected, hout.trans hn,
                hpayload.trans hp.symm, ?_, ?_⟩
              · change selected.view.pendingAtChoice = r.pendingAtChoice ∧
                  selected.view.payload = r.payload
                exact ⟨hpending.trans hpend, hpayload⟩
              · rw [hpayload, hpending, hclock]
                exact hupdate

private theorem confirmation_member
    (x : RoundInput p rate) (selected : Selection x)
    (pending : Finset (Fin (p.m - 1))) (i : Fin (p.m - 1))
    (hi : i ∈ selected.view.pendingAtChoice)
    (hupdate : CoordinatorLocalArmChoice.confirmationUpdate selected.view.payload
      selected.view.pendingAtChoice selected.view.cutoff x.time x.row
      (prepare x).coordinatorObservation = some pending)
    (hno : upSenderIndex x = i →
      ¬ CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
        selected.view.pendingAtChoice selected.view.cutoff x.time (x.row.2 x.time)
        (prepare x).coordinatorObservation) : i ∈ pending := by
  classical
  unfold CoordinatorLocalArmChoice.confirmationUpdate
    CoordinatorLocalArmChoice.confirmationUpdateCore at hupdate
  split at hupdate
  · split at hupdate
    · rename_i hevent
      have he := Option.some.inj hupdate
      rw [← he]
      apply Finset.mem_erase.mpr
      refine ⟨?_, hi⟩
      intro heq
      exact hno (by rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw]; exact heq.symm) hevent
    · exact Option.some.inj hupdate ▸ hi
  · cases hupdate

private theorem connected_live_selections
    {initial final : State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hs : ReferenceFirstLiveConfirmationHistory.FirstLiveState initial)
    (hcut : ∀ record ∈ records, ReferenceCollectionPhaseHistory.cutoffChosen record.input = false)
    (rB : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (qB : CoordinatorLiveServiceFinish.OwnedRegisters rB) (baseB : Fin (p.m - 1) → ℕ)
    (hfinal : final.coordinator = .live rB qB baseB) (i : Fin (p.m - 1))
    (hinitial : match initial.coordinator with
      | .first => True
      | .live r _ _ => i ∈ r.pendingAtChoice
      | _ => False)
    (hno : ∀ record ∈ records, ∀ selected : Selection record.input,
      (prepare record.input).coordinator.selection = some selected →
      upSenderIndex record.input = i →
      ¬ CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
        selected.view.pendingAtChoice selected.view.cutoff record.input.time
        (record.input.row.2 record.input.time) (prepare record.input).coordinatorObservation) :
    (initial.coordinator = .first ∨ ReferenceAssignmentPayloadPersistence.storedPayload
      initial.coordinator = some rB.payload) ∧
    ∀ record ∈ records, ∃ selected : Selection record.input,
      (prepare record.input).coordinator.selection = some selected ∧
      selected.view.payload = rB.payload ∧ i ∈ selected.view.pendingAtChoice := by
  induction records generalizing initial with
  | nil =>
      subst final
      exact ⟨Or.inr (by rw [hfinal]; rfl), fun record hr => (List.not_mem_nil hr).elim⟩
  | cons record rest ih =>
      obtain ⟨hpre, hrest⟩ := chain
      have hnD : (step record.input).next.coordinator ≠ .dagger := by
        intro hd
        have hd' : record.output.next.coordinator = .dagger := by rw [record.output_eq]; exact hd
        have hend := (hrest.coordinator_dagger hd').1
        rw [hfinal] at hend
        cases hend
      have hs' : ReferenceFirstLiveConfirmationHistory.FirstLiveState record.input.state := hpre ▸ hs
      obtain ⟨selected, next, owned, base, hselected, hout, hpayload, hinput, hupdate⟩ :=
        firstLive_selection record.input hs' (hcut record List.mem_cons_self) hnD
      have hi : i ∈ selected.view.pendingAtChoice := by
        rw [hpre] at hinput
        cases hc : initial.coordinator with
        | first =>
            simp only [hc] at hinput
            rw [hinput]
            exact Finset.mem_univ i
        | live old q b =>
            simp only [hc] at hinput hinitial
            rw [hinput.1]
            exact hinitial
        | collection payload ledger proposal => simp only [hc] at hinitial
        | dagger => simp only [hc] at hinitial
      have hnext : record.output.next.coordinator = .live next owned base := by
        rw [record.output_eq]; exact hout
      have hinext := confirmation_member record.input selected next.pendingAtChoice i hi hupdate
        (hno record List.mem_cons_self selected hselected)
      have hsnext : ReferenceFirstLiveConfirmationHistory.FirstLiveState record.output.next := by
        rw [record.output_eq]
        exact ReferenceFirstLiveConfirmationHistory.firstLive_step record.input hs'
          (hcut record List.mem_cons_self)
      obtain ⟨hbefore, hrecords⟩ := ih hrest hsnext
        (fun r hr => hcut r (List.mem_cons_of_mem record hr))
        (by rw [hnext]; exact hinext)
        (fun r hr => hno r (List.mem_cons_of_mem record hr))
      have heq : next.payload = rB.payload := by
        rcases hbefore with hf | hp
        · rw [hnext] at hf; cases hf
        · simpa only [hnext, ReferenceAssignmentPayloadPersistence.storedPayload,
            Option.some.injEq] using hp
      have hwhole := hpayload.trans heq
      constructor
      · rw [hpre] at hinput
        cases hc : initial.coordinator with
        | first => exact Or.inl rfl
        | live old q b =>
            simp only [hc] at hinput
            exact Or.inr (congrArg some (hinput.2.symm.trans hwhole))
        | collection payload ledger proposal => simp only [hc] at hinitial
        | dagger => simp only [hc] at hinitial
      · intro r hr
        rcases List.mem_cons.mp hr with he | ht
        · subst r; exact ⟨selected, hselected, hwhole, hi⟩
        · exact hrecords r ht

private theorem prefix_records
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (mode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (b : ℕ) (hb : b ≤ count) :
    (ReferenceActivePhysicalHorizon.run initial rows J rewards start b (by omega) mode).records =
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span mode).records.take b := by
  have hp : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b (by omega) mode).records.IsPrefix
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span mode).records := by
    obtain ⟨suffix, he⟩ := ReferenceCollectionPhaseHistory.run_records_prefix initial rows J
      rewards start b (count - b) (by omega) mode
    exact ⟨suffix, by simpa only [Nat.add_sub_of_le hb] using he.symm⟩
  have he := List.prefix_iff_eq_take.mp hp
  rw [ReferenceActivePhysicalHorizon.run_record_count] at he
  exact he

/-- An actual live, ordinary endpoint with no accepted DOWN produces successful
selections of one whole payload and actual pending membership throughout the
original first-live prefix. No successful-history or sender-word premise is supplied. -/
theorem run_first_unaccepted_selections
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (mode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hseed : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial)
    (b : ℕ) (hb : b ≤ count)
    (hwindow : b ≤ (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span mode).records).length)
    (rB : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (qB : CoordinatorLiveServiceFinish.OwnedRegisters rB) (baseB : Fin (p.m - 1) → ℕ)
    (hcoord : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b (by omega) mode).finalState.coordinator =
      .live rB qB baseB)
    (i : Fin (p.m - 1)) (sB : ReferencePrelaunchFollower.State p rate.eta)
    (memoryB : ActiveFollowerLifecycle.LocalMemory p)
    (hfocal : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b (by omega) mode).finalState.followers i =
      .ordinary sB memoryB) (hnone : sB.lastDown = none) :
    0 < b ∧ ∀ record ∈ (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span mode).records.take b,
      ∃ selected : Selection record.input,
        record.output.preparation.coordinator.selection = some selected ∧
        selected.view.payload = rB.payload ∧ i ∈ selected.view.pendingAtChoice := by
  classical
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span mode
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  let B := ReferenceActivePhysicalHorizon.run initial rows J rewards start b (by omega) mode
  have he : B.records = E.records.take b := prefix_records initial rows J rewards start count span mode b hb
  have hw : W.IsPrefix E.records := List.takeWhile_prefix _
  have hlen : B.records.length = b := ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have hBW : B.records.IsPrefix W := by
    rw [he, List.prefix_iff_eq_take.mp hw]
    exact List.take_prefix_take_left hwindow
  have hcut : ∀ record ∈ B.records,
      ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
    intro record hr
    have hmem := List.mem_takeWhile_imp (hBW.subset hr)
    simpa only [Bool.not_eq_true'] using hmem
  have noAccepted : ∀ record ∈ B.records, ∀ M, ¬ ReferenceFirstLiveConfirmationHistory.AcceptedDown record i M := by
    intro record hr M
    obtain ⟨a, ha, haeq⟩ := List.mem_iff_getElem.mp hr
    obtain ⟨before, beforeMemory, choice, choiceMemory, next, nextMemory,
      _, _, hout, _, _, hn, _, _, _⟩ :=
      connected_unaccepted_record B.connected hseed i sB memoryB hfocal hnone a ha
    rw [← haeq]
    exact no_acceptedDown_of_output_none _ i next nextMemory hout hn M
  have hno : ∀ record ∈ B.records, ∀ selected : Selection record.input,
      (prepare record.input).coordinator.selection = some selected → upSenderIndex record.input = i →
      ¬ CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload selected.view.pendingAtChoice
        selected.view.cutoff record.input.time (record.input.row.2 record.input.time)
        (prepare record.input).coordinatorObservation := by
    intro record hr selected hselected hindex hevent
    obtain ⟨a, ha, haeq⟩ := List.mem_iff_getElem.mp hr
    have haw : a < W.length := lt_of_lt_of_le ha hBW.length_le
    have helem : W[a] = record := (hBW.getElem ha).symm.trans haeq
    obtain ⟨before, beforeMemory, choice, choiceMemory, next, nextMemory,
      _, hc, _, _, _, _, _, _, _⟩ :=
      connected_unaccepted_record B.connected hseed i sB memoryB hfocal hnone a ha
    rw [haeq] at hc
    have hc' : ((prepare record.input).followers.followers i).configuration = .ordinary choice choiceMemory := by
      change (record.output.preparation.followers.followers i).configuration = _ at hc
      rw [record.output_eq] at hc
      exact hc
    have prior := ReferenceFirstLiveConfirmationHistory.run_firstLive_confirmation_prior_down
      initial rows J rewards start count span mode hfirst hseed ⟨a, haw⟩
    rw [helem] at prior
    have hi : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (record.input.row.2 record.input.time).1 = i := hindex
    simp only [hi] at prior
    obtain ⟨j, hj, haccepted⟩ := prior selected hselected choice choiceMemory hc' hevent
    have hjB : j < B.records.length := lt_trans hj ha
    have hjw : j < W.length := lt_trans hj haw
    have heq : W[j] = B.records[j] := (hBW.getElem hjB).symm
    rw [heq] at haccepted
    exact noAccepted _ (List.getElem_mem hjB) _ haccepted
  have hs : ReferenceFirstLiveConfirmationHistory.FirstLiveState initial := by
    simpa only [ReferenceFirstLiveConfirmationHistory.FirstLiveState, hfirst] using hseed
  have hselections := (connected_live_selections B.connected hs hcut rB qB baseB hcoord i
    (by rw [hfirst]; trivial) hno).2
  constructor
  · by_contra hn
    have hz : b = 0 := by omega
    have hc0 : B.finalState.coordinator = .first := by
      dsimp only [B]
      simpa only [hz, ReferenceActivePhysicalHorizon.run_zero_final] using hfirst
    have hc := hc0.symm.trans hcoord
    cases hc
  · intro record hr
    rw [← he] at hr
    obtain ⟨selected, hselected, hpayload, hpending⟩ := hselections record hr
    refine ⟨selected, ?_, hpayload, hpending⟩
    rw [record.output_eq]
    exact hselected

private theorem down_call_checks
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (own : ReferencePrelaunchFollower.Observation p)
    (logged post : ReferencePrelaunchFollower.State p rate.eta)
    (hselected : ActiveFollowerDownAcceptance.downSelected p i row t)
    (hu : logged.status = .unoccupied) (hnone : post.lastDown = none)
    (hconsume : DeclaredFollowerLocalRound.consumeDownResult rate
      (ReferenceDownReception.referenceDownCut p view i row t own rate logged).outcome = .ok post) :
    ActiveFollowerDownAcceptance.registerInputDomain p rate logged ∧
    ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch ∧
    ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer ∧
    (ReferenceDownReception.referenceDownCut p view i row t own rate logged).rawComparison.isSome = true ∧
    (ReferenceDownReception.referenceDownCut p view i row t own rate logged).raw =
      (ActiveFollowerDownAcceptance.currentDecodeStep p i row t own rate logged).2 ∧
    post = { logged with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep p i row t own rate logged).1 } := by
  classical
  have hr : ActiveFollowerDownAcceptance.registerInputDomain p rate logged := by
    by_contra hn
    simp only [ReferenceDownReception.referenceDownCut, dite_eq_left hselected,
      dite_eq_left hu, dite_eq_right hn, DeclaredFollowerLocalRound.consumeDownResult] at hconsume
    cases hconsume
  have hb : ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch := by
    by_contra hn
    simp only [ReferenceDownReception.referenceDownCut, dite_eq_left hselected,
      dite_eq_left hu, dite_eq_left hr, dite_eq_right hn,
      DeclaredFollowerLocalRound.consumeDownResult] at hconsume
    cases hconsume
  have hf : ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer := by
    by_contra hn
    simp only [ReferenceDownReception.referenceDownCut, dite_eq_left hselected,
      dite_eq_left hu, dite_eq_left hr, dite_eq_left hb, dite_eq_right hn,
      DeclaredFollowerLocalRound.consumeDownResult] at hconsume
    cases hconsume
  have hcall : (ReferenceDownReception.referenceDownCut p view i row t own rate logged).rawComparison.isSome = true := by
    rw [ReferenceActiveAffinePositiveTest.referenceDownCut_has_call]
    exact decide_eq_true ⟨hselected, hu, hr, hb, hf⟩
  refine ⟨hr, hb, hf, hcall, ?_, ?_⟩
  · apply ReferenceDownReception.referenceDownCut_raw_eq_currentDecodeStep_of_compared
    intro hn
    rw [hn] at hcall
    cases hcall
  · simp only [ReferenceDownReception.referenceDownCut, dite_eq_left hselected,
      dite_eq_left hu, dite_eq_left hr, dite_eq_left hb, dite_eq_left hf] at hconsume
    split at hconsume
    · split at hconsume
      · cases hconsume; rfl
      · split at hconsume
        · split at hconsume
          · cases hconsume
          · cases hconsume
            cases hnone
        · cases hconsume; rfl
    · cases hconsume; rfl

private theorem selected_unaccepted_down_call
    (x : RoundInput p rate) (i : Fin (p.m - 1))
    (choice next : ReferencePrelaunchFollower.State p rate.eta)
    (choiceMemory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : ((prepare x).followers.followers i).configuration = .ordinary choice choiceMemory)
    (hout : (step x).next.followers i = .ordinary next nextMemory)
    (hu : choice.status = .unoccupied) (hnone : choice.lastDown = none)
    (hnoneNext : next.lastDown = none)
    (hdown : ActiveFollowerDownAcceptance.downSelected p i x.row x.time) :
    let own := (prepare x).feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    ∃ logged,
      ActiveFollowerLogging.checkedLogging i x.row (x.state.activations i) x.time
        (((prepare x).followers.followers i).arm, own) choice = .ok logged ∧
      ((step x).followers i).downInput = some logged ∧
      ((step x).followers i).down = some
        (ReferenceDownReception.referenceDownCut p (dispatch x).downView i x.row x.time own rate logged) ∧
      logged.lastDown = none ∧ logged.status = .unoccupied ∧
      ActiveFollowerDownAcceptance.registerInputDomain p rate logged ∧
      ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch ∧
      ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer ∧
      (ReferenceDownReception.referenceDownCut p (dispatch x).downView i x.row x.time own rate logged).rawComparison.isSome = true ∧
      (ReferenceDownReception.referenceDownCut p (dispatch x).downView i x.row x.time own rate logged).raw =
        (ActiveFollowerDownAcceptance.currentDecodeStep p i x.row x.time own rate logged).2 ∧
      next = { logged with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep p i x.row x.time own rate logged).1 } := by
  classical
  intro own
  change (finishFollower _ _ _).configuration = _ at hout
  obtain ⟨actualChoice, actualMemory, post, hactual, hr, hfinish, hdi, hd⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion _ _ _ next nextMemory hout
  have he := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hactual.symm.trans hc)
  have hech := he.1
  have hemem := he.2
  subst actualChoice
  subst actualMemory
  have align := (prepare x).follower_alignment i
  have hr' : (recordFollower (dispatch x).downView i x.row (x.state.activations i)
      x.time (x.active i) ((prepare x).followers.followers i).arm own choice).result = .ok post := by
    simpa only [align.1, align.2.1, align.2.2.1, align.2.2.2,
      (prepare x).coordinator_eq, own] using hr
  have hf' : DeclaredFollowerLocalRound.releaseAndFinish rate i x.row x.time own
      choice choiceMemory post = .ok (next, nextMemory) := by
    simpa only [align.1, align.2.1, align.2.2.1] using hfinish
  have hreply := ReferenceFollowerReplyChronology.releaseAndFinish_frame
    i x.row x.time own choice post next choiceMemory nextMemory hf'
  have hnpost : post.lastDown = none := (congrArg Prod.fst hreply.1).symm.trans hnoneNext
  have hepost : next = post := by
    unfold DeclaredFollowerLocalRound.releaseAndFinish at hf'
    rw [ActiveFollowerLifecycle.releaseAfterService_unoccupied rate.eta i x.time
      (ActiveFollowerLifecycle.publicRowOfCompleteRow x.row x.time) own choice post hu] at hf'
    cases hf : ActiveFollowerLifecycle.finishRound rate.eta x.time x.row post choiceMemory with
    | error reason => simp only [hf] at hf'; cases hf'
    | ok pair =>
        have hp : pair = (next, nextMemory) := by simpa only [hf, Except.ok.injEq] using hf'
        have hf'' := hf.trans (congrArg Except.ok hp)
        exact ActiveFollowerLifecycle.finishRound_frame rate.eta x.time x.row post next
          choiceMemory nextMemory hf''
  cases hl : ActiveFollowerLogging.checkedLogging i x.row (x.state.activations i) x.time
      (((prepare x).followers.followers i).arm, own) choice with
  | error reason =>
      simp only [recordFollower, dite_eq_left hu, hl] at hr'
      cases hr'
  | ok logged =>
      have hconsume : DeclaredFollowerLocalRound.consumeDownResult rate
          (ReferenceDownReception.referenceDownCut p (dispatch x).downView i x.row x.time own rate logged).outcome = .ok post := by
        simpa only [recordFollower, dite_eq_left hu, hl] using hr'
      have frame := ActiveFollowerLogging.checkedLogging_success_frame i x.row
        (x.state.activations i) x.time (((prepare x).followers.followers i).arm, own) choice logged hl
      have hnlog : logged.lastDown = none := frame.1.trans hnone
      have hulog : logged.status = .unoccupied := frame.2.2.2.2.1.trans hu
      obtain ⟨hreg, hbatch, hbuffer, hcall, hraw, hpost⟩ :=
        down_call_checks (dispatch x).downView i x.row x.time own logged post hdown hulog hnpost hconsume
      have hlOwn := hl
      dsimp only [own] at hlOwn
      have hdi' : ((step x).followers i).downInput = some logged := by
        change (finishFollower _ _ _).downInput = _
        rw [hdi]
        simp only [align.1, align.2.1, align.2.2.1, align.2.2.2, (prepare x).coordinator_eq,
          recordFollower, dite_eq_left hu, hlOwn]
      have hd' : ((step x).followers i).down = some
          (ReferenceDownReception.referenceDownCut p (dispatch x).downView i x.row x.time own rate logged) := by
        change (finishFollower _ _ _).down = _
        rw [hd]
        simp only [align.1, align.2.1, align.2.2.1, align.2.2.2, (prepare x).coordinator_eq,
          recordFollower, dite_eq_left hu, hlOwn]
        rfl
      exact ⟨logged, rfl, hdi', hd', hnlog, hulog, hreg, hbatch, hbuffer,
        hcall, hraw, hepost.trans hpost⟩

/-- Every actual selected DOWN in the still-unaccepted first-live prefix sends
the endpoint's whole stored word and executes its real checked receiver call.
The current record passes the ordinary codec and local acceptance test at the
logged state. Positivity implies hash one using the produced sender premise. -/
theorem run_first_unaccepted_down_epoch
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (mode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hseed : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial)
    (b : ℕ) (hb : b ≤ count)
    (hwindow : b ≤ (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span mode).records).length)
    (rB : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (qB : CoordinatorLiveServiceFinish.OwnedRegisters rB) (baseB : Fin (p.m - 1) → ℕ)
    (hcoord : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b (by omega) mode).finalState.coordinator =
      .live rB qB baseB)
    (i : Fin (p.m - 1)) (sB : ReferencePrelaunchFollower.State p rate.eta)
    (memoryB : ActiveFollowerLifecycle.LocalMemory p)
    (hfocal : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b (by omega) mode).finalState.followers i =
      .ordinary sB memoryB) (hnone : sB.lastDown = none) :
    0 < b ∧ ∀ record ∈ (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span mode).records.take b,
      ∃ (a : ℕ) (_ha : a < b) (selected : Selection record.input)
        (before : ReferencePrelaunchFollower.State p rate.eta)
        (beforeMemory : ActiveFollowerLifecycle.LocalMemory p)
        (choice : ReferencePrelaunchFollower.State p rate.eta)
        (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
        (next : ReferencePrelaunchFollower.State p rate.eta)
        (nextMemory : ActiveFollowerLifecycle.LocalMemory p),
        record.input.time.val = start + a ∧
        record.input.state = (ReferenceActivePhysicalHorizon.run initial rows J rewards start a (by omega) mode).finalState ∧
        record.input.rows = rows ∧ record.input.selected = J ∧ record.input.rewards = rewards ∧
        record.output.preparation.coordinator.selection = some selected ∧
        selected.view.payload = rB.payload ∧ i ∈ selected.view.pendingAtChoice ∧
        rB.payload.sigma.val ≤ record.input.time.val ∧
        record.input.state.followers i = .ordinary before beforeMemory ∧
        (record.output.preparation.followers.followers i).configuration = .ordinary choice choiceMemory ∧
        record.output.next.followers i = .ordinary next nextMemory ∧
        before.lastDown = none ∧ choice.lastDown = none ∧ next.lastDown = none ∧
        before.status = .unoccupied ∧ choice.status = .unoccupied ∧ next.status = .unoccupied ∧
        (ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time →
          let own := record.output.preparation.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i)
          let word := CoordinatorLocalArmChoice.storedDownFlatWord rB.payload i
          ∃ logged,
            let cut := ReferenceDownReception.referenceDownCut p (dispatch record.input).downView
              i record.input.row record.input.time own rate logged
            ActiveFollowerLogging.checkedLogging i record.input.row (record.input.state.activations i)
              record.input.time (((record.output.preparation.followers.followers i).arm), own) choice = .ok logged ∧
            (record.output.followers i).downInput = some logged ∧
            (record.output.followers i).down = some cut ∧
            logged.lastDown = none ∧ logged.status = .unoccupied ∧
            logged.downBatch = choice.downBatch ∧
            ReferenceActiveAffinePositiveTest.downSent record.input = some word ∧
            ReferenceDownReception.expectedDownFlatWord (some selected.view) i record.input.row record.input.time = some word ∧
            cut.expectedWord = some word ∧
            ReferenceDownReception.ordinaryParse p rate (some word) = some (rB.payload.downRecord i) ∧
            OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta) (acceptedStart logged)
              (record.input.time.val + 1) (rB.payload.downRecord i) ∧
            ActiveFollowerDownAcceptance.registerInputDomain p rate logged ∧
            ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch ∧
            ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer ∧
            cut.rawComparison.isSome = true ∧
            cut.raw = (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time own rate logged).2 ∧
            next = { logged with downBatch :=
              (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time own rate logged).1 } ∧
            ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time own rate choice =
              ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time own rate logged ∧
            (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time own rate logged).sample =
              ReferenceDownPhysicalHashRule.originalDownSample record.input ∧
            (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time own rate logged).roundedReward = own.val.val ∧
            (record.output.preparation.followers.followers i).time = record.input.time ∧
            (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2 = own ∧
            (0 < own.val.val → AffineChannelLaw.affineHash
              (ReferenceDownPhysicalHashRule.originalDownSample record.input) word = 1)) := by
  classical
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span mode
  let B := ReferenceActivePhysicalHorizon.run initial rows J rewards start b (by omega) mode
  have he : B.records = E.records.take b := prefix_records initial rows J rewards start count span mode b hb
  obtain ⟨hpos, hselections⟩ := run_first_unaccepted_selections initial rows J rewards start count span mode
    hfirst hseed b hb hwindow rB qB baseB hcoord i sB memoryB hfocal hnone
  refine ⟨hpos, ?_⟩
  intro record hr
  obtain ⟨selected, hselected, hpayload, hpending⟩ := hselections record hr
  have hrB : record ∈ B.records := by rw [he]; exact hr
  have hrE : record ∈ E.records := List.mem_of_mem_take hr
  obtain ⟨a, ha, htime, hstate⟩ := ReferenceSelectedPayloadChronology.actualRunRecord_has_prefix
    initial rows J rewards start b (by omega) mode record hrB
  obtain ⟨n, hn, helem⟩ := List.mem_iff_getElem.mp hrB
  obtain ⟨before, beforeMemory, choice, choiceMemory, next, nextMemory,
    hbconfig, hcconfig, hnconfig, hbn, hcn, hnn, hbu, hcu, hnu⟩ :=
    connected_unaccepted_record B.connected hseed i sB memoryB hfocal hnone n hn
  rw [helem] at hbconfig hcconfig hnconfig
  obtain ⟨birth, hbirth, hborn, hbirthTime, hbeforeTime⟩ :=
    ReferenceSelectedPayloadChronology.actualRun_selectedPayload_has_birth initial rows J rewards
      start count span mode hfirst record selected hrE hselected
  rw [hpayload] at hbeforeTime
  obtain ⟨hrows, hJ, hrewards⟩ := ReferenceActivePhysicalHorizon.run_record_inputs
    initial rows J rewards start count span mode record hrE
  refine ⟨a, ha, selected, before, beforeMemory, choice, choiceMemory, next, nextMemory,
    htime, hstate, hrows, hJ, hrewards, hselected, hpayload, hpending, hbeforeTime,
    hbconfig, hcconfig, hnconfig, hbn, hcn, hnn, hbu, hcu, hnu, ?_⟩
  intro hdown own word
  have hc' : ((prepare record.input).followers.followers i).configuration = .ordinary choice choiceMemory := by
    change (record.output.preparation.followers.followers i).configuration = _ at hcconfig
    rw [record.output_eq] at hcconfig
    exact hcconfig
  have hn' : (step record.input).next.followers i = .ordinary next nextMemory := by
    rw [← record.output_eq]; exact hnconfig
  obtain ⟨logged, hlog, hdi, hd, hln, hlu, hreg, hbatch, hbuffer, hcall, hraw, hnext⟩ :=
    selected_unaccepted_down_call record.input i choice next choiceMemory nextMemory
      hc' hn' hcu hcn hnn hdown
  have hown : (prepare record.input).feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i) = own := by
    dsimp only [own]; rw [record.output_eq]; rfl
  rw [hown] at hlog hd hcall hraw hnext
  have hlogActual : ActiveFollowerLogging.checkedLogging i record.input.row
      (record.input.state.activations i) record.input.time
      ((record.output.preparation.followers.followers i).arm, own) choice = .ok logged := by
    rw [record.output_eq]; exact hlog
  rw [← record.output_eq] at hdi hd
  have frame := ActiveFollowerLogging.checkedLogging_success_frame _ _ _ _ _ _ _ hlogActual
  have hselected' : (prepare record.input).coordinator.selection = some selected := by
    have hs := hselected
    rw [record.output_eq] at hs
    exact hs
  have hview : (dispatch record.input).downView = some selected.view := by
    change (prepare record.input).coordinator.selection.map (fun s => s.view) = _
    rw [hselected']; rfl
  have hbranch : ReferenceDownReception.selectedDownSenderBranch selected.view i
      record.input.row record.input.time := ⟨hdown.1, hdown.2, hpending⟩
  have hexpected := (ReferenceAssignmentPayloadChronology.actualSelection_expectedDownFlatWord_of_payload_eq
    record selected hselected rB.payload hpayload i hbranch).1
  have hindex : upSenderIndex record.input = i :=
    (ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw record.input).trans hdown.2
  have hsent : ReferenceActiveAffinePositiveTest.downSent record.input = some word := by
    unfold ReferenceActiveAffinePositiveTest.downSent
    rw [hindex, hview]
    exact hexpected
  have hcutExpected : (ReferenceDownReception.referenceDownCut p (dispatch record.input).downView
      i record.input.row record.input.time own rate logged).expectedWord = some word := by
    simp only [ReferenceDownReception.referenceDownCut, dite_eq_left hdown,
      dite_eq_left hlu, dite_eq_left hreg, dite_eq_left hbatch, dite_eq_left hbuffer]
    split <;> (rw [hview]; exact hexpected)
  have hparse : ReferenceDownReception.ordinaryParse p rate (some word) = some (rB.payload.downRecord i) := by
    change OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
      (some ((OrdinaryMessageCodec.wordEquivFlat _).symm
        ((OrdinaryMessageCodec.wordEquivFlat _) (rB.payload.downWord i)))) = _
    rw [Equiv.symm_apply_apply, rB.payload.parseDown_downWord i]
  have haccept : OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta) (acceptedStart logged)
      (record.input.time.val + 1) (rB.payload.downRecord i) := by
    constructor
    · change acceptedStart logged < rB.payload.sigma.val + 1
      simp only [acceptedStart, hln]
      omega
    · change rB.payload.sigma.val + 1 ≤ record.input.time.val + 1
      omega
  have hinput : ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time own rate choice =
      ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time own rate logged := by
    simp only [ActiveFollowerDownAcceptance.currentRoundInput, hcu, hlu]
  have hsample : (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time own rate logged).sample =
      ReferenceDownPhysicalHashRule.originalDownSample record.input := by
    change (record.input.row.2 record.input.time).2 (0, i) = _
    unfold ReferenceDownPhysicalHashRule.originalDownSample
    rw [hindex]
  have htimeChoice := (record.output.preparation.follower_alignment i).2.2.1
  have hentry : (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2 = own := by
    rw [record.output_eq]
    change ((prepare record.input).feedback.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2 = own
    rw [(prepare record.input).feedback.ownEntries_eq]
    exact hown
  refine ⟨logged, hlogActual, hdi, hd, hln, hlu, frame.2.2.2.2.2.1, hsent, hexpected,
    hcutExpected, hparse, haccept, hreg, hbatch, hbuffer, hcall, hraw, hnext, hinput,
    hsample, rfl, htimeChoice, hentry, ?_⟩
  intro hpositive
  have hp : ReferenceActiveAffinePositiveTest.downPositive record.input = true := by
    rw [ReferenceActiveAffinePositiveTest.downPositive_eq_diagnostic, hindex]
    change (ReferenceActiveAffinePositiveTest.downDiagnosticCall ((step record.input).followers i) &&
      decide (0 < ((prepare record.input).feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val)) = true
    rw [hown, ← record.output_eq]
    simp only [ReferenceActiveAffinePositiveTest.downDiagnosticCall, hd, hcall,
      hpositive, decide_true, Bool.true_and]
  exact ReferenceDownPhysicalHashRule.downPositive_sent_hash_one record.input word hsent hp

section ActualLaunch

variable
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : ReferenceActivePhysicalStep.RateInput p) (C_star C_h : ℝ)
    (boundary : ReferenceInitializationRun.Boundary p)
    (hboundary : boundary.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock boundary hboundary))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock boundary hboundary) actual boundary past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) boundary hboundary i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) boundary hboundary).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) boundary hboundary)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) boundary hboundary i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock boundary hboundary) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock boundary hboundary)
        source rewards actual)).disposition = .launched launch learnerSeed)

/-- Source-root specialization on the genuine launched boundary. All original
initialization, private-source, reward, shared-constant, replay and handoff
inputs remain in the telescope. The ordinary initial seed is produced by K. -/
theorem ofActualLaunchedBoundary_first_unaccepted_down_epoch (count : ℕ)
    (span : BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock boundary hboundary) + count ≤ p.T) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary
      source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let rows := source.1.2
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock boundary hboundary)
    let mode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start :=
      fun j => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce launch learnerSeed hlaunched j
    ∀ (b : ℕ) (hb : b ≤ count)
    (hwindow : b ≤ (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span mode).records).length)
    (rB : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (qB : CoordinatorLiveServiceFinish.OwnedRegisters rB) (baseB : Fin (p.m - 1) → ℕ)
    (hcoord : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b (by omega) mode).finalState.coordinator =
      .live rB qB baseB)
    (i : Fin (p.m - 1)) (sB : ReferencePrelaunchFollower.State p rate.eta)
    (memoryB : ActiveFollowerLifecycle.LocalMemory p)
    (hfocal : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b (by omega) mode).finalState.followers i =
      .ordinary sB memoryB) (hnone : sB.lastDown = none),
    0 < b ∧ ∀ record ∈ (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span mode).records.take b,
      ∃ (a : ℕ) (_ha : a < b) (selected : Selection record.input)
        (before : ReferencePrelaunchFollower.State p rate.eta)
        (beforeMemory : ActiveFollowerLifecycle.LocalMemory p)
        (choice : ReferencePrelaunchFollower.State p rate.eta)
        (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
        (next : ReferencePrelaunchFollower.State p rate.eta)
        (nextMemory : ActiveFollowerLifecycle.LocalMemory p),
        record.input.time.val = start + a ∧
        record.input.state = (ReferenceActivePhysicalHorizon.run initial rows J rewards start a (by omega) mode).finalState ∧
        record.input.rows = rows ∧ record.input.selected = J ∧ record.input.rewards = rewards ∧
        record.output.preparation.coordinator.selection = some selected ∧
        selected.view.payload = rB.payload ∧ i ∈ selected.view.pendingAtChoice ∧
        rB.payload.sigma.val ≤ record.input.time.val ∧
        record.input.state.followers i = .ordinary before beforeMemory ∧
        (record.output.preparation.followers.followers i).configuration = .ordinary choice choiceMemory ∧
        record.output.next.followers i = .ordinary next nextMemory ∧
        before.lastDown = none ∧ choice.lastDown = none ∧ next.lastDown = none ∧
        before.status = .unoccupied ∧ choice.status = .unoccupied ∧ next.status = .unoccupied ∧
        (ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time →
          let own := record.output.preparation.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i)
          let word := CoordinatorLocalArmChoice.storedDownFlatWord rB.payload i
          ∃ logged,
            let cut := ReferenceDownReception.referenceDownCut p (dispatch record.input).downView
              i record.input.row record.input.time own rate logged
            ActiveFollowerLogging.checkedLogging i record.input.row (record.input.state.activations i)
              record.input.time (((record.output.preparation.followers.followers i).arm), own) choice = .ok logged ∧
            (record.output.followers i).downInput = some logged ∧
            (record.output.followers i).down = some cut ∧
            logged.lastDown = none ∧ logged.status = .unoccupied ∧
            logged.downBatch = choice.downBatch ∧
            ReferenceActiveAffinePositiveTest.downSent record.input = some word ∧
            ReferenceDownReception.expectedDownFlatWord (some selected.view) i record.input.row record.input.time = some word ∧
            cut.expectedWord = some word ∧
            ReferenceDownReception.ordinaryParse p rate (some word) = some (rB.payload.downRecord i) ∧
            OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta) (acceptedStart logged)
              (record.input.time.val + 1) (rB.payload.downRecord i) ∧
            ActiveFollowerDownAcceptance.registerInputDomain p rate logged ∧
            ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch ∧
            ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer ∧
            cut.rawComparison.isSome = true ∧
            cut.raw = (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time own rate logged).2 ∧
            next = { logged with downBatch :=
              (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time own rate logged).1 } ∧
            ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time own rate choice =
              ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time own rate logged ∧
            (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time own rate logged).sample =
              ReferenceDownPhysicalHashRule.originalDownSample record.input ∧
            (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time own rate logged).roundedReward = own.val.val ∧
            (record.output.preparation.followers.followers i).time = record.input.time ∧
            (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2 = own ∧
            (0 < own.val.val → AffineChannelLaw.affineHash
              (ReferenceDownPhysicalHashRule.originalDownSample record.input) word = 1)) := by
  dsimp only
  intro b hb hwindow rB qB baseB hcoord i sB memoryB hfocal hnone
  exact run_first_unaccepted_down_epoch _ source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards _ count span _
    (ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator
      source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce launch learnerSeed hlaunched)
    (ReferenceFirstLiveConfirmationHistory.ofActualLaunchedBoundary_initialFollowers
      source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce launch learnerSeed hlaunched)
    b hb hwindow rB qB baseB hcoord i sB memoryB hfocal hnone

end ActualLaunch

end Bandits.Support.ReferenceFirstUnacceptedDownEpoch

end
