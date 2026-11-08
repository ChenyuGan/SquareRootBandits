/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActiveDataOwnership
public import Bandits.Support.ReferenceActiveConfirmationRelease
public import Bandits.Support.ReferenceFollowerReplyChronology
public import Bandits.Support.ReferenceCollectionPhaseHistory

import Mathlib.Data.List.TakeWhile

/-!
# The actual first live confirmation window

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-124`,
`sources/zip4/manuscript/06_interruptions.tex:246-275,286-295,303-324`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:100-104`.

The window is the original computed physical run before its first chosen
cutoff. It retains failed rounds; it does not stop physical play. These are
internal status and accepted-DOWN history results for the first-live components
of AppA:100-104 and `LocalReleaseQuota.LocalReleaseTrace`. The confirmation
witness explicitly requires the actual selected follower's ordinary CHOICE;
dagger supplies no arm or collision-free assertion. Replacement initialization,
no-newer-DOWN after accepted UP, first-cutoff alignment, all-player safety,
truthful Gamma/B registers, full local-domain preservation, decoder probability,
and manuscript closure are separate obligations.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstLiveConfirmationHistory

open ConstructorDimensions
open ReferenceActivePhysicalStep


local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {p : Parameters} {rate : RateInput p}

abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev DownRecord := OrdinaryMessageCodec.DownRecord
  (ReferencePrelaunchFollower.codecParams p rate.eta)

/-- The analytical prefix of the original records, excluding the first
actual chosen cutoff. Failure records before that cutoff remain present. -/
def firstLiveWindow (records : List (Record (p := p) (rate := rate))) :=
  records.takeWhile (fun r => !ReferenceCollectionPhaseHistory.cutoffChosen r.input)

/-- An exact record accepted in this round's retained filtered diagnostics.
This says more than equality of the accepted start alone. -/
def AcceptedDown (r : Record (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (M : DownRecord (p := p) (rate := rate)) : Prop :=
  ∃ logged cut after raw scan registers lastService,
    (r.output.followers i).downInput = some logged ∧
    (r.output.followers i).down = some cut ∧
    cut.outcome = ActiveFollowerDownAcceptance.LocalDownResult.accepted
      logged after raw M scan registers lastService

/-- The actual generic initial condition permits dagger followers. Only an
ordinary initial follower is required to be unoccupied with no accepted DOWN. -/
def InitialFollowers (state : State p rate) : Prop :=
  ∀ i s memory, state.followers i = .ordinary s memory →
    s.status = .unoccupied ∧ s.lastDown = none

/-- Literal carried-state induction datum before the first chosen cutoff.
Dagger has no local arm, field, or collision-free assertion. -/
def FirstLiveState (state : State p rate) : Prop :=
  match state.coordinator with
  | .first => InitialFollowers state
  | .live r _ _ => ReferenceActiveDataOwnership.carriedOccupiedFields r.payload state ∧
      ∀ i s memory, state.followers i = .ordinary s memory →
        r.pendingAtChoice.Nonempty → s.status ≠ .released
  | .collection _ _ _ => False
  | .dagger => True

private theorem prepare_not_released (x : RoundInput p rate) (i : Fin (p.m - 1))
    (hbefore : ∀ s memory, x.state.followers i = .ordinary s memory →
      s.status ≠ .released)
    (s : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : ((prepare x).followers.followers i).configuration = .ordinary s memory) :
    s.status ≠ .released := by
  obtain ⟨before, beforeMemory, _, hi, hs, _⟩ := ReferenceActiveDataOwnership.prepare_ordinary_choice i x.row
    (x.state.activations i) x.time (x.active i) (x.state.followers i) s memory hc
  rcases ReferenceActiveDataOwnership.startRound_status x.time before s beforeMemory memory hs with hu | he
  · rw [hu]; decide
  · rw [he]; exact hbefore before beforeMemory hi

private theorem referenceDown_not_released
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (before after : ReferencePrelaunchFollower.State p rate.eta)
    (hb : before.status ≠ .released)
    (h : DeclaredFollowerLocalRound.consumeDownResult rate
      (ReferenceDownReception.referenceDownCut p view i row t observation rate before).outcome =
        .ok after) : after.status ≠ .released := by
  simp only [ReferenceDownReception.referenceDownCut] at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · split at h
            · split at h
              · cases h; exact hb
              · split at h
                · split at h
                  · cases h
                  · cases h
                    split
                    · exact (by decide : ActiveRoundActions.FollowerStatus.pending ≠ .released)
                    · exact (by decide : ActiveRoundActions.FollowerStatus.unoccupied ≠ .released)
                · cases h; exact hb
            · cases h; exact hb
          · cases h
        · cases h
      · cases h
    · cases h; exact hb
  · cases h; exact hb

private theorem record_unoccupied_not_released
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choice post : ReferencePrelaunchFollower.State p rate.eta)
    (hu : choice.status = .unoccupied)
    (h : (recordFollower view i row activation t active arm observation choice).result =
      .ok post) : post.status ≠ .released := by
  rw [recordFollower, dite_eq_left hu] at h
  cases hl : ActiveFollowerLogging.checkedLogging i row activation t (arm, observation) choice with
  | error reason => simp only [hl] at h; cases h
  | ok logged =>
      simp only [hl] at h
      apply referenceDown_not_released view i row t observation logged post _ h
      have hf := ActiveFollowerLogging.checkedLogging_success_frame i row activation
        t (arm, observation) choice logged hl
      rw [hf.2.2.2.2.1, hu]
      decide

/-- Successful ordinary output supplies its own service and finish equations.
No tail-success hypotheses are supplied to this first-live status step. -/
theorem selected_output_not_released (x : RoundInput p rate) (selected : Selection x)
    (hselected : (prepare x).coordinator.selection = some selected)
    (hn : selected.view.pendingAtChoice.Nonempty)
    (i : Fin (p.m - 1))
    (hfields : ReferenceActiveDataOwnership.occupiedFields selected.view.payload i
      ((prepare x).followers.followers i).configuration)
    (hchoice : ∀ s memory,
      ((prepare x).followers.followers i).configuration = .ordinary s memory →
      s.status ≠ .released)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : (step x).next.followers i = .ordinary next nextMemory) :
    next.status ≠ .released := by
  obtain ⟨choice, memory, post, hc, hr, hf, _, _⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion _ _ _ next nextMemory hout
  have hnr := hchoice choice memory hc
  rw [hc] at hfields
  by_cases hu : choice.status = .unoccupied
  · have hp := record_unoccupied_not_released _ _ _ _ _ _ _ _ choice post hu hr
    have hs := (ReferenceActiveDataOwnership.releaseAndFinish_fields _ _ _ _ choice post next memory nextMemory hf).2 hu
    rw [hs]; exact hp
  · have hpend : choice.status = .pending := by
      cases hs : choice.status <;> simp_all
    have hp := ReferenceActiveConfirmationRelease.pending_choice_successful_finish_preserves_status (prepare x)
      selected hselected i choice memory hn hc hpend (hfields hu) post hr next nextMemory hf
    rw [hp.2.1]
    decide

private theorem confirmation_subset (x : RoundInput p rate) (prepared : PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (started : CoordinatorPhaseClock.StartRoundResult p) (pending : Finset (Fin (p.m - 1)))
    (h : CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time x.row prepared.coordinatorObservation = some pending) :
    pending ⊆ started.pending := by
  change CoordinatorLocalArmChoice.confirmationUpdateCore r.payload started.pending
    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time
    (x.row.2 x.time) prepared.coordinatorObservation = some pending at h
  by_cases hv : CoordinatorLocalArmChoice.ConfirmationInputsValid r.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time
  · by_cases hevent : CoordinatorLocalArmChoice.downConfirmationEvent r.payload
        started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
        x.time (x.row.2 x.time) prepared.coordinatorObservation
    · rw [CoordinatorLocalArmChoice.confirmationUpdateCore_removes _ _ _ _ _ _ hv hevent] at h
      cases h
      exact Finset.erase_subset _ _
    · rw [CoordinatorLocalArmChoice.confirmationUpdateCore_preserves _ _ _ _ _ _ hv hevent] at h
      cases h
      exact Finset.Subset.refl _
  · simp only [CoordinatorLocalArmChoice.confirmationUpdateCore, dite_eq_right hv] at h
    cases h

/-- The successful live tail's pending set is the actual confirmation update
passed to the actual finish call. Errors remain coordinator dagger. -/
theorem livePostChoice_frame (x : RoundInput p rate) (prepared : PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    (livePostChoice prepared r q base started).configuration = .dagger ∨
      ∃ next owned,
        (livePostChoice prepared r q base started).configuration = .live next owned base ∧
        next.payload = r.payload ∧ next.pendingAtChoice ⊆ started.pending := by
  unfold livePostChoice
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · rename_i recording hrecord serviced hservice pending hpending
        split
        · exact Or.inl rfl
        · rename_i finished hfinish
          refine Or.inr ⟨_, _, rfl, rfl, ?_⟩
          rw [CoordinatorPhaseClock.finishRound_pending_frame p rate.eta.val x.time
            started.clock pending x.row finished hfinish]
          exact confirmation_subset x prepared r started pending hpending

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

private theorem selectionAt_fields (x : RoundInput p rate) (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (arm : CoordinatorRoundDispatch.ArmSelection payload started time weights x.row)
    (selected : Selection x) (h : selectionAt x payload started time weights arm = some selected) :
    selected.view.payload = payload ∧ selected.view.pendingAtChoice = started.pending := by
  unfold selectionAt at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

/-- Derive the carried current-record and no-release inputs from the actual
first/continuing-live dispatcher. The cutoff test is the literal selector. -/
theorem selected_carried (x : RoundInput p rate) (hs : FirstLiveState x.state)
    (hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen x = false)
    (selected : Selection x) (hselected : (prepare x).coordinator.selection = some selected) :
    ReferenceActiveDataOwnership.carriedOccupiedFields selected.view.payload x.state ∧
      ∀ i s memory, x.state.followers i = .ordinary s memory →
        selected.view.pendingAtChoice.Nonempty → s.status ≠ .released := by
  change (dispatch x).selection = some selected at hselected
  cases hc : x.state.coordinator with
  | first =>
      have hseed : InitialFollowers x.state := by simpa only [FirstLiveState, hc] using hs
      constructor
      · intro i
        cases hf : x.state.followers i with
        | dagger => trivial
        | ordinary s memory =>
            intro ho
            exact (ho (hseed i s memory hf).1).elim
      · intro i s memory hf _
        rw [(hseed i s memory hf).1]
        decide
  | dagger => simp only [dispatch, hc, DispatchCut.selection] at hselected; cases hselected
  | collection payload ledger proposal => simp only [FirstLiveState, hc] at hs
  | live r q base =>
      have hstored : ReferenceActiveDataOwnership.carriedOccupiedFields r.payload x.state ∧
          ∀ i s memory, x.state.followers i = .ordinary s memory →
            r.pendingAtChoice.Nonempty → s.status ≠ .released := by
        simpa only [FirstLiveState, hc] using hs
      have hd : dispatch x = .live r q base
          (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
        simp only [dispatch, hc, CoordinatorRoundDispatch.dispatch]
        rfl
      rw [hd] at hselected
      cases ho : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base) with
      | continuingChosen dispatched hstart continuation arm =>
          rw [ho] at hselected
          have hf := selectionAt_fields x r.payload dispatched.startResult x.time
            (liveRegistersAt r x.time).complementWeights arm selected hselected
          have hp := dispatchLive_continuing_pending (liveInput x r q base)
            dispatched hstart continuation arm ho
          change dispatched.startResult.pending = r.pendingAtChoice at hp
          rw [hf.1]
          refine ⟨hstored.1, ?_⟩
          intro i s memory hi hn
          apply hstored.2 i s memory hi
          simpa only [hf.2, hp] using hn
      | cutoffChosen =>
          simp only [ReferenceCollectionPhaseHistory.cutoffChosen, prepare, hd, ho, Bool.true_eq_false] at hcutoff
      | clockFailure => simp only [ho, DispatchCut.selection] at hselected; cases hselected
      | initializerFailure => simp only [ho, DispatchCut.selection] at hselected; cases hselected
      | localFailure => simp only [ho, DispatchCut.selection] at hselected; cases hselected

/-- The actual ordinary choice inherits both carried first-live invariants.
An interrupted follower may become unoccupied. Dagger yields no assertion. -/
theorem selected_choice (x : RoundInput p rate) (hs : FirstLiveState x.state)
    (hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen x = false)
    (selected : Selection x) (hselected : (prepare x).coordinator.selection = some selected)
    (i : Fin (p.m - 1)) (s : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : ((prepare x).followers.followers i).configuration = .ordinary s memory) :
    (s.status ≠ .unoccupied → s.lastDown = some (selected.view.payload.downRecord i)) ∧
      (selected.view.pendingAtChoice.Nonempty → s.status ≠ .released) := by
  obtain ⟨hfields, hnr⟩ := selected_carried x hs hcutoff selected hselected
  have hf := ReferenceActiveDataOwnership.choice_occupied_fields_preserved selected.view.payload
    i x.row (x.state.activations i) x.time (x.active i) (x.state.followers i) (hfields i)
  rw [show (DeclaredFollowerLocalRound.prepare rate i x.row (x.state.activations i)
    x.time (x.active i) (x.state.followers i)).configuration = .ordinary s memory from hc] at hf
  refine ⟨hf, ?_⟩
  intro hn
  exact prepare_not_released x i (fun before mem hi => hnr i before mem hi hn) s memory hc

private theorem tail_firstLive (x : RoundInput p rate) (hs : FirstLiveState x.state)
    (hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen x = false)
    (selected : Selection x) (hselected : (prepare x).coordinator.selection = some selected)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hcoord : (step x).next.coordinator = (livePostChoice (prepare x) r q base started).configuration)
    (hpayload : selected.view.payload = r.payload)
    (hpending : selected.view.pendingAtChoice = started.pending) :
    FirstLiveState (step x).next := by
  rcases livePostChoice_frame x (prepare x) r q base started with hd | ⟨next, owned, hn, hp, hsub⟩
  · simp only [FirstLiveState, hcoord, hd]
  · have hnext : (step x).next.coordinator = .live next owned base := hcoord.trans hn
    simp only [FirstLiveState, hnext]
    have heq : next.payload = selected.view.payload := hp.trans hpayload.symm
    constructor
    · rw [heq]
      exact ReferenceActiveDataOwnership.step_occupied_fields x selected hselected
        (selected_carried x hs hcutoff selected hselected).1
    · intro i s memory hi hnonempty
      have hnonempty' : selected.view.pendingAtChoice.Nonempty := by
        rw [hpending]
        exact hnonempty.mono hsub
      have hfields := ReferenceActiveDataOwnership.choice_occupied_fields_preserved selected.view.payload
        i x.row (x.state.activations i) x.time (x.active i) (x.state.followers i)
        ((selected_carried x hs hcutoff selected hselected).1 i)
      apply selected_output_not_released x selected hselected hnonempty' i hfields _ s memory hi
      intro choice mem hc
      exact (selected_choice x hs hcutoff selected hselected i choice mem hc).2 hnonempty'

/-- One actual physical step before the first chosen cutoff. A successful
selection runs its actual recorder/service/confirmation/finish tail. Dispatch
and tail failures remain absorbing coordinator dagger. -/
theorem firstLive_step (x : RoundInput p rate) (hs : FirstLiveState x.state)
    (hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen x = false) :
    FirstLiveState (step x).next := by
  cases hc : x.state.coordinator with
  | dagger =>
      simp only [FirstLiveState, (step_coordinator_dagger x hc).1]
  | collection payload ledger proposal => simp only [FirstLiveState, hc] at hs
  | first =>
      have hd : (prepare x).coordinator = .first
          (CoordinatorRoundDispatch.dispatchFirst (firstInput x)) := dispatch_first x hc
      have he := observeCoordinator_first_equation (prepare x) _ hd
      cases ho : CoordinatorRoundDispatch.dispatchFirst (firstInput x) with
      | choiceDomainFailure installed =>
          simp only [step, he, ho, DispatchCut.selection, ite_true, coordinatorFailure,
            FirstLiveState]
      | recorderBoundaryFailure installed =>
          simp only [step, he, ho, DispatchCut.selection, ite_true, coordinatorFailure,
            FirstLiveState]
      | choiceRejected installed =>
          simp only [step, he, ho, DispatchCut.selection, ite_true, coordinatorFailure,
            FirstLiveState]
      | chosen installed arm =>
          cases hsel : (DispatchCut.first (.chosen installed arm)).selection with
          | none =>
              simp only [step, he, ho, hsel, ite_true, coordinatorFailure,
                FirstLiveState]
          | some selected =>
              have hselected : (prepare x).coordinator.selection = some selected := by
                rw [hd, ho]; exact hsel
              obtain ⟨hp, hn⟩ := selectionAt_fields x installed.registers.payload
                installed.startRoundResult installed.registers.time
                installed.registers.complementWeights arm selected hsel
              apply tail_firstLive x hs hcutoff selected hselected installed.registers
                installed.ownedRegisters installed.followerBaseScore installed.startRoundResult _ hp hn
              change (prepare x).observeCoordinator.configuration = _
              rw [he, ho, hsel]
              rfl
  | live r q base =>
      have hd : (prepare x).coordinator = .live r q base
          (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
        change dispatch x = _
        simp only [dispatch, hc, CoordinatorRoundDispatch.dispatch]
        rfl
      have he := observeCoordinator_live_equation (prepare x) r q base _ hd
      cases ho : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base) with
      | clockFailure failure hfailure =>
          simp only [step, he, ho, DispatchCut.selection, ite_true, coordinatorFailure,
            FirstLiveState]
      | initializerFailure dispatched hstart checked hchecked =>
          simp only [step, he, ho, DispatchCut.selection, ite_true, coordinatorFailure,
            FirstLiveState]
      | localFailure dispatched hstart reason =>
          simp only [step, he, ho, DispatchCut.selection, ite_true, coordinatorFailure,
            FirstLiveState]
      | cutoffChosen =>
          simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hd, ho, Bool.true_eq_false] at hcutoff
      | continuingChosen dispatched hstart continuation arm =>
          cases hsel : (DispatchCut.live r q base
              (.continuingChosen dispatched hstart continuation arm)).selection with
          | none =>
              simp only [step, he, ho, hsel, ite_true, coordinatorFailure,
                FirstLiveState]
          | some selected =>
              have hselected : (prepare x).coordinator.selection = some selected := by
                rw [hd, ho]; exact hsel
              obtain ⟨hp, hn⟩ := selectionAt_fields x r.payload dispatched.startResult x.time
                (liveRegistersAt r x.time).complementWeights arm selected hsel
              apply tail_firstLive x hs hcutoff selected hselected (liveRegistersAt r x.time)
                (liveOwnedAt r q x.time) base dispatched.startResult _ hp hn
              change (prepare x).observeCoordinator.configuration = _
              rw [he, ho, hsel]
              rfl

private theorem connected_window_state
    {initial final : State p rate} (records : List (Record (p := p) (rate := rate)))
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hs : FirstLiveState initial) (a : ℕ) (ha : a < (firstLiveWindow records).length) :
    FirstLiveState (firstLiveWindow records)[a].input.state := by
  induction records generalizing initial a with
  | nil => simp only [firstLiveWindow, List.takeWhile_nil, List.length_nil] at ha; omega
  | cons r rs ih =>
      obtain ⟨hpre, hrest⟩ := chain
      cases hcut : ReferenceCollectionPhaseHistory.cutoffChosen r.input with
      | true =>
          simp only [firstLiveWindow, List.takeWhile_cons, hcut, Bool.not_true,
            Bool.false_eq_true, ite_false, List.length_nil] at ha
          omega
      | false =>
          have hw : firstLiveWindow (r :: rs) = r :: firstLiveWindow rs := by
            simp only [firstLiveWindow, List.takeWhile_cons, hcut, Bool.not_false, ite_true]
          cases a with
          | zero => simpa only [hw, List.getElem_cons_zero, hpre] using hs
          | succ a =>
              have hnext : FirstLiveState r.output.next := by
                rw [r.output_eq]
                exact firstLive_step r.input (hpre ▸ hs) hcut
              have ha' : a < (firstLiveWindow rs).length := by
                rw [hw, List.length_cons] at ha
                omega
              simpa only [hw, List.getElem_cons_succ] using ih hrest hnext a ha'

/-- Carried-state invariant at every actual retained input before the first
chosen cutoff, starting from the original computed run and generic seed. -/
theorem run_firstLive_carried (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first) (hseed : InitialFollowers initial) :
    let R := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan hmode
    let W := firstLiveWindow R.records
    ∀ a : Fin W.length, FirstLiveState W[a.val].input.state := by
  intro R W a
  apply connected_window_state R.records R.connected _ a.val a.isLt
  simpa only [FirstLiveState, hfirst] using hseed

/-- Current-record agreement and absence of released ordinary CHOICE while
confirmations are missing, on the exact computed first-live window. -/
theorem run_firstLive_no_released (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first) (hseed : InitialFollowers initial) :
    let R := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan hmode
    let W := firstLiveWindow R.records
    ∀ (a : Fin W.length) (selected : Selection W[a.val].input),
      (prepare W[a.val].input).coordinator.selection = some selected →
      ∀ (i : Fin (p.m - 1)) (s : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        ((prepare W[a.val].input).followers.followers i).configuration = .ordinary s memory →
        (s.status ≠ .unoccupied → s.lastDown = some (selected.view.payload.downRecord i)) ∧
          (selected.view.pendingAtChoice.Nonempty → s.status ≠ .released) := by
  intro R W a selected hselected i s memory hc
  have hs := run_firstLive_carried initial rows J rewards start count hspan hmode hfirst hseed a
  have hmem := List.mem_takeWhile_imp (List.getElem_mem a.isLt : W[a.val] ∈ W)
  have hcut : ReferenceCollectionPhaseHistory.cutoffChosen W[a.val].input = false := by
    simpa only [Bool.not_eq_true'] using hmem
  exact selected_choice W[a.val].input hs hcut selected hselected i s memory hc

private theorem record_down_origin (r : Record (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : r.output.next.followers i = .ordinary next nextMemory)
    (M : DownRecord (p := p) (rate := rate)) (hM : next.lastDown = some M) :
    (∃ before memory, r.input.state.followers i = .ordinary before memory ∧
      before.lastDown = some M) ∨ AcceptedDown r i M := by
  have hout' := hout
  rw [r.output_eq] at hout'
  obtain ⟨choice, memory, post, hc, hr, hf, hdi, hd⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion _ _ _ next nextMemory hout'
  have hc' : (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary choice memory := by
    rw [ReferenceFollowerFixedReply.actualChoice, r.output_eq]
    exact hc
  obtain ⟨before, beforeMemory, hbefore, hreply, _⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice r i choice memory hc'
  have hchoiceLast : choice.lastDown = before.lastDown := congrArg Prod.fst hreply
  have hnextLast := (ReferenceActiveDataOwnership.releaseAndFinish_fields
    _ _ _ _ choice post next memory nextMemory hf).1
  rcases ReferenceFollowerReplyChronology.recordFollower_ordinary_inversion
      _ _ _ _ _ _ _ _ choice post hr with hframe |
      ⟨logged, cut, raw, applied, scan, registers, lastService, hlogged, hcut, heq, ha, _, hlast⟩
  · exact Or.inl ⟨before, beforeMemory, hbefore,
      (hnextLast.trans (hframe.1.trans hchoiceLast)).symm.trans hM⟩
  · have hsame : applied = M := Option.some.inj ((hnextLast.trans hlast).symm.trans hM)
    subst applied
    refine Or.inr ⟨logged, cut, post, raw, scan, registers, lastService, ?_, ?_, ha⟩
    · rw [r.output_eq]
      exact hdi.trans hlogged
    · rw [r.output_eq]
      exact hd.trans hcut

private theorem connected_down_origin
    {initial final : State p rate} (records : List (Record (p := p) (rate := rate)))
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (i : Fin (p.m - 1)) (s : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : final.followers i = .ordinary s memory)
    (M : DownRecord (p := p) (rate := rate)) (hM : s.lastDown = some M) :
    (∃ before mem, initial.followers i = .ordinary before mem ∧ before.lastDown = some M) ∨
      ∃ r ∈ records, AcceptedDown r i M := by
  induction records generalizing initial with
  | nil =>
      subst final
      exact Or.inl ⟨s, memory, hc, hM⟩
  | cons r rs ih =>
      obtain ⟨hpre, hrest⟩ := chain
      rcases ih hrest with ⟨before, mem, hi, hm⟩ | ⟨record, hrecord, ha⟩
      · rcases record_down_origin r i before mem hi M hm with hbefore | ha
        · rw [hpre] at hbefore
          exact Or.inl hbefore
        · exact Or.inr ⟨r, List.mem_cons_self, ha⟩
      · exact Or.inr ⟨record, List.mem_cons_of_mem r hrecord, ha⟩

/-- Exact accepted-record origin on any prefix of the original run. An
ordinary present CHOICE excludes prior dagger for this follower by inversion;
all other followers may be dagger. No service truth or payload agreement is
assumed in this independent origin argument. -/
theorem run_choice_prior_down (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hseed : InitialFollowers initial) :
    let R := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan hmode
    ∀ (a : Fin R.records.length) (i : Fin (p.m - 1))
      (s : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      (ReferenceFollowerFixedReply.actualChoice R.records[a.val] i).configuration = .ordinary s memory →
      ∀ M : DownRecord (p := p) (rate := rate), s.lastDown = some M →
        ∃ (j : ℕ) (hj : j < a.val), AcceptedDown R.records[j] i M := by
  intro R a i s memory hc M hM
  obtain ⟨before, mem, hi, hreply, _⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice R.records[a.val] i s memory hc
  have hm : before.lastDown = some M := (congrArg Prod.fst hreply).symm.trans hM
  have chain := ReferenceFollowerReplyChronology.connected_take_to_input R.connected a.val a.isLt
  rcases connected_down_origin (R.records.take a.val) chain i before mem hi M hm with
    ⟨seed, seedMemory, hseedConfig, hseedLast⟩ | hw
  · rw [(hseed i seed seedMemory hseedConfig).2] at hseedLast
    cases hseedLast
  · obtain ⟨j, hj, ha⟩ := List.exists_mem_iff_getElem.mp hw
    have hja : j < a.val := lt_of_lt_of_le hj (List.length_take_le _ _)
    exact ⟨j, hja, by simpa only [List.getElem_take] using ha⟩

/-- A positive actual DOWN confirmation has a strictly earlier accepted DOWN
diagnostic for the exact current payload record, in the same first-live
window. The ordinary selected follower is explicit; other dagger cases remain. -/
theorem run_firstLive_confirmation_prior_down (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first) (hseed : InitialFollowers initial) :
    let R := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan hmode
    let W := firstLiveWindow R.records
    ∀ (a : Fin W.length) (selected : Selection W[a.val].input),
      (prepare W[a.val].input).coordinator.selection = some selected →
      let i : Fin (p.m - 1) := PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (W[a.val].input.row.2 W[a.val].input.time).1
      ∀ (s : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        ((prepare W[a.val].input).followers.followers i).configuration = .ordinary s memory →
        CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
          selected.view.pendingAtChoice selected.view.cutoff W[a.val].input.time
          (W[a.val].input.row.2 W[a.val].input.time)
          (prepare W[a.val].input).coordinatorObservation →
        ∃ (j : ℕ) (hj : j < a.val), AcceptedDown W[j] i (selected.view.payload.downRecord i) := by
  intro R W a selected hselected i s memory hc hevent
  have ho := ReferenceActiveConfirmationRelease.downConfirmationEvent_implies_occupied
    (prepare W[a.val].input) selected hselected s memory hc hevent
  have hoccupied : s.status ≠ .unoccupied := by
    rcases ho with hp | hr
    · rw [hp]; decide
    · rw [hr]; decide
  have hlast := (run_firstLive_no_released initial rows J rewards start count hspan hmode
    hfirst hseed a selected hselected i s memory hc).1 hoccupied
  have hprefix : W.IsPrefix R.records := List.takeWhile_prefix _
  have ha : a.val < R.records.length := lt_of_lt_of_le a.isLt hprefix.length_le
  have heqa : W[a.val] = R.records[a.val] := hprefix.getElem a.isLt
  have hc' : (ReferenceFollowerFixedReply.actualChoice R.records[a.val] i).configuration =
      .ordinary s memory := by
    rw [← heqa]
    change (W[a.val].output.preparation.followers.followers i).configuration = .ordinary s memory
    rw [(W[a.val]).output_eq]
    exact hc
  obtain ⟨j, hj, hdown⟩ := run_choice_prior_down initial rows J rewards start count hspan hmode
    hseed ⟨a.val, ha⟩ i s memory hc' (selected.view.payload.downRecord i) hlast
  have hjw : j < W.length := lt_trans hj a.isLt
  exact ⟨j, hj, by rw [hprefix.getElem hjw]; exact hdown⟩

private theorem window_no_cutoff (records : List (Record (p := p) (rate := rate)))
    (r : Record (p := p) (rate := rate)) (hr : r ∈ firstLiveWindow records) :
    ReferenceCollectionPhaseHistory.cutoffChosen r.input = false := by
  have h := List.mem_takeWhile_imp hr
  simpa only [Bool.not_eq_true'] using h

private theorem connected_firstLive_state
    {initial final : State p rate} (records : List (Record (p := p) (rate := rate)))
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hs : FirstLiveState initial)
    (hno : ∀ r ∈ records, ReferenceCollectionPhaseHistory.cutoffChosen r.input = false) :
    FirstLiveState final := by
  induction records generalizing initial with
  | nil => subst final; exact hs
  | cons r rs ih =>
      obtain ⟨hpre, hrest⟩ := chain
      have hn : FirstLiveState r.output.next := by
        rw [r.output_eq]
        exact firstLive_step r.input (hpre ▸ hs) (hno r List.mem_cons_self)
      exact ih hrest hn (fun record hr => hno record (List.mem_cons_of_mem r hr))

/-- The corresponding invariant on every computed carried prefix, including
the endpoint immediately before the first chosen cutoff. The prefix is a
shorter invocation of the same physical run on the same rows, J and rewards. -/
theorem run_firstLive_prefix_state (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first) (hseed : InitialFollowers initial) :
    let R := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan hmode
    let W := firstLiveWindow R.records
    ∀ (k : ℕ) (hk : k ≤ count), k ≤ W.length →
      FirstLiveState (ReferenceActivePhysicalHorizon.run initial rows J rewards start k
        (by omega) hmode).finalState := by
  intro R W k hk hkw
  let before := ReferenceActivePhysicalHorizon.run initial rows J rewards start k (by omega) hmode
  have hbefore : before.records.IsPrefix R.records := by
    obtain ⟨suffix, he⟩ := ReferenceCollectionPhaseHistory.run_records_prefix initial rows J
      rewards start k (count - k) (by omega) hmode
    exact ⟨suffix, by simpa only [Nat.add_sub_of_le hk] using he.symm⟩
  have hwindow : W.IsPrefix R.records := List.takeWhile_prefix _
  have hlength : before.records.length = k :=
    ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start k (by omega) hmode
  apply connected_firstLive_state before.records before.connected
    (by simpa only [FirstLiveState, hfirst] using hseed)
  intro r hr
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hr
  have hjw : j < W.length := by rw [hlength] at hj; omega
  have he : before.records[j] = W[j] :=
    (hbefore.getElem hj).trans (hwindow.getElem hjw).symm
  apply window_no_cutoff R.records r
  rw [← heq, he]
  exact List.getElem_mem hjw

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

/-- The actual replay buffers and DOWN batches are retained by the existing
launch conversion. Its register theorem supplies the ordinary unoccupied,
no-accepted-DOWN seed; no replay state is fabricated here. -/
theorem ofActualLaunchedBoundary_initialFollowers :
    InitialFollowers
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched) := by
  intro i s memory hi
  obtain ⟨before, mem, hb, hn, _, _, _, _, hu, _⟩ :=
    ActualInitializationLaunchState.ofActualLaunchedBoundary_follower_registers
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
  rw [hi] at hb
  cases hb
  exact ⟨hu, hn⟩

/-- Actual-boundary specialization with the original whole source rows,
private selected J, rewards, shared constants, replay and launch inputs. -/
theorem ofActualLaunchedBoundary_firstLive_carried (count : ℕ)
    (hspan : BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) +
      count ≤ p.T) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start :=
      fun i => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
    let R := ReferenceActivePhysicalHorizon.run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode
    let W := firstLiveWindow R.records
    ∀ a : Fin W.length, FirstLiveState W[a.val].input.state := by
  dsimp only
  exact run_firstLive_carried _ _ _ _ _ count hspan _
    (ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
    (ofActualLaunchedBoundary_initialFollowers
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)

/-- Actual-boundary specialization with the original whole source rows,
private selected J, rewards, shared constants, replay and launch inputs. -/
theorem ofActualLaunchedBoundary_firstLive_no_released (count : ℕ)
    (hspan : BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) +
      count ≤ p.T) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start :=
      fun i => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
    let R := ReferenceActivePhysicalHorizon.run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode
    let W := firstLiveWindow R.records
    ∀ (a : Fin W.length) (selected : Selection W[a.val].input),
      (prepare W[a.val].input).coordinator.selection = some selected →
      ∀ (i : Fin (p.m - 1)) (s : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        ((prepare W[a.val].input).followers.followers i).configuration = .ordinary s memory →
        (s.status ≠ .unoccupied → s.lastDown = some (selected.view.payload.downRecord i)) ∧
          (selected.view.pendingAtChoice.Nonempty → s.status ≠ .released) := by
  dsimp only
  exact run_firstLive_no_released _ _ _ _ _ count hspan _
    (ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
    (ofActualLaunchedBoundary_initialFollowers
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)

/-- Actual-boundary specialization with the original whole source rows,
private selected J, rewards, shared constants, replay and launch inputs. -/
theorem ofActualLaunchedBoundary_firstLive_confirmation_prior_down (count : ℕ)
    (hspan : BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) +
      count ≤ p.T) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start :=
      fun i => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
    let R := ReferenceActivePhysicalHorizon.run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode
    let W := firstLiveWindow R.records
    ∀ (a : Fin W.length) (selected : Selection W[a.val].input),
      (prepare W[a.val].input).coordinator.selection = some selected →
      let i : Fin (p.m - 1) := PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (W[a.val].input.row.2 W[a.val].input.time).1
      ∀ (s : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        ((prepare W[a.val].input).followers.followers i).configuration = .ordinary s memory →
        CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
          selected.view.pendingAtChoice selected.view.cutoff W[a.val].input.time
          (W[a.val].input.row.2 W[a.val].input.time)
          (prepare W[a.val].input).coordinatorObservation →
        ∃ (j : ℕ) (hj : j < a.val), AcceptedDown W[j] i (selected.view.payload.downRecord i) := by
  dsimp only
  exact run_firstLive_confirmation_prior_down _ _ _ _ _ count hspan _
    (ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
    (ofActualLaunchedBoundary_initialFollowers
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)

/-- Actual-boundary specialization with the original whole source rows,
private selected J, rewards, shared constants, replay and launch inputs. -/
theorem ofActualLaunchedBoundary_firstLive_prefix_state (count : ℕ)
    (hspan : BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) +
      count ≤ p.T) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start :=
      fun i => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
    let R := ReferenceActivePhysicalHorizon.run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode
    let W := firstLiveWindow R.records
    ∀ (k : ℕ) (hk : k ≤ count), k ≤ W.length →
      FirstLiveState (ReferenceActivePhysicalHorizon.run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start k
        (by omega) hmode).finalState := by
  dsimp only
  exact run_firstLive_prefix_state _ _ _ _ _ count hspan _
    (ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
    (ofActualLaunchedBoundary_initialFollowers
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)

end ActualLaunch

end Bandits.Support.ReferenceFirstLiveConfirmationHistory

end
