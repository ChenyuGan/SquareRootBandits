/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOccupiedFieldHistory
public import Bandits.Support.ReferenceFirstLiveConfirmationHistory
public import Bandits.Support.LocalReleaseStoppedQuota

import Mathlib.Data.List.TakeWhile

/-!
# Physical first-live release observations

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-88,155-178,297-308,331-345`,
`sources/zip4/manuscript/06_interruptions.tex:457-492`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:30-64`.

The pending projection reads the actual StartRound subcall before PREPARE's
current-row checks. Release tests use the actual collision-filtered feedback.
The interval is a suffix of the existing first-live window, retaining errors;
no identification with the manuscript's stopped interval is asserted here.

The next consumers are `PhaseStartConditionalWaiting.phase_start_task_charge_condExp_bound`
and `phase_start_totalCharge_condExp_bound` with quota one, together with
`ReleaseRoundKernel.actual_up_release_probability_lower_bound` and
`actual_data_release_probability`. Measurability, conditional means and the
current-control law, occupied-slice geometry, all-player ordinary preparation,
first-detector/stopped-interval identification, and signed-charge assembly
remain separate. In particular, this module does not replace the signed charge
`r_t(U) + r_t(X) - sum Y` or its sentinel term by a positive part.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferencePhysicalReleaseQuota

open ConstructorDimensions ReferenceActivePhysicalStep

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {p : Parameters} {rate : RateInput p}

abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

/-- Literal incoming-state/time projection of the pending StartRound result.
No current row, reward, offer, arm-choice, or successful PREPARE is an input. -/
def pendingAtStart (M : Payload rate) (t : Fin p.T) (state : State p rate) :
    Finset (Fin (p.m - 1)) :=
  match state.coordinator with
  | .live r _ _ =>
      if r.payload = M ∧ r.pendingAtChoice = ∅ then
        Finset.univ.filter fun i =>
          match state.followers i with
          | .dagger => False
          | .ordinary s memory =>
              match ActiveFollowerLifecycle.startRound rate.eta t s memory with
              | .error _ => False
              | .ok (choice, _) => choice.status = .pending
      else ∅
  | _ => ∅

/-- The pre-error pending observation on one original physical record. -/
def pendingSet (M : Payload rate) (r : Record (p := p) (rate := rate)) :=
  pendingAtStart M r.input.time r.input.state

/-- Deterministic independence from current-row and reward coordinates.
Probabilistic measurability and current-control laws are separate obligations. -/
theorem pendingSet_eq_of_state_time_eq (M : Payload rate)
    (r s : Record (p := p) (rate := rate))
    (hstate : r.input.state = s.input.state) (htime : r.input.time = s.input.time) :
    pendingSet M r = pendingSet M s := by
  simp only [pendingSet, hstate, htime]

/-- Literal release predicate on the original own observation. -/
def releaseFlag (M : Payload rate) (r : Record (p := p) (rate := rate))
    (i : Fin (p.m - 1)) : Bool :=
  decide (ActiveFollowerLifecycle.releaseCondition rate.eta i
    (ActiveFollowerLifecycle.publicRowOfCompleteRow r.input.row r.input.time)
    (r.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2 (M.downRecord i))

theorem own_observation_eq (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1)) :
    (r.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2 =
      (prepare r.input).feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
  unfold ReferenceActivePhysicalHorizon.RoundRecord.ownEntries
  rw [r.output_eq]
  rfl

/-- Separate actual UP component of the release test. -/
def upFlag (M : Payload rate) (r : Record (p := p) (rate := rate))
    (i : Fin (p.m - 1)) : Bool :=
  releaseFlag M r i && decide (PublicDiscreteDraws.slotDraw
    (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot)

/-- Separate actual DATA component of the release test. -/
def dataFlag (M : Payload rate) (r : Record (p := p) (rate := rate))
    (i : Fin (p.m - 1)) : Bool :=
  releaseFlag M r i && decide (PublicDiscreteDraws.slotDraw
    (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.dataSlot)

/-- Count the pending test, even if a subsequent operation in this round fails. -/
def releaseCount (M : Payload rate) (records : List (Record (p := p) (rate := rate)))
    (i : Fin (p.m - 1)) : ℕ :=
  records.countP fun r => decide (i ∈ pendingSet M r) && releaseFlag M r i

def upCount (M : Payload rate) (records : List (Record (p := p) (rate := rate)))
    (i : Fin (p.m - 1)) : ℕ :=
  records.countP fun r => decide (i ∈ pendingSet M r) && upFlag M r i

def dataCount (M : Payload rate) (records : List (Record (p := p) (rate := rate)))
    (i : Fin (p.m - 1)) : ℕ :=
  records.countP fun r => decide (i ∈ pendingSet M r) && dataFlag M r i

/-- The computed suffix after a selected record. This selects no confirmation
and asserts no existence of a successful last confirmation. -/
def releaseWindow (records : List (Record (p := p) (rate := rate)))
    (c : Fin (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length) :=
  (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).drop (c.val + 1)

/-- A list projection of the existing physical run, with the original whole
tables and selected private coordinate. This introduces no execution carrier. -/
def runWindow (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hactive : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :=
  ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan hactive).records

theorem mem_pendingAtStart_live (M : Payload rate) (t : Fin p.T) (state : State p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hc : state.coordinator = .live r q base) (hp : r.payload = M)
    (he : r.pendingAtChoice = ∅) (i : Fin (p.m - 1)) :
    i ∈ pendingAtStart M t state ↔
      ∃ before memory choice choiceMemory,
        state.followers i = .ordinary before memory ∧
        ActiveFollowerLifecycle.startRound rate.eta t before memory =
          .ok (choice, choiceMemory) ∧ choice.status = .pending := by
  simp only [pendingAtStart, hc, hp, he, and_self, ite_true, Finset.mem_filter,
    Finset.mem_univ, true_and]
  cases hi : state.followers i with
  | dagger =>
      constructor
      · intro h; exact h.elim
      · rintro ⟨_, _, _, _, h, _, _⟩; cases h
  | ordinary before memory =>
      constructor
      · intro h
        cases hs : ActiveFollowerLifecycle.startRound rate.eta t before memory with
        | error reason => simp only [hs] at h
        | ok pair =>
            rcases pair with ⟨choice, choiceMemory⟩
            exact ⟨before, memory, choice, choiceMemory, rfl, hs, by simpa only [hs] using h⟩
      · rintro ⟨_, _, choice, choiceMemory, h, hs, hpending⟩
        cases h
        simp only [hs]
        exact hpending

theorem pendingAtStart_dagger (M : Payload rate) (t : Fin p.T) (state : State p rate)
    (hc : state.coordinator = .dagger) : pendingAtStart M t state = ∅ := by
  simp only [pendingAtStart, hc]

/-- Ordinary actual PREPARE uses exactly the earlier StartRound result. -/
theorem pendingAtStart_ordinary_prepare (M : Payload rate) (x : RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hc : x.state.coordinator = .live r q base) (hp : r.payload = M)
    (he : r.pendingAtChoice = ∅) (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : ((prepare x).followers.followers i).configuration = .ordinary choice memory) :
    i ∈ pendingAtStart M x.time x.state ↔ choice.status = .pending := by
  obtain ⟨before, beforeMemory, _, hi, hs, _⟩ :=
    ReferenceActiveDataOwnership.prepare_ordinary_choice i x.row (x.state.activations i)
      x.time (x.active i) (x.state.followers i) choice memory hchoice
  rw [mem_pendingAtStart_live M x.time x.state r q base hc hp he i]
  constructor
  · rintro ⟨b, bm, c, cm, hb, hstart, hpend⟩
    rw [hi] at hb
    cases hb
    rw [hs] at hstart
    cases hstart
    exact hpend
  · intro hpend
    exact ⟨before, beforeMemory, choice, memory, hi, hs, hpend⟩

private theorem no_down_status_change
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (own : ReferencePrelaunchFollower.Observation p)
    (before after : ReferencePrelaunchFollower.State p rate.eta)
    (hnone : ReferenceDownReception.expectedDownFlatWord view i row t = none)
    (h : DeclaredFollowerLocalRound.consumeDownResult rate
      (ReferenceDownReception.referenceDownCut p view i row t own rate before).outcome =
        .ok after) : after.status = before.status := by
  unfold ReferenceDownReception.referenceDownCut at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · dsimp only at h
            split at h
            · rename_i hmatch
              rw [hnone] at hmatch
              simp only [hmatch, ReferenceDownReception.ordinaryParse,
                DeclaredFollowerLocalRound.consumeDownResult] at h
              cases h
              rfl
            · cases h
              rfl
          · cases h
        · cases h
      · cases h
    · cases h
      rfl
  · cases h
    rfl

private theorem record_unoccupied_no_down
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (own : ReferencePrelaunchFollower.Observation p)
    (choice post : ReferencePrelaunchFollower.State p rate.eta)
    (hu : choice.status = .unoccupied)
    (hnone : ReferenceDownReception.expectedDownFlatWord view i row t = none)
    (h : (recordFollower view i row activation t active arm own choice).result = .ok post) :
    post.status = .unoccupied := by
  rw [recordFollower, dite_eq_left hu] at h
  cases hl : ActiveFollowerLogging.checkedLogging i row activation t (arm, own) choice with
  | error reason => simp only [hl] at h; cases h
  | ok logged =>
      simp only [hl] at h
      have hf := ActiveFollowerLogging.checkedLogging_success_frame i row activation t
        (arm, own) choice logged hl
      exact (no_down_status_change view i row t own logged post hnone h).trans
        (hf.2.2.2.2.1.trans hu)

private theorem release_finish_inversion (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (own : ReferencePrelaunchFollower.Observation p)
    (choice post next : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (h : DeclaredFollowerLocalRound.releaseAndFinish rate i row t own choice memory post =
      .ok (next, nextMemory)) :
    ∃ released,
      ActiveFollowerLifecycle.releaseAfterService rate.eta i t
        (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) own choice post = .ok released ∧
      ActiveFollowerLifecycle.finishRound rate.eta t row released memory =
        .ok (next, nextMemory) ∧ next = released := by
  unfold DeclaredFollowerLocalRound.releaseAndFinish at h
  split at h
  · cases h
  · rename_i released hr
    split at h
    · cases h
    · rename_i pair hf
      cases h
      exact ⟨released, hr, hf,
        ActiveFollowerLifecycle.finishRound_frame rate.eta t row released next memory nextMemory hf⟩

private theorem service_inversion
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (own : ReferencePrelaunchFollower.Observation p)
    (choice post : ReferencePrelaunchFollower.State p rate.eta)
    (hu : choice.status ≠ .unoccupied)
    (h : (recordFollower view i row activation t active arm own choice).result = .ok post) :
    ∃ result : ActiveFollowerQueueOperation.ServiceSuccess p rate.eta rate.n i row
        activation t own choice,
      ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n rate.n_scale
        i row activation t own choice = .success result ∧ post = result.output := by
  simp only [recordFollower, dite_eq_right hu,
    DeclaredFollowerLocalRound.recordOrServiceThenDown] at h
  split at h
  · cases h
  · rename_i result hs
    cases h
    exact ⟨result, hs, rfl⟩

private theorem pending_release_inversion (i : Fin (p.m - 1)) (t : Fin p.T)
    (row : ActiveFollowerLifecycle.FollowerPublicRow p.m p.K)
    (own : ReferencePrelaunchFollower.Observation p)
    (choice post out : ReferencePrelaunchFollower.State p rate.eta)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hp : choice.status = .pending) (hm : choice.lastDown = some M)
    (h : ActiveFollowerLifecycle.releaseAfterService rate.eta i t row own choice post = .ok out) :
    ActiveFollowerLifecycle.localStateDomainValid choice ∧ M.val.sigma ≤ t.val ∧
      ActiveFollowerLifecycle.localStateDomainValid post ∧
      out = if ActiveFollowerLifecycle.releaseCondition rate.eta i row own M then
        {post with status := .released} else post := by
  unfold ActiveFollowerLifecycle.releaseAfterService at h
  rw [dite_eq_left hp] at h
  split at h
  · rename_i hpre
    simp only [hm] at h
    split at h
    · rename_i ht
      split at h
      · rename_i hpost
        by_cases htest : ActiveFollowerLifecycle.releaseCondition rate.eta i row own M
        · simp only [ite_eq_left htest] at h ⊢
          split at h
          · exact ⟨hpre, ht, hpost, (Except.ok.inj h).symm⟩
          · cases h
        · simp only [ite_eq_right htest] at h ⊢
          split at h
          · exact ⟨hpre, ht, hpost, (Except.ok.inj h).symm⟩
          · cases h
      · cases h
    · cases h
  · cases h

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

private theorem selectionAt_view (x : RoundInput p rate) (payload : Payload rate)
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

/-- Empty pending forbids every accepted DOWN, even when a stale partial
batch produces a unique word: the receiver compares it against `none`. -/
private theorem live_empty_step (M : Payload rate) (x : RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hc : x.state.coordinator = .live r q base) (hp : r.payload = M)
    (he : r.pendingAtChoice = ∅)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen x = false) :
    ((step x).next.coordinator = .dagger ∨
      ∃ next owned, (step x).next.coordinator = .live next owned base ∧
        next.payload = M ∧ next.pendingAtChoice = ∅) ∧
      ∀ i, ReferenceDownReception.expectedDownFlatWord (prepare x).coordinator.downView
        i x.row x.time = none := by
  have hd : (prepare x).coordinator = .live r q base
      (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
    change dispatch x = _
    simp only [dispatch, hc, CoordinatorRoundDispatch.dispatch]
    rfl
  have ho := observeCoordinator_live_equation (prepare x) r q base _ hd
  cases hx : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base) with
  | clockFailure failure hfailure =>
      constructor
      · left; simp only [step, ho, hx, DispatchCut.selection, ite_true, coordinatorFailure]
      · intro i; simp only [hd, hx, DispatchCut.downView, DispatchCut.selection,
          Option.map_none, ReferenceDownReception.expectedDownFlatWord]
  | initializerFailure dispatched hstart checked hchecked =>
      constructor
      · left; simp only [step, ho, hx, DispatchCut.selection, ite_true, coordinatorFailure]
      · intro i; simp only [hd, hx, DispatchCut.downView, DispatchCut.selection,
          Option.map_none, ReferenceDownReception.expectedDownFlatWord]
  | localFailure dispatched hstart reason =>
      constructor
      · left; simp only [step, ho, hx, DispatchCut.selection, ite_true, coordinatorFailure]
      · intro i; simp only [hd, hx, DispatchCut.downView, DispatchCut.selection,
          Option.map_none, ReferenceDownReception.expectedDownFlatWord]
  | cutoffChosen =>
      simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hd, hx,
        Bool.true_eq_false] at hcut
  | continuingChosen dispatched hstart continuation arm =>
      have hpend : dispatched.startResult.pending = ∅ :=
        (continuing_pending (liveInput x r q base) dispatched hstart continuation arm hx).trans he
      cases hsel : (DispatchCut.live r q base
          (.continuingChosen dispatched hstart continuation arm)).selection with
      | none =>
          constructor
          · left; simp only [step, ho, hx, hsel, ite_true, coordinatorFailure]
          · intro i; simp only [hd, hx, DispatchCut.downView, hsel, Option.map_none,
              ReferenceDownReception.expectedDownFlatWord]
      | some selected =>
          have hs := selectionAt_view x r.payload dispatched.startResult x.time
            (liveRegistersAt r x.time).complementWeights arm selected hsel
          constructor
          · have hf := ReferenceFirstLiveConfirmationHistory.livePostChoice_frame x
              (prepare x) (liveRegistersAt r x.time) (liveOwnedAt r q x.time) base
              dispatched.startResult
            change (prepare x).observeCoordinator.configuration = .dagger ∨
              ∃ next owned, (prepare x).observeCoordinator.configuration = .live next owned base ∧
                next.payload = M ∧ next.pendingAtChoice = ∅
            rw [ho, hx, hsel]
            rcases hf with hf | ⟨next, owned, hout, hpay, hsub⟩
            · exact Or.inl hf
            · exact Or.inr ⟨next, owned, hout, hpay.trans hp,
                Finset.eq_empty_iff_forall_notMem.mpr fun i hi => by
                  have hm := hsub hi
                  rw [hpend] at hm
                  exact Finset.notMem_empty i hm⟩
          · intro i
            have hn : ¬ ReferenceDownReception.selectedDownSenderBranch selected.view i x.row x.time := by
              intro hn
              have hm := hn.2.2
              rw [hs.2.1, hpend] at hm
              exact Finset.notMem_empty i hm
            simp only [hd, hx, DispatchCut.downView, hsel, Option.map_some,
              ReferenceDownReception.expectedDownFlatWord, hn, and_false, ite_false]

private theorem ordinary_pending_predecessor (M : Payload rate) (x : RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hc : x.state.coordinator = .live r q base) (hp : r.payload = M)
    (he : r.pendingAtChoice = ∅)
    (hfields : ReferenceActiveDataOwnership.carriedOccupiedFields M x.state)
    (hnone : ∀ i, ReferenceDownReception.expectedDownFlatWord
      (prepare x).coordinator.downView i x.row x.time = none)
    (i : Fin (p.m - 1)) (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : (step x).next.followers i = .ordinary next nextMemory)
    (hnext : next.status = .pending) :
    i ∈ pendingAtStart M x.time x.state ∧
      ¬ ActiveFollowerLifecycle.releaseCondition rate.eta i
        (ActiveFollowerLifecycle.publicRowOfCompleteRow x.row x.time)
        ((prepare x).feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        (M.downRecord i) := by
  obtain ⟨choice, memory, post, hchoice, hr, hf, _, _⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion _ _ _ next nextMemory hout
  obtain ⟨hrow, hi, ht, hactivation⟩ := (prepare x).follower_alignment i
  simp only [hi, hrow, ht, hactivation] at hr hf
  obtain ⟨released, hrelease, hfinish, hframe⟩ :=
    release_finish_inversion _ _ _ _ choice post next memory nextMemory hf
  have hlocal := ReferenceActiveDataOwnership.choice_occupied_fields_preserved M i x.row
    (x.state.activations i) x.time (x.active i) (x.state.followers i) (hfields i)
  change ReferenceActiveDataOwnership.occupiedFields M i
    ((prepare x).followers.followers i).configuration at hlocal
  rw [hchoice] at hlocal
  have hpend : choice.status = .pending := by
    cases hs : choice.status with
    | unoccupied =>
        have hpost := record_unoccupied_no_down _ _ _ _ _ _ _ _ choice post hs (hnone i) hr
        rw [ActiveFollowerLifecycle.releaseAfterService_unoccupied rate.eta i x.time
          _ _ choice post hs] at hrelease
        cases hrelease
        rw [hframe, hpost] at hnext
        cases hnext
    | pending => rfl
    | released =>
        obtain ⟨result, _, hpost⟩ := service_inversion _ _ _ _ _ _ _ _ choice post
          (by rw [hs]; decide) hr
        have hstatus := (LocalReleaseQuota.serviceSuccess_nonqueue_frame result).2.2.2.1
        rw [ActiveFollowerLifecycle.releaseAfterService_not_pending rate.eta i x.time
          _ _ choice post (by rw [hs]; decide)] at hrelease
        cases hrelease
        rw [hframe, hpost, hstatus, hs] at hnext
        cases hnext
  have hm : choice.lastDown = some (M.downRecord i) := hlocal (by rw [hpend]; decide)
  obtain ⟨_, _, _, heq⟩ := pending_release_inversion i x.time _ _ choice post released
    (M.downRecord i) hpend hm hrelease
  refine ⟨(pendingAtStart_ordinary_prepare M x r q base hc hp he i choice memory hchoice).2 hpend, ?_⟩
  intro htest
  rw [hframe, heq, ite_eq_left htest] at hnext
  cases hnext

private theorem confirmation_tail_empty (x : RoundInput p rate) (prepared : PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) (selected : Selection x)
    (hp : selected.view.payload = r.payload)
    (he : selected.view.pendingAtChoice = started.pending)
    (hu : selected.view.cutoff = CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
    (hsingle : selected.view.pendingAtChoice =
      {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 x.time).1})
    (hevent : CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
      selected.view.pendingAtChoice selected.view.cutoff x.time (x.row.2 x.time)
      prepared.coordinatorObservation)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters next) (nextBase : Fin (p.m - 1) → ℕ)
    (hout : (livePostChoice prepared r q base started).configuration = .live next owned nextBase) :
    next.payload = selected.view.payload ∧ next.pendingAtChoice = ∅ := by
  have hev : CoordinatorLocalArmChoice.downConfirmationEvent r.payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time
      (x.row.2 x.time) prepared.coordinatorObservation := by
    simpa only [hp, he, hu] using hevent
  have hupdate := ReferenceActiveConfirmationRelease.livePostChoice_confirmationUpdate_erases
    prepared r started hev
  unfold livePostChoice at hout
  split at hout
  · cases hout
  · split at hout
    · cases hout
    · rw [hupdate] at hout
      dsimp only at hout
      split at hout
      · cases hout
      · rename_i finished hfinish
        cases hout
        refine ⟨hp.symm, ?_⟩
        change finished.pending = ∅
        rw [CoordinatorPhaseClock.finishRound_pending_frame p rate.eta.val x.time
          started.clock _ x.row finished hfinish, ← he, hsingle]
        exact Finset.erase_singleton _

private theorem selected_confirmation_endpoint (x : RoundInput p rate)
    (hstate : ReferenceFirstLiveConfirmationHistory.FirstLiveState x.state)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen x = false)
    (selected : Selection x) (hselected : (prepare x).coordinator.selection = some selected)
    (hsingle : selected.view.pendingAtChoice =
      {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 x.time).1})
    (hevent : CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
      selected.view.pendingAtChoice selected.view.cutoff x.time (x.row.2 x.time)
      (prepare x).coordinatorObservation)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters next) (base : Fin (p.m - 1) → ℕ)
    (hout : (step x).next.coordinator = .live next owned base) :
    next.payload = selected.view.payload ∧ next.pendingAtChoice = ∅ := by
  change (prepare x).observeCoordinator.configuration = _ at hout
  cases hc : x.state.coordinator with
  | dagger =>
      have hd := (step_coordinator_dagger x hc).1
      change (prepare x).observeCoordinator.configuration = .dagger at hd
      rw [hd] at hout
      cases hout
  | collection payload ledger proposal =>
      simp only [ReferenceFirstLiveConfirmationHistory.FirstLiveState, hc] at hstate
  | first =>
      have hd : (prepare x).coordinator = .first
          (CoordinatorRoundDispatch.dispatchFirst (firstInput x)) := dispatch_first x hc
      have ho := observeCoordinator_first_equation (prepare x) _ hd
      rw [hd] at hselected
      cases hx : CoordinatorRoundDispatch.dispatchFirst (firstInput x) with
      | choiceDomainFailure installed =>
          simp only [hx, DispatchCut.selection] at hselected; cases hselected
      | recorderBoundaryFailure installed =>
          simp only [hx, DispatchCut.selection] at hselected; cases hselected
      | choiceRejected installed =>
          simp only [hx, DispatchCut.selection] at hselected; cases hselected
      | chosen installed arm =>
          rw [hx] at hselected
          obtain ⟨hp, he, hu⟩ := selectionAt_view x installed.registers.payload
            installed.startRoundResult installed.registers.time
            installed.registers.complementWeights arm selected hselected
          rw [ho, hx, hselected] at hout
          exact confirmation_tail_empty x (prepare x) installed.registers
            installed.ownedRegisters installed.followerBaseScore installed.startRoundResult
            selected hp he hu hsingle hevent next owned base hout
  | live r q oldBase =>
      have hd : (prepare x).coordinator = .live r q oldBase
          (CoordinatorRoundDispatch.dispatchLive (liveInput x r q oldBase)) := by
        change dispatch x = _
        simp only [dispatch, hc, CoordinatorRoundDispatch.dispatch]
        rfl
      have ho := observeCoordinator_live_equation (prepare x) r q oldBase _ hd
      rw [hd] at hselected
      cases hx : CoordinatorRoundDispatch.dispatchLive (liveInput x r q oldBase) with
      | clockFailure => simp only [hx, DispatchCut.selection] at hselected; cases hselected
      | initializerFailure => simp only [hx, DispatchCut.selection] at hselected; cases hselected
      | localFailure => simp only [hx, DispatchCut.selection] at hselected; cases hselected
      | cutoffChosen =>
          simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hd, hx,
            Bool.true_eq_false] at hcut
      | continuingChosen dispatched hstart continuation arm =>
          rw [hx] at hselected
          obtain ⟨hp, he, hu⟩ := selectionAt_view x r.payload dispatched.startResult x.time
            (liveRegistersAt r x.time).complementWeights arm selected hselected
          rw [ho, hx, hselected] at hout
          exact confirmation_tail_empty x (prepare x) (liveRegistersAt r x.time)
            (liveOwnedAt r q x.time) oldBase dispatched.startResult selected hp he hu
            hsingle hevent next owned base hout

/-- Literal coordinator component of the induction state: failure or the
same live payload with no missing confirmation. -/
private def releaseCoordinator (M : Payload rate) (state : State p rate) : Prop :=
  match state.coordinator with
  | .dagger => True
  | .live r _ _ => r.payload = M ∧ r.pendingAtChoice = ∅
  | _ => False

private theorem pending_input (M : Payload rate) (t : Fin p.T) (state : State p rate)
    (i : Fin (p.m - 1)) (hi : i ∈ pendingAtStart M t state) :
    state.coordinator ≠ .dagger ∧ ∃ s memory,
      state.followers i = .ordinary s memory ∧ s.status = .pending := by
  cases hc : state.coordinator with
  | first => simp only [pendingAtStart, hc, Finset.notMem_empty] at hi
  | collection => simp only [pendingAtStart, hc, Finset.notMem_empty] at hi
  | dagger => simp only [pendingAtStart, hc, Finset.notMem_empty] at hi
  | live r q base =>
      by_cases hg : r.payload = M ∧ r.pendingAtChoice = ∅
      · obtain ⟨s, memory, choice, cm, hs, hstart, hpend⟩ :=
          (mem_pendingAtStart_live M t state r q base hc hg.1 hg.2 i).1 hi
        refine ⟨?_, s, memory, hs, ?_⟩
        · intro h; cases h
        · rcases ReferenceActiveDataOwnership.startRound_status t s choice memory cm hstart with hu | he
          · rw [hpend] at hu; cases hu
          · exact he.symm.trans hpend
      · simp only [pendingAtStart, hc, ite_eq_right hg, Finset.notMem_empty] at hi

private theorem releaseCoordinator_step (M : Payload rate) (x : RoundInput p rate)
    (hmode : releaseCoordinator M x.state)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen x = false) :
    releaseCoordinator M (step x).next := by
  cases hc : x.state.coordinator with
  | first => simp only [releaseCoordinator, hc] at hmode
  | collection => simp only [releaseCoordinator, hc] at hmode
  | dagger => simp only [releaseCoordinator, (step_coordinator_dagger x hc).1]
  | live r q base =>
      have hg : r.payload = M ∧ r.pendingAtChoice = ∅ := by
        simpa only [releaseCoordinator, hc] using hmode
      rcases (live_empty_step M x r q base hc hg.1 hg.2 hcut).1 with hd | ⟨next, owned, hn, hp, he⟩
      · simp only [releaseCoordinator, hd]
      · simp only [releaseCoordinator, hn]; exact ⟨hp, he⟩

private theorem record_predecessor (M : Payload rate) (r : Record (p := p) (rate := rate))
    (hstate : ReferenceFirstLiveConfirmationHistory.FirstLiveState r.input.state)
    (hmode : releaseCoordinator M r.input.state)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen r.input = false)
    (hcoord : r.output.next.coordinator ≠ .dagger)
    (i : Fin (p.m - 1)) (next : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : r.output.next.followers i = .ordinary next memory) (hpending : next.status = .pending) :
    i ∈ pendingSet M r ∧ releaseFlag M r i = false := by
  cases hc : r.input.state.coordinator with
  | first => simp only [releaseCoordinator, hc] at hmode
  | collection => simp only [releaseCoordinator, hc] at hmode
  | dagger => exact (hcoord (r.output_eq ▸ (step_coordinator_dagger r.input hc).1)).elim
  | live registers owned base =>
      have hg : registers.payload = M ∧ registers.pendingAtChoice = ∅ := by
        simpa only [releaseCoordinator, hc] using hmode
      have hf : ReferenceActiveDataOwnership.carriedOccupiedFields M r.input.state := by
        have hs : ReferenceActiveDataOwnership.carriedOccupiedFields registers.payload r.input.state ∧
            ∀ i s memory, r.input.state.followers i = .ordinary s memory →
              registers.pendingAtChoice.Nonempty → s.status ≠ .released := by
          simpa only [ReferenceFirstLiveConfirmationHistory.FirstLiveState, hc] using hstate
        simpa only [hg.1] using hs.1
      have hout' : (step r.input).next.followers i = .ordinary next memory := by
        simpa only [r.output_eq] using hout
      obtain ⟨hm, hn⟩ := ordinary_pending_predecessor M r.input registers owned base hc
        hg.1 hg.2 hf (live_empty_step M r.input registers owned base hc hg.1 hg.2 hcut).2
        i next memory hout' hpending
      refine ⟨hm, ?_⟩
      unfold releaseFlag ReferenceActivePhysicalHorizon.RoundRecord.ownEntries
      rw [r.output_eq]
      change decide (ActiveFollowerLifecycle.releaseCondition rate.eta i
        (ActiveFollowerLifecycle.publicRowOfCompleteRow r.input.row r.input.time)
        ((prepare r.input).feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        (M.downRecord i)) = false
      exact decide_eq_false hn

/-- Backwards extraction through the original connected records. A later
pending observation forces earlier pending observations and excludes their
release tests. Errors remain in the list and can only remove membership. -/
private theorem connected_pending_history (M : Payload rate)
    {initial final : State p rate} (records : List (Record (p := p) (rate := rate)))
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hstate : ReferenceFirstLiveConfirmationHistory.FirstLiveState initial)
    (hmode : releaseCoordinator M initial)
    (hcut : ∀ r ∈ records, ReferenceCollectionPhaseHistory.cutoffChosen r.input = false) :
    ∀ (b : ℕ) (hb : b < records.length) (i : Fin (p.m - 1)),
      i ∈ pendingSet M records[b] →
        initial.coordinator ≠ .dagger ∧
        (∃ s memory, initial.followers i = .ordinary s memory ∧ s.status = .pending) ∧
        ∀ (a : ℕ) (ha : a < b),
          i ∈ pendingSet M records[a] ∧ releaseFlag M records[a] i = false := by
  induction records generalizing initial with
  | nil => intro b hb; simp only [List.length_nil] at hb; omega
  | cons r rest ih =>
      obtain ⟨hpre, hrest⟩ := chain
      have hcutr := hcut r List.mem_cons_self
      have hs : ReferenceFirstLiveConfirmationHistory.FirstLiveState r.input.state := hpre ▸ hstate
      have hm : releaseCoordinator M r.input.state := hpre ▸ hmode
      have hnext : ReferenceFirstLiveConfirmationHistory.FirstLiveState r.output.next := by
        rw [r.output_eq]
        exact ReferenceFirstLiveConfirmationHistory.firstLive_step r.input hs hcutr
      have hmnext : releaseCoordinator M r.output.next := by
        rw [r.output_eq]
        exact releaseCoordinator_step M r.input hm hcutr
      intro b hb i hp
      cases b with
      | zero =>
          obtain ⟨hc, hf⟩ := pending_input M r.input.time r.input.state i hp
          rw [hpre] at hc hf
          exact ⟨hc, hf, fun a ha => by omega⟩
      | succ b =>
          have hb' : b < rest.length := by simp only [List.length_cons] at hb; omega
          obtain ⟨hc, ⟨s, memory, hf, hpend⟩, hprior⟩ := ih hrest hnext hmnext
            (fun record hr => hcut record (List.mem_cons_of_mem r hr)) b hb' i hp
          obtain ⟨hhead, hrelease⟩ := record_predecessor M r hs hm hcutr hc i s memory hf hpend
          obtain ⟨hcin, hfin⟩ := pending_input M r.input.time r.input.state i hhead
          rw [hpre] at hcin hfin
          refine ⟨hcin, hfin, ?_⟩
          intro a ha
          cases a with
          | zero => exact ⟨hhead, hrelease⟩
          | succ a => exact hprior a (by omega)

private theorem window_connected {initial final : State p rate}
    (records : List (Record (p := p) (rate := rate)))
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final) :
    ∃ endpoint, ReferenceActivePhysicalHorizon.Connected initial
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records) endpoint := by
  induction records generalizing initial with
  | nil => exact ⟨initial, rfl⟩
  | cons r rest ih =>
      obtain ⟨hpre, hrest⟩ := chain
      cases hc : ReferenceCollectionPhaseHistory.cutoffChosen r.input with
      | true =>
          exact ⟨initial, by simp only [ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
            List.takeWhile_cons, hc, Bool.not_true, Bool.false_eq_true, ite_false]; rfl⟩
      | false =>
          obtain ⟨endpoint, hchain⟩ := ih hrest
          refine ⟨endpoint, ?_⟩
          simp only [ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
            List.takeWhile_cons, hc, Bool.not_false, ite_true]
          exact ⟨hpre, hchain⟩

private theorem window_no_cutoff (records : List (Record (p := p) (rate := rate)))
    (r : Record (p := p) (rate := rate))
    (hr : r ∈ ReferenceFirstLiveConfirmationHistory.firstLiveWindow records) :
    ReferenceCollectionPhaseHistory.cutoffChosen r.input = false := by
  have h := List.mem_takeWhile_imp hr
  simpa only [Bool.not_eq_true'] using h

private theorem history_count_le_one (M : Payload rate)
    (records : List (Record (p := p) (rate := rate))) (i : Fin (p.m - 1)) :
    (∀ (a b : ℕ) (ha : a < records.length) (hb : b < records.length),
      a < b → i ∈ pendingSet M records[b] → releaseFlag M records[a] i = false) →
    releaseCount M records i ≤ 1 := by
  induction records with
  | nil => intro _; exact Nat.zero_le 1
  | cons r rest ih =>
      intro history
      have htail : ∀ (a b : ℕ) (ha : a < rest.length) (hb : b < rest.length),
          a < b → i ∈ pendingSet M rest[b] → releaseFlag M rest[a] i = false := by
        intro a b ha hb hab hp
        exact history (a + 1) (b + 1) (by simp only [List.length_cons]; omega)
          (by simp only [List.length_cons]; omega) (by omega) hp
      have hbound := ih htail
      cases hhead : decide (i ∈ pendingSet M r) && releaseFlag M r i with
      | false =>
          simpa only [releaseCount, List.countP_cons, hhead, Bool.false_eq_true,
            ite_false, Nat.add_zero] using hbound
      | true =>
          have hzero : releaseCount M rest i = 0 := by
            apply List.countP_eq_zero.mpr
            intro record hr hflag
            obtain ⟨b, hb, rfl⟩ := List.mem_iff_getElem.mp hr
            have hp := of_decide_eq_true (Bool.and_eq_true_iff.mp hflag).1
            have hf := history 0 (b + 1) (by simp only [List.length_cons]; omega)
              (by simp only [List.length_cons]; omega) (by omega) hp
            change releaseFlag M r i = false at hf
            have hrel := (Bool.and_eq_true_iff.mp hhead).2
            rw [hf] at hrel
            cases hrel
          change (r :: rest).countP _ ≤ 1
          rw [List.countP_cons]
          rw [hhead]
          change releaseCount M rest i + 1 ≤ 1
          rw [hzero]

theorem upCount_le_releaseCount (M : Payload rate)
    (records : List (Record (p := p) (rate := rate))) (i : Fin (p.m - 1)) :
    upCount M records i ≤ releaseCount M records i := by
  apply List.countP_mono_left
  intro r _ h
  exact Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp h).1,
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).1⟩

theorem dataCount_le_releaseCount (M : Payload rate)
    (records : List (Record (p := p) (rate := rate))) (i : Fin (p.m - 1)) :
    dataCount M records i ≤ releaseCount M records i := by
  apply List.countP_mono_left
  intro r _ h
  exact Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp h).1,
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).1⟩

section Run

variable (initial : State p rate) (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (start count : ℕ)
    (hspan : start + count ≤ p.T)
    (hactive : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hseed : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial)

/-- Calendar coordinates are inherited from the existing run, without a
second calendar or any source stopping-time identification. -/
theorem runWindow_time (a : Fin (runWindow initial rows J rewards start count hspan hactive).length) :
    (runWindow initial rows J rewards start count hspan hactive)[a.val].input.time.val =
      start + a.val := by
  let R := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan hactive
  have hprefix : (runWindow initial rows J rewards start count hspan hactive).IsPrefix R.records :=
    List.takeWhile_prefix _
  have har : a.val < R.records.length := lt_of_lt_of_le a.isLt hprefix.length_le
  have hac : a.val < count := by
    rw [ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start count
      hspan hactive] at har
    exact har
  have ht := ReferenceActivePhysicalHorizon.run_time_values initial rows J rewards start count hspan hactive
  have hv := congrArg (fun times : List ℕ => times[a.val]?) ht
  rw [List.getElem?_map, List.getElem?_eq_getElem har] at hv
  simp only [ReferenceActivePhysicalHorizon.calendar, List.getElem?_range' hac,
    Nat.one_mul, Option.map_some, Option.some.injEq] at hv
  exact (congrArg (fun r : Record (p := p) (rate := rate) => r.input.time.val)
    (hprefix.getElem a.isLt)).trans hv


variable (c : Fin (runWindow initial rows J rewards start count hspan hactive).length)
    (selected : Selection (runWindow initial rows J rewards start count hspan hactive)[c.val].input)
    (hselected : (prepare (runWindow initial rows J rewards start count hspan hactive)[c.val].input).coordinator.selection = some selected)
    (hsingle : selected.view.pendingAtChoice =
      {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        ((runWindow initial rows J rewards start count hspan hactive)[c.val].input.row.2 (runWindow initial rows J rewards start count hspan hactive)[c.val].input.time).1})
    (hevent : CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
      selected.view.pendingAtChoice selected.view.cutoff
      (runWindow initial rows J rewards start count hspan hactive)[c.val].input.time
      ((runWindow initial rows J rewards start count hspan hactive)[c.val].input.row.2
        (runWindow initial rows J rewards start count hspan hactive)[c.val].input.time)
      (prepare (runWindow initial rows J rewards start count hspan hactive)[c.val].input).coordinatorObservation)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters next) (base : Fin (p.m - 1) → ℕ)
    (hout : (runWindow initial rows J rewards start count hspan hactive)[c.val].output.next.coordinator = .live next owned base)


include hfirst hseed hselected hsingle hevent hout

omit hfirst hseed hselected hsingle hevent hout in
/-- The suffix starts at coordinate `start + c + 1` and advances one calendar
coordinate per record. This is a physical calendar statement only. -/
theorem run_firstLive_release_calendar
    (n : Fin ((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1)).length) :
    ((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))[n.val].input.time.val =
      start + c.val + 1 + n.val := by
  have hn : c.val + 1 + n.val < (runWindow initial rows J rewards start count hspan hactive).length := by
    have h := n.isLt
    simp only [List.length_drop] at h
    omega
  have he : ((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))[n.val] =
      (runWindow initial rows J rewards start count hspan hactive)[c.val + 1 + n.val] := List.getElem_drop
  rw [he]
  have ht := runWindow_time initial rows J rewards start count hspan hactive ⟨c.val + 1 + n.val, hn⟩
  dsimp only at ht
  omega

/-- The singleton confirmation is actually committed by this physical round.
Only its ordinary coordinator endpoint is selected; later success is derived. -/
theorem run_firstLive_release_seed : next.payload = selected.view.payload ∧ next.pendingAtChoice = ∅ := by
  have hs := ReferenceFirstLiveConfirmationHistory.run_firstLive_carried initial rows J
    rewards start count hspan hactive hfirst hseed c
  apply selected_confirmation_endpoint (runWindow initial rows J rewards start count hspan hactive)[c.val].input hs
    (window_no_cutoff ((ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan hactive)).records _ (List.getElem_mem c.isLt)) selected hselected hsingle hevent
    next owned base
  simpa only [(runWindow initial rows J rewards start count hspan hactive)[c.val].output_eq] using hout

private theorem run_release_history :
    ∀ (b : ℕ) (hb : b < (((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))).length) (i : Fin (p.m - 1)),
      i ∈ pendingSet selected.view.payload ((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))[b] → ∀ (a : ℕ) (ha : a < b),
        i ∈ pendingSet selected.view.payload ((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))[a] ∧ releaseFlag selected.view.payload ((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))[a] i = false := by
  obtain ⟨endpoint, hchain⟩ := window_connected ((ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan hactive)).records ((ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan hactive)).connected
  have htail := ReferenceFollowerReplyChronology.connected_drop_from_output hchain c.val c.isLt
  have hcutc := window_no_cutoff ((ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan hactive)).records _ (List.getElem_mem c.isLt)
  have hstatec := ReferenceFirstLiveConfirmationHistory.run_firstLive_carried initial rows J
    rewards start count hspan hactive hfirst hseed c
  have hstate : ReferenceFirstLiveConfirmationHistory.FirstLiveState (runWindow initial rows J rewards start count hspan hactive)[c.val].output.next := by
    rw [(runWindow initial rows J rewards start count hspan hactive)[c.val].output_eq]
    exact ReferenceFirstLiveConfirmationHistory.firstLive_step _ hstatec hcutc
  have hmode : releaseCoordinator selected.view.payload (runWindow initial rows J rewards start count hspan hactive)[c.val].output.next := by
    simp only [releaseCoordinator, hout]
    exact run_firstLive_release_seed initial rows J rewards start count hspan hactive hfirst hseed
      c selected hselected hsingle hevent next owned base hout
  intro b hb i hp a ha
  exact (connected_pending_history selected.view.payload ((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1)) htail hstate hmode
    (fun r hr => window_no_cutoff ((ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan hactive)).records r (List.mem_of_mem_drop hr)) b hb i hp).2.2 a ha

/-- Pending sets are nested on the computed first-live suffix, including
failure records. The theorem makes no stopped-interval identity claim. -/
theorem run_firstLive_release_pending_nested (a b : ℕ) (hab : a ≤ b) (hb : b < (((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))).length) :
    pendingSet selected.view.payload ((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))[b] ⊆ pendingSet selected.view.payload ((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))[a] := by
  intro i hi
  rcases Nat.eq_or_lt_of_le hab with heq | hlt
  · subst a; exact hi
  · exact (run_release_history initial rows J rewards start count hspan hactive hfirst hseed
      c selected hselected hsingle hevent next owned base hout b hb i hi a hlt).1

/-- Every prefix, including a detecting record's pre-error test, has total,
UP, and DATA release quota one. No terminal update is assumed successful. -/
theorem run_firstLive_release_prefix_quota (i : Fin (p.m - 1)) (n : ℕ) (_hn : n ≤ (((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))).length) :
    releaseCount selected.view.payload ((((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))).take n) i ≤ 1 ∧ upCount selected.view.payload ((((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))).take n) i ≤ 1 ∧
      dataCount selected.view.payload ((((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))).take n) i ≤ 1 := by
  have hfull : releaseCount selected.view.payload ((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1)) i ≤ 1 := by
    apply history_count_le_one
    intro a b _ hb hab hp
    exact (run_release_history initial rows J rewards start count hspan hactive hfirst hseed
      c selected hselected hsingle hevent next owned base hout b hb i hp a hab).2
  have hprefix : releaseCount selected.view.payload ((((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))).take n) i ≤ 1 :=
    (List.take_prefix n ((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))).countP_le.trans hfull
  exact ⟨hprefix, (upCount_le_releaseCount _ _ _).trans hprefix,
    (dataCount_le_releaseCount _ _ _).trans hprefix⟩

/-- A follower still pending has zero prior count, supplying the strict
pre-count `< 1` required by the waiting lemma with quota one. -/
theorem run_firstLive_release_precount_zero (i : Fin (p.m - 1)) (n : ℕ) (hn : n < (((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))).length)
    (hpending : i ∈ pendingSet selected.view.payload ((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))[n]) :
    releaseCount selected.view.payload ((((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))).take n) i = 0 ∧ upCount selected.view.payload ((((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))).take n) i = 0 ∧
      dataCount selected.view.payload ((((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))).take n) i = 0 := by
  have hz : releaseCount selected.view.payload ((((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))).take n) i = 0 := by
    apply List.countP_eq_zero.mpr
    intro r hr hflag
    obtain ⟨a, ha, heq⟩ := List.mem_iff_getElem.mp hr
    have han : a < n := lt_of_lt_of_le ha (List.length_take_le n ((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1)))
    have hal : a < (((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))).length := by omega
    have he : r = ((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))[a] := heq.symm.trans List.getElem_take
    have hf := (run_release_history initial rows J rewards start count hspan hactive hfirst hseed
      c selected hselected hsingle hevent next owned base hout n hn i hpending a han).2
    have hrel := (Bool.and_eq_true_iff.mp hflag).2
    rw [he, hf] at hrel
    cases hrel
  exact ⟨hz, Nat.eq_zero_of_le_zero (by simpa only [hz] using upCount_le_releaseCount selected.view.payload ((((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))).take n) i),
    Nat.eq_zero_of_le_zero (by simpa only [hz] using dataCount_le_releaseCount selected.view.payload ((((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))).take n) i)⟩


omit hselected hsingle hevent hout in
/-- Extract only one actual ordinary follower tail. Every domain and numeric
service success below comes from its own checked operations. Other players
may fail; no ordinary tail is asserted for a detecting player in dagger. -/
theorem run_firstLive_release_focal_tail
    (n : Fin ((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1)).length) (i : Fin (p.m - 1))
    (hpending : i ∈ pendingSet selected.view.payload ((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))[n.val])
    (out : ReferencePrelaunchFollower.State p rate.eta)
    (outMemory : ActiveFollowerLifecycle.LocalMemory p)
    (houtput : ((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))[n.val].output.next.followers i = .ordinary out outMemory) :
    let r := ((runWindow initial rows J rewards start count hspan hactive).drop (c.val + 1))[n.val]
    let own := (r.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2
    ∃ (before : ReferencePrelaunchFollower.State p rate.eta)
      (beforeMemory : ActiveFollowerLifecycle.LocalMemory p)
      (choice : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p)
      (service : ActiveFollowerQueueOperation.ServiceSuccess p rate.eta rate.n i r.input.row
        (r.input.state.activations i) r.input.time own choice)
      (released : ReferencePrelaunchFollower.State p rate.eta),
      r.input.state.followers i = .ordinary before beforeMemory ∧
      ActiveFollowerLifecycle.startRound rate.eta r.input.time before beforeMemory =
        .ok (choice, memory) ∧
      choice.lastDown = before.lastDown ∧ memory = beforeMemory ∧
      ((prepare r.input).followers.followers i).configuration = .ordinary choice memory ∧
      choice.status = .pending ∧ choice.lastDown = some (selected.view.payload.downRecord i) ∧
      ActiveFollowerLifecycle.localStateDomainValid choice ∧
      (selected.view.payload.downRecord i).val.sigma ≤ r.input.time.val ∧
      ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n rate.n_scale
        i r.input.row (r.input.state.activations i) r.input.time own choice = .success service ∧
      (recordFollower (prepare r.input).coordinator.downView i r.input.row
        (r.input.state.activations i) r.input.time (r.input.active i)
        ((prepare r.input).followers.followers i).arm own choice).result = .ok service.output ∧
      ActiveFollowerLifecycle.localStateDomainValid service.output ∧
      service.output.lastDown = choice.lastDown ∧ service.output.status = choice.status ∧
      service.output.buffer = choice.buffer ∧ service.output.downBatch = choice.downBatch ∧
      service.output.initializationFailure = choice.initializationFailure ∧
      (∃ M', service.output.lastDown = some M' ∧ M'.val.sigma ≤ r.input.time.val + 1) ∧
      ActiveFollowerLifecycle.releaseAfterService rate.eta i r.input.time
        (ActiveFollowerLifecycle.publicRowOfCompleteRow r.input.row r.input.time)
        own choice service.output = .ok released ∧
      released = (if releaseFlag selected.view.payload r i = true then
        {service.output with status := .released} else service.output) ∧
      ActiveFollowerLifecycle.finishRound rate.eta r.input.time r.input.row released memory =
        .ok (out, outMemory) ∧ out = released := by
  intro r own
  change i ∈ pendingSet selected.view.payload r at hpending
  change r.output.next.followers i = .ordinary out outMemory at houtput
  have hrw : r ∈ (runWindow initial rows J rewards start count hspan hactive) := List.mem_of_mem_drop (List.getElem_mem n.isLt)
  obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hrw
  have hstate := ReferenceFirstLiveConfirmationHistory.run_firstLive_carried initial rows J
    rewards start count hspan hactive hfirst hseed ⟨k, hk⟩
  change ReferenceFirstLiveConfirmationHistory.FirstLiveState (runWindow initial rows J rewards start count hspan hactive)[k].input.state at hstate
  rw [heq] at hstate
  have hout' : (step r.input).next.followers i = .ordinary out outMemory := by
    rw [← r.output_eq]
    exact houtput
  obtain ⟨choice, memory, post, hchoice, hrecord, htail, _, _⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion _ _ _ out outMemory hout'
  obtain ⟨hrow, hi, ht, hactivation⟩ := (prepare r.input).follower_alignment i
  simp only [hi, hrow, ht, hactivation] at hrecord htail
  rw [← own_observation_eq r i] at hrecord htail
  cases hc : r.input.state.coordinator with
  | first => simp only [pendingSet, pendingAtStart, hc, Finset.notMem_empty] at hpending
  | collection => simp only [pendingSet, pendingAtStart, hc, Finset.notMem_empty] at hpending
  | dagger => simp only [pendingSet, pendingAtStart, hc, Finset.notMem_empty] at hpending
  | live registers registersOwned oldBase =>
      by_cases hg : registers.payload = selected.view.payload ∧ registers.pendingAtChoice = ∅
      · have hp : choice.status = .pending :=
          (pendingAtStart_ordinary_prepare selected.view.payload r.input registers registersOwned
            oldBase hc hg.1 hg.2 i choice memory hchoice).1 hpending
        have hfields : ReferenceActiveDataOwnership.carriedOccupiedFields selected.view.payload r.input.state := by
          have hs : ReferenceActiveDataOwnership.carriedOccupiedFields registers.payload r.input.state ∧
              ∀ i s memory, r.input.state.followers i = .ordinary s memory →
                registers.pendingAtChoice.Nonempty → s.status ≠ .released := by
            simpa only [ReferenceFirstLiveConfirmationHistory.FirstLiveState, hc] using hstate
          simpa only [hg.1] using hs.1
        have hlocal := ReferenceActiveDataOwnership.choice_occupied_fields_preserved selected.view.payload i
          r.input.row (r.input.state.activations i) r.input.time (r.input.active i)
          (r.input.state.followers i) (hfields i)
        change ReferenceActiveDataOwnership.occupiedFields selected.view.payload i
          ((prepare r.input).followers.followers i).configuration at hlocal
        rw [hchoice] at hlocal
        have hm : choice.lastDown = some (selected.view.payload.downRecord i) :=
          hlocal (by rw [hp]; decide)
        obtain ⟨service, hservice, hpost⟩ := service_inversion _ _ _ _ _ _ _ _ choice post
          (by rw [hp]; decide) hrecord
        subst post
        obtain ⟨released, hrelease, hfinish, hframe⟩ :=
          release_finish_inversion _ _ _ _ choice service.output out memory outMemory htail
        obtain ⟨hpre, htime, hpost, hformula⟩ := pending_release_inversion i r.input.time
          _ own choice service.output released (selected.view.payload.downRecord i) hp hm hrelease
        obtain ⟨before, bm, _, hbefore, hstart, _⟩ :=
          ReferenceActiveDataOwnership.prepare_ordinary_choice i r.input.row
            (r.input.state.activations i) r.input.time (r.input.active i)
            (r.input.state.followers i) choice memory hchoice
        obtain ⟨hlast, hbatch, hbuffer, hstatus, hmarker⟩ :=
          LocalReleaseQuota.serviceSuccess_nonqueue_frame service
        obtain ⟨hstartRecord, _, _, _, _, _, _, hstartMemory⟩ :=
          ActiveFollowerLifecycle.startRound_frame rate.eta r.input.time before choice bm memory hstart
        exact ⟨before, bm, choice, memory, service, released, hbefore, hstart,
          hstartRecord, hstartMemory, hchoice,
          hp, hm, hpre, htime, hservice, hrecord, hpost, hlast, hstatus, hbuffer, hbatch,
          hmarker, ⟨selected.view.payload.downRecord i, hlast.trans hm, by omega⟩,
          hrelease, by simpa only [releaseFlag, decide_eq_true_eq] using hformula,
          hfinish, hframe⟩
      · simp only [pendingSet, pendingAtStart, hc, ite_eq_right hg, Finset.notMem_empty] at hpending

end Run

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

/-- Specialize the physical release producer to the actual launched boundary.
All source, private-row, rewards, carry, clean-prefix, forcing, exclusion and
computed-handoff inputs are retained. No initialization agreement is assumed. -/
theorem ofActualLaunchedBoundary_release_history (count : ℕ)
    (hspan : BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) +
      count ≤ p.T) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start :=
      fun i => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
    let W := runWindow initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards start count hspan active
    ∀ (c : Fin W.length) (selected : Selection W[c.val].input),
      (prepare W[c.val].input).coordinator.selection = some selected →
      selected.view.pendingAtChoice = {(PublicDiscreteDraws.selectedFollowerDraw p.two_le_m
        p.m_lt_K (W[c.val].input.row.2 W[c.val].input.time).1)} →
      CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
        selected.view.pendingAtChoice selected.view.cutoff W[c.val].input.time
        (W[c.val].input.row.2 W[c.val].input.time) (prepare W[c.val].input).coordinatorObservation →
      ∀ (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (owned : CoordinatorLiveServiceFinish.OwnedRegisters next) (base : Fin (p.m - 1) → ℕ),
        W[c.val].output.next.coordinator = .live next owned base →
        let L := W.drop (c.val + 1)
        (∀ (a d : ℕ) (had : a ≤ d) (hd : d < L.length),
          pendingSet selected.view.payload L[d] ⊆ pendingSet selected.view.payload L[a]) ∧
        (∀ (i : Fin (p.m - 1)) (n : ℕ), n ≤ L.length →
          releaseCount selected.view.payload (L.take n) i ≤ 1 ∧
          upCount selected.view.payload (L.take n) i ≤ 1 ∧
          dataCount selected.view.payload (L.take n) i ≤ 1) ∧
        (∀ (i : Fin (p.m - 1)) (n : ℕ) (hn : n < L.length),
          i ∈ pendingSet selected.view.payload L[n] →
          releaseCount selected.view.payload (L.take n) i = 0 ∧
          upCount selected.view.payload (L.take n) i = 0 ∧
          dataCount selected.view.payload (L.take n) i = 0) := by
  intro initial start active W c selected hselected hsingle hevent next owned base hout L
  have hfirst := ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator source rewards rate
    C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
  have hseed := ReferenceFirstLiveConfirmationHistory.ofActualLaunchedBoundary_initialFollowers source
    rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
  refine ⟨?_, ?_, ?_⟩
  · intro a d had hd
    exact run_firstLive_release_pending_nested initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan active
      hfirst hseed c selected hselected hsingle hevent next owned base hout a d had hd
  · intro i n hn
    exact run_firstLive_release_prefix_quota initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan active
      hfirst hseed c selected hselected hsingle hevent next owned base hout i n hn
  · intro i n hn hp
    exact run_firstLive_release_precount_zero initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan active
      hfirst hseed c selected hselected hsingle hevent next owned base hout i n hn hp

end ActualLaunch

end Bandits.Support.ReferencePhysicalReleaseQuota
