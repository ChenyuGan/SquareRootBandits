/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalStep

/-!
# Physical confirmation and release collision barriers

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-124`,
`sources/zip4/manuscript/06_interruptions.tex:270-295,303-324`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:100-106`.

These are one-round facts about the accepted computed coordinator/follower
actions and their own typed feedback. They retain the whole round input and
make the actual ordinary follower preparation branch explicit. They do not
assert run-wide assignment agreement or exclude any checked failure branch.
-/

@[expose] public section

namespace Bandits.Support.ReferenceActiveConfirmationRelease

open ConstructorDimensions
open ActiveRoundActions
open PublicDiscreteDraws
open ReferenceActivePhysicalStep
open ReferencePrelaunchFollower
open OrdinaryMessageCodec

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The own observation is the typed projection of this same prepared
physical feedback vector. -/
noncomputable def actualOwnObservation {x : RoundInput p rate} (prepared : PreparedRound x)
    (player : Fin p.m) : Observation p := prepared.feedback.observations player

private theorem follower_prepared_arm_choice_of_ordinary
    {x : RoundInput p rate} (prepared : PreparedRound x)
    (i : Fin (p.m - 1)) (s : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : (prepared.followers.followers i).configuration =
      .ordinary s memory) :
    ∃ offered : Option (UpRecord (codecParams p rate.eta)),
      ActiveFollowerArmChoice.followerArmChoice s (x.rows x.selected) x.time i offered =
        some (prepared.followers.followers i).arm := by
  rw [prepared.followers.followers_eq i,
    ReferenceActiveFeedbackCut.prepareFollowers_apply] at hconfiguration ⊢
  change (DeclaredFollowerLocalRound.prepare rate i (x.rows x.selected)
      (x.state.activations i) x.time (x.active i) (x.state.followers i)).configuration =
    .ordinary s memory at hconfiguration
  cases hinput : x.state.followers i with
  | dagger => simp [DeclaredFollowerLocalRound.prepare, hinput] at hconfiguration
  | ordinary inputState inputMemory =>
      cases hstart : ActiveFollowerLifecycle.startRound rate.eta x.time inputState inputMemory with
      | error reason =>
          simp [DeclaredFollowerLocalRound.prepare, hinput, hstart] at hconfiguration
      | ok pair =>
          rcases pair with ⟨choiceState, choiceMemory⟩
          cases hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i (x.rows x.selected)
              (x.state.activations i) x.time choiceState with
          | failure =>
              simp [DeclaredFollowerLocalRound.prepare, hinput, hstart, hoff] at hconfiguration
          | noOffer =>
              cases hchoice : ActiveFollowerArmChoice.followerArmChoice
                  choiceState (x.rows x.selected) x.time i none with
              | none =>
                  simp [DeclaredFollowerLocalRound.prepare, hinput, hstart, hoff, hchoice]
                    at hconfiguration
              | some arm =>
                  have hstates : choiceState = s ∧ choiceMemory = memory := by
                    simpa [DeclaredFollowerLocalRound.prepare, hinput, hstart, hoff,
                      hchoice] using hconfiguration
                  rcases hstates with ⟨rfl, rfl⟩
                  exact ⟨none, by
                    simp [ReferenceActivePhysicalStep.followerInput,
                      DeclaredFollowerLocalRound.prepare, hinput, hstart, hoff, hchoice]⟩
          | offer offered =>
              cases hchoice : ActiveFollowerArmChoice.followerArmChoice
                  choiceState (x.rows x.selected) x.time i (some offered) with
              | none =>
                  simp [DeclaredFollowerLocalRound.prepare, hinput, hstart, hoff, hchoice]
                    at hconfiguration
              | some arm =>
                  have hstates : choiceState = s ∧ choiceMemory = memory := by
                    simpa [DeclaredFollowerLocalRound.prepare, hinput, hstart, hoff,
                      hchoice] using hconfiguration
                  rcases hstates with ⟨rfl, rfl⟩
                  exact ⟨some offered, by
                    simp [ReferenceActivePhysicalStep.followerInput,
                      DeclaredFollowerLocalRound.prepare, hinput, hstart, hoff, hchoice]⟩

private theorem prepared_coordinator_action_eq_selection
    {x : RoundInput p rate} (prepared : PreparedRound x)
    (selected : Selection x)
    (hselection : prepared.coordinator.selection = some selected) :
    prepared.arms.actions (ActiveRoundActions.coordinator p.two_le_m) = selected.arm := by
  simpa only [DispatchCut.arm, hselection] using prepared.action_coordinator

private theorem prepared_follower_action_eq_retained
    {x : RoundInput p rate} (prepared : PreparedRound x) (i : Fin (p.m - 1)) :
    prepared.arms.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      (prepared.followers.followers i).arm := by
  have hretained : prepared.followers.followers i =
      DeclaredFollowerLocalRound.prepare rate i x.row (x.state.activations i)
        x.time (x.active i) (x.state.followers i) := by
    simpa [ReferenceActivePhysicalStep.followerInput,
      ReferenceActivePhysicalStep.RoundInput.row,
      ReferenceActiveFeedbackCut.prepareFollowers] using prepared.followers.followers_eq i
  calc
    _ = (DeclaredFollowerLocalRound.prepare rate i x.row (x.state.activations i)
          x.time (x.active i) (x.state.followers i)).arm := prepared.action_follower i
    _ = (prepared.followers.followers i).arm := by rw [hretained]

private theorem actual_feedback_zero_of_action_collision
    {x : RoundInput p rate} (prepared : PreparedRound x)
    (player other : Fin p.m) (hother : other ≠ player)
    (hactions : prepared.arms.actions other = prepared.arms.actions player) :
    prepared.feedback.feedback player = 0 := by
  have hcollision : ¬ FiniteBanditModel.collisionFreeFor prepared.arms.actions player := by
    intro hfree
    exact (hfree other hother) hactions
  rw [prepared.feedback_rule]
  simp [hcollision]

private theorem actual_observation_zero_of_action_collision
    {x : RoundInput p rate} (prepared : PreparedRound x)
    (player other : Fin p.m) (hother : other ≠ player)
    (hactions : prepared.arms.actions other = prepared.arms.actions player) :
    (actualOwnObservation prepared player).val.val = 0 := by
  have hfeedback := actual_feedback_zero_of_action_collision prepared player other hother hactions
  have hobservation := prepared.feedback.observation_grid_value player
  rw [hfeedback] at hobservation
  norm_num at hobservation
  simpa [actualOwnObservation] using hobservation

private theorem coordinator_arm_eq_tuple_on_up
    {x : RoundInput p rate} (prepared : PreparedRound x)
    (selected : Selection x)
    (hselection : prepared.coordinator.selection = some selected)
    (hnonempty : selected.view.pendingAtChoice.Nonempty)
    (hslot : slotDraw (x.row.2 x.time).1 = upSlot) :
    prepared.arms.actions (ActiveRoundActions.coordinator p.two_le_m) =
      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
        (ActiveRoundActions.coordinator p.two_le_m) := by
  have hchoice : CoordinatorLocalArmChoice.coordinatorArmChoice
      selected.view.payload selected.view.pendingAtChoice selected.view.cutoff x.time
      selected.view.complementWeights x.row ≠ none := selected.choice_ne_none
  have hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
      selected.view.cutoff x.time selected.view.complementWeights := by
    by_contra hinvalid
    apply hchoice
    rw [CoordinatorLocalArmChoice.coordinatorArmChoice_eq_core]
    exact CoordinatorLocalArmChoice.coordinatorArmChoiceCore_none_of_invalid
      selected.view.payload selected.view.pendingAtChoice selected.view.cutoff x.time
      selected.view.complementWeights (x.row.2 x.time) hinvalid
  have hnotfast : ¬ (CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
      selected.view.cutoff x.time ∧ selected.view.pendingAtChoice = ∅) := by
    rintro ⟨_, hempty⟩
    exact Finset.Nonempty.ne_empty hnonempty hempty
  have hnotdata : slotDraw (x.row.2 x.time).1 ≠ dataSlot := by
    rw [hslot]
    decide
  have hnotdown : ¬ (slotDraw (x.row.2 x.time).1 = downSlot ∧
      selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 x.time).1 ∈
        selected.view.pendingAtChoice) := by
    intro h
    rw [hslot] at h
    exact (by decide : upSlot ≠ downSlot) h.1
  have hcore := CoordinatorLocalArmChoice.coordinatorArmChoiceCore_other
    selected.view.payload selected.view.pendingAtChoice selected.view.cutoff x.time
    selected.view.complementWeights (x.row.2 x.time) hvalid hnotfast hnotdata hnotdown
  have hrow : CoordinatorLocalArmChoice.coordinatorArmChoice selected.view.payload
      selected.view.pendingAtChoice selected.view.cutoff x.time
      selected.view.complementWeights x.row =
        some ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          (x.row.2 x.time).1).val (ActiveRoundActions.coordinator p.two_le_m)) := by
    rw [CoordinatorLocalArmChoice.coordinatorArmChoice_eq_core]
    exact hcore
  rw [selected.choice_eq] at hrow
  have harm : selected.arm =
      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
        (ActiveRoundActions.coordinator p.two_le_m) := Option.some.inj hrow
  exact (prepared_coordinator_action_eq_selection prepared selected hselection).trans harm

private theorem coordinator_arm_eq_pilot_on_data
    {x : RoundInput p rate} (prepared : PreparedRound x)
    (selected : Selection x)
    (hselection : prepared.coordinator.selection = some selected)
    (hnonempty : selected.view.pendingAtChoice.Nonempty)
    (hslot : slotDraw (x.row.2 x.time).1 = dataSlot) :
    prepared.arms.actions (ActiveRoundActions.coordinator p.two_le_m) =
      pilotDraw (K_pos p) (ActiveRoundActions.coordinator p.two_le_m)
        (x.row.2 x.time).1 := by
  have hchoice : CoordinatorLocalArmChoice.coordinatorArmChoice
      selected.view.payload selected.view.pendingAtChoice selected.view.cutoff x.time
      selected.view.complementWeights x.row ≠ none := selected.choice_ne_none
  have hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
      selected.view.cutoff x.time selected.view.complementWeights := by
    by_contra hinvalid
    apply hchoice
    rw [CoordinatorLocalArmChoice.coordinatorArmChoice_eq_core]
    exact CoordinatorLocalArmChoice.coordinatorArmChoiceCore_none_of_invalid
      selected.view.payload selected.view.pendingAtChoice selected.view.cutoff x.time
      selected.view.complementWeights (x.row.2 x.time) hinvalid
  have hnotfast : ¬ (CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
      selected.view.cutoff x.time ∧ selected.view.pendingAtChoice = ∅) := by
    rintro ⟨_, hempty⟩
    exact Finset.Nonempty.ne_empty hnonempty hempty
  have hcore := CoordinatorLocalArmChoice.coordinatorArmChoiceCore_data
    selected.view.payload selected.view.pendingAtChoice selected.view.cutoff x.time
    selected.view.complementWeights (x.row.2 x.time) hvalid hnotfast hslot
  have hrow : CoordinatorLocalArmChoice.coordinatorArmChoice selected.view.payload
      selected.view.pendingAtChoice selected.view.cutoff x.time
      selected.view.complementWeights x.row =
        some (pilotDraw (K_pos p) (ActiveRoundActions.coordinator p.two_le_m)
          (x.row.2 x.time).1) := by
    rw [CoordinatorLocalArmChoice.coordinatorArmChoice_eq_core]
    exact hcore
  rw [selected.choice_eq] at hrow
  have harm : selected.arm = pilotDraw (K_pos p) (ActiveRoundActions.coordinator p.two_le_m)
      (x.row.2 x.time).1 := Option.some.inj hrow
  exact (prepared_coordinator_action_eq_selection prepared selected hselection).trans harm

private theorem accepted_escape_eq_down_auxiliary
    (M : DownRecord (codecParams p rate.eta)) :
    ActiveFollowerLifecycle.acceptedEscapeArm M = ActiveFollowerArmChoice.downAuxiliaryArm
      rate.eta M := by
  apply Fin.ext
  rfl

private theorem releaseAfterService_success_keeps_post_state
    (eta : LearningRate) (i : Fin (p.m - 1)) (t : Fin p.T)
    (row : ActiveFollowerLifecycle.FollowerPublicRow p.m p.K)
    (own : Observation p) (preChoice postService out : ReferencePrelaunchFollower.State p eta)
    (M : DownRecord (codecParams p eta))
    (hpending : preChoice.status = .pending)
    (hrecord : preChoice.lastDown = some M)
    (hfailed : ¬ ActiveFollowerLifecycle.releaseCondition eta i row own M)
    (hout : ActiveFollowerLifecycle.releaseAfterService eta i t row own preChoice postService =
      .ok out) : out = postService := by
  classical
  unfold ActiveFollowerLifecycle.releaseAfterService at hout
  simp only [dite_eq_left hpending, hrecord] at hout
  by_cases hpre : ActiveFollowerLifecycle.localStateDomainValid preChoice
  · simp only [dite_eq_left hpre] at hout
    by_cases htime : M.val.sigma ≤ t.val
    · simp only [dite_eq_left htime] at hout
      by_cases hpost : ActiveFollowerLifecycle.localStateDomainValid postService
      · simp only [dite_eq_left hpost, ite_eq_right hfailed] at hout
        split at hout
        · exact (Except.ok.inj hout).symm
        · simp at hout
      · simp [hpost] at hout
    · simp [htime] at hout
  · simp [hpre] at hout

/-- A pending selected assignment's actual release observation is zero on
each literal UP or DATA release test. The accepted `lastDown` is used only to
identify this follower's own arm on those tests. -/
theorem no_releaseObservation_while_missing
    {x : RoundInput p rate} (prepared : PreparedRound x)
    (selected : Selection x)
    (hselection : prepared.coordinator.selection = some selected)
    (i : Fin (p.m - 1))
    (choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hnonempty : selected.view.pendingAtChoice.Nonempty)
    (hconfiguration : (prepared.followers.followers i).configuration =
      .ordinary choiceState memory)
    (hpending : choiceState.status = .pending)
    (hlastDown : choiceState.lastDown = some (selected.view.payload.downRecord i)) :
    ¬ ActiveFollowerLifecycle.releaseCondition rate.eta i
      (ActiveFollowerLifecycle.publicRowOfCompleteRow x.row x.time)
      (actualOwnObservation prepared (PublicDiscreteDraws.followerPlayer p.two_le_m i))
      (selected.view.payload.downRecord i) := by
  unfold ActiveFollowerLifecycle.releaseCondition ActiveFollowerLifecycle.releaseTests
    ActiveFollowerLifecycle.publicRowOfCompleteRow
  rintro ⟨hpositive, hup | hdata⟩
  · rcases hup with ⟨hslot, hselected, htuple⟩
    obtain ⟨offered, hlocal⟩ := follower_prepared_arm_choice_of_ordinary
      prepared i choiceState memory hconfiguration
    have htupleAux :
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
          (ActiveRoundActions.coordinator p.two_le_m) =
          ActiveFollowerArmChoice.downAuxiliaryArm rate.eta
            (selected.view.payload.downRecord i) := by
      calc
        _ = ActiveFollowerLifecycle.acceptedEscapeArm
              (selected.view.payload.downRecord i) := htuple
        _ = ActiveFollowerArmChoice.downAuxiliaryArm rate.eta
              (selected.view.payload.downRecord i) :=
          accepted_escape_eq_down_auxiliary (selected.view.payload.downRecord i)
    have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_pending_selected_up_escape
      choiceState (x.row.2 x.time) i offered (selected.view.payload.downRecord i)
      hpending hlastDown hslot hselected htupleAux
    have hlocalAux : ActiveFollowerArmChoice.followerArmChoice choiceState x.row x.time i
        offered = some (ActiveFollowerArmChoice.downAuxiliaryArm rate.eta
          (selected.view.payload.downRecord i)) := by
      rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
      exact hcore
    have harm := Option.some.inj (hlocal.symm.trans hlocalAux)
    have hcoord := coordinator_arm_eq_tuple_on_up prepared selected hselection
      hnonempty hslot
    have hcollision : prepared.arms.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
        prepared.arms.actions (ActiveRoundActions.coordinator p.two_le_m) := by
      calc
        _ = (prepared.followers.followers i).arm := prepared_follower_action_eq_retained prepared i
        _ = ActiveFollowerArmChoice.downAuxiliaryArm rate.eta
              (selected.view.payload.downRecord i) := harm
        _ = (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
              (x.row.2 x.time).1).val (ActiveRoundActions.coordinator p.two_le_m) :=
          htupleAux.symm
        _ = prepared.arms.actions (ActiveRoundActions.coordinator p.two_le_m) := hcoord.symm
    have hzero := actual_observation_zero_of_action_collision prepared
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
      (ActiveRoundActions.coordinator p.two_le_m)
      (ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i).symm hcollision.symm
    rw [hzero] at hpositive
    exact (lt_irrefl 0) hpositive
  · rcases hdata with ⟨hslot, hpilot⟩
    obtain ⟨offered, hlocal⟩ := follower_prepared_arm_choice_of_ordinary
      prepared i choiceState memory hconfiguration
    have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_occupied_data_or_released
      choiceState (x.row.2 x.time) i offered (selected.view.payload.downRecord i)
      (by rw [hpending]; decide) hlastDown (Or.inr hslot)
    have hlocalDown : ActiveFollowerArmChoice.followerArmChoice choiceState x.row x.time i
        offered = some (PrelaunchBufferRecovery.downArm rate.eta
          (selected.view.payload.downRecord i)) := by
      rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
      exact hcore
    have harm := Option.some.inj (hlocal.symm.trans hlocalDown)
    have hcoord := coordinator_arm_eq_pilot_on_data prepared selected hselection
      hnonempty hslot
    have hcollision : prepared.arms.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
        prepared.arms.actions (ActiveRoundActions.coordinator p.two_le_m) := by
      calc
        _ = (prepared.followers.followers i).arm := prepared_follower_action_eq_retained prepared i
        _ = PrelaunchBufferRecovery.downArm rate.eta
              (selected.view.payload.downRecord i) := harm
        _ = pilotDraw (K_pos p) (ActiveRoundActions.coordinator p.two_le_m)
              (x.row.2 x.time).1 := hpilot.symm
        _ = prepared.arms.actions (ActiveRoundActions.coordinator p.two_le_m) := hcoord.symm
    have hzero := actual_observation_zero_of_action_collision prepared
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
      (ActiveRoundActions.coordinator p.two_le_m)
      (ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i).symm hcollision.symm
    rw [hzero] at hpositive
    exact (lt_irrefl 0) hpositive

/-- The literal confirmation updater used by `livePostChoice` erases the
selected pending follower when its actual coordinator observation satisfies
the DOWN confirmation event. The event is evaluated on the same complete row
and the same `PreparedRound` feedback projection consumed by that call. -/
theorem livePostChoice_confirmationUpdate_erases
    {x : RoundInput p rate} (prepared : PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hevent : CoordinatorLocalArmChoice.downConfirmationEvent r.payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time
      (x.row.2 x.time) prepared.coordinatorObservation) :
    CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time x.row prepared.coordinatorObservation =
      some (started.pending.erase (selectedFollowerDraw p.two_le_m p.m_lt_K
        (x.row.2 x.time).1)) := by
  have hevent' := hevent
  rcases hevent with ⟨⟨hstarted, hbeforecutoff⟩, _, _, _, _, _⟩
  have hcutoff : CoordinatorLocalArmChoice.assignmentStart r.payload ≤
      CoordinatorLocalArmChoice.cutoffRound
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) := by
    exact le_trans hstarted (Nat.le_of_lt hbeforecutoff)
  have hvalid := CoordinatorLocalArmChoice.confirmationInputsValid_mk r.payload
    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time
    hstarted hcutoff
  unfold CoordinatorLocalArmChoice.confirmationUpdate
  exact CoordinatorLocalArmChoice.confirmationUpdateCore_removes r.payload started.pending
    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time
    (x.row.2 x.time) prepared.coordinatorObservation hvalid hevent'

/-- Under the actual successful recorder, service, and FinishRound branches,
the erasure above is consumed by `livePostChoice` itself. Its returned live
registers therefore contain the accepted post-confirmation pending set. -/
theorem livePostChoice_confirmation_success
    {x : RoundInput p rate} (prepared : PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (serviced : CoordinatorLiveServiceFinish.ServicedRegisters r q)
    (finished : CoordinatorPhaseClock.FinishRoundResult p)
    (hrecord : CoordinatorRecorderComplementBridge.run
      (liveRecordingInput prepared r started) = some recording)
    (hservice : CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced)
    (hevent : CoordinatorLocalArmChoice.downConfirmationEvent r.payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time
      (x.row.2 x.time) prepared.coordinatorObservation)
    (hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
      (started.pending.erase (selectedFollowerDraw p.two_le_m p.m_lt_K
        (x.row.2 x.time).1)) x.row = .ok finished) :
    ReferenceActivePhysicalStep.livePostChoice prepared r q base started =
      ⟨.live {
          payload := r.payload
          priorClock := finished.clock
          pendingAtChoice := finished.pending
          time := x.time
          gridBoundary := finished.clock.g
          complementScores := serviced.score }
        { queue := serviced.queue, previousService := serviced.previousService } base,
        x.state.upDecoderBank, none, some recording, none⟩ := by
  have hconfirmation := livePostChoice_confirmationUpdate_erases prepared r started hevent
  exact ReferenceActivePhysicalStep.livePostChoice_success prepared r q base started
    recording serviced (started.pending.erase (selectedFollowerDraw p.two_le_m p.m_lt_K
      (x.row.2 x.time).1)) finished hrecord hservice hconfirmation hfinish

/-- A positive actual DOWN confirmation observation cannot come from an
unoccupied selected follower. It therefore leaves the prepared ordinary
choice snapshot in one of the two occupied states. -/
theorem downConfirmationEvent_implies_occupied
    {x : RoundInput p rate} (prepared : PreparedRound x)
    (selected : Selection x)
    (hselection : prepared.coordinator.selection = some selected)
    (choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : (prepared.followers.followers
      (selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 x.time).1)).configuration =
      .ordinary choiceState memory)
    (hevent : CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
      selected.view.pendingAtChoice selected.view.cutoff x.time (x.row.2 x.time)
      prepared.coordinatorObservation) :
    choiceState.status = .pending ∨ choiceState.status = .released := by
  let i : Fin (p.m - 1) :=
    selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 x.time).1
  have hindex : i = selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 x.time).1 := rfl
  rcases hevent with ⟨_, hnonempty, hslot, hmember, hhash, hpositive⟩
  by_cases hpending : choiceState.status = .pending
  · exact Or.inl hpending
  · by_cases hreleased : choiceState.status = .released
    · exact Or.inr hreleased
    · have hunoccupied : choiceState.status = .unoccupied := by
        cases hstatus : choiceState.status <;> simp_all
      obtain ⟨offered, hlocal⟩ := follower_prepared_arm_choice_of_ordinary
        prepared i choiceState memory hconfiguration
      have hnotdata : slotDraw (x.row.2 x.time).1 ≠ dataSlot := by
        rw [hslot]
        decide
      have hnotselectedUp : ¬ (slotDraw (x.row.2 x.time).1 = upSlot ∧
          selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 x.time).1 = i) := by
        intro h
        rw [hslot] at h
        exact (by decide : downSlot ≠ upSlot) h.1
      have hfollowerCore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other
        choiceState (x.row.2 x.time) i offered hunoccupied hnotdata hnotselectedUp
      have hfollowerChoice : ActiveFollowerArmChoice.followerArmChoice choiceState x.row x.time i
          offered = some ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
            (x.row.2 x.time).1).val
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
        rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
        exact hfollowerCore
      have hfollowerArm : (prepared.followers.followers i).arm =
          (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i) :=
        Option.some.inj (hlocal.symm.trans hfollowerChoice)
      have hnotfast : ¬ (CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
          selected.view.cutoff x.time ∧ selected.view.pendingAtChoice = ∅) := by
        rintro ⟨_, hempty⟩
        exact Finset.Nonempty.ne_empty hnonempty hempty
      have hchoice : CoordinatorLocalArmChoice.coordinatorArmChoice selected.view.payload
          selected.view.pendingAtChoice selected.view.cutoff x.time
          selected.view.complementWeights x.row ≠ none := selected.choice_ne_none
      have hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
          selected.view.cutoff x.time selected.view.complementWeights := by
        by_contra hinvalid
        apply hchoice
        rw [CoordinatorLocalArmChoice.coordinatorArmChoice_eq_core]
        exact CoordinatorLocalArmChoice.coordinatorArmChoiceCore_none_of_invalid
          selected.view.payload selected.view.pendingAtChoice selected.view.cutoff x.time
          selected.view.complementWeights (x.row.2 x.time) hinvalid
      have hcore := CoordinatorLocalArmChoice.coordinatorArmChoiceCore_down
        selected.view.payload selected.view.pendingAtChoice selected.view.cutoff x.time
        selected.view.complementWeights (x.row.2 x.time) hvalid hnotfast hnotdata hslot hmember
      have hhash' : CoordinatorLocalArmChoice.currentDownHash selected.view.payload
          (x.row.2 x.time) i = 0 := by
        simpa only [← hindex] using hhash
      have hrow : CoordinatorLocalArmChoice.coordinatorArmChoice selected.view.payload
          selected.view.pendingAtChoice selected.view.cutoff x.time
          selected.view.complementWeights x.row =
            some (ActiveRoundActions.sendArm 0
              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                (x.row.2 x.time).1).val (ActiveRoundActions.coordinator p.two_le_m))
              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                (x.row.2 x.time).1).val
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i))) := by
        rw [CoordinatorLocalArmChoice.coordinatorArmChoice_eq_core]
        simpa only [← hindex, hhash'] using hcore
      rw [selected.choice_eq] at hrow
      have hselectedArm : selected.arm =
          (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
            (x.row.2 x.time).1).val
              (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
        have h := Option.some.inj hrow
        simpa only [ActiveRoundActions.sendArm_zero] using h
      have hcoordAction := prepared_coordinator_action_eq_selection prepared selected hselection
      have hcollision : prepared.arms.actions
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
          prepared.arms.actions (ActiveRoundActions.coordinator p.two_le_m) := by
        calc
          _ = (prepared.followers.followers i).arm := prepared_follower_action_eq_retained prepared i
          _ = (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
                (PublicDiscreteDraws.followerPlayer p.two_le_m i) := hfollowerArm
          _ = selected.arm := hselectedArm.symm
          _ = prepared.arms.actions (ActiveRoundActions.coordinator p.two_le_m) := hcoordAction.symm
      have hzero := actual_feedback_zero_of_action_collision prepared
        (ActiveRoundActions.coordinator p.two_le_m)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
        (ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i) hcollision
      have hpositiveIndex : 0 < prepared.coordinatorObservation.val :=
        (CoordinatorLocalArmChoice.ownGridObservationValue_pos_iff
          (p := p) prepared.coordinatorObservation).mp hpositive
      have hgridZero : prepared.coordinatorObservation = 0 := by
        change prepared.feedback.feedback (ActiveRoundActions.coordinator p.two_le_m) = 0
        exact hzero
      rw [hgridZero] at hpositiveIndex
      exact False.elim (by norm_num at hpositiveIndex)

/-- A successful ordinary `recordFollower` / `releaseAndFinish` branch in this
actual pending choice retains the accepted record and pending status. The
recording result is derived through checked occupied service; release reads
the saved choice snapshot; FinishRound returns its input state. -/
theorem pending_choice_successful_finish_preserves_status
    {x : RoundInput p rate} (prepared : PreparedRound x)
    (selected : Selection x)
    (hselection : prepared.coordinator.selection = some selected)
    (i : Fin (p.m - 1))
    (choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hnonempty : selected.view.pendingAtChoice.Nonempty)
    (hconfiguration : (prepared.followers.followers i).configuration =
      .ordinary choiceState memory)
    (hpending : choiceState.status = .pending)
    (hlastDown : choiceState.lastDown = some (selected.view.payload.downRecord i))
    (postRecord : ReferencePrelaunchFollower.State p rate.eta)
    (hrecord : (recordFollower prepared.coordinator.downView
      (prepared.followers.followers i).follower (prepared.followers.followers i).row
      (prepared.followers.followers i).activation (prepared.followers.followers i).time
      (prepared.followers.followers i).active (prepared.followers.followers i).arm
      (actualOwnObservation prepared (PublicDiscreteDraws.followerPlayer p.two_le_m i))
      choiceState).result = .ok postRecord)
    (nextState : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate
      (prepared.followers.followers i).follower (prepared.followers.followers i).row
      (prepared.followers.followers i).time
      (actualOwnObservation prepared (PublicDiscreteDraws.followerPlayer p.two_le_m i))
      choiceState memory postRecord = .ok (nextState, nextMemory)) :
    (finishFollower prepared.coordinator.downView (prepared.followers.followers i)
      (actualOwnObservation prepared (PublicDiscreteDraws.followerPlayer p.two_le_m i))).configuration =
        .ordinary nextState nextMemory ∧
    nextState.status = .pending ∧
      nextState.lastDown = some (selected.view.payload.downRecord i) := by
  let localPrepared := prepared.followers.followers i
  let observation := actualOwnObservation prepared
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hrecord' : (recordFollower prepared.coordinator.downView localPrepared.follower
      localPrepared.row localPrepared.activation localPrepared.time localPrepared.active
      localPrepared.arm observation choiceState).result = .ok postRecord := by
    simpa [localPrepared, observation] using hrecord
  have hfinish' : DeclaredFollowerLocalRound.releaseAndFinish rate localPrepared.follower
      localPrepared.row localPrepared.time observation choiceState memory postRecord =
        .ok (nextState, nextMemory) := by
    simpa [localPrepared, observation] using hfinish
  have hrecordService : DeclaredFollowerLocalRound.recordOrServiceThenDown rate
      localPrepared.follower localPrepared.row localPrepared.activation localPrepared.time
      localPrepared.active localPrepared.arm observation choiceState = .ok postRecord := by
    have hresult := ReferenceActivePhysicalStep.recordFollower_result
      prepared.coordinator.downView localPrepared.follower localPrepared.row
      localPrepared.activation localPrepared.time localPrepared.active localPrepared.arm
      observation choiceState
    rw [hresult] at hrecord'
    simpa [ReferenceDownReception.loggingThenReferenceDown, hpending] using hrecord'
  have hserviceFields : postRecord.status = .pending ∧
      postRecord.lastDown = some (selected.view.payload.downRecord i) := by
    cases hservice : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
        rate.n rate.n_scale localPrepared.follower localPrepared.row localPrepared.activation
        localPrepared.time observation choiceState with
    | failure =>
        simp [DeclaredFollowerLocalRound.recordOrServiceThenDown, hpending, hservice]
          at hrecordService
    | success serviced =>
        have hpost : postRecord = serviced.output := by
          have heq : serviced.output = postRecord := by
            simpa [DeclaredFollowerLocalRound.recordOrServiceThenDown, hpending,
              hservice] using hrecordService
          exact heq.symm
        have hfields := ActiveFollowerQueueOperation.serviceOutput_preserves_other_registers
          rate.n choiceState serviced.arrival
        constructor
        · rw [hpost, serviced.queueUpdate]
          exact hfields.2.2.2.1.trans hpending
        · rw [hpost, serviced.queueUpdate]
          exact hfields.1.trans hlastDown
  have hrelease := no_releaseObservation_while_missing prepared selected hselection i
    choiceState memory hnonempty hconfiguration hpending hlastDown
  have halign := prepared.follower_alignment i
  have hreleaseLocal : ¬ ActiveFollowerLifecycle.releaseCondition rate.eta
      localPrepared.follower
      (ActiveFollowerLifecycle.publicRowOfCompleteRow localPrepared.row localPrepared.time)
      observation (selected.view.payload.downRecord i) := by
    rw [show localPrepared.follower = i from halign.2.1,
      show localPrepared.row = x.row from halign.1,
      show localPrepared.time = x.time from halign.2.2.1]
    exact hrelease
  unfold DeclaredFollowerLocalRound.releaseAndFinish at hfinish'
  cases hreleaseCall : ActiveFollowerLifecycle.releaseAfterService rate.eta
      localPrepared.follower localPrepared.time
      (ActiveFollowerLifecycle.publicRowOfCompleteRow localPrepared.row localPrepared.time)
      observation choiceState postRecord with
  | error failure => simp [hreleaseCall] at hfinish'
  | ok afterRelease =>
      cases hfinishCall : ActiveFollowerLifecycle.finishRound rate.eta localPrepared.time
          localPrepared.row afterRelease memory with
      | error failure => simp [hreleaseCall, hfinishCall] at hfinish'
      | ok result =>
          simp only [hreleaseCall, hfinishCall] at hfinish'
          have hpair : result = (nextState, nextMemory) := Except.ok.inj hfinish'
          have hfinishSuccess : ActiveFollowerLifecycle.finishRound rate.eta
              localPrepared.time localPrepared.row afterRelease memory =
                .ok (nextState, nextMemory) := by
            rw [hpair] at hfinishCall
            exact hfinishCall
          have hnext := ActiveFollowerLifecycle.finishRound_frame rate.eta
            localPrepared.time localPrepared.row afterRelease nextState memory nextMemory
            hfinishSuccess
          have hreleaseState := releaseAfterService_success_keeps_post_state
            rate.eta localPrepared.follower localPrepared.time
            (ActiveFollowerLifecycle.publicRowOfCompleteRow localPrepared.row localPrepared.time)
            observation choiceState postRecord afterRelease
            (selected.view.payload.downRecord i)
            hpending hlastDown hreleaseLocal hreleaseCall
          have hnextPostRecord : nextState = postRecord := hnext.trans hreleaseState
          have hsuccess := ReferenceActivePhysicalStep.finishFollower_success
            prepared.coordinator.downView localPrepared observation choiceState postRecord
            nextState memory nextMemory hconfiguration hrecord' hfinish
          refine ⟨hsuccess.1, ?_, ?_⟩
          · rw [hnextPostRecord]
            exact hserviceFields.1
          · rw [hnextPostRecord]
            exact hserviceFields.2

/-- A logging, service, or DOWN failure in the actual follower tail keeps its
exact first failure tag and enters the dagger configuration. -/
theorem finishFollower_record_failure_is_dagger
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (failure : DeclaredFollowerLocalRound.RoundFailure)
    (hconfiguration : prepared.configuration = .ordinary choiceState memory)
    (hrecord : (recordFollower view prepared.follower prepared.row prepared.activation
      prepared.time prepared.active prepared.arm observation choiceState).result = .error failure) :
    (finishFollower view prepared observation).configuration = .dagger ∧
      (finishFollower view prepared observation).failure = some failure := by
  simp [finishFollower, hconfiguration, hrecord]

/-- A release or FinishRound failure in the actual follower tail keeps its
exact tag and enters the dagger configuration. -/
theorem finishFollower_release_finish_failure_is_dagger
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (postRecord : ReferencePrelaunchFollower.State p rate.eta)
    (failure : DeclaredFollowerLocalRound.RoundFailure)
    (hconfiguration : prepared.configuration = .ordinary choiceState memory)
    (hrecord : (recordFollower view prepared.follower prepared.row prepared.activation
      prepared.time prepared.active prepared.arm observation choiceState).result = .ok postRecord)
    (hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row
      prepared.time observation choiceState memory postRecord = .error failure) :
    (finishFollower view prepared observation).configuration = .dagger ∧
      (finishFollower view prepared observation).failure = some failure := by
  simp [finishFollower, hconfiguration, hrecord, hfinish]

end Bandits.Support.ReferenceActiveConfirmationRelease

end
