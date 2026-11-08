/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CoordinatorRoundDispatch
public import Bandits.Support.ReferenceActiveFeedbackCut
public import Bandits.Support.ReferenceDownReception
public import Bandits.Support.ReferenceUpReception

/-!
# Canonical postlaunch registers and the reference round's choice cut

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-70,123-177,192-297,355-426`,
`sources/zip4/manuscript/08_main_theorem.tex:29-42`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.

There is one coordinator register store, one local configuration per follower,
and one persistent UP bank. Row, calendar coordinate, and feedback are transient
inputs. The dispatcher result is retained in full, including every original
start result and failure. Sender words come from its actual choice and the
followers' actual preparations. No probability law, history invariant, overflow
stopping rule, or manuscript closure is asserted here.

The transition runs one checked post-choice tail per player and stores the
resulting canonical fields. Decoder diagnostics are transient round evidence;
no arbitrary physical history is an input.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceActivePhysicalStep

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition


abbrev RateInput := ActiveFollowerDownAcceptance.RateInput
abbrev Payload {p : Parameters} (rate : RateInput p) :=
  AssignmentStartPayload.Input p rate.eta
abbrev Ledger {p : Parameters} (rate : RateInput p) :=
  CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
    rate.n rate.n_scale

variable {p : Parameters} {rate : RateInput p}

/-- The disjoint coordinator phases. Collection retains its original payload;
its moving queues, pending set, and base scores are stored only in the ledger.
Live scores and queues use the accepted register carriers. -/
inductive CoordinatorConfiguration (p : Parameters) (rate : RateInput p) where
  | first
  | live (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (baseScores : Fin (p.m - 1) → ℕ)
  | collection (payload : Payload rate) (ledger : Ledger rate)
      (savedProposal : Option (Fin p.T × Bool))
  | dagger

/-- The sole postlaunch storage carrier. UP batches survive all coordinator
phase changes. Follower configurations already contain their ordinary state,
sparse buffer, DOWN batch, proposal memory, or the absorbing dagger tag. -/
structure State (p : Parameters) (rate : RateInput p) where
  coordinator : CoordinatorConfiguration p rate
  upDecoderBank : CoordinatorUpReception.UpDecoderBank p
  activations : Fin (p.m - 1) → ReferencePrelaunchFollower.Activation p
  followers : Fin (p.m - 1) → DeclaredFollowerLocalRound.LocalConfiguration p rate

/-- Honest inputs for one active calendar round. The active-time typing proof
is explicit; it is not a successful-decoding or physical-history assumption.
The reward input ranges over the entire denominator-D table. -/
structure RoundInput (p : Parameters) (rate : RateInput p) where
  state : State p rate
  rows : CompletePublicTable.CompleteRows p
  selected : Fin (M p)
  time : Fin p.T
  active : ∀ i, (state.activations i).val ≤ time.val + 1
  rewards : ActualInitializationPhysicalStep.GridRewardTable p

def RoundInput.row (x : RoundInput p rate) : CompletePublicTable.CompleteRow p :=
  x.rows x.selected

/-- Reindex the call coordinate of the stored live registers for this round.
The payload, prior clock, grid boundary, pending set, and scores are untouched.
The carried `time` field is a local call index, not a second protocol clock. -/
def liveRegistersAt (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta) (t : Fin p.T) :
    CoordinatorLiveChoiceRecorderStep.Registers p rate.eta := { r with time := t }

def liveOwnedAt (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta) (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (t : Fin p.T) : CoordinatorLiveServiceFinish.OwnedRegisters (liveRegistersAt r t) :=
  { queue := q.queue, previousService := q.previousService }

def firstInput (x : RoundInput p rate) : CoordinatorRoundDispatch.FirstInput p :=
  { eta := rate.eta, eta_le_source_cap := rate.sourceCap
    n := rate.n, n_eq_eta_mul_D := rate.n_scale, time := x.time, row := x.row }

def liveInput (x : RoundInput p rate) (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ) : CoordinatorRoundDispatch.LiveInput p :=
  { eta := rate.eta, registers := liveRegistersAt r x.time
    ownedRegisters := liveOwnedAt r q x.time
    followerBaseScore := base, row := x.row }

/-- A collection clock is a transient projection of the sole ledger clock
fields, the immutable original start, and retained proposal memory. -/
def collectionClock (payload : Payload rate) (ledger : Ledger rate)
    (savedProposal : Option (Fin p.T × Bool)) (cutoff : Fin p.T) :
    CoordinatorPhaseClock.ClockRegisters p := {
  sigma := some payload.sigma
  u := some cutoff
  g := ledger.freezeAt
  lastProposal := savedProposal }

/-- The collection view reads the cutoff from the actual clock, base scores
from the actual ledger, and the bank from the sole persistent store. The
dispatcher checks all ledger/clock/payload matching conditions. -/
def collectionInput (x : RoundInput p rate) (payload : Payload rate)
    (ledger : Ledger rate) (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T) :
    CoordinatorRoundDispatch.CollectionInput p :=
  { etaReal := rate.eta.val, etaPositive := rate.eta.property
    n := rate.n, n_cast_identity := rate.n_scale
    payload := payload, baseScores := ledger.baseScore, ledger := ledger
    clock := clock, upDecoderBank := x.state.upDecoderBank
    cutoffIndex := cutoff, time := x.time, row := x.row }

/-- The shared rate forces the payload's exact integer numerator. No separate
rate or numerator equality is supplied as a premise. -/
theorem payload_n_eq (payload : Payload rate) : payload.n = rate.n := by
  apply Nat.cast_injective (R := ℝ)
  exact payload.n_eq_eta_mul_D.trans rate.n_scale.symm

theorem liveRegistersAt_fields (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta) (t : Fin p.T) :
    (liveRegistersAt r t).payload = r.payload ∧
    (liveRegistersAt r t).priorClock = r.priorClock ∧
    (liveRegistersAt r t).pendingAtChoice = r.pendingAtChoice ∧
    (liveRegistersAt r t).gridBoundary = r.gridBoundary ∧
    (liveRegistersAt r t).complementScores = r.complementScores ∧
    (liveRegistersAt r t).time = t := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Full retained outcomes, with no translation of the dispatcher's failure
tags. An out-of-domain ledger cutoff is a malformed collection phase; dagger performs no call.
These values are transient evidence, not additional mutable protocol stores. -/
inductive DispatchCut (x : RoundInput p rate) where
  | first (outcome : CoordinatorRoundDispatch.FirstOutcome (firstInput x))
  | live (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta) (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (base : Fin (p.m - 1) → ℕ)
      (outcome : CoordinatorRoundDispatch.LiveOutcome (liveInput x registers owned base))
  | collection (payload : Payload rate) (ledger : Ledger rate)
      (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
      (outcome : CoordinatorRoundDispatch.CollectionOutcome (collectionInput x payload ledger clock cutoff))
  | invalidCollectionCutoff
  | dagger

/-- Invoke the accepted dispatcher on the state's actual transient view once.
There is no second StartRound, assignment sample, receiver, or dispatcher. -/
def dispatch (x : RoundInput p rate) : DispatchCut x :=
  match x.state.coordinator with
  | .first =>
      match CoordinatorRoundDispatch.dispatch (.first (firstInput x)) with
      | .first outcome => .first outcome
  | .live r q base =>
      match CoordinatorRoundDispatch.dispatch (.live (liveInput x r q base)) with
      | .live outcome => .live r q base outcome
  | .collection payload ledger savedProposal =>
      if hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T then
        let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := collectionClock payload ledger savedProposal cutoff
        match CoordinatorRoundDispatch.dispatch
            (.collection (collectionInput x payload ledger clock cutoff)) with
        | .collection outcome => .collection payload ledger clock cutoff outcome
      else .invalidCollectionCutoff
  | .dagger => .dagger

/-- The coordinator's source arm on active dagger rounds is source arm 1. -/
def coordinatorFallback (p : Parameters) : Fin p.K := ⟨0, K_pos p⟩

/-- A successful choice tied to its original dispatcher clock and actual
choice equation. Its row and time are those of the one physical round. -/
structure Selection (x : RoundInput p rate) where
  view : ReferenceDownReception.ChoiceTimeView p rate.eta
  started : CoordinatorPhaseClock.StartRoundResult p
  pending_eq : view.pendingAtChoice = started.pending
  cutoff_eq : view.cutoff = CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u
  arm : Fin p.K
  choice_eq : CoordinatorLocalArmChoice.coordinatorArmChoice view.payload
    view.pendingAtChoice view.cutoff x.time view.complementWeights x.row = some arm

/-- Check the literal choice coordinate before exposing a sender view.
This is an operation-domain check on the whole outcome carrier, not a supplied
agreement premise. The original dispatcher outcome remains in `DispatchCut`.
-/
def selectionAt (x : RoundInput p rate) (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (selection : CoordinatorRoundDispatch.ArmSelection payload started time weights x.row) :
    Option (Selection x) := by
  classical
  if htime : time = x.time then
    exact some {
      view := {
        payload := payload
        pendingAtChoice := started.pending
        cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u
        complementWeights := weights }
      started := started, pending_eq := rfl, cutoff_eq := rfl
      arm := selection.arm
      choice_eq := by simpa only [htime] using selection.armChoice_eq }
  else exact none

/-- Derive the checked same-round sender/arm view from all successful dispatch
branches. Every other branch retains its original failure and uses fallback.
Installed first/later registers and the changed cutoff result are used directly.
-/
def DispatchCut.selection {x : RoundInput p rate} (cut : DispatchCut x) :
    Option (Selection x) := by
  classical
  match cut with
  | .first (.chosen installed selected) =>
      exact selectionAt x installed.registers.payload installed.startRoundResult
        installed.registers.time installed.registers.complementWeights selected
  | .live r q base (.continuingChosen dispatched _ _ selected) =>
      exact selectionAt x r.payload dispatched.startResult x.time
        (liveRegistersAt r x.time).complementWeights selected
  | .live r q base (.cutoffChosen dispatched _ _ _ _ _ _ _ _ selected) =>
      exact selectionAt x r.payload dispatched.startResult x.time
        (liveRegistersAt r x.time).complementWeights selected
  | .collection payload ledger clock cutoff (.continuing _ prepared boundary _) =>
      let source := collectionInput x payload ledger clock cutoff
      have hcutoff : CoordinatorLiveChoiceRecorderStep.cutoffFromClock p prepared.clockStarted.clock.u =
          some (CoordinatorCollectionUpRoundStep.localCutoff cutoff) := by
        rw [prepared.clockStarted_frame.1]
        change CoordinatorLiveChoiceRecorderStep.cutoffFromClock p clock.u = _
        have hc : clock.u = some cutoff := prepared.inputsValid.clock_cutoff_eq
        rw [hc]
        rfl
      exact some {
        view := {
          payload := payload
          pendingAtChoice := prepared.clockStarted.pending
          cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p prepared.clockStarted.clock.u
          complementWeights := CoordinatorCollectionInteractive.PreObservationInputs.weights source
            prepared.inputsValid.ledger_valid prepared.inputsValid.assignment_eq }
        started := prepared.clockStarted, pending_eq := rfl, cutoff_eq := rfl
        arm := prepared.arm
        choice_eq := by
          change CoordinatorLocalArmChoice.coordinatorArmChoice payload
            prepared.clockStarted.pending _ x.time _ x.row = some prepared.arm
          rw [hcutoff]
          exact prepared.armChoice_eq }
  | .collection _ _ _ _
      (.laterChosen _ _ started _ instruction _ _ _ _ installed selected) =>
      exact selectionAt x installed.registers.payload started instruction.time
        installed.registers.complementWeights selected
  | _ => exact none

def DispatchCut.arm {x : RoundInput p rate} (cut : DispatchCut x) : Fin p.K :=
  match cut.selection with
  | some selected => selected.arm
  | none => coordinatorFallback p

def DispatchCut.downView {x : RoundInput p rate} (cut : DispatchCut x) :
    Option (ReferenceDownReception.ChoiceTimeView p rate.eta) := cut.selection.map Selection.view

/-- A retained successful selection proves same-round ordinary choice, so the
DOWN expected word cannot be supplied independently of the dispatched action.
-/
theorem Selection.choice_ne_none {x : RoundInput p rate} (selected : Selection x) :
    CoordinatorLocalArmChoice.coordinatorArmChoice selected.view.payload
      selected.view.pendingAtChoice selected.view.cutoff x.time
      selected.view.complementWeights x.row ≠ none := by
  rw [selected.choice_eq]
  exact Option.some_ne_none _

theorem Selection.expected_down_word {x : RoundInput p rate}
    (selected : Selection x) (i : Fin (p.m - 1))
    (hbranch : ReferenceDownReception.selectedDownSenderBranch selected.view i x.row x.time) :
    ReferenceDownReception.expectedDownFlatWord (some selected.view) i x.row x.time =
      some (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i) :=
  (ReferenceDownReception.expectedDownFlatWord_eq_some_iff selected.view i x.row x.time).mpr
    ⟨selected.choice_ne_none, hbranch⟩

/-- Preserve the immutable assignment-start q field, rather than substituting
any of the canonical collection ledger's moving queues. -/
theorem Selection.down_initial_queue {x : RoundInput p rate}
    (selected : Selection x) (i : ActiveRoundActions.Follower p.m) :
    (selected.view.payload.downRecord i).val.q =
      selected.view.payload.queues (selected.view.payload.assignment.assigned i) :=
  selected.view.payload.downRecord_initialQueue i

def followerInput (x : RoundInput p rate) : ReferenceActiveFeedbackCut.RoundInput p rate :=
  { rows := x.rows, selected := x.selected, time := x.time
    activations := x.state.activations, active := x.active
    configurations := x.state.followers }

/-- The preparation stores the complete original coordinator outcome and the
one preparation of every follower, before actions or feedback are evaluated. -/
structure PreparedRound (x : RoundInput p rate) where
  coordinator : DispatchCut x
  coordinator_eq : coordinator = dispatch x
  followers : ReferenceActiveFeedbackCut.PreparedRound (followerInput x)

def prepare (x : RoundInput p rate) : PreparedRound x :=
  { coordinator := dispatch x, coordinator_eq := rfl
    followers := ReferenceActiveFeedbackCut.prepare (followerInput x) }

def PreparedRound.arms {x : RoundInput p rate} (prepared : PreparedRound x) :
    ReferenceActiveFeedbackCut.ActionInputs (followerInput x) :=
  { coordinatorArm := prepared.coordinator.arm, preparation := prepared.followers }

def PreparedRound.feedback {x : RoundInput p rate} (prepared : PreparedRound x) :
    ReferenceActiveFeedbackCut.FeedbackCut prepared.arms x.rewards := ReferenceActiveFeedbackCut.assembleFeedback prepared.arms x.rewards

/-- Derive every follower preparation's row, player index, calendar coordinate,
and activation from the actual PREPARE operation. No alignment input is added.
-/
theorem local_prepare_alignment (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1) (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate) :
    let prepared := DeclaredFollowerLocalRound.prepare rate i row activation t active configuration
    prepared.row = row ∧ prepared.follower = i ∧ prepared.time = t ∧
      prepared.activation = activation := by
  classical
  cases configuration with
  | dagger => exact ⟨rfl, rfl, rfl, rfl⟩
  | ordinary state memory =>
      cases hstart : ActiveFollowerLifecycle.startRound rate.eta t state memory with
      | error reason => simp [DeclaredFollowerLocalRound.prepare, hstart]
      | ok pair =>
          obtain ⟨choiceState, choiceMemory⟩ := pair
          cases hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation t
              choiceState with
          | failure => simp [DeclaredFollowerLocalRound.prepare, hstart, hoff]
          | noOffer =>
              cases hchoice : ActiveFollowerArmChoice.followerArmChoice choiceState row t i none <;>
                simp [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice]
          | offer offered =>
              cases hchoice : ActiveFollowerArmChoice.followerArmChoice choiceState row t i
                  (some offered) <;>
                simp [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice]

theorem PreparedRound.follower_alignment {x : RoundInput p rate}
    (prepared : PreparedRound x) (i : Fin (p.m - 1)) :
    (prepared.followers.followers i).row = x.row ∧
    (prepared.followers.followers i).follower = i ∧
    (prepared.followers.followers i).time = x.time ∧
    (prepared.followers.followers i).activation = x.state.activations i := by
  rw [prepared.followers.followers_eq i]
  exact local_prepare_alignment i x.row (x.state.activations i) x.time
    (x.active i) (x.state.followers i)

/-- No coordinator arm is a free input to the physical feedback cut. -/
theorem PreparedRound.action_coordinator {x : RoundInput p rate}
    (prepared : PreparedRound x) :
    prepared.arms.actions (ActiveRoundActions.coordinator p.two_le_m) =
      prepared.coordinator.arm := prepared.arms.actions_coordinator

theorem PreparedRound.action_follower {x : RoundInput p rate}
    (prepared : PreparedRound x) (i : Fin (p.m - 1)) :
    prepared.arms.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      (DeclaredFollowerLocalRound.prepare rate i x.row (x.state.activations i) x.time (x.active i)
        (x.state.followers i)).arm := prepared.arms.actions_follower_eq_prepare i

theorem PreparedRound.feedback_rule {x : RoundInput p rate}
    (prepared : PreparedRound x) (player : Fin p.m) :
    prepared.feedback.feedback player =
      if FiniteBanditModel.collisionFreeFor prepared.arms.actions player then
        x.rewards x.time (prepared.arms.actions player) else 0 :=
  prepared.feedback.feedback_collision_rule player

theorem PreparedRound.own_entry {x : RoundInput p rate}
    (prepared : PreparedRound x) (player : Fin p.m) :
    prepared.feedback.ownEntries player =
      (prepared.arms.actions player,
        ActualInitializationPhysicalStep.observationOfGrid p
          (prepared.feedback.feedback player)) := prepared.feedback.own_entry_eq player

/-- The first post-choice follower stage keeps the exact checked logging or
service result and, only when called, the actual pre-effect DOWN cut. -/
structure FollowerRecord where
  result : Except DeclaredFollowerLocalRound.RoundFailure (ReferencePrelaunchFollower.State p rate.eta)
  downInput : Option (ReferencePrelaunchFollower.State p rate.eta)
  down : Option (ReferenceDownReception.ReferenceDownCutOutput p rate)

def recordFollower (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState : ReferencePrelaunchFollower.State p rate.eta) :
    FollowerRecord (rate := rate) := by
  classical
  if hunoccupied : choiceState.status = .unoccupied then
    match ActiveFollowerLogging.checkedLogging i row activation t (arm, observation)
        choiceState with
    | .error reason => exact ⟨.error (.logging reason), none, none⟩
    | .ok logged =>
        let cut := ReferenceDownReception.referenceDownCut p view i row t observation rate logged
        exact ⟨DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome, some logged, some cut⟩
  else
    exact ⟨DeclaredFollowerLocalRound.recordOrServiceThenDown rate i row activation t active arm observation
      choiceState, none, none⟩

/-- This diagnostic-preserving decomposition is exactly the accepted
logging/reference-DOWN wrapper, including occupied service and all failures.
-/
theorem recordFollower_result (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState : ReferencePrelaunchFollower.State p rate.eta) :
    (recordFollower view i row activation t active arm observation choiceState).result =
      ReferenceDownReception.loggingThenReferenceDown rate view i row activation t active arm observation
        choiceState := by
  classical
  by_cases hstatus : choiceState.status = .unoccupied
  · simp only [recordFollower, ReferenceDownReception.loggingThenReferenceDown,
      dite_eq_left hstatus]
    cases hlogging : ActiveFollowerLogging.checkedLogging i row activation t
        (arm, observation) choiceState <;> rfl
  · simp only [recordFollower, ReferenceDownReception.loggingThenReferenceDown,
      dite_eq_right hstatus]

/-- The complete follower tail retains failure stages and actual DOWN data.
The final proposal read is performed by the accepted release/finish tail.
-/
structure FollowerObservation (p : Parameters) (rate : RateInput p) where
  configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate
  failure : Option DeclaredFollowerLocalRound.RoundFailure
  downInput : Option (ReferencePrelaunchFollower.State p rate.eta)
  down : Option (ReferenceDownReception.ReferenceDownCutOutput p rate)

def finishFollower (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p) :
    FollowerObservation p rate :=
  match prepared.configuration with
  | .dagger => ⟨.dagger, none, none, none⟩
  | .ordinary state memory =>
      let recorded := recordFollower view prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm observation state
      match recorded.result with
      | .error failure => ⟨.dagger, some failure, recorded.downInput, recorded.down⟩
      | .ok postRecord =>
          match DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row prepared.time
              observation state memory postRecord with
          | .error failure => ⟨.dagger, some failure, recorded.downInput, recorded.down⟩
          | .ok (next, nextMemory) => ⟨.ordinary next nextMemory, none, recorded.downInput, recorded.down⟩

/-- The actual own observation is derived from the simultaneous collision
vector; the sender view is derived from the same retained dispatcher result.
-/
def PreparedRound.observeFollower {x : RoundInput p rate}
    (prepared : PreparedRound x) (i : Fin (p.m - 1)) : FollowerObservation p rate :=
  finishFollower prepared.coordinator.downView (prepared.followers.followers i)
    (prepared.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i))

theorem finishFollower_dagger (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (hdagger : prepared.configuration = .dagger) :
    (finishFollower view prepared observation).configuration = .dagger ∧
      (finishFollower view prepared observation).down = none := by
  simp [finishFollower, hdagger]

/-- A successful post-choice decomposition, with branch conditions on the
literal calls. This helper does not assert successful recovery or no dagger.
-/
theorem finishFollower_success (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state postRecord next : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : prepared.configuration = .ordinary state memory)
    (hrecord : (recordFollower view prepared.follower prepared.row prepared.activation
      prepared.time prepared.active prepared.arm observation state).result = .ok postRecord)
    (hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row prepared.time
      observation state memory postRecord = .ok (next, nextMemory)) :
    (finishFollower view prepared observation).configuration = .ordinary next nextMemory ∧
      (finishFollower view prepared observation).failure = none := by
  simp [finishFollower, hconfiguration, hrecord, hfinish]

/-- The per-decision no-mismatch condition is evaluated only on the actual
logged state, after successful logging. It asserts no truthful score or UP
history, and contains no condition on occupied service or logging failure.
-/
def no_down_mismatch (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p) : Prop :=
  match prepared.configuration with
  | .dagger => True
  | .ordinary state _ =>
      state.status = .unoccupied →
        ∀ logged, ActiveFollowerLogging.checkedLogging prepared.follower prepared.row
          prepared.activation prepared.time (prepared.arm, observation) state = .ok logged →
          ¬ ReferenceDownReception.rawMismatch (ReferenceDownReception.referenceDownCut p view prepared.follower prepared.row
            prepared.time observation rate logged)

theorem recordFollower_eq_ordinary_of_no_mismatch
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hmatch : state.status = .unoccupied → ∀ logged,
      ActiveFollowerLogging.checkedLogging i row activation t (arm, observation) state =
        .ok logged → ¬ ReferenceDownReception.rawMismatch (ReferenceDownReception.referenceDownCut p view i row t observation rate logged)) :
    (recordFollower view i row activation t active arm observation state).result =
      DeclaredFollowerLocalRound.recordOrServiceThenDown rate i row activation t active arm observation state := by
  classical
  rw [recordFollower_result]
  by_cases hunoccupied : state.status = .unoccupied
  · cases hlogging : ActiveFollowerLogging.checkedLogging i row activation t
        (arm, observation) state with
    | error reason =>
        simp only [ReferenceDownReception.loggingThenReferenceDown, DeclaredFollowerLocalRound.recordOrServiceThenDown,
          dite_eq_left hunoccupied, hlogging]
    | ok logged =>
        exact ReferenceDownReception.loggingThenReferenceDown_eq_declared_of_matching rate view i row
          activation t active arm observation state logged hunoccupied hlogging
          (hmatch hunoccupied logged hlogging)
  · simp only [ReferenceDownReception.loggingThenReferenceDown, dite_eq_right hunoccupied]

/-- Under the literal decision condition, the next follower configuration is
exactly the accepted ordinary observer's configuration. This is a conditional
local comparison, not a reference/ordinary execution coupling. -/
theorem finishFollower_eq_observe_of_no_mismatch
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (hmatch : no_down_mismatch view prepared observation) :
    (finishFollower view prepared observation).configuration =
      (DeclaredFollowerLocalRound.observe prepared observation).configuration := by
  classical
  cases hconfiguration : prepared.configuration with
  | dagger => simp [finishFollower, DeclaredFollowerLocalRound.observe, hconfiguration]
  | ordinary state memory =>
      have hrecord := recordFollower_eq_ordinary_of_no_mismatch view prepared.follower
        prepared.row prepared.activation prepared.time prepared.active prepared.arm
        observation state (by simpa only [no_down_mismatch, hconfiguration] using hmatch)
      cases hstage : DeclaredFollowerLocalRound.recordOrServiceThenDown rate
          prepared.follower prepared.row prepared.activation prepared.time prepared.active
          prepared.arm observation state with
      | error reason =>
          simp [finishFollower, DeclaredFollowerLocalRound.observe, hconfiguration,
            hrecord, DeclaredFollowerLocalRound.observeOrdinary, hstage]
      | ok postRecord =>
          cases hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower
              prepared.row prepared.time observation state memory postRecord <;>
            simp [finishFollower, DeclaredFollowerLocalRound.observe, hconfiguration,
              hrecord, DeclaredFollowerLocalRound.observeOrdinary, hstage, hfinish]

/-- Adapt only the phantom numerator/cap indices of a collection ledger. Both
numerators obey the same exact scale identity; all stored fields are copied
literally. This is used for the dispatcher's newly initialized cutoff ledger.
-/
def sharedLedger {n : ℕ} {hn : (n : ℝ) = rate.eta.val * (D p : ℝ)}
    {cap : CoordinatorCollectionLedger.sourceLearningCap p rate.eta.val}
    (ledger : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property cap n hn) :
    Ledger rate := {
  assignment := ledger.assignment
  sigma := ledger.sigma
  cutoff := ledger.cutoff
  freezeAt := ledger.freezeAt
  baseScore := ledger.baseScore
  pending := ledger.pending
  cutoffRegisters := ledger.cutoffRegisters
  currentRegisters := ledger.currentRegisters
  increment := ledger.increment
  gammaLoc := ledger.gammaLoc
  rawBuffer := ledger.rawBuffer
  enabledHistory := ledger.enabledHistory
  cursor := ledger.cursor
  phase := ledger.phase }

theorem shared_n_eq {n : ℕ} (hn : (n : ℝ) = rate.eta.val * (D p : ℝ)) :
    n = rate.n := by
  apply Nat.cast_injective (R := ℝ)
  exact hn.trans rate.n_scale.symm

/-- All concrete UP decoder input/batch data and the actual raw/parsed tests
are retained. A `none` raw word is not classified as ambiguity or false
acceptance. The input includes the old persistent bank and current sample.
-/
structure UpDiagnostic (p : Parameters) (rate : RateInput p) where
  input : CoordinatorUpReception.ReceptionInput p rate.eta.val rate.eta.property
    (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
  expected : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))
  decoderAfter : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)
  raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))
  parsed : Option (OrdinaryMessageCodec.UpRecord
    (CoordinatorCollectionLedger.codecParams p rate.eta.val))
  locallyAccepted : Bool
  rawMatches : Bool
  wrongUniqueAccepted : Bool

structure UpCut (p : Parameters) (rate : RateInput p) where
  result : CoordinatorCollectionLedger.Checked
    (Ledger rate × CoordinatorUpReception.UpDecoderBank p)
  diagnostic : Option (UpDiagnostic p rate)

def PreparedRound.coordinatorObservation {x : RoundInput p rate}
    (prepared : PreparedRound x) : Fin (D p + 1) :=
  prepared.feedback.feedback (ActiveRoundActions.coordinator p.two_le_m)

def upInputs {x : RoundInput p rate} (prepared : PreparedRound x)
    (ledger : Ledger rate) : ReferenceUpReception.ReceptionLocalInputs rate :=
  (ledger, (x.state.upDecoderBank, (x.time, prepared.coordinatorObservation)))

/-- Exactly the sender selected by the coordinator's same-row UP adapter. -/
def upSenderIndex (x : RoundInput p rate) : Fin (p.m - 1) :=
  CoordinatorUpMeasurability.selectedFollowerIndex (x.row.2 x.time)

def upExpected {x : RoundInput p rate} (prepared : PreparedRound x) : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)) :=
  ReferenceUpReception.currentOfferWord rate x.row (upSenderIndex x) x.time
    (prepared.followers.followers (upSenderIndex x))
    (prepared.follower_alignment _).1
    (prepared.follower_alignment _).2.1
    (prepared.follower_alignment _).2.2.1

/-- Invoke the accepted pre-effect filtered receiver, using the actual
prepared selected follower and the ledger after same-round service. Alignment
is derived from the original PREPARE calls and the literal row adapter.
-/
def receiveUp {x : RoundInput p rate} (prepared : PreparedRound x)
    (ledger : Ledger rate) : UpCut p rate := by
  classical
  let inputs := upInputs prepared ledger
  let input := ReferenceUpReception.receptionInputAtRow rate x.row inputs x.time
  let sender := prepared.followers.followers (upSenderIndex x)
  have hrow : sender.row = x.row := (prepared.follower_alignment _).1
  have hplayer : sender.follower = input.selectedFollower :=
    (prepared.follower_alignment _).2.1
  have htime : sender.time = input.time := (prepared.follower_alignment _).2.2.1
  let result := ReferenceUpReception.receiveUpFilteredAtRow rate x.row inputs x.time
    sender hrow hplayer htime rfl
  let diagnostic : Option (UpDiagnostic p rate) :=
    if CoordinatorUpReception.receptionInputCheck input = true then
    let expected := upExpected prepared
    let transition := CoordinatorUpReception.decoderTransition input
    some {
      input := input
      expected := expected
      decoderAfter := transition.1
      raw := transition.2
      parsed := ReferenceUpReception.rawParsedOutput rate input
      locallyAccepted := ReferenceUpReception.rawParsedLocalAcceptance rate input
      rawMatches := decide (transition.2 = expected)
      wrongUniqueAccepted := ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow
        rate x.row inputs x.time sender hrow hplayer htime rfl }
    else none
  exact ⟨result, diagnostic⟩

/-- The no-mismatch condition uses this exact decoder input and this exact
prepared checked UP offer; it contains no truthful-UP or score premise. -/
theorem receiveUp_eq_ordinary_of_no_mismatch {x : RoundInput p rate}
    (prepared : PreparedRound x) (ledger : Ledger rate)
    (hmatch : (CoordinatorUpReception.decoderTransition
      (ReferenceUpReception.receptionInputAtRow rate x.row (upInputs prepared ledger)
        x.time)).2 = upExpected prepared) :
    (receiveUp prepared ledger).result = CoordinatorUpReception.receiveUp
      (ReferenceUpReception.receptionInputAtRow rate x.row (upInputs prepared ledger) x.time) := by
  exact ReferenceUpReception.receiveUpFilteredAtRow_eq_receiveUp_of_no_mismatch rate x.row
    (upInputs prepared ledger) x.time (prepared.followers.followers (upSenderIndex x))
    (prepared.follower_alignment _).1 (prepared.follower_alignment _).2.1
    (prepared.follower_alignment _).2.2.1 rfl hmatch

/-- Failure stages after dispatch. Original dispatch failure tags and all
original start results remain separately available in `PreparedRound`.
-/
inductive CoordinatorFailure where
  | dispatchRejected
  | live (reason : CoordinatorLiveServiceFinish.Failure)
  | collection (reason : CoordinatorCollectionUpRoundStep.Failure)

structure CoordinatorObservation (p : Parameters) (rate : RateInput p) where
  configuration : CoordinatorConfiguration p rate
  upDecoderBank : CoordinatorUpReception.UpDecoderBank p
  failure : Option CoordinatorFailure
  recording : Option (CoordinatorRecordingOperation.Output p)
  up : Option (UpDiagnostic p rate)

def coordinatorFailure (bank : CoordinatorUpReception.UpDecoderBank p)
    (reason : CoordinatorFailure) (recording : Option (CoordinatorRecordingOperation.Output p))
    (up : Option (UpDiagnostic p rate)) : CoordinatorObservation p rate :=
  ⟨.dagger, bank, some reason, recording, up⟩

def liveRecordingInput {x : RoundInput p rate} (prepared : PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    CoordinatorRecorderComplementBridge.Input r.payload := {
  currentWeights := r.complementWeights
  time := x.time
  gridBoundary := started.clock.g
  row := x.row
  ownArm := prepared.coordinator.arm
  observation := prepared.coordinatorObservation
  mode := .live (decide (started.pending = ∅)) }

/-- Direct live post-choice tail. This consumes the original start result;
it creates no unchanged-clock continuation and never calls StartRound.
All scores/queues are the actual accepted service-pass outputs.
-/
def livePostChoice {x : RoundInput p rate} (prepared : PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
    CoordinatorObservation p rate := by
  classical
  match CoordinatorRecorderComplementBridge.run (liveRecordingInput prepared r started) with
  | none => exact coordinatorFailure x.state.upDecoderBank (.live .recorderRejected) none none
  | some recording =>
      match CoordinatorLiveServiceFinish.servicePass r q recording with
      | .error reason =>
          exact coordinatorFailure x.state.upDecoderBank (.live reason) (some recording) none
      | .ok serviced =>
          match CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row prepared.coordinatorObservation with
          | none =>
              exact coordinatorFailure x.state.upDecoderBank (.live .confirmationRejected)
                (some recording) none
          | some pending =>
              match CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
                  pending x.row with
              | .error reason =>
                  exact coordinatorFailure x.state.upDecoderBank
                    (.live (CoordinatorLiveServiceFinish.finishFailureCode reason))
                    (some recording) none
              | .ok finished =>
                  let next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta := {
                    payload := r.payload
                    priorClock := finished.clock
                    pendingAtChoice := finished.pending
                    time := x.time
                    gridBoundary := finished.clock.g
                    complementScores := serviced.score }
                  exact ⟨.live next {
                      queue := serviced.queue, previousService := serviced.previousService } base,
                    x.state.upDecoderBank, none, some recording, none⟩

/-- Finish the actual filtered collection reception, including ordinary
decoder rejection. The bank returned by reception survives even if a later
finish operation fails. Finishing does not issue a same-round new start.
-/
def collectionFinish {x : RoundInput p rate} (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p) (cut : UpCut p rate) :
    CoordinatorObservation p rate := by
  let finish := fun (ledger : Ledger rate) (bank : CoordinatorUpReception.UpDecoderBank p) =>
    match CoordinatorCollectionLedger.finishRound ledger with
    | .invalid => coordinatorFailure bank (.collection .ledgerFinishDomain) (some recording)
        cut.diagnostic
    | .rejected _ => coordinatorFailure bank (.collection .ledgerFinishDomain) (some recording)
        cut.diagnostic
    | .success ledgerFinished =>
        match CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
            ledgerFinished.pending x.row with
        | .error reason => coordinatorFailure bank (.collection (.clockFinish reason))
            (some recording) cut.diagnostic
        | .ok clockFinished =>
            ⟨.collection payload ledgerFinished clockFinished.clock.lastProposal, bank, none,
              some recording, cut.diagnostic⟩
  exact match cut.result with
  | .invalid => coordinatorFailure x.state.upDecoderBank (.collection .upReceptionDomain)
      (some recording) cut.diagnostic
  | .success (ledger, bank) => finish ledger bank
  | .rejected (ledger, bank) => finish ledger bank

def collectionRecordingInput {x : RoundInput p rate} (prepared : PreparedRound x)
    (payload : Payload rate) (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    CoordinatorRecorderComplementBridge.Input payload := {
  currentWeights := weights
  time := x.time
  gridBoundary := started.clock.g
  row := x.row
  ownArm := prepared.coordinator.arm
  observation := prepared.coordinatorObservation
  mode := .collection }

/-- The freeze test controls service, not whether collection/decoding runs. -/
def collectionEnabled (ledger : Ledger rate) (time : Fin p.T) : Bool :=
  decide (0 < ledger.sigma ∧ ledger.cutoff ≤ time.val + 1 ∧ time.val + 1 < ledger.freezeAt)

/-- Direct collection post-choice tail, also used on the first cutoff round.
Stage (1) serves known queues or preserves them when disabled, retaining raw
arrivals for unknown queues. The UP filter precedes decode acceptance/replay;
only then are the ledger and original phase clock finished.
-/
def collectionPostChoice {x : RoundInput p rate} (prepared : PreparedRound x)
    (payload : Payload rate) (ledger : Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    CoordinatorObservation p rate := by
  classical
  match CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput prepared payload started weights) with
  | none => exact coordinatorFailure x.state.upDecoderBank (.collection .recorderDomain) none none
  | some recording =>
      let enabled := collectionEnabled ledger x.time
      let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording
      match CoordinatorCollectionLedger.startRound ledger (x.time.val + 1) enabled raw with
      | .invalid =>
          exact coordinatorFailure x.state.upDecoderBank (.collection .ledgerStartDomain)
            (some recording) none
      | .rejected _ =>
          exact coordinatorFailure x.state.upDecoderBank (.collection .ledgerStartDomain)
            (some recording) none
      | .success ledgerStarted =>
          exact collectionFinish (x := x) payload started recording (receiveUp prepared ledgerStarted)

/-- Consume precisely the successful dispatch branches. On failed dispatch or
time alignment, enter the source's local absorbing state. The full original
dispatcher outcome is retained by the caller, rather than compressed here.
-/
def PreparedRound.observeCoordinator {x : RoundInput p rate} (prepared : PreparedRound x) :
    CoordinatorObservation p rate := by
  classical
  if prepared.coordinator.selection = none then
    exact match prepared.coordinator with
    | .dagger => ⟨.dagger, x.state.upDecoderBank, none, none, none⟩
    | _ => coordinatorFailure x.state.upDecoderBank .dispatchRejected none none
  else
    match prepared.coordinator with
    | .first (.chosen installed _) =>
        exact livePostChoice prepared installed.registers installed.ownedRegisters
          installed.followerBaseScore installed.startRoundResult
    | .live r q base (.continuingChosen dispatched _ _ _) =>
        exact livePostChoice prepared (liveRegistersAt r x.time) (liveOwnedAt r q x.time)
          base dispatched.startResult
    | .live r q _ (.cutoffChosen dispatched _ ledger _ _ _ _ _ _ _) =>
        exact collectionPostChoice prepared r.payload (sharedLedger ledger)
          dispatched.startResult (liveRegistersAt r x.time).complementWeights
    | .collection payload ledger clock cutoff (.continuing _ snapshot _ _) =>
        let source := collectionInput x payload ledger clock cutoff
        exact collectionPostChoice prepared payload ledger snapshot.clockStarted
          (CoordinatorCollectionInteractive.PreObservationInputs.weights source
            snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
    | .collection _ _ _ _ (.laterChosen _ _ started _ _ _ _ _ _ installed _) =>
        exact livePostChoice prepared installed.registers installed.ownedRegisters
          installed.retainedBaseScore started
    | _ => exact coordinatorFailure x.state.upDecoderBank .dispatchRejected none none

/-- Exact one-round result. Preparation and decoder data are transient proof
evidence; `next` is the one mutable-state successor. Its own entries come from
the already fixed simultaneous profile and grid feedback.
-/
structure RoundOutput (x : RoundInput p rate) where
  preparation : PreparedRound x
  coordinator : CoordinatorObservation p rate
  followers : Fin (p.m - 1) → FollowerObservation p rate
  next : State p rate
  ownEntries : Fin p.m → Fin p.K × ReferencePrelaunchFollower.Observation p

/-- One deterministic physical round. There is no analytical-overflow guard,
no horizon recursion, and no action coordinate beyond `Fin T`.
-/
def step (x : RoundInput p rate) : RoundOutput x :=
  let prepared := prepare x
  let coordinator := prepared.observeCoordinator
  let followers := prepared.observeFollower
  { preparation := prepared
    coordinator := coordinator
    followers := followers
    next := {
      coordinator := coordinator.configuration
      upDecoderBank := coordinator.upDecoderBank
      activations := x.state.activations
      followers := fun i => (followers i).configuration }
    ownEntries := prepared.feedback.ownEntries }

theorem step_next_fields (x : RoundInput p rate) :
    (step x).next.coordinator = (prepare x).observeCoordinator.configuration ∧
    (step x).next.upDecoderBank = (prepare x).observeCoordinator.upDecoderBank ∧
    (step x).next.activations = x.state.activations ∧
    (∀ i, (step x).next.followers i = ((prepare x).observeFollower i).configuration) :=
  ⟨rfl, rfl, rfl, fun _ => rfl⟩

theorem step_own_entry (x : RoundInput p rate) (player : Fin p.m) :
    (step x).ownEntries player =
      ((prepare x).arms.actions player,
        ActualInitializationPhysicalStep.observationOfGrid p
          ((prepare x).feedback.feedback player)) := (prepare x).own_entry player

theorem dispatch_dagger (x : RoundInput p rate)
    (hstate : x.state.coordinator = .dagger) : dispatch x = .dagger := by
  simp only [dispatch, hstate]

theorem dispatch_first (x : RoundInput p rate)
    (hstate : x.state.coordinator = .first) :
    dispatch x = .first (CoordinatorRoundDispatch.dispatchFirst (firstInput x)) := by
  simp only [dispatch, hstate, CoordinatorRoundDispatch.dispatch]
  rfl

/-- A malformed collection cutoff does not silently become a first/live
state. It retains its distinct pre-choice failure and the source fallback arm.
-/
theorem dispatch_collection_invalid_cutoff (x : RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate) (savedProposal : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger savedProposal)
    (hcutoff : ¬ (1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T)) :
    dispatch x = .invalidCollectionCutoff ∧
      (dispatch x).arm = coordinatorFallback p := by
  simp [dispatch, hstate, hcutoff, DispatchCut.arm, DispatchCut.selection]

/-- The first installation in the computed dispatcher uses the actual call
coordinate. The branch equation is a condition on this concrete operation,
not a supplied invariant of a history or an independent installed snapshot.
-/
theorem dispatchFirst_chosen_installation (x : RoundInput p rate)
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput (firstInput x)))
    (selection : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights x.row)
    (hchosen : CoordinatorRoundDispatch.dispatchFirst (firstInput x) =
      .chosen installed selection) : installed =
      CoordinatorAssignmentRegisterInstall.installFirst
        (CoordinatorRoundDispatch.firstLaunchInput (firstInput x)) := by
  classical
  unfold CoordinatorRoundDispatch.dispatchFirst at hchosen
  extract_lets launch actualInstall started payload weights cutoff hpayload hstarted hcutoff
    hweights hchoice hboundary hnonempty at hchosen
  split at hchosen
  · contradiction
  · exact (CoordinatorRoundDispatch.FirstOutcome.chosen.inj hchosen).1.symm

theorem dispatchFirst_chosen_time (x : RoundInput p rate)
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput (firstInput x)))
    (selection : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights x.row)
    (hchosen : CoordinatorRoundDispatch.dispatchFirst (firstInput x) =
      .chosen installed selection) : installed.registers.time = x.time := by
  rw [dispatchFirst_chosen_installation x installed selection hchosen]
  exact CoordinatorAssignmentRegisterInstall.first_registers_time _

/-- The actual computed first start has zero learner scores/queues/services
and follower bases. This is not a score-reconstruction truth assumption. -/
theorem dispatchFirst_zero_seed (x : RoundInput p rate)
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput (firstInput x)))
    (selection : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights x.row)
    (hchosen : CoordinatorRoundDispatch.dispatchFirst (firstInput x) =
      .chosen installed selection) :
    (∀ a, installed.registers.complementScores a = 0) ∧
    (∀ a, installed.ownedRegisters.queue a = 0) ∧
    (∀ a, installed.ownedRegisters.previousService a = 0) ∧
    (∀ i, installed.followerBaseScore i = 0) := by
  rw [dispatchFirst_chosen_installation x installed selection hchosen]
  exact ⟨fun a => CoordinatorAssignmentRegisterInstall.first_registers_complement_scores _ a,
    fun a => CoordinatorAssignmentRegisterInstall.first_owned_queue _ a,
    fun a => CoordinatorAssignmentRegisterInstall.first_owned_previous_service _ a,
    fun i => CoordinatorAssignmentRegisterInstall.first_follower_base_score _ i⟩

/-- The later instruction's calendar coordinate follows from the original
checked StartRound result. In particular the alignment check cannot resample
or substitute a new start on the corrected or renewed branch.
-/
theorem later_instruction_time (x : RoundInput p rate) (payload : Payload rate)
    (ledger : Ledger rate) (clock : CoordinatorPhaseClock.ClockRegisters p)
    (cutoff : Fin p.T)
    (core : CoordinatorRoundDispatch.CollectionCoreValid
      (collectionInput x payload ledger clock cutoff))
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val x.time clock ledger.pending =
      .ok started)
    (hinstruction : started.assignmentStart = some instruction) :
    instruction.time = x.time :=
  (CoordinatorPhaseClock.startRound_assignment_effect p rate.eta.val x.time clock
    ledger.pending started instruction core.clock_parameter_valid core.clock_registers_valid
    core.clock_start_time_valid hstart hinstruction).1

theorem selectionAt_arm (x : RoundInput p rate) (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (selected : CoordinatorRoundDispatch.ArmSelection payload started time weights x.row)
    (htime : time = x.time) :
    (selectionAt x payload started time weights selected).map Selection.arm =
      some selected.arm := by
  simp [selectionAt, htime]

/-- Every selected DOWN word is derived from the same actual coordinator
choice used in the simultaneous action profile, including the actual hash
and source-selected follower. -/
theorem action_eq_down_sendArm {x : RoundInput p rate} (prepared : PreparedRound x)
    (selected : Selection x) (hselected : prepared.coordinator.selection = some selected)
    (i : Fin (p.m - 1))
    (hbranch : ReferenceDownReception.selectedDownSenderBranch selected.view i x.row x.time) :
    prepared.arms.actions (ActiveRoundActions.coordinator p.two_le_m) =
      ActiveRoundActions.sendArm
        (CoordinatorLocalArmChoice.currentDownHash selected.view.payload (x.row.2 x.time) i)
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
          (ActiveRoundActions.coordinator p.two_le_m))
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
  rw [prepared.action_coordinator]
  have hsend := ReferenceDownReception.coordinatorArmChoice_eq_sendArm_of_selectedDownSenderBranch
    selected.view i x.row x.time selected.choice_ne_none hbranch
  rw [selected.choice_eq] at hsend
  have harm := Option.some.inj hsend
  simpa only [DispatchCut.arm, hselected] using harm

/-- Disabled collection preserves its scheduling: only the service bit is
zero. The collectionPostChoice decomposition below still calls the receiver
and both finish operations on every successfully started frozen round.
-/
theorem collectionEnabled_of_frozen (ledger : Ledger rate) (time : Fin p.T)
    (hfrozen : ledger.freezeAt ≤ time.val + 1) : collectionEnabled ledger time = false := by
  simp [collectionEnabled, Nat.not_lt_of_ge hfrozen]

theorem collectionPostChoice_after_start {x : RoundInput p rate} (prepared : PreparedRound x)
    (payload : Payload rate) (ledger : Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (recording : CoordinatorRecordingOperation.Output p) (ledgerStarted : Ledger rate)
    (hrecord : CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput prepared payload started weights) = some recording)
    (hservice : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
      (collectionEnabled ledger x.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
        .success ledgerStarted) :
    collectionPostChoice prepared payload ledger started weights =
      collectionFinish (x := x) payload started recording (receiveUp prepared ledgerStarted) := by
  simp only [collectionPostChoice, hrecord, hservice]

/-- Parser/acceptance rejection and acceptance both retain the actual bank and
proceed to FinishRound. The flag distinguishes the two actual receiver tags.
-/
theorem collectionFinish_success {x : RoundInput p rate} (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p) (cut : UpCut p rate)
    (ledgerDecoded ledgerFinished : Ledger rate)
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (clockFinished : CoordinatorPhaseClock.FinishRoundResult p)
    (hreception : cut.result = .success (ledgerDecoded, bank) ∨
      cut.result = .rejected (ledgerDecoded, bank))
    (hfinish : CoordinatorCollectionLedger.finishRound ledgerDecoded = .success ledgerFinished)
    (hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
      ledgerFinished.pending x.row = .ok clockFinished) :
    collectionFinish (x := x) payload started recording cut =
      ⟨.collection payload ledgerFinished clockFinished.clock.lastProposal, bank, none,
        some recording, cut.diagnostic⟩ := by
  rcases hreception with haccepted | hrejected
  · simp only [collectionFinish, haccepted, hfinish, hclock]
  · simp only [collectionFinish, hrejected, hfinish, hclock]

/-- Literal live recorder/service/confirmation/clock decomposition. Every
condition names an actual runtime operation in livePostChoice; no successful
physical history or score identity is a premise. The exact service outputs,
rather than arrival-only updates, form the next canonical registers.
-/
theorem livePostChoice_success {x : RoundInput p rate} (prepared : PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (serviced : CoordinatorLiveServiceFinish.ServicedRegisters r q)
    (pending : Finset (Fin (p.m - 1)))
    (finished : CoordinatorPhaseClock.FinishRoundResult p)
    (hrecord : CoordinatorRecorderComplementBridge.run (liveRecordingInput prepared r started) =
      some recording)
    (hservice : CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced)
    (hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time x.row prepared.coordinatorObservation = some pending)
    (hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
      pending x.row = .ok finished) :
    livePostChoice prepared r q base started =
      ⟨.live {
          payload := r.payload
          priorClock := finished.clock
          pendingAtChoice := finished.pending
          time := x.time
          gridBoundary := finished.clock.g
          complementScores := serviced.score }
        { queue := serviced.queue, previousService := serviced.previousService } base,
        x.state.upDecoderBank, none, some recording, none⟩ := by
  simp only [livePostChoice, hrecord, hservice, hconfirmation, hfinish]

/-- An absorbing coordinator performs no learning or transport update. Other
players still take their independently computed physical actions.
-/
theorem observeCoordinator_dagger {x : RoundInput p rate} (prepared : PreparedRound x)
    (hdagger : prepared.coordinator = .dagger) :
    prepared.observeCoordinator = ⟨.dagger, x.state.upDecoderBank, none, none, none⟩ := by
  simp [PreparedRound.observeCoordinator, hdagger, DispatchCut.selection]

/-- Both live dispatch branches are exposed. A first cutoff uses the newly
initialized ledger and the changed original clock; continuing live play uses
the original live stores. Failures have no post-choice learning operation.
-/
theorem observeCoordinator_live_equation {x : RoundInput p rate} (prepared : PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome (liveInput x r q base))
    (hcut : prepared.coordinator = .live r q base outcome) :
    prepared.observeCoordinator =
      if (DispatchCut.live r q base outcome).selection = none then
        coordinatorFailure x.state.upDecoderBank .dispatchRejected none none
      else match outcome with
      | .continuingChosen dispatched _ _ _ =>
          livePostChoice prepared (liveRegistersAt r x.time) (liveOwnedAt r q x.time)
            base dispatched.startResult
      | .cutoffChosen dispatched _ ledger _ _ _ _ _ _ _ =>
          collectionPostChoice prepared r.payload (sharedLedger ledger) dispatched.startResult
            (liveRegistersAt r x.time).complementWeights
      | _ => coordinatorFailure x.state.upDecoderBank .dispatchRejected none none := by
  simp only [PreparedRound.observeCoordinator, hcut]
  cases outcome <;> rfl

/-- Pending collection, including rounds at/after freeze, uses its same clock
result and ledger. A later start uses the actual installed sampler result;
its original instruction distinguishes corrected from renewal starts.
-/
theorem observeCoordinator_collection_equation {x : RoundInput p rate}
    (prepared : PreparedRound x) (payload : Payload rate) (ledger : Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (outcome : CoordinatorRoundDispatch.CollectionOutcome
      (collectionInput x payload ledger clock cutoff))
    (hcut : prepared.coordinator = .collection payload ledger clock cutoff outcome) :
    prepared.observeCoordinator =
      if (DispatchCut.collection payload ledger clock cutoff outcome).selection = none then
        coordinatorFailure x.state.upDecoderBank .dispatchRejected none none
      else match outcome with
      | .continuing _ snapshot _ _ =>
          collectionPostChoice prepared payload ledger snapshot.clockStarted
            (CoordinatorCollectionInteractive.PreObservationInputs.weights
              (collectionInput x payload ledger clock cutoff)
              snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
      | .laterChosen _ _ started _ _ _ _ _ _ installed _ =>
          livePostChoice prepared installed.registers installed.ownedRegisters
            installed.retainedBaseScore started
      | _ => coordinatorFailure x.state.upDecoderBank .dispatchRejected none none := by
  simp only [PreparedRound.observeCoordinator, hcut]
  cases outcome <;> rfl

theorem observeCoordinator_first_equation {x : RoundInput p rate} (prepared : PreparedRound x)
    (outcome : CoordinatorRoundDispatch.FirstOutcome (firstInput x))
    (hcut : prepared.coordinator = .first outcome) :
    prepared.observeCoordinator =
      if (DispatchCut.first outcome).selection = none then
        coordinatorFailure x.state.upDecoderBank .dispatchRejected none none
      else match outcome with
      | .chosen installed _ => livePostChoice prepared installed.registers
          installed.ownedRegisters installed.followerBaseScore installed.startRoundResult
      | _ => coordinatorFailure x.state.upDecoderBank .dispatchRejected none none := by
  simp only [PreparedRound.observeCoordinator, hcut]
  cases outcome <;> rfl

/-- A raw UP mismatch advances the real persistent decoder and only the
ledger's decode phase. Recovery and installation are suppressed before effect.
-/
theorem receiveUp_mismatch {x : RoundInput p rate} (prepared : PreparedRound x)
    (ledger : Ledger rate)
    (hinput : CoordinatorUpReception.receptionInputCheck
      (ReferenceUpReception.receptionInputAtRow rate x.row (upInputs prepared ledger) x.time) = true)
    (hmismatch : (CoordinatorUpReception.decoderTransition
      (ReferenceUpReception.receptionInputAtRow rate x.row (upInputs prepared ledger) x.time)).2 ≠
        upExpected prepared) :
    (receiveUp prepared ledger).result = .rejected
      ({ ledger with phase := .decoded }, CoordinatorUpReception.decoderBankAfter
        (ReferenceUpReception.receptionInputAtRow rate x.row (upInputs prepared ledger) x.time)) :=
  ReferenceUpReception.receiveUpFilteredAtRow_mismatch_rejected rate x.row
    (upInputs prepared ledger) x.time (prepared.followers.followers (upSenderIndex x))
    (prepared.follower_alignment _).1 (prepared.follower_alignment _).2.1
    (prepared.follower_alignment _).2.2.1 rfl hinput hmismatch

theorem receiveUp_unselected_bank {x : RoundInput p rate} (prepared : PreparedRound x)
    (ledger : Ledger rate)
    (hinput : CoordinatorUpReception.receptionInputCheck
      (ReferenceUpReception.receptionInputAtRow rate x.row (upInputs prepared ledger) x.time) = true)
    (out : Ledger rate × CoordinatorUpReception.UpDecoderBank p)
    (hout : (receiveUp prepared ledger).result = .success out ∨
      (receiveUp prepared ledger).result = .rejected out)
    (i : Fin (p.m - 1)) (hi : i ≠ upSenderIndex x) :
    out.2 i = x.state.upDecoderBank i :=
  ReferenceUpReception.receiveUpFilteredAtRow_preserves_unselected_bank rate x.row
    (upInputs prepared ledger) x.time (prepared.followers.followers (upSenderIndex x))
    (prepared.follower_alignment _).1 (prepared.follower_alignment _).2.1
    (prepared.follower_alignment _).2.2.1 rfl hinput out hout i hi

/-- After logging, both the exact receiver input (including partial/completed
batches) and the actual pre-effect cut are retained for event consumers.
-/
theorem recordFollower_logged (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state logged : ReferencePrelaunchFollower.State p rate.eta)
    (hstatus : state.status = .unoccupied)
    (hlogging : ActiveFollowerLogging.checkedLogging i row activation t
      (arm, observation) state = .ok logged) :
    (recordFollower view i row activation t active arm observation state).downInput = some logged ∧
    (recordFollower view i row activation t active arm observation state).down =
      some (ReferenceDownReception.referenceDownCut p view i row t observation rate logged) := by
  simp [recordFollower, hstatus, hlogging]

theorem step_coordinator_dagger (x : RoundInput p rate)
    (hdagger : x.state.coordinator = .dagger) :
    (step x).next.coordinator = .dagger ∧
      (step x).next.upDecoderBank = x.state.upDecoderBank := by
  have hprepared : (prepare x).coordinator = .dagger := dispatch_dagger x hdagger
  have hfinished := observeCoordinator_dagger (prepare x) hprepared
  change (prepare x).observeCoordinator.configuration = .dagger ∧
    (prepare x).observeCoordinator.upDecoderBank = x.state.upDecoderBank
  rw [hfinished]
  exact ⟨rfl, rfl⟩

theorem step_follower_dagger (x : RoundInput p rate) (i : Fin (p.m - 1))
    (hdagger : x.state.followers i = .dagger) :
    (step x).next.followers i = .dagger := by
  change ((prepare x).observeFollower i).configuration = .dagger
  apply (finishFollower_dagger _ _ _ ?_).1
  rw [(prepare x).followers.followers_eq i, ReferenceActiveFeedbackCut.prepareFollowers_apply]
  change (DeclaredFollowerLocalRound.prepare rate i x.row (x.state.activations i)
    x.time (x.active i) (x.state.followers i)).configuration = .dagger
  rw [hdagger]
  exact (DeclaredFollowerLocalRound.prepare_dagger rate i x.row (x.state.activations i)
    x.time (x.active i)).2

theorem collectionClock_fields (payload : Payload rate) (ledger : Ledger rate)
    (proposal : Option (Fin p.T × Bool)) (cutoff : Fin p.T) :
    (collectionClock payload ledger proposal cutoff).sigma = some payload.sigma ∧
    (collectionClock payload ledger proposal cutoff).u = some cutoff ∧
    (collectionClock payload ledger proposal cutoff).g = ledger.freezeAt ∧
    (collectionClock payload ledger proposal cutoff).lastProposal = proposal :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- In particular, index adaptation changes neither known/unknown registers,
partial accumulators, raw buffers, nor the ledger cursor/within-round phase.
-/
theorem sharedLedger_fields {n : ℕ} {hn : (n : ℝ) = rate.eta.val * (D p : ℝ)}
    {cap : CoordinatorCollectionLedger.sourceLearningCap p rate.eta.val}
    (ledger : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property cap n hn) :
    (sharedLedger ledger).assignment = ledger.assignment ∧
    (sharedLedger ledger).sigma = ledger.sigma ∧
    (sharedLedger ledger).cutoff = ledger.cutoff ∧
    (sharedLedger ledger).freezeAt = ledger.freezeAt ∧
    (sharedLedger ledger).baseScore = ledger.baseScore ∧
    (sharedLedger ledger).pending = ledger.pending ∧
    (sharedLedger ledger).cutoffRegisters = ledger.cutoffRegisters ∧
    (sharedLedger ledger).currentRegisters = ledger.currentRegisters ∧
    (sharedLedger ledger).increment = ledger.increment ∧
    (sharedLedger ledger).gammaLoc = ledger.gammaLoc ∧
    (sharedLedger ledger).rawBuffer = ledger.rawBuffer ∧
    (sharedLedger ledger).enabledHistory = ledger.enabledHistory ∧
    (sharedLedger ledger).cursor = ledger.cursor ∧
    (sharedLedger ledger).phase = ledger.phase :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem collection_started_candidate (ledger out : Ledger rate) (time : Fin p.T)
    (raw : Option (Fin p.K × ℕ))
    (hstart : CoordinatorCollectionLedger.startRound ledger (time.val + 1)
      (collectionEnabled ledger time) raw = .success out) :
    out = CoordinatorCollectionLedger.startRoundCandidate ledger time
      (collectionEnabled ledger time) raw := by
  simpa only [Nat.add_sub_cancel, Fin.eta] using
    (CoordinatorCollectionUpRoundStep.InputsValid.startRound_success_candidate ledger
      (time.val + 1) (by omega) (Nat.succ_le_of_lt time.isLt)
      (collectionEnabled ledger time) raw out hstart)

/-- Actual frozen stage-(1) service leaves known queues unchanged and has
zero local service. This is a field equation on the successful checked call;
collectionPostChoice still executes reception and finishing afterwards.
-/
theorem collection_started_frozen (ledger out : Ledger rate) (time : Fin p.T)
    (raw : Option (Fin p.K × ℕ)) (a : Fin p.K)
    (current : CoordinatorCollectionLedger.CurrentRegister)
    (hknown : ledger.currentRegisters a = some current)
    (hfrozen : ledger.freezeAt ≤ time.val + 1)
    (hstart : CoordinatorCollectionLedger.startRound ledger (time.val + 1)
      (collectionEnabled ledger time) raw = .success out) :
    out.currentRegisters a = some ⟨current.queue, 0⟩ ∧ out.gammaLoc a = 0 := by
  rw [collection_started_candidate ledger out time raw hstart,
    collectionEnabled_of_frozen ledger time hfrozen]
  constructor
  · simpa [CoordinatorCollectionLedger.localQueueRecord, QueueReplay.transition] using
      (CoordinatorCollectionLedger.startRoundCandidate_known_transition ledger time false raw
        a current hknown)
  · simp [CoordinatorCollectionLedger.startRoundCandidate, hknown,
      CoordinatorCollectionLedger.localQueueRecord, QueueReplay.transition]

/-- Enabled zero-arrival service drains the carried backlog. This separates a
missing gate/zero arrival from disabled service in the actual checked update.
-/
theorem collection_started_zero_arrival (ledger out : Ledger rate) (time : Fin p.T)
    (a : Fin p.K) (current : CoordinatorCollectionLedger.CurrentRegister)
    (hknown : ledger.currentRegisters a = some current)
    (henabled : collectionEnabled ledger time = true)
    (hstart : CoordinatorCollectionLedger.startRound ledger (time.val + 1)
      (collectionEnabled ledger time) none = .success out) :
    out.currentRegisters a = some ⟨current.queue - min (4 * rate.n) current.queue,
      min (4 * rate.n) current.queue⟩ := by
  have hconditions : 0 < ledger.sigma ∧ ledger.cutoff ≤ time.val + 1 ∧
      time.val + 1 < ledger.freezeAt := of_decide_eq_true henabled
  rw [collection_started_candidate ledger out time none hstart, henabled]
  simpa [CoordinatorCollectionLedger.localQueueRecord, CoordinatorCollectionLedger.sourceRound,
    hconditions.2.2, CoordinatorCollectionLedger.localArrival, QueueReplay.transition] using
    (CoordinatorCollectionLedger.startRoundCandidate_known_transition ledger time true none
      a current hknown)

/-- On the computed first-start branch the additional whole-carrier time
check preserves exactly the dispatcher's returned arm. -/
theorem first_chosen_arm (x : RoundInput p rate)
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput (firstInput x)))
    (selected : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights x.row)
    (hchosen : CoordinatorRoundDispatch.dispatchFirst (firstInput x) =
      .chosen installed selected) :
    (DispatchCut.first (.chosen installed selected)).arm = selected.arm := by
  have ht := dispatchFirst_chosen_time x installed selected hchosen
  simp [DispatchCut.arm, DispatchCut.selection, selectionAt, ht]

/-- Both continuing-live and first-cutoff physical choices use the exact arm
returned by the original dispatch result; every rejected result uses fallback.
-/
theorem live_arm_equation {x : RoundInput p rate}
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome (liveInput x r q base)) :
    (DispatchCut.live r q base outcome).arm = match outcome with
      | .continuingChosen _ _ _ selected => selected.arm
      | .cutoffChosen _ _ _ _ _ _ _ _ _ selected => selected.arm
      | _ => coordinatorFallback p := by
  cases outcome <;> simp [DispatchCut.arm, DispatchCut.selection, selectionAt]

/-- Pending, corrected, and renewal physical choices preserve the computed
arm. The later-start time equation is derived from the retained original
clock call, with no independently supplied snapshot alignment.
-/
theorem collection_arm_equation {x : RoundInput p rate}
    (payload : Payload rate) (ledger : Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (outcome : CoordinatorRoundDispatch.CollectionOutcome
      (collectionInput x payload ledger clock cutoff)) :
    (DispatchCut.collection payload ledger clock cutoff outcome).arm = match outcome with
      | .continuing _ snapshot _ _ => snapshot.arm
      | .laterChosen _ _ _ _ _ _ _ _ _ _ selected => selected.arm
      | _ => coordinatorFallback p := by
  cases outcome
  case laterChosen core consistent started hstart instruction hinstruction output
      hlocal clockData installed selected =>
    have ht := later_instruction_time x payload ledger clock cutoff core started instruction
      hstart hinstruction
    simp [DispatchCut.arm, DispatchCut.selection, selectionAt, ht]
  all_goals simp [DispatchCut.arm, DispatchCut.selection]

end Bandits.Support.ReferenceActivePhysicalStep

end
