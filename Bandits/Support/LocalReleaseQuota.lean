/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.DeclaredFollowerLocalRound
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Count
public import Mathlib.Data.List.Pairwise

/-!
# Conditional local release quota

This module proves deterministic status monotonicity and quota one for a
source-ordered finite chain of successful existing follower operations.  Its
trace carries the complete local state, local memory, complete table row,
typed own feedback, and the existing active-round action data.  The equalities
that identify these supplied local and action views remain explicit inputs.

The mathematical cost argument is in
`sources/zip4/manuscript/05_binary_transport.tex:293-348`; the local
release, acceptance, and lifecycle order is in
`sources/zip4/manuscript/06_interruptions.tex:270-295,302-325`.  No producer
of the physical reference trace, conditional law, waiting bound, or source
lemma is proved here.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.LocalReleaseQuota

open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ActiveFollowerQueueOperation
open Bandits.Support.ActiveRoundActions
open Bandits.Support.AffineChannelLaw
open Bandits.Support.CompletePublicTable
open Bandits.Support.ConstructorDimensions
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.FiniteBanditModel
open Bandits.Support.FollowerCutoffScan
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.PrelaunchBufferRecovery
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ReferencePrelaunchFollower

variable {p : Parameters}

/-- A successful checked service changes only the three queue registers.
The equality `queueUpdate` is the actual `checkedService` result equation;
the unchanged fields are obtained from its literal `serviceOutput`. -/
theorem serviceSuccess_nonqueue_frame {rate : RateInput p} {n : ℕ}
    {i : Fin (p.m - 1)} {row : CompletePublicTable.CompleteRow p}
    {activation : Activation p} {t : Fin p.T} {own : Observation p}
    {input : State p rate.eta}
    (result : ServiceSuccess p rate.eta n i row activation t own input) :
    result.output.lastDown = input.lastDown ∧
      result.output.downBatch = input.downBatch ∧
      result.output.buffer = input.buffer ∧
      result.output.status = input.status ∧
      result.output.initializationFailure = input.initializationFailure := by
  rw [result.queueUpdate]
  exact serviceOutput_preserves_other_registers n input result.arrival

/-- One supplied calendar round of the existing local preparation, service,
release, and finish operations for every follower in one fixed assignment.
The record, operation-result, local-domain, time, and row/feedback
correspondence fields are deliberately visible. -/
structure LocalReleaseRound (rate : RateInput p)
    (assignment : ActiveRoundActions.Assignment p.m p.K) (B : ℕ)
    (record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) where
  time : Fin p.T
  row : CompletePublicTable.CompleteRow p
  activation : ActiveRoundActions.Follower p.m → Activation p
  active : ∀ i, (activation i).val ≤ time.val + 1
  own : ActiveRoundActions.Follower p.m → Observation p
  state : ActiveRoundActions.Follower p.m → State p rate.eta
  memory : ActiveRoundActions.Follower p.m → ActiveFollowerLifecycle.LocalMemory p
  arm : ActiveRoundActions.Follower p.m → Fin p.K
  snapshot : ActiveRoundActions.Snapshot assignment
  action : ActiveRoundActions.RoundInput assignment B
  reward : ActiveRoundActions.RewardRow p.K
  serviceResult : ∀ i, ActiveFollowerQueueOperation.ServiceSuccess p rate.eta rate.n i
    row (activation i) time (own i) (state i)
  afterRelease : ActiveRoundActions.Follower p.m → State p rate.eta
  nextState : ActiveRoundActions.Follower p.m → State p rate.eta
  nextMemory : ActiveRoundActions.Follower p.m → ActiveFollowerLifecycle.LocalMemory p
  prepared : ∀ i,
    DeclaredFollowerLocalRound.prepare rate i row (activation i) time (active i)
        (.ordinary (state i) (memory i)) =
      ⟨i, row, activation i, time, active i, arm i,
        .ordinary (state i) (memory i)⟩
  checkedService : ∀ i,
    ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n
        rate.n_scale i row (activation i) time (own i) (state i) =
      .success (serviceResult i)
  localDomain : ∀ i, ActiveFollowerLifecycle.localStateDomainValid (state i)
  postServiceDomain : ∀ i,
    ActiveFollowerLifecycle.localStateDomainValid (serviceResult i).output
  carriedRecord : ∀ i, (state i).lastDown = some (record i)
  recordStarted : ∀ i, (record i).val.sigma ≤ time.val
  beforeCutoff : ∀ i,
    time.val + 1 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val
      (ActiveFollowerLifecycle.acceptedStartCoordinate (record i))
  release : ∀ i,
    ActiveFollowerLifecycle.releaseAfterService rate.eta i time
      (ActiveFollowerLifecycle.publicRowOfCompleteRow row time) (own i) (state i)
      (serviceResult i).output = .ok (afterRelease i)
  finish : ∀ i,
    ActiveFollowerLifecycle.finishRound rate.eta time row (afterRelease i) (memory i) =
      .ok (nextState i, nextMemory i)
  assignmentArm : ∀ i,
    assignment.assigned i = PrelaunchBufferRecovery.downArm rate.eta (record i)
  auxiliaryArm : ∀ i,
    assignment.auxiliary = ActiveFollowerLifecycle.acceptedEscapeArm (record i)
  publicRowMatches :
    ActiveFollowerLifecycle.publicRowOfCompleteRow row time =
      ActiveFollowerLifecycle.publicRowOfActionInput action
  snapshotStatus : ∀ i, snapshot.status i = (state i).status
  ownFeedback : ∀ i,
    (own i).val.val = ActiveRoundActions.feedback p.two_le_m snapshot action reward
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)

/-- Adjacent rounds use consecutive source calendar coordinates and carry the
entire local state and memory from `FinishRound` to the next `Prepare` input. -/
def localReleaseFollows {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (earlier later : LocalReleaseRound rate assignment B record) : Prop :=
  later.time.val = earlier.time.val + 1 ∧
    (∀ i, later.state i = earlier.nextState i) ∧
    (∀ i, later.memory i = earlier.nextMemory i)

/-- A finite successful local trace covers exactly a half-open calendar
interval.  Its explicit endpoints are after the named last confirmation,
before every follower cutoff, and before the horizon.  These are supplied
trace and window facts, not a global last-confirmation invariant. -/
structure LocalReleaseTrace (rate : RateInput p)
    (assignment : ActiveRoundActions.Assignment p.m p.K) (B : ℕ)
    (record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) where
  rounds : List (LocalReleaseRound rate assignment B record)
  initialState : ActiveRoundActions.Follower p.m → State p rate.eta
  initialMemory : ActiveRoundActions.Follower p.m → ActiveFollowerLifecycle.LocalMemory p
  initialRecord : ∀ i, (initialState i).lastDown = some (record i)
  initialStatus : ∀ i,
    (initialState i).status = .pending ∨ (initialState i).status = .released
  firstState : ∀ r, rounds.head? = some r →
    ∀ i, r.state i = initialState i ∧ r.memory i = initialMemory i
  follows : List.IsChain localReleaseFollows rounds
  lastConfirmation : ℕ
  intervalStart : ℕ
  intervalStop : ℕ
  confirmation_before_start : lastConfirmation < intervalStart
  interval_endpoints : intervalStart ≤ intervalStop ∧ intervalStop ≤ p.T
  cutoff_endpoint : ∀ i,
    intervalStop ≤ FollowerCutoffScan.gridBoundary p rate.eta.val
      (ActiveFollowerLifecycle.acceptedStartCoordinate (record i))
  exact_calendar : rounds.map (fun r => r.time.val) =
    List.range' intervalStart (intervalStop - intervalStart) 1

/-- The literal pending release test in one supplied round.  Its event is the
existing `ActiveRoundActions.releaseObservation`, with pending status taken
from the same PRE-CHOICE snapshot used by arm choice. -/
def pendingReleaseObservation {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (r : LocalReleaseRound rate assignment B record)
    (i : ActiveRoundActions.Follower p.m) : Prop :=
  r.snapshot.status i = .pending ∧
    ActiveRoundActions.releaseObservation p.two_le_m r.snapshot r.action r.reward i

/-- The Boolean predicate counted on the literal calendar. -/
def pendingReleaseFlag {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (r : LocalReleaseRound rate assignment B record)
    (i : ActiveRoundActions.Follower p.m) : Bool := by
  classical
  exact decide (pendingReleaseObservation r i)

/-- Calendar count of literal pending release observations for one follower. -/
def pendingReleaseCalendarCount {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (rounds : List (LocalReleaseRound rate assignment B record))
    (i : ActiveRoundActions.Follower p.m) : ℕ := by
  classical
  exact rounds.countP (fun r => pendingReleaseFlag r i)

/-- UP-only pending release observations, still counted from the literal
existing release observation and the actual action slot. -/
def pendingUpReleaseCalendarCount {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (rounds : List (LocalReleaseRound rate assignment B record))
    (i : ActiveRoundActions.Follower p.m) : ℕ := by
  classical
  exact rounds.countP (fun r => decide
    (pendingReleaseObservation r i ∧ r.action.slot = upSlot))

/-- DATA-only pending release observations, still counted from the literal
existing release observation and the actual action slot. -/
def pendingDataReleaseCalendarCount {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (rounds : List (LocalReleaseRound rate assignment B record))
    (i : ActiveRoundActions.Follower p.m) : ℕ := by
  classical
  exact rounds.countP (fun r => decide
    (pendingReleaseObservation r i ∧ r.action.slot = dataSlot))

/-- The family of PRE-CHOICE pending sets in the actual assignment snapshot. -/
def pendingFollowerSet {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (r : LocalReleaseRound rate assignment B record) :
    Finset (ActiveRoundActions.Follower p.m) := by
  classical
  exact Finset.univ.filter (fun i => r.snapshot.status i = .pending)

private theorem list_countP_le_of_imp {α : Type} (rounds : List α)
    (P Q : α → Bool) (himp : ∀ x, P x = true → Q x = true) :
    rounds.countP P ≤ rounds.countP Q := by
  induction rounds with
  | nil => simp
  | cons x rest ih =>
      have hhead : (if P x then 1 else 0) ≤ (if Q x then 1 else 0) := by
        cases hp : P x <;> cases hq : Q x <;> simp_all
      rw [List.countP_cons, List.countP_cons]
      omega

private theorem list_countP_eq_zero_of_false {α : Type} (rounds : List α)
    (P : α → Bool) (hfalse : ∀ x ∈ rounds, P x = false) : rounds.countP P = 0 := by
  induction rounds with
  | nil => rfl
  | cons x rest ih =>
      have hx := hfalse x (by simp)
      have hrest : ∀ y ∈ rest, P y = false := by
        intro y hy
        exact hfalse y (by simp [hy])
      simp [hx, ih hrest]

private theorem pendingReleaseCount_cons {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (first : LocalReleaseRound rate assignment B record)
    (tail : List (LocalReleaseRound rate assignment B record))
    (i : ActiveRoundActions.Follower p.m) :
    pendingReleaseCalendarCount (first :: tail) i =
      pendingReleaseCalendarCount tail i +
        if pendingReleaseFlag first i then 1 else 0 := by
  by_cases h : pendingReleaseFlag first i <;>
    simp [pendingReleaseCalendarCount, h]

/-- A successful local service result frames every non-queue field of the
actual state through its `queueUpdate`. -/
theorem round_service_frame {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (r : LocalReleaseRound rate assignment B record)
    (i : ActiveRoundActions.Follower p.m) :
    (r.serviceResult i).output.lastDown = (r.state i).lastDown ∧
      (r.serviceResult i).output.downBatch = (r.state i).downBatch ∧
      (r.serviceResult i).output.buffer = (r.state i).buffer ∧
      (r.serviceResult i).output.status = (r.state i).status ∧
      (r.serviceResult i).output.initializationFailure =
        (r.state i).initializationFailure :=
  serviceSuccess_nonqueue_frame (r.serviceResult i)

/-- The actual occupied observation continuation succeeds with the state and
memory returned by the supplied lifecycle stages. -/
theorem observeOrdinary_success {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (r : LocalReleaseRound rate assignment B record)
    (i : ActiveRoundActions.Follower p.m)
    (hoccupied : (r.state i).status ≠ .unoccupied) :
    DeclaredFollowerLocalRound.observeOrdinary rate i r.row (r.activation i) r.time
      (r.active i) (r.arm i) (r.own i) (r.state i) (r.memory i) =
        .ok (r.nextState i, r.nextMemory i) := by
  have hrecordOr := DeclaredFollowerLocalRound.recordOrServiceThenDown_occupied
    rate i r.row (r.activation i) r.time (r.active i) (r.arm i) (r.own i)
    (r.state i) hoccupied
  unfold DeclaredFollowerLocalRound.observeOrdinary
  rw [hrecordOr, r.checkedService i]
  simp only [DeclaredFollowerLocalRound.releaseAndFinish, r.release i, r.finish i]

/-- The existing unoccupied-at-choice branch does not release a DOWN record
accepted later in that same observation.  This source operation lemma records
the PRE-CHOICE status rule at the boundary of the occupied interval proved
below. -/
theorem acceptedDown_stays_pending_in_acceptance_round {rate : RateInput p}
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : Activation p) (t : Fin p.T)
    (hactive : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : Observation p) (choiceState post : State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : choiceState.status = .unoccupied)
    (hpost : DeclaredFollowerLocalRound.recordOrServiceThenDown rate i row activation t
      hactive arm observation choiceState = .ok post)
    (hpending : post.status = .pending)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid post)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hrecord : post.lastDown = some M) (htime : M.val.sigma ≤ t.val + 1) :
    DeclaredFollowerLocalRound.observeOrdinary rate i row activation t hactive arm
      observation choiceState memory =
        .ok (post, ⟨some ⟨t,
          FollowerCutoffScan.completeRowProposalBit p rate.eta.val row t⟩⟩) :=
  DeclaredFollowerLocalRound.observeOrdinary_new_acceptance_not_released rate i row
    activation t hactive arm observation choiceState post memory hchoice hpost hpending
    hvalid M hrecord htime

/-- The exact local status update.  `checkedService` preserves status; the
PRE-CHOICE pending branch releases exactly on the lifecycle predicate, and an
already released follower remains released. `FinishRound` frames the entire
state. -/
theorem round_status_update {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (r : LocalReleaseRound rate assignment B record)
    (i : ActiveRoundActions.Follower p.m)
    (hoccupied : (r.state i).status ≠ .unoccupied) :
    ((r.nextState i).status = .released ↔
      (r.state i).status = .released ∨ pendingReleaseObservation r i) ∧
    ((r.nextState i).status = .pending ↔
      (r.state i).status = .pending ∧ ¬ pendingReleaseObservation r i) := by
  classical
  have hserviceFrame := round_service_frame r i
  have hfinishFrame := ActiveFollowerLifecycle.finishRound_frame rate.eta r.time r.row
    (r.afterRelease i) (r.nextState i) (r.memory i) (r.nextMemory i) (r.finish i)
  have hpostRecord :
      (¬ ActiveFollowerLifecycle.releaseCondition rate.eta i
          (ActiveFollowerLifecycle.publicRowOfCompleteRow r.row r.time) (r.own i)
          (record i) ∧ (r.serviceResult i).output.status = .unoccupied) ∨
        (∃ M', (r.serviceResult i).output.lastDown = some M' ∧
          M'.val.sigma ≤ r.time.val + 1) := by
    right
    refine ⟨record i, ?_, ?_⟩
    · rw [hserviceFrame.1, r.carriedRecord i]
    · exact Nat.le_trans (r.recordStarted i) (Nat.le_succ _)
  have hcondition :
      ActiveFollowerLifecycle.releaseCondition rate.eta i
        (ActiveFollowerLifecycle.publicRowOfCompleteRow r.row r.time) (r.own i)
        (record i) =
      ActiveRoundActions.releaseObservation p.two_le_m r.snapshot r.action r.reward i := by
    rw [r.publicRowMatches]
    exact ActiveFollowerLifecycle.releaseCondition_eq_activeRoundActions rate.eta
      assignment r.snapshot r.action r.reward i (record i) (r.own i)
      (r.assignmentArm i) (r.auxiliaryArm i) (r.ownFeedback i)
  cases hstatus : (r.state i).status with
  | unoccupied => exact (hoccupied hstatus).elim
  | released =>
      have hnotPending : (r.state i).status ≠ .pending := by simp [hstatus]
      have hreleaseNoop := ActiveFollowerLifecycle.releaseAfterService_not_pending
        rate.eta i r.time (ActiveFollowerLifecycle.publicRowOfCompleteRow r.row r.time)
        (r.own i) (r.state i) (r.serviceResult i).output hnotPending
      have hafterEq : r.afterRelease i = (r.serviceResult i).output :=
        (Except.ok.inj (hreleaseNoop.symm.trans (r.release i))).symm
      have hnextReleased : (r.nextState i).status = .released := by
        rw [hfinishFrame, hafterEq, hserviceFrame.2.2.2.1]
        exact hstatus
      constructor
      · constructor
        · intro _
          exact Or.inl rfl
        · intro _
          exact hnextReleased
      · constructor
        · intro h
          have hbad : FollowerStatus.released = FollowerStatus.pending := by
            rw [hnextReleased] at h
            exact h
          cases hbad
        · intro h
          cases h.1
  | pending =>
      have hpostPending : (r.serviceResult i).output.status = .pending := by
        rw [hserviceFrame.2.2.2.1, hstatus]
      have hbranch := ActiveFollowerLifecycle.releaseAfterService_pending_branch
        rate.eta i r.time (ActiveFollowerLifecycle.publicRowOfCompleteRow r.row r.time)
        (r.own i) (r.state i) (r.serviceResult i).output hstatus (r.localDomain i)
        (record i) (r.carriedRecord i) (r.recordStarted i)
        (r.postServiceDomain i) hpostRecord
      have hbranchState : r.afterRelease i =
          (if ActiveFollowerLifecycle.releaseCondition rate.eta i
              (ActiveFollowerLifecycle.publicRowOfCompleteRow r.row r.time)
              (r.own i) (record i)
            then {(r.serviceResult i).output with status := .released}
            else (r.serviceResult i).output) :=
        Except.ok.inj ((r.release i).symm.trans hbranch)
      have hstatusIff := ActiveFollowerLifecycle.releaseAfterService_status_iff
        rate.eta i r.time (ActiveFollowerLifecycle.publicRowOfCompleteRow r.row r.time)
        (r.own i) (r.state i) (r.serviceResult i).output hstatus (r.localDomain i)
        (record i) (r.carriedRecord i) (r.recordStarted i)
        (r.postServiceDomain i) hpostRecord hpostPending
      have hstatusEqProps : ((r.afterRelease i).status = .released) =
          (ActiveFollowerLifecycle.releaseCondition rate.eta i
            (ActiveFollowerLifecycle.publicRowOfCompleteRow r.row r.time) (r.own i)
            (record i)) := by
        have hmapped := hstatusIff
        rw [r.release i] at hmapped
        exact Except.ok.inj (by simpa only [Except.map] using hmapped)
      have hafterReleased : (r.afterRelease i).status = .released ↔
          ActiveFollowerLifecycle.releaseCondition rate.eta i
            (ActiveFollowerLifecycle.publicRowOfCompleteRow r.row r.time) (r.own i)
            (record i) := by
        exact Iff.of_eq hstatusEqProps
      have hpendingSnapshot : r.snapshot.status i = .pending := by
        rw [r.snapshotStatus i]
        exact hstatus
      have hpendingObservation :
          ActiveRoundActions.releaseObservation p.two_le_m r.snapshot r.action r.reward i ↔
          ActiveFollowerLifecycle.releaseCondition rate.eta i
            (ActiveFollowerLifecycle.publicRowOfCompleteRow r.row r.time) (r.own i)
            (record i) := by
        exact (Iff.of_eq hcondition).symm
      constructor
      · constructor
        · intro h
          have hafter : (r.afterRelease i).status = .released := by
            rw [hfinishFrame] at h
            exact h
          exact Or.inr ⟨hpendingSnapshot, hpendingObservation.mpr (hafterReleased.mp hafter)⟩
        · intro h
          rcases h with hreleased | ⟨hpending, hobs⟩
          · exact False.elim (by cases hreleased)
          · rw [hfinishFrame]
            exact hafterReleased.mpr (hpendingObservation.mp hobs)
      · constructor
        · intro h
          have hafter : (r.afterRelease i).status = .pending := by
            rw [hfinishFrame] at h
            exact h
          have hnotRelease :
              ¬ ActiveFollowerLifecycle.releaseCondition rate.eta i
                (ActiveFollowerLifecycle.publicRowOfCompleteRow r.row r.time)
                (r.own i) (record i) := by
            intro hc
            have hrel := hafterReleased.mpr hc
            rw [hafter] at hrel
            cases hrel
          exact ⟨rfl, fun hobs => hnotRelease (hpendingObservation.mp hobs.2)⟩
        · rintro ⟨hpending, hnotObs⟩
          rw [hfinishFrame, hbranchState]
          have hnotCondition :
              ¬ ActiveFollowerLifecycle.releaseCondition rate.eta i
                (ActiveFollowerLifecycle.publicRowOfCompleteRow r.row r.time)
                (r.own i) (record i) := by
            intro hc
            exact hnotObs ⟨hpendingSnapshot, hpendingObservation.mpr hc⟩
          by_cases hc : ActiveFollowerLifecycle.releaseCondition rate.eta i
              (ActiveFollowerLifecycle.publicRowOfCompleteRow r.row r.time)
              (r.own i) (record i)
          · exact (hnotCondition hc).elim
          · simp [hc, hpostPending]

/-- At a pending pre-choice, the released status is equivalent to the existing
lifecycle release condition, with the public action identification discharged
from the supplied arm and own-feedback equalities. -/
theorem pendingStatus_released_iff_releaseCondition {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (r : LocalReleaseRound rate assignment B record)
    (i : ActiveRoundActions.Follower p.m)
    (hpending : (r.state i).status = .pending) :
    (r.nextState i).status = .released ↔
      ActiveFollowerLifecycle.releaseCondition rate.eta i
        (ActiveFollowerLifecycle.publicRowOfCompleteRow r.row r.time) (r.own i)
        (record i) := by
  have hcondition :
      ActiveFollowerLifecycle.releaseCondition rate.eta i
        (ActiveFollowerLifecycle.publicRowOfCompleteRow r.row r.time) (r.own i)
        (record i) =
      ActiveRoundActions.releaseObservation p.two_le_m r.snapshot r.action r.reward i := by
    rw [r.publicRowMatches]
    exact ActiveFollowerLifecycle.releaseCondition_eq_activeRoundActions rate.eta
      assignment r.snapshot r.action r.reward i (record i) (r.own i)
      (r.assignmentArm i) (r.auxiliaryArm i) (r.ownFeedback i)
  have hevent : pendingReleaseObservation r i ↔
      ActiveFollowerLifecycle.releaseCondition rate.eta i
        (ActiveFollowerLifecycle.publicRowOfCompleteRow r.row r.time) (r.own i)
        (record i) := by
    simp [pendingReleaseObservation, r.snapshotStatus i, hpending, hcondition]
  have hupdate := round_status_update r i (by rw [hpending]; decide)
  constructor
  · intro h
    rcases hupdate.1.mp h with hreleased | he
    · rw [hpending] at hreleased
      cases hreleased
    · exact hevent.mp he
  · intro hcondition
    exact hupdate.1.mpr (Or.inr (hevent.mpr hcondition))

/-- On a pending pre-choice, the existing lifecycle release operation frames
all non-status state fields. -/
theorem round_pending_release_frames_nonstatus {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (r : LocalReleaseRound rate assignment B record)
    (i : ActiveRoundActions.Follower p.m)
    (hpending : (r.state i).status = .pending) :
    (r.afterRelease i).lastDown = (r.serviceResult i).output.lastDown ∧
      (r.afterRelease i).S = (r.serviceResult i).output.S ∧
      (r.afterRelease i).delta = (r.serviceResult i).output.delta ∧
      (r.afterRelease i).backlog = (r.serviceResult i).output.backlog ∧
      (r.afterRelease i).downBatch = (r.serviceResult i).output.downBatch ∧
      (r.afterRelease i).buffer = (r.serviceResult i).output.buffer ∧
      (r.afterRelease i).initializationFailure =
        (r.serviceResult i).output.initializationFailure := by
  have hserviceFrame := round_service_frame r i
  have hpostRecord :
      (¬ ActiveFollowerLifecycle.releaseCondition rate.eta i
          (ActiveFollowerLifecycle.publicRowOfCompleteRow r.row r.time) (r.own i)
          (record i) ∧ (r.serviceResult i).output.status = .unoccupied) ∨
        (∃ M', (r.serviceResult i).output.lastDown = some M' ∧
          M'.val.sigma ≤ r.time.val + 1) := by
    right
    refine ⟨record i, ?_, ?_⟩
    · rw [hserviceFrame.1, r.carriedRecord i]
    · exact Nat.le_trans (r.recordStarted i) (Nat.le_succ _)
  exact ActiveFollowerLifecycle.releaseAfterService_pending_frame rate.eta i r.time
    (ActiveFollowerLifecycle.publicRowOfCompleteRow r.row r.time) (r.own i)
    (r.state i) (r.serviceResult i).output (r.afterRelease i) hpending
    (r.localDomain i) (record i) (r.carriedRecord i) (r.recordStarted i)
    (r.postServiceDomain i) hpostRecord (r.release i)

private theorem localReleaseChain_occupied {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (rounds : List (LocalReleaseRound rate assignment B record))
    (i : ActiveRoundActions.Follower p.m)
    (hchain : List.IsChain localReleaseFollows rounds)
    (hhead : ∀ r, rounds.head? = some r → (r.state i).status ≠ .unoccupied) :
    ∀ r ∈ rounds, (r.state i).status ≠ .unoccupied := by
  induction rounds with
  | nil => simp
  | cons first tail ih =>
      have hfirst := hhead first (by simp)
      cases tail with
      | nil =>
          intro r hr
          simp at hr
          subst r
          exact hfirst
      | cons second rest =>
          have hparts := List.isChain_cons_cons.mp hchain
          have hstatusUpdate := round_status_update first i hfirst
          have hnextOccupied : (first.nextState i).status = .pending ∨
              (first.nextState i).status = .released := by
            cases hstatus : (first.state i).status with
            | unoccupied => exact (hfirst hstatus).elim
            | pending =>
                by_cases hobs : pendingReleaseObservation first i
                · exact Or.inr (hstatusUpdate.1.mpr (Or.inr hobs))
                · exact Or.inl (hstatusUpdate.2.mpr ⟨hstatus, hobs⟩)
            | released => exact Or.inr (hstatusUpdate.1.mpr (Or.inl hstatus))
          have hsecond : (second.state i).status ≠ .unoccupied := by
            rw [hparts.1.2.1 i]
            intro hu
            rcases hnextOccupied with h | h
            · rw [h] at hu
              cases hu
            · rw [h] at hu
              cases hu
          have htailHead : ∀ r, (second :: rest).head? = some r →
              (r.state i).status ≠ .unoccupied := by
            intro r hr
            simp at hr
            subst r
            exact hsecond
          have htail := ih hparts.2 htailHead
          intro r hr
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact hfirst
          · exact htail r (by simp [hr])

private theorem localReleaseTrace_occupied {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseTrace rate assignment B record)
    (i : ActiveRoundActions.Follower p.m) :
    ∀ r ∈ trace.rounds, (r.state i).status ≠ .unoccupied := by
  have hhead : ∀ r, trace.rounds.head? = some r →
      (r.state i).status ≠ .unoccupied := by
    intro r hr
    have hstart := trace.firstState r hr i
    rw [hstart.1]
    rcases trace.initialStatus i with h | h
    · rw [h]
      decide
    · rw [h]
      decide
  exact localReleaseChain_occupied trace.rounds i trace.follows hhead

/-- The successful local observation's full output state is the framed
`FinishRound` state; the only status update occurs in the lifecycle release
stage. -/
theorem round_finish_frames_state {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (r : LocalReleaseRound rate assignment B record)
    (i : ActiveRoundActions.Follower p.m) : r.nextState i = r.afterRelease i := by
  exact ActiveFollowerLifecycle.finishRound_frame rate.eta r.time r.row
    (r.afterRelease i) (r.nextState i) (r.memory i) (r.nextMemory i) (r.finish i)

/-- Adjacent successful rounds have nested pending sets. -/
theorem pendingSet_mono_of_follows {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (earlier later : LocalReleaseRound rate assignment B record)
    (hfollow : localReleaseFollows earlier later)
    (hoccupied : ∀ i, (earlier.state i).status ≠ .unoccupied) :
    pendingFollowerSet later ⊆ pendingFollowerSet earlier := by
  intro i hi
  have hlaterPending : later.snapshot.status i = .pending :=
    (Finset.mem_filter.mp hi).2
  have hnextPending : (earlier.nextState i).status = .pending := by
    have hstate := hlaterPending
    rw [later.snapshotStatus i] at hstate
    rw [(hfollow.2.1 i)] at hstate
    exact hstate
  have hbeforePending :=
    (round_status_update earlier i (hoccupied i)).2.mp hnextPending
  have hearlierPending : earlier.snapshot.status i = .pending := by
    rw [earlier.snapshotStatus i]
    exact hbeforePending.1
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hearlierPending⟩

/-- The literal pending-set sequence is a chronological chain under subset.
Transitivity of subset gives nesting between any two rounds in the interval. -/
theorem pendingSet_sequence_chain {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (rounds : List (LocalReleaseRound rate assignment B record))
    (hchain : List.IsChain localReleaseFollows rounds)
    (hoccupied : ∀ r ∈ rounds, ∀ i, (r.state i).status ≠ .unoccupied) :
    List.IsChain (fun earlier later : Finset (ActiveRoundActions.Follower p.m) =>
      later ⊆ earlier)
      (rounds.map (fun r => pendingFollowerSet (rate := rate) (assignment := assignment)
        (B := B) (record := record) r)) := by
  induction rounds with
  | nil => exact .nil
  | cons earlier tail ih =>
      cases tail with
      | nil => exact .singleton _
      | cons later rest =>
          have hparts := List.isChain_cons_cons.mp hchain
          have hfirstOccupied : ∀ i, (earlier.state i).status ≠ .unoccupied :=
            hoccupied earlier (by simp)
          have htailOccupied : ∀ r ∈ later :: rest, ∀ i,
              (r.state i).status ≠ .unoccupied := by
            intro r hr i
            exact hoccupied r (by simp [hr]) i
          exact .cons_cons
            (pendingSet_mono_of_follows earlier later hparts.1 hfirstOccupied)
            (ih hparts.2 htailOccupied)

private theorem pairwise_of_isChain_trans {α : Type} {R : α → α → Prop}
    [IsTrans α R] (xs : List α) (hchain : List.IsChain R xs) :
    xs.Pairwise R := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons first tail ih =>
      cases tail with
      | nil => exact List.Pairwise.cons (by simp) List.Pairwise.nil
      | cons second rest =>
          have hparts := List.isChain_cons_cons.mp hchain
          rw [List.pairwise_cons_cons_iff_of_trans]
          exact ⟨hparts.1, ih hparts.2⟩

/-- Promote adjacent pending-set nesting to pairwise nesting of the complete
calendar family. -/
theorem pendingSet_sequence_pairwise_nested {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (rounds : List (LocalReleaseRound rate assignment B record))
    (hchain : List.IsChain localReleaseFollows rounds)
    (hoccupied : ∀ r ∈ rounds, ∀ i, (r.state i).status ≠ .unoccupied) :
    (rounds.map (fun r => pendingFollowerSet (rate := rate) (assignment := assignment)
      (B := B) (record := record) r)).Pairwise
      (fun earlier later : Finset (ActiveRoundActions.Follower p.m) => later ⊆ earlier) := by
  have hsetChain := pendingSet_sequence_chain rounds hchain hoccupied
  let R : Finset (ActiveRoundActions.Follower p.m) →
      Finset (ActiveRoundActions.Follower p.m) → Prop :=
    fun earlier later => later ⊆ earlier
  have htrans : IsTrans (Finset (ActiveRoundActions.Follower p.m)) R :=
    ⟨fun _ _ _ h₁ h₂ => Finset.Subset.trans h₂ h₁⟩
  change (rounds.map (fun r => pendingFollowerSet (rate := rate) (assignment := assignment)
    (B := B) (record := record) r)).Pairwise R
  exact @pairwise_of_isChain_trans _ R htrans _ hsetChain

/-- The trace's actual pending-set family is nested without an additional
occupancy hypothesis; occupancy follows from the initial live states, the
successful local updates, and the no-interruption preparation equations. -/
theorem trace_pendingSet_sequence_chain {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseTrace rate assignment B record) :
    List.IsChain (fun earlier later : Finset (ActiveRoundActions.Follower p.m) =>
      later ⊆ earlier)
      (trace.rounds.map (fun r => pendingFollowerSet (rate := rate)
        (assignment := assignment) (B := B) (record := record) r)) :=
  pendingSet_sequence_chain trace.rounds trace.follows
    (fun r hr i => localReleaseTrace_occupied trace i r hr)

/-- Pairwise form of the nested pending-set family over the whole interval. -/
theorem trace_pendingSet_pairwise_nested {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseTrace rate assignment B record) :
    (trace.rounds.map (fun r => pendingFollowerSet (rate := rate)
      (assignment := assignment) (B := B) (record := record) r)).Pairwise
      (fun earlier later : Finset (ActiveRoundActions.Follower p.m) => later ⊆ earlier) :=
  pendingSet_sequence_pairwise_nested trace.rounds trace.follows
    (fun r hr i => localReleaseTrace_occupied trace i r hr)

/-- A released follower has zero pending release observations in any successful
suffix of the fixed interval. -/
private theorem pendingReleaseCount_zero_of_first_released {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (rounds : List (LocalReleaseRound rate assignment B record))
    (i : ActiveRoundActions.Follower p.m)
    (hchain : List.IsChain localReleaseFollows rounds)
    (hreleased : ∀ r, rounds.head? = some r → (r.state i).status = .released) :
    pendingReleaseCalendarCount rounds i = 0 := by
  have hallReleased : ∀ r ∈ rounds, (r.state i).status = .released := by
    induction rounds with
    | nil => simp
    | cons first tail ih =>
        have hfirstReleased := hreleased first (by simp)
        cases tail with
        | nil =>
            intro r hr
            simp at hr
            subst r
            exact hfirstReleased
        | cons second rest =>
            have hparts := List.isChain_cons_cons.mp hchain
            have hfirstOccupied : (first.state i).status ≠ .unoccupied := by
              rw [hfirstReleased]
              decide
            have hnextReleased :=
              (round_status_update first i hfirstOccupied).1.mpr (Or.inl hfirstReleased)
            have hsecondReleased : (second.state i).status = .released := by
              rw [hparts.1.2.1 i]
              exact hnextReleased
            have htailHead : ∀ r, (second :: rest).head? = some r →
                (r.state i).status = .released := by
              intro r hr
              simp at hr
              subst r
              exact hsecondReleased
            have htail := ih hparts.2 htailHead
            intro r hr
            simp only [List.mem_cons] at hr
            rcases hr with rfl | hr
            · exact hfirstReleased
            · exact htail r (by simp [hr])
  have hfalse : ∀ r ∈ rounds, pendingReleaseFlag r i = false := by
    intro r hr
    have hs := hallReleased r hr
    simp [pendingReleaseFlag, pendingReleaseObservation, r.snapshotStatus i, hs]
  change rounds.countP (fun r => pendingReleaseFlag r i) = 0
  exact list_countP_eq_zero_of_false rounds (fun r => pendingReleaseFlag r i) hfalse

private theorem pendingReleaseCount_quota_aux {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (rounds : List (LocalReleaseRound rate assignment B record))
    (i : ActiveRoundActions.Follower p.m)
    (hchain : List.IsChain localReleaseFollows rounds)
    (hhead : ∀ r, rounds.head? = some r → (r.state i).status ≠ .unoccupied) :
    pendingReleaseCalendarCount rounds i ≤ 1 := by
  classical
  induction rounds with
  | nil => simp [pendingReleaseCalendarCount]
  | cons first tail ih =>
      have hfirstOccupied := hhead first (by simp)
      cases tail with
      | nil =>
          by_cases hobs : pendingReleaseObservation first i <;>
            simp [pendingReleaseCalendarCount, pendingReleaseFlag, hobs]
      | cons second rest =>
          have hparts := List.isChain_cons_cons.mp hchain
          have hstatusUpdate := round_status_update first i hfirstOccupied
          have hnextStatus : (first.nextState i).status = .pending ∨
              (first.nextState i).status = .released := by
            cases hstatus : (first.state i).status with
            | unoccupied => exact (hfirstOccupied hstatus).elim
            | pending =>
                by_cases hobs : pendingReleaseObservation first i
                · exact Or.inr (hstatusUpdate.1.mpr (Or.inr hobs))
                · exact Or.inl (hstatusUpdate.2.mpr ⟨hstatus, hobs⟩)
            | released =>
                exact Or.inr (hstatusUpdate.1.mpr (Or.inl hstatus))
          have hsecondStatus : (second.state i).status = .pending ∨
              (second.state i).status = .released := by
            rw [hparts.1.2.1 i]
            exact hnextStatus
          have htailHead : ∀ r, (second :: rest).head? = some r →
              (r.state i).status ≠ .unoccupied := by
            intro r hr
            simp at hr
            subst r
            rcases hsecondStatus with h | h
            · rw [h]
              decide
            · rw [h]
              decide
          have htailQuota := ih hparts.2 htailHead
          have hcount := pendingReleaseCount_cons first (second :: rest) i
          cases hfirstStatus : (first.state i).status with
          | unoccupied => exact (hfirstOccupied hfirstStatus).elim
          | released =>
              have hobs : ¬ pendingReleaseObservation first i := by
                simp [pendingReleaseObservation, first.snapshotStatus i, hfirstStatus]
              have hnextReleased := hstatusUpdate.1.mpr (Or.inl hfirstStatus)
              have hsecondReleased : (second.state i).status = .released := by
                rw [hparts.1.2.1 i]
                exact hnextReleased
              have htailReleased : ∀ r, (second :: rest).head? = some r →
                  (r.state i).status = .released := by
                intro r hr
                simp at hr
                subst r
                exact hsecondReleased
              have hzero := pendingReleaseCount_zero_of_first_released
                (second :: rest) i hparts.2 htailReleased
              rw [hcount]
              simp [pendingReleaseFlag, hobs, hzero]
          | pending =>
              by_cases hobs : pendingReleaseObservation first i
              · have hnextReleased := hstatusUpdate.1.mpr (Or.inr hobs)
                have hsecondReleased : (second.state i).status = .released := by
                  rw [hparts.1.2.1 i]
                  exact hnextReleased
                have htailReleased : ∀ r, (second :: rest).head? = some r →
                    (r.state i).status = .released := by
                  intro r hr
                  simp at hr
                  subst r
                  exact hsecondReleased
                have hzero := pendingReleaseCount_zero_of_first_released
                  (second :: rest) i hparts.2 htailReleased
                rw [hcount]
                simp [pendingReleaseFlag, hobs, hzero]
              · have hnextPending := hstatusUpdate.2.mpr ⟨hfirstStatus, hobs⟩
                rw [hcount]
                simp [pendingReleaseFlag, hobs]
                exact htailQuota

/-- Calendar quota one for every follower in a finite successful local
interval. Pending status is PRE-CHOICE; release tests use the literal action
observation. The theorem derives absorbing release and pending-set nesting
from the local operations, rather than assuming either property. -/
theorem pendingReleaseCalendarCount_le_one {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseTrace rate assignment B record)
    (i : ActiveRoundActions.Follower p.m) :
    pendingReleaseCalendarCount trace.rounds i ≤ 1 := by
  have hheadOccupied : ∀ r, trace.rounds.head? = some r →
      (r.state i).status ≠ .unoccupied := by
    intro r hr
    have hstart := trace.firstState r hr i
    rw [hstart.1]
    rcases trace.initialStatus i with h | h
    · rw [h]
      decide
    · rw [h]
      decide
  exact pendingReleaseCount_quota_aux trace.rounds i trace.follows hheadOccupied

/-- Backward propagation over a source-ordered chain: pending at the endpoint
forces every prior choice to have been pending with no release observation. -/
private theorem prior_rounds_pending_before_endpoint {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (i : ActiveRoundActions.Follower p.m)
    (priorRounds : List (LocalReleaseRound rate assignment B record))
    (current : LocalReleaseRound rate assignment B record)
    (suffix : List (LocalReleaseRound rate assignment B record))
    (hchain : List.IsChain localReleaseFollows (priorRounds ++ current :: suffix))
    (hcurrentPending : (current.state i).status = .pending)
    (hoccupied : ∀ r ∈ priorRounds, (r.state i).status ≠ .unoccupied) :
    ∀ r ∈ priorRounds,
      (r.state i).status = .pending ∧ ¬ pendingReleaseObservation r i := by
  induction priorRounds with
  | nil => simp
  | cons first rest ih =>
      have hfirstOccupied : (first.state i).status ≠ .unoccupied :=
        hoccupied first (by simp)
      cases rest with
      | nil =>
          have hlocal : List.IsChain localReleaseFollows (first :: current :: suffix) := by
            simpa using hchain
          have hfollow := (List.isChain_cons_cons.mp hlocal).1
          have hnextPending : (first.nextState i).status = .pending := by
            rw [← hfollow.2.1 i]
            exact hcurrentPending
          have hsource := (round_status_update first i hfirstOccupied).2.mp hnextPending
          intro r hr
          simp at hr
          subst r
          exact hsource
      | cons second tail =>
          have hlocal : List.IsChain localReleaseFollows
              (first :: second :: (tail ++ current :: suffix)) := by
            simpa [List.cons_append] using hchain
          have hparts := List.isChain_cons_cons.mp hlocal
          have hrestChain : List.IsChain localReleaseFollows
              ((second :: tail) ++ current :: suffix) := by
            simpa [List.cons_append] using hparts.2
          have hrestOccupied : ∀ r ∈ second :: tail,
              (r.state i).status ≠ .unoccupied := by
            intro r hr
            exact hoccupied r (by simp [hr])
          have hrestPending := ih hrestChain hrestOccupied
          have hsecondPending := hrestPending second (by simp)
          have hnextPending : (first.nextState i).status = .pending := by
            rw [← hparts.1.2.1 i]
            exact hsecondPending.1
          have hsource := (round_status_update first i hfirstOccupied).2.mp hnextPending
          intro r hr
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact hsource
          · exact hrestPending r (by simp [hr])

/-- If a follower is pending at an included round, its strict pre-count of
literal pending release observations is zero (hence `< 1`). `priorRounds` is
the complete calendar prefix before that round. -/
theorem pendingRelease_preCount_lt_one {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseTrace rate assignment B record)
    (i : ActiveRoundActions.Follower p.m)
    (priorRounds : List (LocalReleaseRound rate assignment B record))
    (current : LocalReleaseRound rate assignment B record)
    (suffix : List (LocalReleaseRound rate assignment B record))
    (hdecomposition : trace.rounds = priorRounds ++ current :: suffix)
    (hpending : current.snapshot.status i = .pending) :
    pendingReleaseCalendarCount priorRounds i < 1 := by
  have hcurrentPending : (current.state i).status = .pending := by
    rw [← current.snapshotStatus i]
    exact hpending
  have hchain : List.IsChain localReleaseFollows (priorRounds ++ current :: suffix) := by
    rw [← hdecomposition]
    exact trace.follows
  have hpriorOccupied : ∀ r ∈ priorRounds, (r.state i).status ≠ .unoccupied := by
    intro r hr
    exact (localReleaseTrace_occupied trace i) r (by
      rw [hdecomposition]
      simp only [List.mem_append]
      exact Or.inl hr)
  have hpriorPending := prior_rounds_pending_before_endpoint i priorRounds current suffix
    hchain hcurrentPending hpriorOccupied
  have hcountZero : pendingReleaseCalendarCount priorRounds i = 0 := by
    classical
    change priorRounds.countP (fun r => pendingReleaseFlag r i) = 0
    apply list_countP_eq_zero_of_false
    intro r hr
    have hno := (hpriorPending r hr).2
    simp [pendingReleaseFlag, hno]
  omega

/-- UP-only release count is at most one, as a subcount of the literal total. -/
theorem pendingUpReleaseCalendarCount_le_one {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseTrace rate assignment B record)
    (i : ActiveRoundActions.Follower p.m) :
    pendingUpReleaseCalendarCount trace.rounds i ≤ 1 := by
  classical
  have hmono : pendingUpReleaseCalendarCount trace.rounds i ≤
      pendingReleaseCalendarCount trace.rounds i := by
    change trace.rounds.countP (fun r => decide
      (pendingReleaseObservation r i ∧ r.action.slot = upSlot)) ≤
      trace.rounds.countP (fun r => decide (pendingReleaseObservation r i))
    apply list_countP_le_of_imp
    intro r h
    have htest : pendingReleaseObservation r i ∧ r.action.slot = upSlot :=
      of_decide_eq_true h
    change decide (pendingReleaseObservation r i) = true
    rw [decide_eq_true_eq]
    exact htest.1
  exact hmono.trans (pendingReleaseCalendarCount_le_one trace i)

/-- DATA-only release count is at most one, as a subcount of the literal total. -/
theorem pendingDataReleaseCalendarCount_le_one {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseTrace rate assignment B record)
    (i : ActiveRoundActions.Follower p.m) :
    pendingDataReleaseCalendarCount trace.rounds i ≤ 1 := by
  classical
  have hmono : pendingDataReleaseCalendarCount trace.rounds i ≤
      pendingReleaseCalendarCount trace.rounds i := by
    change trace.rounds.countP (fun r => decide
      (pendingReleaseObservation r i ∧ r.action.slot = dataSlot)) ≤
      trace.rounds.countP (fun r => decide (pendingReleaseObservation r i))
    apply list_countP_le_of_imp
    intro r h
    have htest : pendingReleaseObservation r i ∧ r.action.slot = dataSlot :=
      of_decide_eq_true h
    change decide (pendingReleaseObservation r i) = true
    rw [decide_eq_true_eq]
    exact htest.1
  exact hmono.trans (pendingReleaseCalendarCount_le_one trace i)

end Bandits.Support.LocalReleaseQuota

end
