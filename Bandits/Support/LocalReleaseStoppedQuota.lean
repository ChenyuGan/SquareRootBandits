/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.LocalReleaseQuota
public import Mathlib.Data.List.Count

/-!
# Conditional local release quota through a terminal observation

This module extends the accepted successful local release trace by at most one
pre-choice observation at the interval endpoint. The observation may be the
round where a local checked operation first fails, or a round stopped by an
external coordinator/other-player failure. Its record contains no post-error
continuation and is not an alternative execution.

The interval and quota argument is sourced from
`sources/zip4/manuscript/05_binary_transport.tex:293-348` and
`sources/zip4/manuscript/06_interruptions.tex:270-325`. The producer of the
physical source window, any external failure witness, conditional laws,
waiting bound, and source theorem remain separate obligations.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.LocalReleaseStoppedQuota

open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ActiveFollowerQueueOperation
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ConstructorDimensions
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.FollowerCutoffScan
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.PrelaunchBufferRecovery
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ReferencePrelaunchFollower

variable {p : Parameters}

/-- The final observed round is proof data for the existing local operations.
It fixes the same complete row, choice snapshot, action, reward row, typed
own-feedback, assignment, state, memory and accepted DOWN record as an
ordinary successful release round. `prepared` is the actual successful
`prepare` equation. There is deliberately no service-success, release-success,
finish-success, next-state, or continuation field. -/
structure LocalReleaseTerminalObservation (rate : RateInput p)
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
  prepared : ∀ i,
    DeclaredFollowerLocalRound.prepare rate i row (activation i) time (active i)
        (.ordinary (state i) (memory i)) =
      ⟨i, row, activation i, time, active i, arm i,
        .ordinary (state i) (memory i)⟩
  beforeCutoff : ∀ i,
    time.val + 1 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val
      (ActiveFollowerLifecycle.acceptedStartCoordinate (record i))
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
  /-- A future physical producer supplies this event only when the interval is
  stopped by the coordinator or another player. It is not itself an execution
  or transition definition. -/
  externalCoordinatorOrOtherPlayerFailure : Prop
  /-- Exact local terminal causes: a failed checked service on the occupied
  branch, an error from the actual ordinary observation composition, or the
  separately supplied external failure event. -/
  terminalFailure :
    (∃ i, (state i).status ≠ .unoccupied ∧
      ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
        rate.n rate.n_scale i row (activation i) time (own i) (state i) = .failure) ∨
    (∃ i reason, DeclaredFollowerLocalRound.observeOrdinary rate i row
      (activation i) time (active i) (arm i) (own i) (state i) (memory i) =
        .error reason) ∨ externalCoordinatorOrOtherPlayerFailure

/-- A terminal checked-service failure is the exact first-stage error in the
existing `observeOrdinary` composition, before release or finish is attempted. -/
theorem terminal_checkedService_failure_is_observeOrdinary_failure {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (terminal : LocalReleaseTerminalObservation rate assignment B record)
    (i : ActiveRoundActions.Follower p.m)
    (hoccupied : (terminal.state i).status ≠ .unoccupied)
    (hservice : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
      rate.n rate.n_scale i terminal.row (terminal.activation i) terminal.time
      (terminal.own i) (terminal.state i) = .failure) :
    DeclaredFollowerLocalRound.observeOrdinary rate i terminal.row
      (terminal.activation i) terminal.time (terminal.active i) (terminal.arm i)
      (terminal.own i) (terminal.state i) (terminal.memory i) = .error .service := by
  have hfirst := DeclaredFollowerLocalRound.recordOrServiceThenDown_service_failure
    rate i terminal.row (terminal.activation i) terminal.time (terminal.active i)
    (terminal.arm i) (terminal.own i) (terminal.state i) hoccupied hservice
  exact DeclaredFollowerLocalRound.observeOrdinary_first_stage_failure rate i
    terminal.row (terminal.activation i) terminal.time (terminal.active i)
    (terminal.arm i) (terminal.own i) (terminal.state i) (terminal.memory i)
    .service hfirst

/-- Literal PRE-CHOICE pending release observation on the terminal action.
The observation is counted even when its subsequent release update is not
executed because this round fails. -/
def terminalPendingReleaseObservation {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (terminal : LocalReleaseTerminalObservation rate assignment B record)
    (i : ActiveRoundActions.Follower p.m) : Prop :=
  terminal.snapshot.status i = .pending ∧
    ActiveRoundActions.releaseObservation p.two_le_m terminal.snapshot
      terminal.action terminal.reward i

/-- Boolean form of the literal terminal PRE-CHOICE observation. -/
def terminalPendingReleaseFlag {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (terminal : LocalReleaseTerminalObservation rate assignment B record)
    (i : ActiveRoundActions.Follower p.m) : Bool := by
  classical
  exact decide (terminalPendingReleaseObservation terminal i)

/-- The terminal observation's pre-choice pending follower set. -/
def terminalPendingFollowerSet {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (terminal : LocalReleaseTerminalObservation rate assignment B record) :
    Finset (ActiveRoundActions.Follower p.m) := by
  classical
  exact Finset.univ.filter (fun i => terminal.snapshot.status i = .pending)

/-- A source-ordered successful prefix followed by zero or one terminal
pre-choice observation. The accepted trace supplies the exact successful
calendar interval and all horizon/cutoff bounds. A terminal observation is at
the exclusive endpoint, linked to the last successful `FinishRound` state and
memory, or to the initial state and memory when the successful prefix is
empty. With no terminal observation, the endpoint is explicitly a horizon or
cutoff truncation. -/
structure LocalReleaseStoppedTrace (rate : RateInput p)
    (assignment : ActiveRoundActions.Assignment p.m p.K) (B : ℕ)
    (record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) where
  successful : LocalReleaseQuota.LocalReleaseTrace rate assignment B record
  terminal : Option (LocalReleaseTerminalObservation rate assignment B record)
  terminalEndpoint : ∀ t, terminal = some t → t.time.val = successful.intervalStop
  terminalBeforeHorizon : ∀ t, terminal = some t → t.time.val + 1 ≤ p.T
  terminalAfterLast : ∀ t, terminal = some t → ∀ last,
    successful.rounds.getLast? = some last → ∀ i,
      t.state i = last.nextState i ∧ t.memory i = last.nextMemory i
  terminalAfterEmpty : ∀ t, terminal = some t → successful.rounds = [] → ∀ i,
    t.state i = successful.initialState i ∧ t.memory i = successful.initialMemory i
  noTerminalTruncation : terminal = none →
    successful.intervalStop = p.T ∨
      ∃ i, successful.intervalStop =
        FollowerCutoffScan.gridBoundary p rate.eta.val
          (ActiveFollowerLifecycle.acceptedStartCoordinate (record i))

/-- The successful-prefix event counted by the stopped interval. -/
def stoppedPendingReleaseCalendarCount {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseStoppedTrace rate assignment B record)
    (i : ActiveRoundActions.Follower p.m) : ℕ :=
  LocalReleaseQuota.pendingReleaseCalendarCount trace.successful.rounds i +
    (match trace.terminal with
    | none => 0
    | some terminal => if terminalPendingReleaseFlag terminal i then 1 else 0)

/-- UP-only count, including the terminal PRE-CHOICE observation. -/
def stoppedPendingUpReleaseCalendarCount {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseStoppedTrace rate assignment B record)
    (i : ActiveRoundActions.Follower p.m) : ℕ :=
  LocalReleaseQuota.pendingUpReleaseCalendarCount trace.successful.rounds i +
    (match trace.terminal with
    | none => 0
    | some terminal =>
        if terminalPendingReleaseFlag terminal i && decide (terminal.action.slot = upSlot)
        then 1 else 0)

/-- DATA-only count, including the terminal PRE-CHOICE observation. -/
def stoppedPendingDataReleaseCalendarCount {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseStoppedTrace rate assignment B record)
    (i : ActiveRoundActions.Follower p.m) : ℕ :=
  LocalReleaseQuota.pendingDataReleaseCalendarCount trace.successful.rounds i +
    (match trace.terminal with
    | none => 0
    | some terminal =>
        if terminalPendingReleaseFlag terminal i && decide (terminal.action.slot = dataSlot)
        then 1 else 0)

/-- The pending set on the whole stopped interval, in calendar order: all
successful pre-choice sets and, if present, the terminal pre-choice set. -/
def stoppedPendingSetSequence {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseStoppedTrace rate assignment B record) :
    List (Finset (ActiveRoundActions.Follower p.m)) :=
  trace.successful.rounds.map (fun r => LocalReleaseQuota.pendingFollowerSet r) ++
    trace.terminal.toList.map terminalPendingFollowerSet

private theorem stopped_countP_eq_zero_of_false {α : Type} (xs : List α)
    (P : α → Bool) (hfalse : ∀ x ∈ xs, P x = false) : xs.countP P = 0 := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      have hx := hfalse x (by simp)
      have hrest : ∀ y ∈ rest, P y = false := by
        intro y hy
        exact hfalse y (by simp [hy])
      simp [hx, ih hrest]

private theorem successful_chain_occupied {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (rounds : List (LocalReleaseQuota.LocalReleaseRound rate assignment B record))
    (i : ActiveRoundActions.Follower p.m)
    (hchain : List.IsChain LocalReleaseQuota.localReleaseFollows rounds)
    (hhead : ∀ r, rounds.head? = some r → (r.state i).status ≠ .unoccupied) :
    ∀ r ∈ rounds, (r.state i).status ≠ .unoccupied := by
  induction rounds with
  | nil => simp
  | cons first tail ih =>
      have hfirst := hhead first (by simp)
      cases tail with
      | nil =>
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          subst r
          exact hfirst
      | cons second rest =>
          have hparts := List.isChain_cons_cons.mp hchain
          have hupdate := LocalReleaseQuota.round_status_update first i hfirst
          have hnext : (first.nextState i).status = .pending ∨
              (first.nextState i).status = .released := by
            cases hs : (first.state i).status with
            | unoccupied => exact (hfirst hs).elim
            | pending =>
                by_cases ho : LocalReleaseQuota.pendingReleaseObservation first i
                · exact Or.inr (hupdate.1.mpr (Or.inr ho))
                · exact Or.inl (hupdate.2.mpr ⟨hs, ho⟩)
            | released => exact Or.inr (hupdate.1.mpr (Or.inl hs))
          have hsecond : (second.state i).status ≠ .unoccupied := by
            rw [hparts.1.2.1 i]
            intro hu
            rcases hnext with hp | hr
            · rw [hp] at hu
              cases hu
            · rw [hr] at hu
              cases hu
          have htailHead : ∀ r, (second :: rest).head? = some r →
              (r.state i).status ≠ .unoccupied := by
            intro r hr
            simp only [List.head?_cons, Option.some.injEq] at hr
            subst r
            exact hsecond
          have htailOccupied := ih hparts.2 htailHead
          intro r hr
          have hmem : r = first ∨ r ∈ second :: rest := List.mem_cons.mp hr
          rcases hmem with hfirstMem | htailMem
          · subst r
            exact hfirst
          · exact htailOccupied r htailMem

private theorem successful_prefix_occupied {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseQuota.LocalReleaseTrace rate assignment B record)
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
  exact successful_chain_occupied trace.rounds i trace.follows hhead

/-- A pending terminal endpoint forces every successful pre-choice state for
that follower to have been pending, with no earlier literal release
observation. This is derived backwards from the actual status/finish frames. -/
private theorem pending_successful_prefix_of_endpoint {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (rounds : List (LocalReleaseQuota.LocalReleaseRound rate assignment B record))
    (i : ActiveRoundActions.Follower p.m)
    (endpointState : State p rate.eta)
    (hchain : List.IsChain LocalReleaseQuota.localReleaseFollows rounds)
    (hoccupied : ∀ r ∈ rounds, (r.state i).status ≠ .unoccupied)
    (hendpoint : ∀ last, rounds.getLast? = some last →
      last.nextState i = endpointState)
    (hendPending : endpointState.status = .pending) :
    ∀ r ∈ rounds,
      (r.state i).status = .pending ∧
        ¬ LocalReleaseQuota.pendingReleaseObservation r i := by
  revert endpointState hchain hoccupied hendpoint hendPending
  induction rounds with
  | nil => intro; simp
  | cons first tail ih =>
      intro endpointState hchain hoccupied hendpoint hendPending
      have hfirstOccupied := hoccupied first (by simp)
      cases tail with
      | nil =>
          have hlast : [first].getLast? = some first := by simp
          have hnext := hendpoint first hlast
          have hupdate := LocalReleaseQuota.round_status_update first i hfirstOccupied
          have hbefore := hupdate.2.mp (by rw [hnext]; exact hendPending)
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          subst r
          exact hbefore
      | cons second rest =>
          have hchain : List.IsChain LocalReleaseQuota.localReleaseFollows
              (first :: second :: rest) := by
            exact hchain
          have hparts := List.isChain_cons_cons.mp hchain
          have htailChain : List.IsChain LocalReleaseQuota.localReleaseFollows
              (second :: rest) := hparts.2
          have htailLast : ∀ last, (second :: rest).getLast? = some last →
              last.nextState i = endpointState := by
            intro last hl
            exact hendpoint last (by simpa using hl)
          have htailOccupied : ∀ r ∈ second :: rest,
              (r.state i).status ≠ .unoccupied := by
            intro r hr
            exact hoccupied r (List.mem_cons_of_mem first hr)
          have htail : ∀ r ∈ second :: rest,
              (r.state i).status = .pending ∧
                ¬ LocalReleaseQuota.pendingReleaseObservation r i :=
            ih endpointState htailChain htailOccupied htailLast hendPending
          have hsecondPending := htail second (by simp)
          have hnext : (first.nextState i).status = .pending := by
            rw [← hparts.1.2.1 i]
            exact hsecondPending.1
          have hupdate := LocalReleaseQuota.round_status_update first i hfirstOccupied
          have hbefore := hupdate.2.mp hnext
          intro r hr
          have hmem : r = first ∨ r ∈ second :: rest := List.mem_cons.mp hr
          rcases hmem with hfirst | htailMem
          · subst r
            exact hbefore
          · exact htail r htailMem

/-- Strict successful-calendar pre-count immediately before a terminal
pre-choice state that is still pending. -/
theorem pendingRelease_terminal_preCount_lt_one {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseStoppedTrace rate assignment B record)
    (terminal : LocalReleaseTerminalObservation rate assignment B record)
    (hterminal : trace.terminal = some terminal)
    (i : ActiveRoundActions.Follower p.m)
    (hpending : terminal.snapshot.status i = .pending) :
    LocalReleaseQuota.pendingReleaseCalendarCount trace.successful.rounds i < 1 := by
  have hstate : (terminal.state i).status = .pending := by
    rw [← terminal.snapshotStatus i]
    exact hpending
  classical
  have hoccupied := successful_prefix_occupied trace.successful i
  have hnoRelease := pending_successful_prefix_of_endpoint trace.successful.rounds i
    (terminal.state i) trace.successful.follows hoccupied
    (fun last hlast => by
      have hlink := trace.terminalAfterLast terminal hterminal last hlast i
      exact hlink.1.symm) hstate
  have hfalse : ∀ r ∈ trace.successful.rounds,
      LocalReleaseQuota.pendingReleaseFlag r i = false := by
    intro r hr
    have h := (hnoRelease r hr).2
    simp [LocalReleaseQuota.pendingReleaseFlag, h]
  have hzero : LocalReleaseQuota.pendingReleaseCalendarCount trace.successful.rounds i = 0 := by
    change trace.successful.rounds.countP
      (fun r => LocalReleaseQuota.pendingReleaseFlag r i) = 0
    exact stopped_countP_eq_zero_of_false _ _ hfalse
  omega

/-- The endpoint status is occupied: an empty prefix carries its accepted
initial pending/released status; a nonempty prefix carries the last successful
round's actual framed status. -/
theorem terminalStatus_pending_or_released {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseStoppedTrace rate assignment B record)
    (terminal : LocalReleaseTerminalObservation rate assignment B record)
    (hterminal : trace.terminal = some terminal)
    (i : ActiveRoundActions.Follower p.m) :
    (terminal.state i).status = .pending ∨ (terminal.state i).status = .released := by
  cases hrounds : trace.successful.rounds with
  | nil =>
      have hlink := trace.terminalAfterEmpty terminal hterminal hrounds i
      rw [hlink.1]
      exact trace.successful.initialStatus i
  | cons first rest =>
      have hne : trace.successful.rounds ≠ [] := by simp [hrounds]
      let last := trace.successful.rounds.getLast hne
      have hlast : trace.successful.rounds.getLast? = some last :=
        List.getLast?_eq_getLast_of_ne_nil hne
      have hmem : last ∈ trace.successful.rounds := List.getLast_mem hne
      have hoccupied := successful_prefix_occupied trace.successful i last hmem
      have hupdate := LocalReleaseQuota.round_status_update last i hoccupied
      have hnext : (last.nextState i).status = .pending ∨
          (last.nextState i).status = .released := by
        cases hs : (last.state i).status with
        | unoccupied => exact (hoccupied hs).elim
        | pending =>
            by_cases ho : LocalReleaseQuota.pendingReleaseObservation last i
            · exact Or.inr (hupdate.1.mpr (Or.inr ho))
            · exact Or.inl (hupdate.2.mpr ⟨hs, ho⟩)
        | released => exact Or.inr (hupdate.1.mpr (Or.inl hs))
      have hlink := trace.terminalAfterLast terminal hterminal last hlast i
      rw [hlink.1]
      exact hnext

/-- If a release was counted on the successful prefix, the terminal follower
is already released. Hence the terminal PRE-CHOICE pending-release flag is
false, even though the observation itself has been retained. -/
theorem terminalStatus_released_of_priorRelease {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseStoppedTrace rate assignment B record)
    (terminal : LocalReleaseTerminalObservation rate assignment B record)
    (hterminal : trace.terminal = some terminal)
    (i : ActiveRoundActions.Follower p.m)
    (hprior : 0 < LocalReleaseQuota.pendingReleaseCalendarCount
      trace.successful.rounds i) :
    terminal.snapshot.status i = .released := by
  have hnotPending : terminal.snapshot.status i ≠ .pending := by
    intro hpending
    have hpre := pendingRelease_terminal_preCount_lt_one trace terminal hterminal i hpending
    omega
  rcases terminalStatus_pending_or_released trace terminal hterminal i with hp | hr
  · have hsnapshot : terminal.snapshot.status i = .pending := by
      rw [terminal.snapshotStatus i]
      exact hp
    exact (hnotPending hsnapshot).elim
  · rw [terminal.snapshotStatus i]
    exact hr

/-- A previous successful release excludes a pending literal release event at
the terminal observation. -/
theorem terminalPendingReleaseObservation_false_of_priorRelease {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseStoppedTrace rate assignment B record)
    (terminal : LocalReleaseTerminalObservation rate assignment B record)
    (hterminal : trace.terminal = some terminal)
    (i : ActiveRoundActions.Follower p.m)
    (hprior : 0 < LocalReleaseQuota.pendingReleaseCalendarCount
      trace.successful.rounds i) :
    ¬ terminalPendingReleaseObservation terminal i := by
  intro hobs
  have hreleased := terminalStatus_released_of_priorRelease trace terminal hterminal i hprior
  change terminal.snapshot.status i = .pending ∧
    ActiveRoundActions.releaseObservation p.two_le_m terminal.snapshot
      terminal.action terminal.reward i at hobs
  rw [hreleased] at hobs
  cases hobs.1

/-- Boolean terminal flag form of the no-reentry endpoint conclusion. -/
theorem terminalPendingReleaseFlag_eq_false_of_priorRelease {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseStoppedTrace rate assignment B record)
    (terminal : LocalReleaseTerminalObservation rate assignment B record)
    (hterminal : trace.terminal = some terminal)
    (i : ActiveRoundActions.Follower p.m)
    (hprior : 0 < LocalReleaseQuota.pendingReleaseCalendarCount
      trace.successful.rounds i) :
    terminalPendingReleaseFlag terminal i = false := by
  have hfalse := terminalPendingReleaseObservation_false_of_priorRelease
    trace terminal hterminal i hprior
  simp [terminalPendingReleaseFlag, hfalse]

/-- If the terminal observation sees a follower pending, every successful
pre-choice set contains that follower. Thus the terminal set is nested below
all successful sets, including in the empty-prefix case (vacuously). -/
theorem terminalPendingSet_subset_each_successful {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseStoppedTrace rate assignment B record)
    (terminal : LocalReleaseTerminalObservation rate assignment B record)
    (hterminal : trace.terminal = some terminal)
    (r : LocalReleaseQuota.LocalReleaseRound rate assignment B record)
    (hr : r ∈ trace.successful.rounds) :
    terminalPendingFollowerSet terminal ⊆ LocalReleaseQuota.pendingFollowerSet r := by
  intro i hi
  have hpending : terminal.snapshot.status i = .pending := (Finset.mem_filter.mp hi).2
  have hstate : (terminal.state i).status = .pending := by
    rw [← terminal.snapshotStatus i]
    exact hpending
  have hoccupied := successful_prefix_occupied trace.successful i
  have hnoRelease := pending_successful_prefix_of_endpoint trace.successful.rounds i
    (terminal.state i) trace.successful.follows hoccupied (fun last hlast => by
      have hlink := trace.terminalAfterLast terminal hterminal last hlast i
      exact hlink.1.symm) hstate
  have hround := hnoRelease r hr
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, by
    rw [r.snapshotStatus i]
    exact hround.1⟩

/-- Exact partition of every counted pending release observation into its
literal UP and DATA slot counts. -/
private theorem countP_release_eq_slot_counts {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (rounds : List (LocalReleaseQuota.LocalReleaseRound rate assignment B record))
    (i : ActiveRoundActions.Follower p.m) :
    LocalReleaseQuota.pendingReleaseCalendarCount rounds i =
      LocalReleaseQuota.pendingUpReleaseCalendarCount rounds i +
        LocalReleaseQuota.pendingDataReleaseCalendarCount rounds i := by
  classical
  induction rounds with
  | nil => simp [LocalReleaseQuota.pendingReleaseCalendarCount,
      LocalReleaseQuota.pendingUpReleaseCalendarCount,
      LocalReleaseQuota.pendingDataReleaseCalendarCount]
  | cons r rest ih =>
      have hpart : (if LocalReleaseQuota.pendingReleaseFlag r i then 1 else 0) =
          (if decide (LocalReleaseQuota.pendingReleaseObservation r i ∧
              r.action.slot = upSlot) then 1 else 0) +
            (if decide (LocalReleaseQuota.pendingReleaseObservation r i ∧
              r.action.slot = dataSlot) then 1 else 0) := by
        by_cases h : LocalReleaseQuota.pendingReleaseObservation r i
        · have huOrData : r.action.slot = upSlot ∨ r.action.slot = dataSlot := by
            rcases h.2.2 with ⟨hslot, _, _⟩ | ⟨hslot, _⟩
            · exact Or.inl hslot
            · exact Or.inr hslot
          rcases huOrData with hu | hd
          · have hflag : LocalReleaseQuota.pendingReleaseFlag r i = true := by
              simp [LocalReleaseQuota.pendingReleaseFlag, h]
            have hup : decide (LocalReleaseQuota.pendingReleaseObservation r i ∧
                r.action.slot = upSlot) = true := by simp [h, hu]
            have hdata : decide (LocalReleaseQuota.pendingReleaseObservation r i ∧
                r.action.slot = dataSlot) = false := by
              have hne : upSlot ≠ dataSlot := by decide
              simp [h, hu, hne]
            simp [hflag, hup, hdata]
          · have hne : dataSlot ≠ upSlot := by decide
            have hflag : LocalReleaseQuota.pendingReleaseFlag r i = true := by
              simp [LocalReleaseQuota.pendingReleaseFlag, h]
            have hup : decide (LocalReleaseQuota.pendingReleaseObservation r i ∧
                r.action.slot = upSlot) = false := by simp [h, hd, hne]
            have hdata : decide (LocalReleaseQuota.pendingReleaseObservation r i ∧
                r.action.slot = dataSlot) = true := by simp [h, hd]
            simp [hflag, hup, hdata]
        · have hflag : LocalReleaseQuota.pendingReleaseFlag r i = false := by
            simp [LocalReleaseQuota.pendingReleaseFlag, h]
          have hup : decide (LocalReleaseQuota.pendingReleaseObservation r i ∧
              r.action.slot = upSlot) = false := by simp [h]
          have hdata : decide (LocalReleaseQuota.pendingReleaseObservation r i ∧
              r.action.slot = dataSlot) = false := by simp [h]
          simp [hflag, hup, hdata]
      simp only [LocalReleaseQuota.pendingReleaseCalendarCount,
        LocalReleaseQuota.pendingUpReleaseCalendarCount,
        LocalReleaseQuota.pendingDataReleaseCalendarCount,
        List.countP_cons]
      have ihCount : rest.countP (fun x => LocalReleaseQuota.pendingReleaseFlag x i) =
          rest.countP (fun x => decide (LocalReleaseQuota.pendingReleaseObservation x i ∧
            x.action.slot = upSlot)) +
          rest.countP (fun x => decide (LocalReleaseQuota.pendingReleaseObservation x i ∧
            x.action.slot = dataSlot)) := by
        simpa [LocalReleaseQuota.pendingReleaseCalendarCount,
          LocalReleaseQuota.pendingUpReleaseCalendarCount,
          LocalReleaseQuota.pendingDataReleaseCalendarCount] using ih
      rw [hpart, ihCount]
      omega

/-- The stopped total is exactly the sum of its UP and DATA subcounts. -/
theorem stoppedPendingReleaseCalendarCount_eq_subcounts {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseStoppedTrace rate assignment B record)
    (i : ActiveRoundActions.Follower p.m) :
    stoppedPendingReleaseCalendarCount trace i =
      stoppedPendingUpReleaseCalendarCount trace i +
        stoppedPendingDataReleaseCalendarCount trace i := by
  classical
  cases hterminal : trace.terminal with
  | none =>
      simp [stoppedPendingReleaseCalendarCount, stoppedPendingUpReleaseCalendarCount,
        stoppedPendingDataReleaseCalendarCount, hterminal,
        countP_release_eq_slot_counts]
  | some terminal =>
      have htermPart : (if terminalPendingReleaseFlag terminal i then 1 else 0) =
          (if terminalPendingReleaseFlag terminal i &&
              decide (terminal.action.slot = upSlot) then 1 else 0) +
            (if terminalPendingReleaseFlag terminal i &&
              decide (terminal.action.slot = dataSlot) then 1 else 0) := by
        change (if terminalPendingReleaseFlag terminal i = true then 1 else 0) =
          (if terminalPendingReleaseFlag terminal i &&
              decide (terminal.action.slot = upSlot) = true then 1 else 0) +
            (if terminalPendingReleaseFlag terminal i &&
              decide (terminal.action.slot = dataSlot) = true then 1 else 0)
        by_cases h : terminalPendingReleaseObservation terminal i
        · have huOrData : terminal.action.slot = upSlot ∨
              terminal.action.slot = dataSlot := by
            rcases h.2.2 with ⟨hslot, _, _⟩ | ⟨hslot, _⟩
            · exact Or.inl hslot
            · exact Or.inr hslot
          rcases huOrData with hu | hd
          · have hflag : terminalPendingReleaseFlag terminal i = true := by
              simp [terminalPendingReleaseFlag, h]
            have hup : decide (terminal.action.slot = upSlot) = true := by simp [hu]
            have hdata : decide (terminal.action.slot = dataSlot) = false := by
              have hne : upSlot ≠ dataSlot := by decide
              simp [hu, hne]
            simp [hflag, hup, hdata]
          · have hne : dataSlot ≠ upSlot := by decide
            have hflag : terminalPendingReleaseFlag terminal i = true := by
              simp [terminalPendingReleaseFlag, h]
            have hup : decide (terminal.action.slot = upSlot) = false := by
              simp [hd, hne]
            have hdata : decide (terminal.action.slot = dataSlot) = true := by simp [hd]
            simp [hflag, hup, hdata]
        · have hflag : terminalPendingReleaseFlag terminal i = false := by
            simp [terminalPendingReleaseFlag, h]
          simp [hflag]
      simp only [stoppedPendingReleaseCalendarCount,
        stoppedPendingUpReleaseCalendarCount,
        stoppedPendingDataReleaseCalendarCount, hterminal]
      rw [countP_release_eq_slot_counts]
      omega

/-- Quota one through the first terminal observation. If its literal
PRE-CHOICE release test is pending, the endpoint status equations force all
successful-prefix counts to be zero; otherwise the accepted successful quota
applies directly. -/
theorem stoppedPendingReleaseCalendarCount_le_one {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseStoppedTrace rate assignment B record)
    (i : ActiveRoundActions.Follower p.m) :
    stoppedPendingReleaseCalendarCount trace i ≤ 1 := by
  cases hterminal : trace.terminal with
  | none =>
      simpa [stoppedPendingReleaseCalendarCount, hterminal] using
        LocalReleaseQuota.pendingReleaseCalendarCount_le_one trace.successful i
  | some terminal =>
      by_cases hflag : terminalPendingReleaseObservation terminal i
      · have hpre := pendingRelease_terminal_preCount_lt_one trace terminal hterminal i hflag.1
        have hzero : LocalReleaseQuota.pendingReleaseCalendarCount trace.successful.rounds i = 0 := by
          omega
        simp [stoppedPendingReleaseCalendarCount, terminalPendingReleaseFlag,
          hterminal, hflag, hzero]
      · have hsuccess := LocalReleaseQuota.pendingReleaseCalendarCount_le_one trace.successful i
        simp [stoppedPendingReleaseCalendarCount, terminalPendingReleaseFlag,
          hterminal, hflag]
        exact hsuccess

/-- The UP release subquota is at most one. -/
theorem stoppedPendingUpReleaseCalendarCount_le_one {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseStoppedTrace rate assignment B record)
    (i : ActiveRoundActions.Follower p.m) :
    stoppedPendingUpReleaseCalendarCount trace i ≤ 1 := by
  have hsplit := stoppedPendingReleaseCalendarCount_eq_subcounts trace i
  have htotal := stoppedPendingReleaseCalendarCount_le_one trace i
  rw [hsplit] at htotal
  exact Nat.le_trans (Nat.le_add_right _ _) htotal

/-- The DATA release subquota is at most one. -/
theorem stoppedPendingDataReleaseCalendarCount_le_one {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseStoppedTrace rate assignment B record)
    (i : ActiveRoundActions.Follower p.m) :
    stoppedPendingDataReleaseCalendarCount trace i ≤ 1 := by
  have hsplit := stoppedPendingReleaseCalendarCount_eq_subcounts trace i
  have htotal := stoppedPendingReleaseCalendarCount_le_one trace i
  rw [hsplit] at htotal
  exact Nat.le_trans (Nat.le_add_left _ _) htotal

/-- The complete stopped pending-set sequence is pairwise nested. The
successful portion uses the accepted sequence theorem; every terminal set is
proved to be a subset of each successful set from the actual endpoint status
update. -/
theorem stoppedPendingSetSequence_pairwise_nested {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseStoppedTrace rate assignment B record) :
    (stoppedPendingSetSequence trace).Pairwise
      (fun earlier later : Finset (ActiveRoundActions.Follower p.m) => later ⊆ earlier) := by
  cases hterminal : trace.terminal with
  | none =>
      simpa [stoppedPendingSetSequence, hterminal] using
        LocalReleaseQuota.trace_pendingSet_pairwise_nested trace.successful
  | some terminal =>
      classical
      rw [stoppedPendingSetSequence, hterminal, Option.toList_some, List.map_singleton,
        List.pairwise_append]
      refine ⟨LocalReleaseQuota.trace_pendingSet_pairwise_nested trace.successful,
        (by simp), ?_⟩
      intro earlier hearlier later hlater
      simp only [List.mem_singleton] at hlater
      subst later
      rcases List.mem_map.mp hearlier with ⟨r, hr, rfl⟩
      exact terminalPendingSet_subset_each_successful trace terminal hterminal r hr

/-- The accepted exact calendar equality makes an empty successful interval
equivalent to coincident explicit endpoints. -/
theorem successfulPrefix_empty_iff_endpoints {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseQuota.LocalReleaseTrace rate assignment B record) :
    trace.rounds = [] ↔ trace.intervalStart = trace.intervalStop := by
  constructor
  · intro hempty
    have hcalendar := trace.exact_calendar
    rw [hempty] at hcalendar
    have hlength := congrArg List.length hcalendar
    simp only [List.length_map, List.length_nil, List.length_range'] at hlength
    have hstartLE := trace.interval_endpoints.1
    omega
  · intro hendpoints
    have hcalendar := trace.exact_calendar
    have hlen : trace.rounds.length = 0 := by
      have hlength := congrArg List.length hcalendar
      simp only [List.length_map, List.length_range'] at hlength
      omega
    cases hs : trace.rounds with
    | nil => rfl
    | cons r rs => simp [hs] at hlen

/-- A terminal observation is strictly after the prior confirmation and is
included before the exclusive successful-prefix endpoint. -/
theorem terminal_after_confirmation {rate : RateInput p}
    {assignment : ActiveRoundActions.Assignment p.m p.K} {B : ℕ}
    {record : ActiveRoundActions.Follower p.m →
      DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)}
    (trace : LocalReleaseStoppedTrace rate assignment B record)
    (terminal : LocalReleaseTerminalObservation rate assignment B record)
    (hterminal : trace.terminal = some terminal) :
    trace.successful.lastConfirmation < terminal.time.val ∧
      terminal.time.val < p.T ∧
      ∀ i, terminal.time.val + 1 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val
        (ActiveFollowerLifecycle.acceptedStartCoordinate (record i)) := by
  have hstart := trace.successful.confirmation_before_start
  have hbounds := trace.successful.interval_endpoints
  have hend := trace.terminalEndpoint terminal hterminal
  have hhor := trace.terminalBeforeHorizon terminal hterminal
  constructor
  · rw [hend]
    exact lt_of_lt_of_le hstart hbounds.1
  constructor
  · omega
  · exact terminal.beforeCutoff

end Bandits.Support.LocalReleaseStoppedQuota

end
