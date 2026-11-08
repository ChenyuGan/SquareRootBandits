/-
Copyright (c) 2026 Bandits Lean preparation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.FollowerCutoffScan
public import Bandits.Support.CompletePublicTable

/-!
# Literal coordinator phase clock operations

This module implements the coordinator's local `StartRound` and `FinishRound`
clock branches from `sources/zip4/manuscript/06_interruptions.tex:9-14,37-70`
and `sources/zip4/manuscript/06_interruptions.tex:235-296`. The checked local
domain convention follows `sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.

The clock stores the source assignment start `sigma`, cutoff `u`, and grid
boundary `g`. `sigma = none` means source `sigma = 0`; `u = none` means source
`u = T + 1`. A finite coordinate `r : Fin p.T` denotes source calendar round
`r.val + 1`, through `FollowerCutoffScan.calendarRound`. The stored `g` is
checked against `FollowerCutoffScan.gridBoundary` at the stored `sigma`.
Initial `sigma = 0` does not constrain the launch calendar round: the
coordinator first calls `StartRound` on activation, as in
`sources/zip4/manuscript/07_public_setup.tex:27-32,98-114`. Collection may
continue after the old grid boundary; only learning freezes there
(`sources/zip4/manuscript/06_interruptions.tex:80-100`).

The only proposal memory is an optional timestamp and the bit actually read
from a declared complete row. `StartRound` has no current-row input and can
read this saved bit only when it is correctly stamped for the preceding
calendar round. `FinishRound` does not inspect its row during collection.
The pending follower set is supplied and returned as its actual finite set;
this module owns neither the collection ledger nor assignment payloads.

The output ledger commands leave accumulator and buffer storage to the ledger
owner. These operations do not establish that an input snapshot is reachable,
that a command was applied, or that a later assignment constructor implements
its sampler instruction.
-/

@[expose] public section

namespace Bandits.Support.CoordinatorPhaseClock

open Bandits.Support.ConstructorDimensions
open Bandits.Support.FollowerCutoffScan
open Bandits.Support.CompletePublicTable

/-- The source clock registers and the last proposal bit actually read. -/
structure ClockRegisters (p : ConstructorDimensions.Parameters) where
  sigma : Option (Fin p.T)
  u : Option (Fin p.T)
  g : ℕ
  lastProposal : Option (Fin p.T × Bool)
  deriving DecidableEq

/-- The initial source clock has `sigma = 0`, `u = T + 1`, and no read bit. -/
def initialClock (p : ConstructorDimensions.Parameters) : ClockRegisters p :=
  ⟨none, none, p.T + 1, none⟩

/-- The source boundary determined by the stored assignment start. -/
noncomputable def boundaryFromSigma (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (sigma : Option (Fin p.T)) : ℕ :=
  match sigma with
  | none => p.T + 1
  | some sigma => FollowerCutoffScan.gridBoundary p eta sigma

/-- A source proposal hazard is in the prescribed Bernoulli domain. -/
def proposalParameterValid (p : ConstructorDimensions.Parameters) (eta : ℝ) : Prop :=
  0 < eta ∧ 0 < FollowerCutoffScan.proposalHazard p eta ∧
    FollowerCutoffScan.proposalHazard p eta ≤ 1

/-- The stored registers agree with the source meanings and time bounds.
For an active assignment, `u` is either the `T + 1` sentinel or a later
calendar coordinate no later than the boundary. -/
def clockRegistersValid (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (clock : ClockRegisters p) : Prop :=
  clock.g = boundaryFromSigma p eta clock.sigma ∧
    match clock.sigma with
    | none => clock.u = none ∧ clock.lastProposal = none
    | some sigma =>
        sigma.val + 1 < clock.g ∧ clock.g ≤ p.T + 1 ∧
          match clock.u with
          | none => True
          | some u => sigma.val < u.val ∧ u.val + 1 ≤ clock.g

/-- The checked source grid bounds for a clock register. -/
def clockGridDomain (p : ConstructorDimensions.Parameters)
    (clock : ClockRegisters p) : Prop :=
  match clock.sigma with
  | none => clock.g = p.T + 1
  | some sigma => sigma.val + 1 < clock.g ∧ clock.g ≤ p.T + 1

/-- A locally valid source clock has a boundary in its prescribed range. -/
theorem clockRegistersValid_gridDomain (p : ConstructorDimensions.Parameters)
    (eta : ℝ) (clock : ClockRegisters p)
    (h : clockRegistersValid p eta clock) : clockGridDomain p clock := by
  cases hsigma : clock.sigma with
  | none =>
      have hg := h.1
      simpa [clockGridDomain, boundaryFromSigma, hsigma] using hg
  | some sigma =>
      have hrest := h.2
      simp only [hsigma] at hrest
      simp only [clockGridDomain, hsigma]
      exact ⟨hrest.1, hrest.2.1⟩

/-- The local time supplied to `StartRound` agrees with the source clock.
An initial clock permits any active calendar coordinate. Before cutoff the
old boundary has not been passed; during collection only `u ≤ t` is required,
including after the old boundary. The `Fin T` input supplies the horizon. -/
def startRoundTimeValid (p : ConstructorDimensions.Parameters)
    (t : Fin p.T) (clock : ClockRegisters p) : Prop :=
  match clock.sigma with
  | none => True
  | some sigma =>
      sigma.val < t.val ∧
        match clock.u with
        | none => FollowerCutoffScan.calendarRound t ≤ clock.g
        | some u => u.val ≤ t.val

/-- The local time supplied to `FinishRound` is at or after the assignment
start and any recorded cutoff. Only an assignment with sentinel cutoff is
checked against its old boundary; collection continues throughout `Fin T`. -/
def finishRoundTimeValid {p : ConstructorDimensions.Parameters} (t : Fin p.T)
    (clock : ClockRegisters p) : Prop :=
  match clock.sigma with
  | none => False
  | some sigma =>
      sigma.val ≤ t.val ∧
        match clock.u with
        | none => FollowerCutoffScan.calendarRound t ≤ clock.g
        | some u => u.val ≤ t.val

/-- Whether the recorded cutoff is active by the current local coordinate. -/
def cutoffAtOrBefore {p : ConstructorDimensions.Parameters}
    (u : Option (Fin p.T)) (t : Fin p.T) : Prop :=
  match u with
  | none => False
  | some u => u.val ≤ t.val

/-- A finite table coordinate is a source round in `[1,T]`. -/
theorem calendarRound_bounds {p : ConstructorDimensions.Parameters}
    (t : Fin p.T) :
    1 ≤ FollowerCutoffScan.calendarRound t ∧
      FollowerCutoffScan.calendarRound t ≤ p.T := by
  simp only [FollowerCutoffScan.calendarRound]
  omega

/-- A locally valid start stays inside the calendar horizon. The old-grid
upper bound applies only when the cutoff is still the sentinel. -/
theorem startRound_source_time_bounds
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (t : Fin p.T)
    (clock : ClockRegisters p)
    (hclock : clockRegistersValid p eta clock)
    (htime : startRoundTimeValid p t clock) :
    1 ≤ FollowerCutoffScan.calendarRound t ∧
      FollowerCutoffScan.calendarRound t ≤ p.T ∧
      (clock.u = none → FollowerCutoffScan.calendarRound t ≤ clock.g) := by
  rcases calendarRound_bounds t with ⟨hlo, hhi⟩
  refine ⟨hlo, hhi, ?_⟩
  intro hu
  cases hsigma : clock.sigma with
  | none =>
      have hdomain := clockRegistersValid_gridDomain p eta clock hclock
      have hg : clock.g = p.T + 1 := by
        simpa [clockGridDomain, hsigma] using hdomain
      omega
  | some sigma =>
      have htime' := htime
      simp only [startRoundTimeValid, hsigma, hu] at htime'
      exact htime'.2

/-- The source start test, using the actual pending follower set. -/
def sourceStartTest {p : ConstructorDimensions.Parameters}
    (sigma u : Option (Fin p.T)) (t : Fin p.T)
    (pending : Finset (Fin (p.m - 1))) : Prop :=
  sigma = none ∨ (cutoffAtOrBefore u t ∧ pending = ∅)

/-- The actual follower carrier is nonempty because `m ≥ 2`. -/
theorem allFollowers_card (p : ConstructorDimensions.Parameters) :
    (Finset.univ : Finset (Fin (p.m - 1))).card = p.m - 1 := by
  simp only [Finset.card_univ, Fintype.card_fin]

/-- The actual follower carrier is nonempty because its cardinality is `m - 1`. -/
theorem allFollowers_nonempty (p : ConstructorDimensions.Parameters) :
    (Finset.univ : Finset (Fin (p.m - 1))).Nonempty := by
  have hm := p.two_le_m
  have hcard : 0 < (Finset.univ : Finset (Fin (p.m - 1))).card := by
    rw [allFollowers_card]
    omega
  exact Finset.card_pos.mp hcard

/-- The source full-follower reset cannot be the empty pending set. -/
theorem allFollowers_ne_empty (p : ConstructorDimensions.Parameters) :
    (Finset.univ : Finset (Fin (p.m - 1))) ≠ ∅ := by
  intro h
  have hm := p.two_le_m
  have hcard := allFollowers_card p
  rw [h] at hcard
  simp only [Finset.card_empty] at hcard
  omega

/-- A cutoff at the current round cannot satisfy the source assignment-start
test when an assignment is already live. -/
theorem sourceStartTest_false_after_cutoff (p : ConstructorDimensions.Parameters)
    (sigma t : Fin p.T) :
    ¬ sourceStartTest (some sigma) (some t) t
      (Finset.univ : Finset (Fin (p.m - 1))) := by
  intro h
  rcases h with h | ⟨_, hpending⟩
  · cases h
  · exact allFollowers_ne_empty p hpending

/-- After a recorded cutoff, assignment readiness requires both that its time
has been reached and that the actual pending set is empty. -/
theorem sourceStartTest_collection_iff {p : ConstructorDimensions.Parameters}
    (sigma u t : Fin p.T) (pending : Finset (Fin (p.m - 1))) :
    sourceStartTest (some sigma) (some u) t pending ↔
      u.val ≤ t.val ∧ pending = ∅ := by
  simp [sourceStartTest, cutoffAtOrBefore]

/-- Without a cutoff, a nonzero assignment cannot pass the collection
completion branch, even if the actual pending set is empty. -/
theorem sourceStartTest_false_without_cutoff {p : ConstructorDimensions.Parameters}
    (sigma t : Fin p.T) (pending : Finset (Fin (p.m - 1))) :
    ¬ sourceStartTest (some sigma) none t pending := by
  simp [sourceStartTest, cutoffAtOrBefore]

/-- The assignment construction law requested by the source clock. -/
inductive AssignmentStartKind where
  | first
  | renewal
  | corrected
  deriving DecidableEq

/-- Classify an actual requested start using the old `sigma` and `g`. -/
def classifyAssignmentStart {p : ConstructorDimensions.Parameters}
    (sigma : Option (Fin p.T)) (t : Fin p.T)
    (oldG : ℕ) : AssignmentStartKind :=
  match sigma with
  | none => .first
  | some _ =>
      if oldG ≤ FollowerCutoffScan.calendarRound t then .renewal else .corrected

/-- An instruction to the separately owned assignment constructor. -/
structure AssignmentStartInstruction (p : ConstructorDimensions.Parameters) where
  time : Fin p.T
  kind : AssignmentStartKind
  deriving DecidableEq

/-- A command whose accumulator and raw-buffer effects are applied by the
separately owned collection ledger. `initializeAt t` means set `u := t`, set
the pending set to all followers, set the ledger accumulator to zero, and
initialize collection raw buffers, preserving known clock/queue entries. -/
inductive CollectionLedgerCommand (p : ConstructorDimensions.Parameters) where
  | initializeAt (time : Fin p.T)
  | accumulateLocalServiceAt (time : Fin p.T)
  deriving DecidableEq

/-- The result of one checked `StartRound` clock computation. -/
structure StartRoundResult (p : ConstructorDimensions.Parameters) where
  clock : ClockRegisters p
  gridDomain : clockGridDomain p clock
  pending : Finset (Fin (p.m - 1))
  ledgerCommand : Option (CollectionLedgerCommand p)
  assignmentStart : Option (AssignmentStartInstruction p)
  deriving DecidableEq

/-- The result of one checked `FinishRound` clock computation. -/
structure FinishRoundResult (p : ConstructorDimensions.Parameters) where
  clock : ClockRegisters p
  pending : Finset (Fin (p.m - 1))
  ledgerCommand : Option (CollectionLedgerCommand p)
  deriving DecidableEq

/-- Checked failures for malformed source clock, time, proposal, or grid data. -/
inductive ClockFailure where
  | invalidProposalParameter
  | invalidClockRegisters
  | incompatibleStartTime
  | missingPriorProposal
  | stalePriorProposal
  | invalidNewGridBoundary
  | noLiveAssignment
  | incompatibleFinishTime
  deriving DecidableEq

/-- The result of checking this round for a source interruption. A cutoff
constructor records the old live assignment start rather than accepting a
cutoff decision from a caller. -/
inductive CutoffDecision {p : ConstructorDimensions.Parameters}
    (clock : ClockRegisters p) where
  | noCutoff
  | cutoff (sigma : Fin p.T) (sigma_eq : clock.sigma = some sigma)

/-- The clipped source boundary computed by the accepted cutoff API is after
the current source round and within the source horizon. -/
def newGridBoundaryValid (p : ConstructorDimensions.Parameters)
    (t : Fin p.T) (g : ℕ) : Prop :=
  FollowerCutoffScan.calendarRound t < g ∧ g ≤ p.T + 1

/-- Read only the saved bit for the immediately preceding source round. -/
def savedPriorProposal {p : ConstructorDimensions.Parameters}
    (clock : ClockRegisters p) (t : Fin p.T) :
    Except ClockFailure Bool :=
  match clock.lastProposal with
  | none => .error .missingPriorProposal
  | some (stamp, bit) =>
      if stamp.val + 1 = t.val then .ok bit else .error .stalePriorProposal

/-- A required but absent saved proposal bit is a checked failure. -/
theorem savedPriorProposal_missing {p : ConstructorDimensions.Parameters}
    (clock : ClockRegisters p) (t : Fin p.T) (h : clock.lastProposal = none) :
    savedPriorProposal clock t = .error .missingPriorProposal := by
  simp [savedPriorProposal, h]

/-- A correctly stamped saved proposal bit is the only bit returned. -/
theorem savedPriorProposal_correct {p : ConstructorDimensions.Parameters}
    (clock : ClockRegisters p) (t stamp : Fin p.T) (bit : Bool)
    (h : clock.lastProposal = some (stamp, bit))
    (hstamp : stamp.val + 1 = t.val) :
    savedPriorProposal clock t = .ok bit := by
  simp [savedPriorProposal, h, hstamp]

/-- A stale saved proposal timestamp is a checked failure. -/
theorem savedPriorProposal_stale {p : ConstructorDimensions.Parameters}
    (clock : ClockRegisters p) (t stamp : Fin p.T) (bit : Bool)
    (h : clock.lastProposal = some (stamp, bit))
    (hstamp : stamp.val + 1 ≠ t.val) :
    savedPriorProposal clock t = .error .stalePriorProposal := by
  simp [savedPriorProposal, h, hstamp]

/-- Apply the source interruption test for a known live assignment. The grid
branch short-circuits without reading a proposal; otherwise only the saved,
correctly stamped preceding bit is inspected. Collection rounds return
`noCutoff` without inspecting proposal memory. -/
noncomputable def detectCutoff {p : ConstructorDimensions.Parameters}
    (clock : ClockRegisters p) (t : Fin p.T) :
    Except ClockFailure (CutoffDecision clock) := by
  classical
  exact
    match hsigma : clock.sigma, hu : clock.u with
    | some sigma, none =>
        if FollowerCutoffScan.calendarRound t = clock.g then
          .ok (.cutoff sigma hsigma)
        else do
          let bit ← savedPriorProposal clock t
          if bit then .ok (.cutoff sigma hsigma) else .ok .noCutoff
    | _, _ => .ok .noCutoff

/-- In collection, cutoff detection returns without inspecting the saved
proposal token. -/
theorem detectCutoff_collection_noRead {p : ConstructorDimensions.Parameters}
    (clock : ClockRegisters p) (t u : Fin p.T) (hu : clock.u = some u) :
    detectCutoff clock t = .ok .noCutoff := by
  classical
  cases hsigma : clock.sigma <;> simp [detectCutoff, hsigma, hu]

/-- Changing only the saved token cannot change collection cutoff detection. -/
theorem detectCutoff_collection_savedProposal_irrel
    {p : ConstructorDimensions.Parameters} (clock : ClockRegisters p)
    (t u : Fin p.T) (token₁ token₂ : Option (Fin p.T × Bool))
    (hu : clock.u = some u) :
    detectCutoff { clock with lastProposal := token₁ } t = .ok .noCutoff ∧
      detectCutoff { clock with lastProposal := token₂ } t = .ok .noCutoff := by
  have hu₁ : ({ clock with lastProposal := token₁ } : ClockRegisters p).u = some u := by
    simpa using hu
  have hu₂ : ({ clock with lastProposal := token₂ } : ClockRegisters p).u = some u := by
    simpa using hu
  exact ⟨detectCutoff_collection_noRead _ t u hu₁,
    detectCutoff_collection_noRead _ t u hu₂⟩

/-- The source `StartRound`: apply a known interruption first, then test the
actual updated pending set for assignment readiness. No current or future
proposal row is an input. On an interruption the returned command initializes
collection while preserving the old `sigma` and `g`; a requested assignment
sets `sigma := t`, `u := T + 1`, `g := g(t)`, and all followers pending. -/
noncomputable def startRound (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (t : Fin p.T) (clock : ClockRegisters p)
    (pending : Finset (Fin (p.m - 1))) :
    Except ClockFailure (StartRoundResult p) := by
  classical
  exact
    if proposalParameterValid p eta then
      if hc : clockRegistersValid p eta clock then
        if ht : startRoundTimeValid p t clock then
          match detectCutoff clock t with
          | .error failure => .error failure
          | .ok cutoff =>
              match cutoff with
              | .cutoff sigma hsigma =>
                  let cutoffClock : ClockRegisters p := { clock with u := some t }
                  have hnoStart :
                      ¬ sourceStartTest cutoffClock.sigma cutoffClock.u t Finset.univ := by
                    simpa [cutoffClock, hsigma] using
                      sourceStartTest_false_after_cutoff p sigma t
                  if hstart : sourceStartTest cutoffClock.sigma cutoffClock.u t
                      Finset.univ then
                    False.elim (hnoStart hstart)
                  else
                    pure
                      { clock := cutoffClock
                        gridDomain := by
                          simpa [clockGridDomain, cutoffClock] using
                            clockRegistersValid_gridDomain p eta clock hc
                        pending := Finset.univ
                        ledgerCommand := some (.initializeAt t)
                        assignmentStart := none }
              | .noCutoff =>
                  if hstart : sourceStartTest clock.sigma clock.u t pending then
                    let kind := classifyAssignmentStart clock.sigma t clock.g
                    let nextG := FollowerCutoffScan.gridBoundary p eta t
                    if hgrid : newGridBoundaryValid p t nextG then
                      pure
                        { clock :=
                            { sigma := some t
                              u := none
                              g := nextG
                              lastProposal := clock.lastProposal }
                          gridDomain := by
                            simpa [clockGridDomain, newGridBoundaryValid,
                              FollowerCutoffScan.calendarRound] using hgrid
                          pending := Finset.univ
                          ledgerCommand := none
                          assignmentStart := some ⟨t, kind⟩ }
                    else .error .invalidNewGridBoundary
                  else
                    pure
                      { clock := clock
                        gridDomain :=
                          clockRegistersValid_gridDomain p eta clock hc
                        pending := pending
                        ledgerCommand := none
                        assignmentStart := none }
        else .error .incompatibleStartTime
      else .error .invalidClockRegisters
    else .error .invalidProposalParameter

/-- A checked cutoff outcome gives the exact collection-start frame. The
operation preserves the old start and grid registers, stamps `u` with the
current time, resets the actual pending set to all followers, emits the
ledger initialization command, and returns no assignment instruction. -/
theorem startRound_cutoff_effect
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (t sigma : Fin p.T)
    (clock : ClockRegisters p) (pending : Finset (Fin (p.m - 1)))
    (hparam : proposalParameterValid p eta)
    (hclock : clockRegistersValid p eta clock)
    (htime : startRoundTimeValid p t clock)
    (hsigma : clock.sigma = some sigma)
    (hcutoff : detectCutoff clock t = .ok (.cutoff sigma hsigma)) :
    ∃ result,
      startRound p eta t clock pending = .ok result ∧
        result.clock = { clock with u := some t } ∧
        result.pending = Finset.univ ∧
        result.ledgerCommand = some (.initializeAt t) ∧
        result.assignmentStart = none := by
  classical
  let cutoffClock : ClockRegisters p := { clock with u := some t }
  have hdomain : clockGridDomain p clock :=
    clockRegistersValid_gridDomain p eta clock hclock
  have hcutDomain : clockGridDomain p cutoffClock := by
    simpa [cutoffClock, clockGridDomain] using hdomain
  let result : StartRoundResult p :=
    { clock := cutoffClock
      gridDomain := hcutDomain
      pending := Finset.univ
      ledgerCommand := some (.initializeAt t)
      assignmentStart := none }
  refine ⟨result, ?_⟩
  constructor
  · simp [startRound, hparam, hclock, htime, hsigma, hcutoff, cutoffClock,
      result, sourceStartTest_false_after_cutoff]; rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- Every successful assignment-start instruction is the branch selected by
the source clock. Its clock update, actual pending-set reset, and frame are
the literal source updates. -/
theorem startRound_assignment_effect
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (t : Fin p.T)
    (clock : ClockRegisters p) (pending : Finset (Fin (p.m - 1)))
    (result : StartRoundResult p) (instruction : AssignmentStartInstruction p)
    (hparam : proposalParameterValid p eta)
    (hclock : clockRegistersValid p eta clock)
    (htime : startRoundTimeValid p t clock)
    (hresult : startRound p eta t clock pending = .ok result)
    (hinstruction : result.assignmentStart = some instruction) :
    instruction.time = t ∧
      instruction.kind = classifyAssignmentStart clock.sigma t clock.g ∧
      result.clock.sigma = some t ∧ result.clock.u = none ∧
      result.clock.g = FollowerCutoffScan.gridBoundary p eta t ∧
      result.clock.lastProposal = clock.lastProposal ∧
      result.pending = Finset.univ ∧ result.ledgerCommand = none := by
  classical
  cases hdecision : detectCutoff clock t with
  | error failure =>
      simp [startRound, hparam, hclock, htime, hdecision] at hresult
  | ok decision =>
      cases decision with
      | cutoff sigma hsigma =>
          simp [startRound, hparam, hclock, htime, hdecision, hsigma,
            sourceStartTest_false_after_cutoff] at hresult
          cases hresult
          simp at hinstruction
      | noCutoff =>
          by_cases hstart : sourceStartTest clock.sigma clock.u t pending
          · by_cases hgrid :
                newGridBoundaryValid p t (FollowerCutoffScan.gridBoundary p eta t)
            · simp [startRound, hparam, hclock, htime, hdecision, hstart, hgrid]
                at hresult
              cases hresult
              have hinstr := Option.some.inj hinstruction
              cases hinstr
              simp [classifyAssignmentStart]
            · simp [startRound, hparam, hclock, htime, hdecision, hstart, hgrid]
                at hresult
          · simp [startRound, hparam, hclock, htime, hdecision, hstart] at hresult
            cases hresult
            simp at hinstruction

/-- The source `FinishRound`: collection emits only the ledger service command;
otherwise read the proposal bit from the supplied declared complete row and
save its actual round coordinate and value. -/
noncomputable def finishRound (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (t : Fin p.T) (clock : ClockRegisters p)
    (pending : Finset (Fin (p.m - 1)))
    (row : CompletePublicTable.CompleteRow p) :
    Except ClockFailure (FinishRoundResult p) := by
  classical
  exact do
    if hc : clockRegistersValid p eta clock then pure ()
    else throw .invalidClockRegisters
    if ht : finishRoundTimeValid t clock then pure ()
    else throw .incompatibleFinishTime
    match clock.sigma, clock.u with
    | none, _ => throw .noLiveAssignment
    | some _, some _ =>
        pure
          { clock := clock
            pending := pending
            ledgerCommand := some (.accumulateLocalServiceAt t) }
    | some _, none =>
        if hη : proposalParameterValid p eta then
          let bit := FollowerCutoffScan.completeRowProposalBit p eta row t
          pure
            { clock := { clock with lastProposal := some (t, bit) }
              pending := pending
              ledgerCommand := none }
        else throw .invalidProposalParameter

/-- The initial source registers satisfy the literal initial clock checks. -/
theorem initialClock_registersValid (p : ConstructorDimensions.Parameters)
    (eta : ℝ) : clockRegistersValid p eta (initialClock p) := by
  simp [clockRegistersValid, initialClock, boundaryFromSigma]

/-- Activation may occur at any in-horizon calendar coordinate; initial
registers impose no round-one condition (`07_public_setup.tex:27,106-112`). -/
theorem initialClock_startRoundTimeValid (p : ConstructorDimensions.Parameters)
    (t : Fin p.T) : startRoundTimeValid p t (initialClock p) := by
  trivial

/-- A valid collection clock needs only to have reached its cutoff. In
particular neither time check bounds the current round by the old `g`.
The assignment-start ordering follows from the stored `sigma < u`. -/
theorem collection_timeValid (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (clock : ClockRegisters p) (sigma u t : Fin p.T)
    (hclock : clockRegistersValid p eta clock)
    (hsigma : clock.sigma = some sigma) (hu : clock.u = some u)
    (hut : u.val ≤ t.val) :
    startRoundTimeValid p t clock ∧ finishRoundTimeValid t clock := by
  have hrest := hclock.2
  simp only [hsigma, hu] at hrest
  have hst : sigma.val < t.val := lt_of_lt_of_le hrest.2.2.1 hut
  simp only [startRoundTimeValid, finishRoundTimeValid, hsigma, hu]
  exact ⟨⟨hst, hut⟩, ⟨hst.le, hut⟩⟩

/-- A finite cutoff in a valid clock has been reached on every in-horizon
round at or beyond the old grid boundary. This is not a bound on collection
completion (`06_interruptions.tex:98,277-283`). -/
theorem collection_cutoff_le_of_grid_le
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (clock : ClockRegisters p)
    (sigma u t : Fin p.T) (hclock : clockRegistersValid p eta clock)
    (hsigma : clock.sigma = some sigma) (hu : clock.u = some u)
    (hgt : clock.g ≤ FollowerCutoffScan.calendarRound t) : u.val ≤ t.val := by
  have hrest := hclock.2
  simp only [hsigma, hu] at hrest
  have hug := hrest.2.2.2
  simp only [FollowerCutoffScan.calendarRound] at hgt
  omega

/-- A first assignment is produced at the supplied active calendar round
under exactly the checked proposal and new-grid domains. No launch-time
reindexing, prior proposal token, or current row is needed. -/
theorem startRound_initial (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (t : Fin p.T) (pending : Finset (Fin (p.m - 1)))
    (hparam : proposalParameterValid p eta)
    (hgrid : newGridBoundaryValid p t (FollowerCutoffScan.gridBoundary p eta t)) :
    startRound p eta t (initialClock p) pending = .ok
      { clock :=
          { sigma := some t, u := none
            g := FollowerCutoffScan.gridBoundary p eta t, lastProposal := none }
        gridDomain := hgrid
        pending := Finset.univ
        ledgerCommand := none
        assignmentStart := some ⟨t, .first⟩ } := by
  classical
  have hclock := initialClock_registersValid p eta
  have htime := initialClock_startRoundTimeValid p t
  simp only [startRound, hparam, hclock, htime, ↓reduceIte, ↓reduceDIte]
  simp [detectCutoff, initialClock, sourceStartTest, classifyAssignmentStart, hgrid]
  rfl

/-- An initial launch with an invalid computed boundary is still a checked
source-domain failure, at any calendar round. -/
theorem startRound_initial_invalidNewGridBoundary
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (t : Fin p.T)
    (pending : Finset (Fin (p.m - 1))) (hparam : proposalParameterValid p eta)
    (hgrid : ¬ newGridBoundaryValid p t (FollowerCutoffScan.gridBoundary p eta t)) :
    startRound p eta t (initialClock p) pending = .error .invalidNewGridBoundary := by
  classical
  have hclock := initialClock_registersValid p eta
  have htime := initialClock_startRoundTimeValid p t
  simp only [startRound, hparam, hclock, htime, ↓reduceIte, ↓reduceDIte]
  simp [detectCutoff, initialClock, sourceStartTest, hgrid]

/-- Nonempty actual pending replies keep collection running at every
remaining calendar round. Proposal memory is unrestricted and is not read. -/
theorem startRound_collection_pending
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (t sigma u : Fin p.T)
    (clock : ClockRegisters p) (pending : Finset (Fin (p.m - 1)))
    (hparam : proposalParameterValid p eta)
    (hclock : clockRegistersValid p eta clock)
    (hsigma : clock.sigma = some sigma) (hu : clock.u = some u)
    (hut : u.val ≤ t.val) (hpending : pending ≠ ∅) :
    startRound p eta t clock pending = .ok
      { clock := clock
        gridDomain := clockRegistersValid_gridDomain p eta clock hclock
        pending := pending, ledgerCommand := none, assignmentStart := none } := by
  classical
  have htime := (collection_timeValid p eta clock sigma u t hclock hsigma hu hut).1
  have hdecision := detectCutoff_collection_noRead clock t u hu
  have hstart : ¬ sourceStartTest clock.sigma clock.u t pending := by
    simp only [sourceStartTest, hsigma, hu, cutoffAtOrBefore, Option.some_ne_none,
      false_or]
    exact fun h => hpending h.2
  simp [startRound, hparam, hclock, htime, hdecision, hstart]
  rfl

/-- An empty actual pending set produces an assignment, before or after the
old grid. The instruction retains the source's literal branch classifier. -/
theorem startRound_collection_empty
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (t sigma u : Fin p.T)
    (clock : ClockRegisters p) (hparam : proposalParameterValid p eta)
    (hclock : clockRegistersValid p eta clock)
    (hsigma : clock.sigma = some sigma) (hu : clock.u = some u)
    (hut : u.val ≤ t.val)
    (hgrid : newGridBoundaryValid p t (FollowerCutoffScan.gridBoundary p eta t)) :
    startRound p eta t clock ∅ = .ok
      { clock :=
          { sigma := some t, u := none
            g := FollowerCutoffScan.gridBoundary p eta t
            lastProposal := clock.lastProposal }
        gridDomain := hgrid
        pending := Finset.univ, ledgerCommand := none
        assignmentStart := some ⟨t, classifyAssignmentStart clock.sigma t clock.g⟩ } := by
  classical
  have htime := (collection_timeValid p eta clock sigma u t hclock hsigma hu hut).1
  have hdecision := detectCutoff_collection_noRead clock t u hu
  have hstart : sourceStartTest clock.sigma clock.u t ∅ := by
    exact Or.inr ⟨by simpa only [cutoffAtOrBefore, hu] using hut, rfl⟩
  simp [startRound, hparam, hclock, htime, hdecision, hstart, hgrid]
  rfl

/-- At or after old `g`, completed collection actually reaches renewal and
resets the source registers and actual pending set. No successful-result or
producer-conclusion premise is assumed (`06_interruptions.tex:46-61`). -/
theorem startRound_collection_renewal
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (t sigma u : Fin p.T)
    (clock : ClockRegisters p) (hparam : proposalParameterValid p eta)
    (hclock : clockRegistersValid p eta clock)
    (hsigma : clock.sigma = some sigma) (hu : clock.u = some u)
    (hgt : clock.g ≤ FollowerCutoffScan.calendarRound t)
    (hgrid : newGridBoundaryValid p t (FollowerCutoffScan.gridBoundary p eta t)) :
    startRound p eta t clock ∅ = .ok
      { clock :=
          { sigma := some t, u := none
            g := FollowerCutoffScan.gridBoundary p eta t
            lastProposal := clock.lastProposal }
        gridDomain := hgrid
        pending := Finset.univ, ledgerCommand := none
        assignmentStart := some ⟨t, .renewal⟩ } := by
  have hut := collection_cutoff_le_of_grid_le p eta clock sigma u t hclock hsigma hu hgt
  have h := startRound_collection_empty p eta t sigma u clock hparam hclock hsigma hu hut hgrid
  simpa only [classifyAssignmentStart, hsigma, hgt, ↓reduceIte] using h

/-- The source start test is exactly `sigma = 0` or a completed collection
with the actual pending follower set empty. -/
theorem sourceStartTest_iff {p : ConstructorDimensions.Parameters}
    (sigma u : Option (Fin p.T)) (t : Fin p.T)
    (pending : Finset (Fin (p.m - 1))) :
    sourceStartTest sigma u t pending ↔
      sigma = none ∨ (cutoffAtOrBefore u t ∧ pending = ∅) := Iff.rfl

/-- `FinishRound` in collection is independent of every coordinate of the
declared complete row. It returns the actual pending set unchanged. -/
theorem finishRound_collection_row_irrel
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (t : Fin p.T)
    (clock : ClockRegisters p) (pending : Finset (Fin (p.m - 1)))
    (row₁ row₂ : CompletePublicTable.CompleteRow p)
    (hclock : clockRegistersValid p eta clock)
    (htime : finishRoundTimeValid t clock)
    (hu : ∃ u, clock.u = some u) :
    finishRound p eta t clock pending row₁ =
      finishRound p eta t clock pending row₂ := by
  rcases hu with ⟨u, hu⟩
  cases hsigma : clock.sigma with
  | none =>
      have hclock' := hclock
      simp only [clockRegistersValid, hsigma] at hclock'
      have hu' : clock.u = none := hclock'.2.1
      rw [hu] at hu'
      contradiction
  | some sigma =>
      simp [finishRound, hclock, htime, hsigma, hu]

/-- In collection, `FinishRound` preserves the clock and pending set and emits
the ledger command that accumulates the actual local service for this round. -/
theorem finishRound_collection_effect
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (t : Fin p.T)
    (clock : ClockRegisters p) (pending : Finset (Fin (p.m - 1)))
    (row : CompletePublicTable.CompleteRow p)
    (hclock : clockRegistersValid p eta clock)
    (htime : finishRoundTimeValid t clock)
    (hσ : clock.sigma ≠ none)
    (u : Fin p.T) (hu : clock.u = some u) :
    ∃ result,
      finishRound p eta t clock pending row = .ok result ∧
        result.clock = clock ∧ result.pending = pending ∧
        result.ledgerCommand = some (.accumulateLocalServiceAt t) := by
  cases hsigma : clock.sigma with
  | none =>
      simp [hsigma] at hσ
  | some sigma =>
      let result : FinishRoundResult p :=
        { clock := clock
          pending := pending
          ledgerCommand := some (.accumulateLocalServiceAt t) }
      refine ⟨result, ?_⟩
      constructor
      · simp [finishRound, hclock, htime, hsigma, hu, result]; rfl
      constructor
      · rfl
      constructor
      · rfl
      · rfl

/-- In a live assignment, a successful finish saves exactly the actual
complete-row proposal bit at the current time coordinate. -/
theorem finishRound_live_savedProposal
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (t : Fin p.T)
    (clock : ClockRegisters p) (pending : Finset (Fin (p.m - 1)))
    (row : CompletePublicTable.CompleteRow p)
    (hclock : clockRegistersValid p eta clock)
    (htime : finishRoundTimeValid t clock)
    (hσ : clock.sigma ≠ none)
    (hu : clock.u = none)
    (hparam : proposalParameterValid p eta) :
    ∃ result,
      finishRound p eta t clock pending row = .ok result ∧
        result.clock =
          ({ clock with
            lastProposal :=
              some (t, FollowerCutoffScan.completeRowProposalBit p eta row t) }) ∧
        result.pending = pending ∧ result.ledgerCommand = none := by
  let result : FinishRoundResult p :=
    { clock :=
        { clock with
          lastProposal :=
            some (t, FollowerCutoffScan.completeRowProposalBit p eta row t) }
      pending := pending
      ledgerCommand := none }
  cases hsigma : clock.sigma with
  | none =>
      simp [hsigma] at hσ
  | some sigma =>
      refine ⟨result, ?_⟩
      constructor
      · simp [finishRound, hclock, htime, hu, hparam, hsigma, result]; rfl
      constructor
      · simp [result, hsigma]
      constructor
      · rfl
      · rfl

/-- On every successful finish, the supplied pending set is returned intact. -/
theorem finishRound_pending_frame
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (t : Fin p.T)
    (clock : ClockRegisters p) (pending : Finset (Fin (p.m - 1)))
    (row : CompletePublicTable.CompleteRow p) (result : FinishRoundResult p)
    (h : finishRound p eta t clock pending row = .ok result) :
    result.pending = pending := by
  simp only [finishRound] at h
  repeat' split at h
  all_goals
    cases h
    all_goals simp_all

/-- In any successful start result, the grid register remains within the
source terminal bound. -/
theorem startRoundResult_grid_upper_bound
    (p : ConstructorDimensions.Parameters) (result : StartRoundResult p) :
    result.clock.g ≤ p.T + 1 := by
  have hdomain := result.gridDomain
  cases hsigma : result.clock.sigma with
  | none =>
      have hg : result.clock.g = p.T + 1 := by
        simpa [clockGridDomain, hsigma] using hdomain
      omega
  | some sigma =>
      have hdom := hdomain
      simp only [clockGridDomain, hsigma] at hdom
      exact hdom.2

/-- A start instruction preserves the old-clock classification: first at
`sigma = 0`, otherwise renewal at or beyond the old `g`, corrected before it. -/
theorem classifyAssignmentStart_eq_source
    {_p : ConstructorDimensions.Parameters}
    (sigma : Option (Fin _p.T)) (t : Fin _p.T) (oldG : ℕ) :
    classifyAssignmentStart sigma t oldG =
      match sigma with
      | none => .first
      | some _ =>
          if oldG ≤ FollowerCutoffScan.calendarRound t then .renewal else .corrected :=
  rfl

/-- A reached collection cutoff produces the exact finish command, with no
proposal-parameter or timestamp premise and with an arbitrary declared row. -/
theorem finishRound_collection
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (t sigma u : Fin p.T)
    (clock : ClockRegisters p) (pending : Finset (Fin (p.m - 1)))
    (row : CompletePublicTable.CompleteRow p)
    (hclock : clockRegistersValid p eta clock)
    (hsigma : clock.sigma = some sigma) (hu : clock.u = some u)
    (hut : u.val ≤ t.val) :
    finishRound p eta t clock pending row = .ok
      { clock := clock, pending := pending
        ledgerCommand := some (.accumulateLocalServiceAt t) } := by
  have htime := (collection_timeValid p eta clock sigma u t hclock hsigma hu hut).2
  simp [finishRound, hclock, htime, hsigma, hu]
  rfl

/-- Regression for collection after old `g`: even with proposal memory
absent, StartRound preserves a nonempty actual pending set and FinishRound
emits service accumulation for any row. No current-row coordinate is read.
This describes the phase-clock substate, not physical-history reachability. -/
theorem collection_after_grid_without_proposal
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (t sigma u : Fin p.T)
    (clock : ClockRegisters p) (pending : Finset (Fin (p.m - 1)))
    (row : CompletePublicTable.CompleteRow p)
    (hparam : proposalParameterValid p eta)
    (hclock : clockRegistersValid p eta clock)
    (hsigma : clock.sigma = some sigma) (hu : clock.u = some u)
    (hgt : clock.g < FollowerCutoffScan.calendarRound t) (hpending : pending ≠ ∅) :
    let c : ClockRegisters p := { clock with lastProposal := none }
    startRound p eta t c pending = .ok
        { clock := c
          gridDomain := clockRegistersValid_gridDomain p eta clock hclock
          pending := pending, ledgerCommand := none, assignmentStart := none } ∧
      finishRound p eta t c pending row = .ok
        { clock := c, pending := pending
          ledgerCommand := some (.accumulateLocalServiceAt t) } := by
  let c : ClockRegisters p := { clock with lastProposal := none }
  have hclock' : clockRegistersValid p eta c := by
    simpa only [clockRegistersValid, c, hsigma] using hclock
  have hut := collection_cutoff_le_of_grid_le p eta clock sigma u t hclock hsigma hu hgt.le
  exact ⟨startRound_collection_pending p eta t sigma u c pending hparam hclock'
      hsigma hu hut hpending,
    finishRound_collection p eta t sigma u c pending row hclock' hsigma hu hut⟩

/-- A grid cutoff needs no proposal token and cannot request another
assignment in the same call: the actual nonempty follower set is reset first. -/
theorem startRound_grid_cutoff
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (t sigma : Fin p.T)
    (clock : ClockRegisters p) (pending : Finset (Fin (p.m - 1)))
    (hparam : proposalParameterValid p eta)
    (hclock : clockRegistersValid p eta clock)
    (htime : startRoundTimeValid p t clock)
    (hsigma : clock.sigma = some sigma) (hu : clock.u = none)
    (hg : FollowerCutoffScan.calendarRound t = clock.g) :
    ∃ result,
      startRound p eta t clock pending = .ok result ∧
        result.clock = { clock with u := some t } ∧
        result.pending = Finset.univ ∧
        result.ledgerCommand = some (.initializeAt t) ∧
        result.assignmentStart = none := by
  have hcutoff : detectCutoff clock t = .ok (.cutoff sigma hsigma) := by
    rcases clock with ⟨s, v, g, token⟩
    change s = some sigma at hsigma
    change v = none at hu
    subst s
    subst v
    simp [detectCutoff, hg]
  exact startRound_cutoff_effect p eta t sigma clock pending hparam hclock htime
    hsigma hcutoff

/-- Away from a grid cutoff, a live pre-cutoff start still requires an
authentic prior-time token; missing memory remains a checked failure. -/
theorem startRound_live_missingPriorProposal
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (t sigma : Fin p.T)
    (clock : ClockRegisters p) (pending : Finset (Fin (p.m - 1)))
    (hparam : proposalParameterValid p eta)
    (hclock : clockRegistersValid p eta clock)
    (htime : startRoundTimeValid p t clock)
    (hsigma : clock.sigma = some sigma) (hu : clock.u = none)
    (hg : FollowerCutoffScan.calendarRound t ≠ clock.g)
    (htoken : clock.lastProposal = none) :
    startRound p eta t clock pending = .error .missingPriorProposal := by
  have hdecision : detectCutoff clock t = .error .missingPriorProposal := by
    rcases clock with ⟨s, v, g, token⟩
    change s = some sigma at hsigma
    change v = none at hu
    subst s
    subst v
    change token = none at htoken
    subst token
    simp [detectCutoff, hg, savedPriorProposal]
    rfl
  simp [startRound, hparam, hclock, htime, hdecision]

/-- A stale timestamp remains a failure precisely in the live branch that
needs the preceding proposal. Collection and grid-cutoff equations above
place no such condition on saved memory. -/
theorem startRound_live_stalePriorProposal
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (t sigma stamp : Fin p.T)
    (clock : ClockRegisters p) (pending : Finset (Fin (p.m - 1))) (bit : Bool)
    (hparam : proposalParameterValid p eta)
    (hclock : clockRegistersValid p eta clock)
    (htime : startRoundTimeValid p t clock)
    (hsigma : clock.sigma = some sigma) (hu : clock.u = none)
    (hg : FollowerCutoffScan.calendarRound t ≠ clock.g)
    (htoken : clock.lastProposal = some (stamp, bit))
    (hstamp : stamp.val + 1 ≠ t.val) :
    startRound p eta t clock pending = .error .stalePriorProposal := by
  have hdecision : detectCutoff clock t = .error .stalePriorProposal := by
    rcases clock with ⟨s, v, g, token⟩
    change s = some sigma at hsigma
    change v = none at hu
    subst s
    subst v
    change token = some (stamp, bit) at htoken
    subst token
    simp [detectCutoff, hg, savedPriorProposal, hstamp]
    rfl
  simp [startRound, hparam, hclock, htime, hdecision]

/-- Exact domain checks for review-0148's parameters: calendar launch 2,
and collection at 5 after cutoff/boundary 4 for assignment 2. These checks
instantiate the general successful branch equations; they assert no bootstrap
or physical-history realization. The missing token is deliberate. -/
theorem review0148_counterexample_domains :
    let p : ConstructorDimensions.Parameters := ⟨3, 2, 10, by decide, by decide, by decide⟩
    let eta : ℝ := 1 / 256
    let t₂ : Fin p.T := ⟨1, by decide⟩
    let t₅ : Fin p.T := ⟨4, by decide⟩
    let clock : ClockRegisters p := ⟨some t₂, some ⟨3, by decide⟩, 4, none⟩
    proposalParameterValid p eta ∧
      Bandits.Support.ReplayWeightStability.episodeHorizon eta = 4 ∧
      FollowerCutoffScan.proposalHazard p eta = 1 / 32 ∧
      FollowerCutoffScan.gridBoundary p eta t₂ = 4 ∧
      newGridBoundaryValid p t₂ (FollowerCutoffScan.gridBoundary p eta t₂) ∧
      clockRegistersValid p eta clock ∧
      startRoundTimeValid p t₅ clock ∧ finishRoundTimeValid t₅ clock ∧
      clock.g < FollowerCutoffScan.calendarRound t₅ ∧
      FollowerCutoffScan.gridBoundary p eta t₅ = 8 ∧
      newGridBoundaryValid p t₅ (FollowerCutoffScan.gridBoundary p eta t₅) := by
  norm_num [proposalParameterValid, FollowerCutoffScan.proposalHazard,
    Bandits.Support.ReplayWeightStability.episodeHorizon,
    FollowerCutoffScan.gridBoundary, FollowerCutoffScan.calendarRound,
    newGridBoundaryValid, clockRegistersValid, boundaryFromSigma,
    startRoundTimeValid, finishRoundTimeValid]

end Bandits.Support.CoordinatorPhaseClock

end
