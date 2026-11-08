/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CoordinatorPhaseClock
public import Bandits.Support.CoordinatorCollectionLedger
public import Bandits.Support.CoordinatorLiveChoiceRecorderStep
public import Bandits.Support.CoordinatorLiveServiceFinish
public import Bandits.Support.AssignmentStartPayload

/-!
# Coordinator start-round cutoff dispatch

This module connects one `StartRound` clock result to the separately checked
collection-ledger initializer.  It uses the old assignment payload and the
coordinator-owned complement scores, queues, and previous services; all other
collection storage remains outside this returned value.

Sources: `sources/zip4/manuscript/06_interruptions.tex:23-70,235-250` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.
-/

@[expose] public section

namespace Bandits.Support.CoordinatorStartRoundCutoffDispatch

open Bandits.Support.ConstructorDimensions

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters}
variable {eta : CoordinatorLiveChoiceRecorderStep.LearningRate}

/-- The exact ledger carrier indexed by the accepted payload's rate cap and
integer numerator. -/
abbrev NewLedger (r : CoordinatorLiveChoiceRecorderStep.Registers p eta) :=
  CoordinatorCollectionLedger.Ledger p eta.val eta.property
    r.payload.eta_le_source_cap
    r.payload.n r.payload.n_eq_eta_mul_D

/-- Convert the old payload assignment to the collection ledger's narrower
arm map.  This is a representation change only; it does not construct a new
assignment. -/
noncomputable def ledgerAssignment
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta) :
    CoordinatorCollectionLedger.Assignment p where
  arm := r.payload.assignment.assigned
  injective := r.payload.assignment.injective

/-- Cutoff registers on the actual complement of the old payload slow set.
Slow assignment arms are unknown, while every complement entry is assembled
from the live coordinator's three local register vectors. -/
def outsideRegisters (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) :
    Fin p.K → Option CoordinatorCollectionLedger.CutoffRegister := fun a =>
  if h : a ∈ CanonicalFastSampling.fastArmFinset r.payload.slowSet then
    let j : CanonicalFastSampling.FastArm r.payload.slowSet := ⟨a, h⟩
    some
      { score := r.complementScores j
        queue := q.queue j
        lastService := q.previousService j }
  else
    none

/-- Literal ready-phase ledger produced at an accepted cutoff, before any
later round operation is applied. -/
noncomputable def collectionStartLedger
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (time : Fin p.T) : NewLedger r :=
  { assignment := ledgerAssignment r
    sigma := r.payload.sigma.val + 1
    cutoff := time.val + 1
    freezeAt := r.gridBoundary
    baseScore := base
    pending := Finset.univ
    cutoffRegisters := outsideRegisters r q
    currentRegisters := fun a =>
      (outsideRegisters r q a).map fun reg => ⟨reg.queue, reg.lastService⟩
    increment := fun _ => 0
    gammaLoc := fun _ => 0
    rawBuffer := fun _ _ => none
    enabledHistory := fun _ => none
    cursor := time.val + 1
    phase := .ready }

/-- Source and numeric domains checked before exposing an initialized ledger.
The two ledger booleans are the accepted initializer's literal input and
result checks, applied to the exact payload-derived assignment and registers. -/
noncomputable def initializationDomainValid
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (time : Fin p.T) : Prop :=
  r.priorClock.sigma = some r.payload.sigma ∧
  r.gridBoundary = r.priorClock.g ∧
  r.payload.sigma.val < time.val ∧
  time.val + 1 ≤ r.gridBoundary ∧
  r.gridBoundary ≤ p.T + 1 ∧
  (∀ a, r.payload.queues a ≤ p.T * D p) ∧
  r.scoreDomainValid ∧
  q.queueDomainValid ∧
  q.previousServiceDomainValid ∧
  (∀ i, base i ≤ p.T * D p) ∧
  CoordinatorCollectionLedger.validInitialInputsCheck (ledgerAssignment r)
    (r.payload.sigma.val + 1) (time.val + 1) r.gridBoundary base
    (outsideRegisters r q) = true ∧
  CoordinatorCollectionLedger.validLedgerCheck
    (collectionStartLedger r q base time) = true

/-- Preserve invalid and rejected collection outcomes. A successful ledger is
exposed only when the additional payload, clock, grid, and numeric checks pass. -/
def checkedOptionIfValid {α : Type} (valid : Bool) :
    CoordinatorCollectionLedger.Checked α →
      CoordinatorCollectionLedger.Checked (Option α)
  | .success value => if valid then .success (some value) else .invalid
  | .rejected value => .rejected (some value)
  | .invalid => .invalid

/-- The actual clock result and the checked optional collection initialization.
`.success none` means no initialization command was issued; `.success (some l)`
is a new ledger; `.invalid` and `.rejected` retain the ledger check's outcomes. -/
structure Output
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) where
  startResult : CoordinatorPhaseClock.StartRoundResult p
  collectionInitialization :
    CoordinatorCollectionLedger.Checked (Option (NewLedger r))

/-- Run the clock once and dispatch its actual initialization command.  The
outer clock error is returned unchanged.  No existing collection state is
accepted or overwritten by this command consumer. -/
noncomputable def dispatch
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) :
    Except CoordinatorPhaseClock.ClockFailure (Output r q base) := by
  classical
  exact match CoordinatorPhaseClock.startRound p eta.val r.time r.priorClock
      r.clockPending with
  | .error failure => .error failure
  | .ok startResult =>
      let initialization :=
        match startResult.ledgerCommand with
        | some (.initializeAt time) =>
            checkedOptionIfValid
              (decide (initializationDomainValid r q base time))
              (CoordinatorCollectionLedger.startCollectionChecked
                p eta.val eta.property
                r.payload.eta_le_source_cap r.payload.n
                r.payload.n_eq_eta_mul_D (ledgerAssignment r)
                (r.payload.sigma.val + 1) (time.val + 1) r.gridBoundary
                base (outsideRegisters r q))
        | _ => .success none
      .ok ⟨startResult, initialization⟩

/-- An `initializeAt` result can only have the cutoff clock shape: the old
clock is preserved except for its newly stamped cutoff, every follower is
pending, and no assignment instruction is returned. -/
theorem startRound_initializeAt_shape
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (result : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p eta.val r.time r.priorClock
      r.clockPending =
      .ok result)
    (hcommand : result.ledgerCommand = some (.initializeAt r.time)) :
    result.clock = { r.priorClock with u := some r.time } ∧
      result.pending = Finset.univ ∧ result.assignmentStart = none := by
  classical
  by_cases hparam : CoordinatorPhaseClock.proposalParameterValid p eta.val
  · by_cases hclock :
        CoordinatorPhaseClock.clockRegistersValid p eta.val r.priorClock
    · by_cases htime :
          CoordinatorPhaseClock.startRoundTimeValid p r.time r.priorClock
      · cases hdetect : CoordinatorPhaseClock.detectCutoff r.priorClock r.time with
        | error failure =>
            simp [CoordinatorPhaseClock.startRound, hparam, hclock, htime,
              hdetect] at hstart
        | ok decision =>
            cases decision with
            | cutoff sigma hsigma =>
                obtain ⟨expected, hrun, hclockShape, hpending, hledger,
                  hassignment⟩ :=
                  CoordinatorPhaseClock.startRound_cutoff_effect p eta.val
                    r.time sigma r.priorClock r.clockPending hparam hclock htime
                    hsigma hdetect
                have hresult : expected = result := by
                  rw [hrun] at hstart
                  injection hstart with heq
                subst result
                exact ⟨hclockShape, hpending, hassignment⟩
            | noCutoff =>
                by_cases hsource : CoordinatorPhaseClock.sourceStartTest
                    r.priorClock.sigma r.priorClock.u r.time r.clockPending
                · by_cases hgrid : CoordinatorPhaseClock.newGridBoundaryValid p
                      r.time (FollowerCutoffScan.gridBoundary p eta.val r.time)
                  · simp only [CoordinatorPhaseClock.startRound, hparam, hclock,
                      htime, hdetect, hsource, hgrid] at hstart
                    change Except.ok _ = Except.ok result at hstart
                    cases hstart
                    simp at hcommand
                  · simp [CoordinatorPhaseClock.startRound, hparam, hclock,
                      htime, hdetect, hsource, hgrid] at hstart
                · simp only [CoordinatorPhaseClock.startRound, hparam, hclock,
                    htime, hdetect, hsource] at hstart
                  change Except.ok _ = Except.ok result at hstart
                  cases hstart
                  simp at hcommand
      · simp [CoordinatorPhaseClock.startRound, hparam, hclock, htime] at hstart
    · simp [CoordinatorPhaseClock.startRound, hparam, hclock] at hstart
  · simp [CoordinatorPhaseClock.startRound, hparam] at hstart

/-- The candidate's fields are the source assignment start, current cutoff,
old grid endpoint, original base scores, full pending set, complement
registers, zero accumulators, empty raw/history buffers, and ready phase. -/
theorem collectionStartLedger_fields
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (time : Fin p.T) :
    (collectionStartLedger r q base time).assignment.arm =
        r.payload.assignment.assigned ∧
      (collectionStartLedger r q base time).sigma = r.payload.sigma.val + 1 ∧
      (collectionStartLedger r q base time).cutoff = time.val + 1 ∧
      (collectionStartLedger r q base time).freezeAt = r.gridBoundary ∧
      (collectionStartLedger r q base time).baseScore = base ∧
      (collectionStartLedger r q base time).pending = Finset.univ ∧
      (collectionStartLedger r q base time).assignment = ledgerAssignment r ∧
      (collectionStartLedger r q base time).cutoffRegisters =
        outsideRegisters r q ∧
      (collectionStartLedger r q base time).currentRegisters =
        (fun a => (outsideRegisters r q a).map
          (fun reg => ⟨reg.queue, reg.lastService⟩)) ∧
      (collectionStartLedger r q base time).increment =
        (fun _ : Fin p.K => 0) ∧
      (collectionStartLedger r q base time).gammaLoc =
        (fun _ : Fin p.K => 0) ∧
      (collectionStartLedger r q base time).rawBuffer =
        (fun _ _ => none) ∧
      (collectionStartLedger r q base time).enabledHistory =
        (fun _ => none) ∧
      (collectionStartLedger r q base time).cursor = time.val + 1 ∧
      (collectionStartLedger r q base time).phase = .ready := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩

/-- Literal input and candidate-state checks make the accepted checked
initializer return the exact ledger candidate; this does not assume an
initialization result. -/
theorem startCollectionChecked_success_of_domains
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (time : Fin p.T)
    (h : initializationDomainValid r q base time) :
    CoordinatorCollectionLedger.startCollectionChecked p eta.val eta.property
      r.payload.eta_le_source_cap r.payload.n r.payload.n_eq_eta_mul_D
      (ledgerAssignment r) (r.payload.sigma.val + 1) (time.val + 1)
      r.gridBoundary base (outsideRegisters r q) =
        .success (collectionStartLedger r q base time) := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hinputs, hledger⟩
  unfold CoordinatorCollectionLedger.startCollectionChecked
  simp only [hinputs, collectionStartLedger] at hledger ⊢
  rw [hledger]
  rfl

/-- Every phase-clock error, including each individual `ClockFailure`, is
returned with the same constructor and value. -/
theorem dispatch_clockError_iff
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (failure : CoordinatorPhaseClock.ClockFailure) :
    dispatch r q base = .error failure ↔
    CoordinatorPhaseClock.startRound p eta.val r.time r.priorClock
      r.clockPending =
        .error failure := by
  cases h : CoordinatorPhaseClock.startRound p eta.val r.time r.priorClock
      r.clockPending <;> simp [dispatch, h]

/-- On a checked `initializeAt` branch, the consumer returns the original
clock result together with the newly initialized ledger and all its literal
field equations. -/
theorem dispatch_initializeAt_success
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (result : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p eta.val r.time r.priorClock
      r.clockPending =
      .ok result)
    (hcommand : result.ledgerCommand = some (.initializeAt r.time))
    (hdomains : initializationDomainValid r q base r.time) :
    dispatch r q base =
      .ok ⟨result, .success (some (collectionStartLedger r q base r.time))⟩ := by
  simp [dispatch, hstart, hcommand, hdomains, checkedOptionIfValid,
    startCollectionChecked_success_of_domains]

/-- If the clock succeeds without a collection initialization command, the
same clock result is returned and no new ledger is attached. -/
theorem dispatch_no_initialization
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (result : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p eta.val r.time r.priorClock
      r.clockPending =
      .ok result)
    (hcommand : ∀ time, result.ledgerCommand ≠ some (.initializeAt time)) :
    dispatch r q base = .ok ⟨result, .success none⟩ := by
  simp [dispatch, hstart]

end Bandits.Support.CoordinatorStartRoundCutoffDispatch

end
