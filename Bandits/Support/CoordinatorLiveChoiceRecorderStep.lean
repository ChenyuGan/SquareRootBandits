/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CoordinatorPhaseClock
public import Bandits.Support.CoordinatorLocalArmChoice
public import Bandits.Support.AssignmentStartPayload
public import Bandits.Support.CoordinatorRecorderComplementBridge
public import Bandits.Support.CoordinatorRecordingMeasurability
public import Bandits.Support.AssignmentScoreReconstruction
public import Bandits.Support.ScoreWeights
public import Bandits.Support.CoordinatorRecordingOperation
public import Bandits.Support.CompletePublicTable

import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# One checked live coordinator choice and own-observation recorder step

This module composes the accepted phase clock, live coordinator arm choice,
complement recorder, and confirmation update for one supplied complete row.
The prior clock, payload, pending set, time, grid endpoint, and complement
integer scores are explicit local inputs. `prepare` calls `StartRound` first
and only creates a continuation for its unchanged live branch. `finish` takes
only the coordinator's typed own observation and consumes the arm selected
before that observation was available.

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-14,37-70,235-296`,
`sources/zip4/manuscript/05_binary_transport.tex:74-104`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.

This is a conditional local operation. The clock/payload and grid equalities,
score domains, source time/rate conditions, and complement envelope are
checked local obligations; this module proves no physical reachability, score
identity with a physical run, freshness, conditional recording law, no-dagger
claim, or manuscript theorem closure. The envelope and integer scores remain
inputs for a chronological producer; in particular `z = Z` is not inferred.
-/

@[expose] public section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.ReferencePrelaunchFollower

namespace Bandits.Support.CoordinatorLiveChoiceRecorderStep

abbrev Parameters := ConstructorDimensions.Parameters
abbrev LearningRate := ReferencePrelaunchFollower.LearningRate

variable {p : Parameters} {eta : LearningRate}

local instance optionArmMeasurableSpace (n : ℕ) :
    MeasurableSpace (Option (Fin n)) := ⊤

local instance optionPendingMeasurableSpace (m : ℕ) :
    MeasurableSpace (Option (Finset (Fin m))) := ⊤

local instance optionObservedFlowMeasurableSpace (p : Parameters) :
    MeasurableSpace (Option (CoordinatorRecordingOperation.Output p ×
      Finset (ActiveRoundActions.Follower p.m) × Fin p.K)) := ⊤

/-- The coordinator's retained local registers before the live pre-choice
step. Scores are indexed only by the actual complement of the payload's slow
set; no peer history or slow-arm current score vector is accepted. -/
structure Registers (p : Parameters) (eta : LearningRate) where
  payload : AssignmentStartPayload.Input p eta
  priorClock : ClockRegisters p
  pendingAtChoice : Finset (ActiveRoundActions.Follower p.m)
  time : Fin p.T
  gridBoundary : ℕ
  complementScores :
    CanonicalFastSampling.FastArm payload.slowSet → ℕ

namespace Registers

variable (r : Registers p eta)

/-- The source's current weights, derived coordinatewise from the supplied
complement integer scores. -/
noncomputable def complementWeights :
    CanonicalFastSampling.FastArm r.payload.slowSet → ℝ :=
  fun j => ScoreWeights.scoreWeight
    (AssignmentScoreReconstruction.sourceWeightBase p) (r.complementScores j)

/-- The integer score coordinates satisfy the appendix's `[0,TD]` domain.
Their nonnegativity is represented by the natural-number carrier. -/
def scoreDomainValid : Prop :=
  ∀ j, r.complementScores j ≤ p.T * D p

/-- The source envelope is checked only on coordinator-owned complement
coordinates. This predicate makes no assertion that the supplied scores or
anchor arose from an execution. -/
def complementEnvelopeValid : Prop :=
  ∀ j, r.payload.anchor j.1 ≤ r.complementWeights j ∧
    r.complementWeights j ≤ 2 * r.payload.anchor j.1

/-- The recorder's local time and complement-envelope checks, in the exact
shape consumed by the accepted bridge. -/
def recorderDomainValid : Prop :=
  r.gridBoundary ≤ p.T + 1 ∧ r.complementEnvelopeValid

/-- The phase-clock API uses the definitional `Fin (m - 1)` presentation of
the same follower indices. -/
def clockPending : Finset (Fin (p.m - 1)) := by
  simpa [ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount]
    using r.pendingAtChoice

theorem clockPending_eq :
    r.clockPending = r.pendingAtChoice := by
  rfl

theorem complementWeights_pos (j : CanonicalFastSampling.FastArm r.payload.slowSet) :
    0 < r.complementWeights j := by
  exact ScoreWeights.scoreWeight_pos
    (AssignmentScoreReconstruction.sourceWeightBase_pos p) _

end Registers

/-- The clock stores a zero-based finite cutoff, while the local arm and
recorder operators use an optional one-based endpoint. `none` is the source
sentinel `T+1`; a finite clock coordinate `u` becomes `u.val+1`. -/
def cutoffFromClock (p : Parameters) (u : Option (Fin p.T)) :
    Option (CoordinatorLocalArmChoice.Cutoff p) :=
  u.map fun v =>
    ⟨v.val + 1, by
      constructor
      · omega
      · omega⟩

/-- Exact one-based cutoff interpretation, including the terminal sentinel. -/
theorem cutoffRoundFromClock (u : Option (Fin p.T)) :
    CoordinatorLocalArmChoice.cutoffRound (cutoffFromClock p u) =
      u.elim (p.T + 1) fun v => v.val + 1 := by
  cases u <;> rfl

/-- The exact start-round frame accepted by `prepare`: no cutoff command, no
new assignment instruction, and no clock or pending-set transition. -/
def unchangedLiveClockFrame (r : Registers p eta)
    (result : CoordinatorPhaseClock.StartRoundResult p) : Prop :=
  result.clock = r.priorClock ∧
    result.pending = r.clockPending ∧
    result.ledgerCommand = none ∧
    result.assignmentStart = none

/-- Failures at the phase-clock/local-choice preparation boundary. A clock
failure is kept separate from the later source-domain and arm-choice failures. -/
inductive PrepareFailure where
  | clockRejected
  | clockTransition
  | payloadClockMismatch
  | gridBoundaryMismatch
  | scoreDomainFailure
  | notLive
  | choiceDomainFailure
  | recorderBoundaryFailure
  | complementEnvelopeFailure
  deriving DecidableEq

/-- Failures after the arm has already been fixed at pre-choice time. -/
inductive FinishFailure where
  | recorderRejected
  | confirmationRejected
  deriving DecidableEq

/-- All row-independent obligations checked by `prepare`. This carries the
actual accepted clock result and keeps source time/rate/envelope conditions
visible as local hypotheses. -/
structure PreparationDomain (r : Registers p eta) where
  startResult : CoordinatorPhaseClock.StartRoundResult p
  startRound_eq : CoordinatorPhaseClock.startRound p eta.val r.time
    r.priorClock r.clockPending = .ok startResult
  clockFrame : unchangedLiveClockFrame r startResult
  payloadClockStart : r.priorClock.sigma = some r.payload.sigma
  gridBoundary_eq_clock : r.gridBoundary = r.priorClock.g
  scoreDomainValid : r.scoreDomainValid
  assignmentLive : CoordinatorLocalArmChoice.assignmentIsLive r.payload
    (cutoffFromClock p r.priorClock.u) r.time
  choiceInputsValid : CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
    (cutoffFromClock p r.priorClock.u) r.time r.complementWeights
  recorderInputsValid : r.recorderDomainValid

/-- A continuation freezes the actual selected arm together with its full
row, current slice, and pre-choice confirmation mode. The proof fields expose
the checked source-local inputs used by the continuation. -/
structure Continuation {p : Parameters} {eta : LearningRate}
    (r : Registers p eta) (row : CompleteRow p) where
  startRoundResult : CoordinatorPhaseClock.StartRoundResult p
  clockFrame : unchangedLiveClockFrame r startRoundResult
  payloadClockStart : r.priorClock.sigma = some r.payload.sigma
  gridBoundary_eq_clock : r.gridBoundary = r.priorClock.g
  sourceTimeValid :
    CoordinatorLocalArmChoice.SourceTimeValid r.payload
      (cutoffFromClock p r.priorClock.u) r.time
  choiceInputsValid :
    CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
      (cutoffFromClock p r.priorClock.u) r.time
      r.complementWeights
  scoreDomainValid : r.scoreDomainValid
  recorderInputsValid : r.recorderDomainValid
  confirmationInputsValid :
    CoordinatorLocalArmChoice.ConfirmationInputsValid r.payload
      (cutoffFromClock p r.priorClock.u) r.time
  currentControl : ContinuousLearningRows.TimeControl p
  currentControl_eq : currentControl = row.2 r.time
  preChoiceMode : CoordinatorRecorderComplementBridge.LocalMode r.payload
  preChoiceMode_eq : preChoiceMode =
    .live (decide (r.pendingAtChoice = ∅))
  armChoice_ne_none :
    CoordinatorLocalArmChoice.coordinatorArmChoice r.payload r.pendingAtChoice
      (cutoffFromClock p r.priorClock.u) r.time r.complementWeights row ≠ none

namespace Continuation

variable {p : Parameters} {eta : LearningRate} {r : Registers p eta}
variable {row : CompleteRow p} (c : Continuation r row)

/-- The selected arm is the accepted complete-row choice's `getD` view; the
stored non-`none` proof makes the fallback unreachable. -/
noncomputable def ownArm (c : Continuation r row) : Fin p.K :=
  let _ := c
  (CoordinatorLocalArmChoice.coordinatorArmChoice r.payload r.pendingAtChoice
    (cutoffFromClock p r.priorClock.u) r.time r.complementWeights row).getD
      ⟨0, K_pos p⟩

theorem armChoice_eq :
    CoordinatorLocalArmChoice.coordinatorArmChoice r.payload r.pendingAtChoice
      (cutoffFromClock p r.priorClock.u) r.time r.complementWeights row =
        some c.ownArm := by
  cases hchoice : CoordinatorLocalArmChoice.coordinatorArmChoice r.payload
      r.pendingAtChoice (cutoffFromClock p r.priorClock.u) r.time
      r.complementWeights row with
  | none => exact False.elim (c.armChoice_ne_none hchoice)
  | some arm => simp [ownArm, hchoice]

/-- The one-based cutoff carried by the same prior clock used at preparation. -/
def sourceCutoff (c : Continuation r row) :
    Option (CoordinatorLocalArmChoice.Cutoff p) :=
  let _ := c
  cutoffFromClock p r.priorClock.u

end Continuation

/-- The checked result of the local operation retains the prior clock and
payload unchanged and returns the exact raw recorder output and confirmation
set update. -/
structure Output (p : Parameters) (eta : LearningRate) where
  priorClock : ClockRegisters p
  startRoundResult : CoordinatorPhaseClock.StartRoundResult p
  payload : AssignmentStartPayload.Input p eta
  time : Fin p.T
  pendingBefore : Finset (ActiveRoundActions.Follower p.m)
  pendingAfter : Finset (ActiveRoundActions.Follower p.m)
  ownArm : Fin p.K
  recorderOutput : CoordinatorRecordingOperation.Output p

/-- Exact accepted recorder input for a prepared continuation and a supplied
own observation. The stored arm, row, time, scores, and pre-choice mode are
used literally. -/
noncomputable def recorderInput
    {r : Registers p eta} {row : CompleteRow p} (c : Continuation r row)
    (observation : Fin (D p + 1)) :
    CoordinatorRecorderComplementBridge.Input r.payload :=
  { currentWeights := r.complementWeights
    time := r.time
    gridBoundary := r.gridBoundary
    row := row
    ownArm := c.ownArm
    observation := observation
    mode := c.preChoiceMode }

/-- Call the checked source clock first, then accept only its unchanged live
branch and check each retained local domain before choosing the coordinator
arm from this same row and the pre-choice pending set. -/
theorem coordinatorArmChoice_ne_none
    (s : AssignmentStartPayload.Input p eta)
    (pending : Finset (ActiveRoundActions.Follower p.m))
    (u : Option (CoordinatorLocalArmChoice.Cutoff p)) (t : Fin p.T)
    (weights : CanonicalFastSampling.FastArm s.slowSet → ℝ)
    (row : CompleteRow p)
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid s u t weights) :
    CoordinatorLocalArmChoice.coordinatorArmChoice s pending u t weights row ≠ none := by
  rw [CoordinatorLocalArmChoice.coordinatorArmChoice_eq_core]
  unfold CoordinatorLocalArmChoice.coordinatorArmChoiceCore
  rw [dite_eq_left hvalid]
  split_ifs <;> simp

noncomputable def prepare (r : Registers p eta) (row : CompleteRow p) :
    Except PrepareFailure (Continuation r row) := by
  classical
  exact
    match CoordinatorPhaseClock.startRound p eta.val r.time
        r.priorClock r.clockPending with
    | .error _ => .error .clockRejected
    | .ok startResult =>
        if hframe : unchangedLiveClockFrame r startResult then
          if hsigma : r.priorClock.sigma = some r.payload.sigma then
            if hgrid : r.gridBoundary = r.priorClock.g then
              if hscore : r.scoreDomainValid then
                if hlive : CoordinatorLocalArmChoice.assignmentIsLive
                    r.payload (cutoffFromClock p r.priorClock.u) r.time then
                  if hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid
                      r.payload (cutoffFromClock p r.priorClock.u) r.time
                      r.complementWeights then
                    if hboundary : r.gridBoundary ≤ p.T + 1 then
                      if henvelope : r.complementEnvelopeValid then
                        have hchoiceResult_ne := coordinatorArmChoice_ne_none
                          r.payload r.pendingAtChoice
                          (cutoffFromClock p r.priorClock.u) r.time
                          r.complementWeights row hchoice
                        have hbridge : r.recorderDomainValid :=
                          ⟨hboundary, henvelope⟩
                        .ok
                          { startRoundResult := startResult
                            clockFrame := hframe
                            payloadClockStart := hsigma
                            gridBoundary_eq_clock := hgrid
                            sourceTimeValid := hchoice.time
                            choiceInputsValid := hchoice
                            scoreDomainValid := hscore
                            recorderInputsValid := hbridge
                            confirmationInputsValid :=
                              CoordinatorLocalArmChoice.confirmationInputsValid_mk
                                r.payload (cutoffFromClock p r.priorClock.u) r.time
                                hchoice.time.assignment_started
                                hchoice.time.cutoff_after_start
                            currentControl := row.2 r.time
                            currentControl_eq := rfl
                            preChoiceMode :=
                              .live (decide (r.pendingAtChoice = ∅))
                            preChoiceMode_eq := rfl
                            armChoice_ne_none := hchoiceResult_ne }
                      else .error .complementEnvelopeFailure
                    else .error .recorderBoundaryFailure
                  else .error .choiceDomainFailure
                else .error .notLive
              else .error .scoreDomainFailure
            else .error .gridBoundaryMismatch
          else .error .payloadClockMismatch
        else .error .clockTransition

/-- Under the explicit row-independent local domain, preparation succeeds for
every complete row and stores the result of the accepted row choice. -/
theorem prepare_success_of_domain {r : Registers p eta}
    (domain : PreparationDomain r) (row : CompleteRow p) :
    ∃ c, prepare r row = .ok c ∧ c.startRoundResult = domain.startResult := by
  classical
  have hchoiceResult_ne := coordinatorArmChoice_ne_none r.payload
    r.pendingAtChoice (cutoffFromClock p r.priorClock.u) r.time
    r.complementWeights row domain.choiceInputsValid
  have hboundary : r.gridBoundary ≤ p.T + 1 := domain.recorderInputsValid.1
  have henvelope : r.complementEnvelopeValid := domain.recorderInputsValid.2
  have hclockBoundary : r.priorClock.g ≤ p.T + 1 := by
    rw [← domain.gridBoundary_eq_clock]
    exact hboundary
  let c : Continuation r row := {
        startRoundResult := domain.startResult
        clockFrame := domain.clockFrame
        payloadClockStart := domain.payloadClockStart
        gridBoundary_eq_clock := domain.gridBoundary_eq_clock
        sourceTimeValid := domain.choiceInputsValid.time
        choiceInputsValid := domain.choiceInputsValid
        scoreDomainValid := domain.scoreDomainValid
        recorderInputsValid := domain.recorderInputsValid
        confirmationInputsValid :=
          CoordinatorLocalArmChoice.confirmationInputsValid_mk r.payload
            (cutoffFromClock p r.priorClock.u) r.time
            domain.choiceInputsValid.time.assignment_started
            domain.choiceInputsValid.time.cutoff_after_start
        currentControl := row.2 r.time
        currentControl_eq := rfl
        preChoiceMode := .live (decide (r.pendingAtChoice = ∅))
        preChoiceMode_eq := rfl
        armChoice_ne_none := hchoiceResult_ne }
  refine ⟨c, ?_, rfl⟩
  unfold prepare
  simp [domain.startRound_eq, domain.clockFrame,
    domain.payloadClockStart, domain.gridBoundary_eq_clock,
    domain.scoreDomainValid, domain.assignmentLive,
    domain.choiceInputsValid, henvelope, hclockBoundary, c]

/-- The checked finish uses the observation only after the continuation has
stored the current arm. It runs the complement recorder once, then applies the
accepted confirmation update to the same pre-choice pending set. -/
noncomputable def finish {r : Registers p eta} {row : CompleteRow p}
    (c : Continuation r row)
    (observation : Fin (D p + 1)) : Except FinishFailure (Output p eta) := by
  classical
  let recording := CoordinatorRecorderComplementBridge.run
    (recorderInput c observation)
  exact match recording with
  | none => .error .recorderRejected
  | some recorderOutput =>
      match CoordinatorLocalArmChoice.confirmationUpdate r.payload
          r.pendingAtChoice c.sourceCutoff r.time row observation with
      | none => .error .confirmationRejected
      | some pendingAfter =>
          .ok
            { priorClock := r.priorClock
              startRoundResult := c.startRoundResult
              payload := r.payload
              time := r.time
              pendingBefore := r.pendingAtChoice
              pendingAfter := pendingAfter
              ownArm := c.ownArm
              recorderOutput := recorderOutput }

/-- The recorder-facing local domain condition is exactly the boundary and
complement envelope check already exposed by `Registers`. -/
theorem recorderInput_inputsValid_iff {r : Registers p eta}
    {row : CompleteRow p} (c : Continuation r row)
    (observation : Fin (D p + 1)) :
    CoordinatorRecordingOperation.InputsValid
      (CoordinatorRecorderComplementBridge.recorderInput
        (recorderInput c observation)) ↔ r.recorderDomainValid := by
  rw [CoordinatorRecorderComplementBridge.recorderInput_inputsValid_iff
    (recorderInput c observation)]
  rfl

/-- A successful preparation records the exact first-stage clock call and
its no-cutoff/no-collection/no-new-assignment frame. -/
theorem prepare_success_stage {r : Registers p eta} {row : CompleteRow p}
    {c : Continuation r row} (domain : PreparationDomain r)
    (h : prepare r row = .ok c) :
    CoordinatorPhaseClock.startRound p eta.val r.time
        r.priorClock r.pendingAtChoice = .ok c.startRoundResult ∧
      c.startRoundResult.clock = r.priorClock ∧
      c.startRoundResult.pending = r.pendingAtChoice ∧
      c.startRoundResult.ledgerCommand = none ∧
      c.startRoundResult.assignmentStart = none := by
  rcases prepare_success_of_domain domain row with ⟨c₀, h₀, hresult₀⟩
  have hc : c₀ = c := Except.ok.inj (h₀.symm.trans h)
  have hresult : c.startRoundResult = domain.startResult := by
    rw [← hc]
    exact hresult₀
  have hpending : c.startRoundResult.pending = r.pendingAtChoice :=
    (by rw [hresult]; exact domain.clockFrame.2.1.trans (Registers.clockPending_eq r))
  exact ⟨by rw [hresult]; exact domain.startRound_eq,
    c.clockFrame.1, hpending,
    c.clockFrame.2.2.1, c.clockFrame.2.2.2⟩

/-- A successful preparation keeps the payload start and recorder grid
endpoint tied to the actual carried prior clock. -/
theorem prepare_success_clock_payload {r : Registers p eta} {row : CompleteRow p}
    {c : Continuation r row} (_h : prepare r row = .ok c) :
    r.priorClock.sigma = some r.payload.sigma ∧
      r.gridBoundary = r.priorClock.g ∧ c.startRoundResult.clock.g = r.priorClock.g := by
  have hg : c.startRoundResult.clock.g = r.priorClock.g :=
    congrArg ClockRegisters.g c.clockFrame.1
  exact ⟨c.payloadClockStart, c.gridBoundary_eq_clock, hg⟩

/-- The cutoff presented to the local operators is exactly the one-based
source endpoint carried by the unchanged phase clock; `none` remains `T+1`. -/
theorem prepare_success_cutoff {r : Registers p eta} {row : CompleteRow p}
    {c : Continuation r row} (_h : prepare r row = .ok c) :
    CoordinatorLocalArmChoice.cutoffRound
        (cutoffFromClock p c.startRoundResult.clock.u) =
      r.priorClock.u.elim (p.T + 1) fun u => u.val + 1 := by
  rw [cutoffRoundFromClock]
  have hu := congrArg ClockRegisters.u c.clockFrame.1
  rw [hu]

/-- The own arm is fixed by the accepted complete-row choice before any own
observation is supplied to `finish`. -/
theorem prepare_success_arm {r : Registers p eta} {row : CompleteRow p}
    {c : Continuation r row} (_h : prepare r row = .ok c) :
    CoordinatorLocalArmChoice.coordinatorArmChoice r.payload r.pendingAtChoice
      (cutoffFromClock p r.priorClock.u) r.time r.complementWeights row =
        some c.ownArm :=
  c.armChoice_eq

/-- The stored mode is exactly the pre-choice emptiness test. -/
theorem prepare_success_preChoiceMode {r : Registers p eta}
    {row : CompleteRow p} (c : Continuation r row) :
    c.preChoiceMode = .live (decide (r.pendingAtChoice = ∅)) :=
  c.preChoiceMode_eq

/-- Invalid prior-clock input is returned as a clock failure before any
payload, score, or row-dependent local operation is attempted. -/
theorem prepare_clock_failure {r : Registers p eta} {row : CompleteRow p}
    {failure : CoordinatorPhaseClock.ClockFailure}
    (h : CoordinatorPhaseClock.startRound p eta.val r.time
      r.priorClock r.clockPending = .error failure) :
    prepare r row = .error .clockRejected := by
  unfold prepare
  rw [h]

/-- A successful clock call that changes the retained live frame is rejected
before any payload, score, or row-dependent local check. -/
theorem prepare_clock_transition_failure {r : Registers p eta}
    {row : CompleteRow p} {result : CoordinatorPhaseClock.StartRoundResult p}
    (hstart : CoordinatorPhaseClock.startRound p eta.val r.time
      r.priorClock r.clockPending = .ok result)
    (hframe : ¬ unchangedLiveClockFrame r result) :
    prepare r row = .error .clockTransition := by
  unfold prepare
  rw [hstart]
  simp [hframe]

/-- Once the clock frame is accepted, a payload/clock sigma mismatch is a
separate preparation failure. -/
theorem prepare_payload_clock_failure {r : Registers p eta}
    {row : CompleteRow p} {result : CoordinatorPhaseClock.StartRoundResult p}
    (hstart : CoordinatorPhaseClock.startRound p eta.val r.time
      r.priorClock r.clockPending = .ok result)
    (hframe : unchangedLiveClockFrame r result)
    (hsigma : r.priorClock.sigma ≠ some r.payload.sigma) :
    prepare r row = .error .payloadClockMismatch := by
  unfold prepare
  rw [hstart]
  simp [hframe, hsigma]

/-- The recorder endpoint must be the endpoint of the same carried clock. -/
theorem prepare_grid_boundary_failure {r : Registers p eta}
    {row : CompleteRow p} {result : CoordinatorPhaseClock.StartRoundResult p}
    (hstart : CoordinatorPhaseClock.startRound p eta.val r.time
      r.priorClock r.clockPending = .ok result)
    (hframe : unchangedLiveClockFrame r result)
    (hsigma : r.priorClock.sigma = some r.payload.sigma)
    (hgrid : r.gridBoundary ≠ r.priorClock.g) :
    prepare r row = .error .gridBoundaryMismatch := by
  unfold prepare
  rw [hstart]
  simp [hframe, hsigma, hgrid]

/-- Out-of-domain complement integer scores are rejected before live/time or
recorder-envelope checks. -/
theorem prepare_score_domain_failure {r : Registers p eta}
    {row : CompleteRow p} {result : CoordinatorPhaseClock.StartRoundResult p}
    (hstart : CoordinatorPhaseClock.startRound p eta.val r.time
      r.priorClock r.clockPending = .ok result)
    (hframe : unchangedLiveClockFrame r result)
    (hsigma : r.priorClock.sigma = some r.payload.sigma)
    (hgrid : r.gridBoundary = r.priorClock.g)
    (hscore : ¬ r.scoreDomainValid) :
    prepare r row = .error .scoreDomainFailure := by
  unfold prepare
  rw [hstart]
  simp [hframe, hsigma, hgrid, hscore]

/-- A locally non-live assignment is rejected after score-domain validation. -/
theorem prepare_not_live_failure {r : Registers p eta}
    {row : CompleteRow p} {result : CoordinatorPhaseClock.StartRoundResult p}
    (hstart : CoordinatorPhaseClock.startRound p eta.val r.time
      r.priorClock r.clockPending = .ok result)
    (hframe : unchangedLiveClockFrame r result)
    (hsigma : r.priorClock.sigma = some r.payload.sigma)
    (hgrid : r.gridBoundary = r.priorClock.g)
    (hscore : r.scoreDomainValid)
    (hlive : ¬ CoordinatorLocalArmChoice.assignmentIsLive r.payload
      (cutoffFromClock p r.priorClock.u) r.time) :
    prepare r row = .error .notLive := by
  unfold prepare
  rw [hstart]
  simp [hframe, hsigma, hgrid, hscore, hlive]

/-- Invalid source time/rate/current-weight data is rejected before recorder
boundary and envelope checks. -/
theorem prepare_choice_domain_failure {r : Registers p eta}
    {row : CompleteRow p} {result : CoordinatorPhaseClock.StartRoundResult p}
    (hstart : CoordinatorPhaseClock.startRound p eta.val r.time
      r.priorClock r.clockPending = .ok result)
    (hframe : unchangedLiveClockFrame r result)
    (hsigma : r.priorClock.sigma = some r.payload.sigma)
    (hgrid : r.gridBoundary = r.priorClock.g)
    (hscore : r.scoreDomainValid)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive r.payload
      (cutoffFromClock p r.priorClock.u) r.time)
    (hchoice : ¬ CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
      (cutoffFromClock p r.priorClock.u) r.time r.complementWeights) :
    prepare r row = .error .choiceDomainFailure := by
  unfold prepare
  rw [hstart]
  simp [hframe, hsigma, hgrid, hscore, hlive, hchoice]

/-- A source endpoint beyond the recorder horizon is reported separately
from a failed complement envelope. -/
theorem prepare_recorder_boundary_failure {r : Registers p eta}
    {row : CompleteRow p} {result : CoordinatorPhaseClock.StartRoundResult p}
    (hstart : CoordinatorPhaseClock.startRound p eta.val r.time
      r.priorClock r.clockPending = .ok result)
    (hframe : unchangedLiveClockFrame r result)
    (hsigma : r.priorClock.sigma = some r.payload.sigma)
    (hgrid : r.gridBoundary = r.priorClock.g)
    (hscore : r.scoreDomainValid)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive r.payload
      (cutoffFromClock p r.priorClock.u) r.time)
    (hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
      (cutoffFromClock p r.priorClock.u) r.time r.complementWeights)
    (hboundary : ¬ r.gridBoundary ≤ p.T + 1) :
    prepare r row = .error .recorderBoundaryFailure := by
  unfold prepare
  rw [hstart]
  have hclockBoundary : ¬ r.priorClock.g ≤ p.T + 1 := by
    simpa [hgrid] using hboundary
  simp [hframe, hsigma, hgrid, hscore, hlive, hchoice, hclockBoundary]

/-- A malformed complement envelope is rejected after the recorder endpoint
has passed its local horizon check. -/
theorem prepare_complement_envelope_failure {r : Registers p eta}
    {row : CompleteRow p} {result : CoordinatorPhaseClock.StartRoundResult p}
    (hstart : CoordinatorPhaseClock.startRound p eta.val r.time
      r.priorClock r.clockPending = .ok result)
    (hframe : unchangedLiveClockFrame r result)
    (hsigma : r.priorClock.sigma = some r.payload.sigma)
    (hgrid : r.gridBoundary = r.priorClock.g)
    (hscore : r.scoreDomainValid)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive r.payload
      (cutoffFromClock p r.priorClock.u) r.time)
    (hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
      (cutoffFromClock p r.priorClock.u) r.time r.complementWeights)
    (hboundary : r.gridBoundary ≤ p.T + 1)
    (henvelope : ¬ r.complementEnvelopeValid) :
    prepare r row = .error .complementEnvelopeFailure := by
  unfold prepare
  rw [hstart]
  have hclockBoundary : r.priorClock.g ≤ p.T + 1 := by
    simpa [hgrid] using hboundary
  simp [hframe, hsigma, hgrid, hscore, hlive, hchoice, hclockBoundary,
    henvelope]

/-- A successful preparation certifies the exact score interval on every
coordinator-owned complement coordinate. -/
theorem prepare_success_scoreDomain {r : Registers p eta} {row : CompleteRow p}
    {c : Continuation r row} (_h : prepare r row = .ok c) : r.scoreDomainValid :=
  c.scoreDomainValid

/-- A successful continuation includes the source time/rate/envelope
conditions required by the arm choice and the complement recorder. These are
local checked inputs, not physical-run conclusions. -/
theorem prepare_success_domains {r : Registers p eta} {row : CompleteRow p}
    {c : Continuation r row} (_h : prepare r row = .ok c) :
    CoordinatorLocalArmChoice.SourceTimeValid r.payload
      (cutoffFromClock p r.priorClock.u) r.time ∧
    CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
      (cutoffFromClock p r.priorClock.u) r.time r.complementWeights ∧
    r.recorderDomainValid ∧
    CoordinatorLocalArmChoice.ConfirmationInputsValid r.payload
      (cutoffFromClock p r.priorClock.u) r.time :=
  ⟨c.sourceTimeValid, c.choiceInputsValid, c.recorderInputsValid,
    c.confirmationInputsValid⟩

/-- The four source arm equations, all on the same stored row/time and
pre-choice pending set. -/
theorem prepared_fast_arm {r : Registers p eta} {row : CompleteRow p}
    (c : Continuation r row)
    (hfast : CoordinatorLocalArmChoice.assignmentIsLive r.payload c.sourceCutoff
      r.time ∧ r.pendingAtChoice = ∅) :
    c.ownArm =
      (CoordinatorLocalArmChoice.localFastDraw r.payload c.sourceCutoff r.time
        r.complementWeights c.choiceInputsValid c.currentControl).1 := by
  have hcore : CoordinatorLocalArmChoice.coordinatorArmChoiceCore
      r.payload r.pendingAtChoice c.sourceCutoff r.time r.complementWeights
      c.currentControl = some c.ownArm := by
    simpa [CoordinatorLocalArmChoice.coordinatorArmChoice_eq_core,
      Continuation.sourceCutoff, c.currentControl_eq] using c.armChoice_eq
  have hbranch := CoordinatorLocalArmChoice.coordinatorArmChoiceCore_live_empty
    r.payload r.pendingAtChoice c.sourceCutoff r.time r.complementWeights
    c.currentControl c.choiceInputsValid hfast.1 hfast.2
  exact Option.some.inj (hcore.symm.trans hbranch)

/-- On a live round whose pre-choice confirmations are missing, DATA returns
the coordinator's own pilot arm from this exact slice. -/
theorem prepared_data_arm {r : Registers p eta} {row : CompleteRow p}
    (c : Continuation r row)
    (hnotfast : ¬ (CoordinatorLocalArmChoice.assignmentIsLive r.payload
      c.sourceCutoff r.time ∧ r.pendingAtChoice = ∅))
    (hdata : PublicDiscreteDraws.slotDraw c.currentControl.1 =
      PublicDiscreteDraws.dataSlot) :
    c.ownArm = PublicDiscreteDraws.pilotDraw (K_pos p)
      (ActiveRoundActions.coordinator p.two_le_m) c.currentControl.1 := by
  have hcore : CoordinatorLocalArmChoice.coordinatorArmChoiceCore
      r.payload r.pendingAtChoice c.sourceCutoff r.time r.complementWeights
      c.currentControl = some c.ownArm := by
    simpa [CoordinatorLocalArmChoice.coordinatorArmChoice_eq_core,
      Continuation.sourceCutoff, c.currentControl_eq] using c.armChoice_eq
  have hbranch := CoordinatorLocalArmChoice.coordinatorArmChoiceCore_data
    r.payload r.pendingAtChoice c.sourceCutoff r.time r.complementWeights
    c.currentControl c.choiceInputsValid hnotfast hdata
  exact Option.some.inj (hcore.symm.trans hbranch)

/-- On a selected pending DOWN slot outside the fast and DATA branches, the
coordinator transmits the stored DOWN word on the actual current tuple. -/
theorem prepared_down_arm {r : Registers p eta} {row : CompleteRow p}
    (c : Continuation r row)
    (hnotfast : ¬ (CoordinatorLocalArmChoice.assignmentIsLive r.payload
      c.sourceCutoff r.time ∧ r.pendingAtChoice = ∅))
    (hnotdata : PublicDiscreteDraws.slotDraw c.currentControl.1 ≠
      PublicDiscreteDraws.dataSlot)
    (hdown : PublicDiscreteDraws.slotDraw c.currentControl.1 =
      PublicDiscreteDraws.downSlot)
    (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m
      p.m_lt_K c.currentControl.1 ∈ r.pendingAtChoice) :
    c.ownArm = ActiveRoundActions.sendArm
      (CoordinatorLocalArmChoice.currentDownHash r.payload c.currentControl
        (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          c.currentControl.1))
      ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.currentControl.1).val
        (ActiveRoundActions.coordinator p.two_le_m))
      ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.currentControl.1).val
        (PublicDiscreteDraws.followerPlayer p.two_le_m
          (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            c.currentControl.1))) := by
  have hcore : CoordinatorLocalArmChoice.coordinatorArmChoiceCore
      r.payload r.pendingAtChoice c.sourceCutoff r.time r.complementWeights
      c.currentControl = some c.ownArm := by
    simpa [CoordinatorLocalArmChoice.coordinatorArmChoice_eq_core,
      Continuation.sourceCutoff, c.currentControl_eq] using c.armChoice_eq
  have hbranch := CoordinatorLocalArmChoice.coordinatorArmChoiceCore_down
    r.payload r.pendingAtChoice c.sourceCutoff r.time r.complementWeights
    c.currentControl c.choiceInputsValid hnotfast hnotdata hdown hselected
  exact Option.some.inj (hcore.symm.trans hbranch)

/-- Outside live-fast, DATA, and a selected pending DOWN tuple, the
coordinator arm is the coordinator component of the same ordered tuple. -/
theorem prepared_tuple_arm {r : Registers p eta} {row : CompleteRow p}
    (c : Continuation r row)
    (hnotfast : ¬ (CoordinatorLocalArmChoice.assignmentIsLive r.payload
      c.sourceCutoff r.time ∧ r.pendingAtChoice = ∅))
    (hnotdata : PublicDiscreteDraws.slotDraw c.currentControl.1 ≠
      PublicDiscreteDraws.dataSlot)
    (hnotdown : ¬ (PublicDiscreteDraws.slotDraw c.currentControl.1 =
        PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        c.currentControl.1 ∈ r.pendingAtChoice)) :
    c.ownArm =
      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.currentControl.1).val
        (ActiveRoundActions.coordinator p.two_le_m) := by
  have hcore : CoordinatorLocalArmChoice.coordinatorArmChoiceCore
      r.payload r.pendingAtChoice c.sourceCutoff r.time r.complementWeights
      c.currentControl = some c.ownArm := by
    simpa [CoordinatorLocalArmChoice.coordinatorArmChoice_eq_core,
      Continuation.sourceCutoff, c.currentControl_eq] using c.armChoice_eq
  have hbranch := CoordinatorLocalArmChoice.coordinatorArmChoiceCore_other
    r.payload r.pendingAtChoice c.sourceCutoff r.time r.complementWeights
    c.currentControl c.choiceInputsValid hnotfast hnotdata hnotdown
  exact Option.some.inj (hcore.symm.trans hbranch)

/-- Successful finishing returns precisely the checked bridge output and the
accepted update computed from the stored pre-choice state. -/
theorem finish_success_equations {r : Registers p eta} {row : CompleteRow p}
    {c : Continuation r row}
    {observation : Fin (D p + 1)} {out : Output p eta}
    (h : finish c observation = .ok out) :
    CoordinatorRecorderComplementBridge.run (recorderInput c observation) =
        some out.recorderOutput ∧
      CoordinatorLocalArmChoice.confirmationUpdate r.payload r.pendingAtChoice
        c.sourceCutoff r.time row observation = some out.pendingAfter := by
  classical
  unfold finish at h
  dsimp only at h
  cases hrecording : CoordinatorRecorderComplementBridge.run
      (recorderInput c observation) with
  | none => simp [hrecording] at h
  | some recorderOutput =>
      cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate
          r.payload r.pendingAtChoice c.sourceCutoff r.time row observation with
      | none => simp [hrecording, hconfirmation] at h
      | some pendingAfter =>
          simp [hrecording, hconfirmation] at h
          cases h
          constructor
          · simp
          · simp

/-- The finished result retains the arm selected during preparation. -/
theorem finish_success_arm {r : Registers p eta} {row : CompleteRow p}
    {c : Continuation r row} {observation : Fin (D p + 1)}
    {out : Output p eta} (h : finish c observation = .ok out) :
    out.ownArm = c.ownArm := by
  classical
  unfold finish at h
  dsimp only at h
  cases hrecording : CoordinatorRecorderComplementBridge.run
      (recorderInput c observation) with
  | none => simp [hrecording] at h
  | some recorderOutput =>
      cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate
          r.payload r.pendingAtChoice c.sourceCutoff r.time row observation with
      | none => simp [hrecording, hconfirmation] at h
      | some pendingAfter =>
          simp [hrecording, hconfirmation] at h
          cases h
          rfl

/-- A recorder-domain failure remains distinct from a successful zero raw
arrival. -/
theorem finish_recorder_failure_iff {r : Registers p eta} {row : CompleteRow p}
    (c : Continuation r row) (observation : Fin (D p + 1)) :
    finish c observation = .error .recorderRejected ↔
      CoordinatorRecorderComplementBridge.run (recorderInput c observation) = none := by
  classical
  unfold finish
  dsimp only
  cases hrecording : CoordinatorRecorderComplementBridge.run
      (recorderInput c observation) with
  | none => simp
  | some recorderOutput =>
      cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate
          r.payload r.pendingAtChoice c.sourceCutoff r.time row observation with
      | none => simp
      | some pendingAfter => simp

/-- Confirmation rejection occurs only after a successful recorder result and
is distinct from the recorder's own checked-domain failure. -/
theorem finish_confirmation_failure_iff {r : Registers p eta}
    {row : CompleteRow p} (c : Continuation r row)
    (observation : Fin (D p + 1)) :
    finish c observation = .error .confirmationRejected ↔
      (∃ recorderOutput,
        CoordinatorRecorderComplementBridge.run (recorderInput c observation) =
          some recorderOutput) ∧
        CoordinatorLocalArmChoice.confirmationUpdate r.payload r.pendingAtChoice
          c.sourceCutoff r.time row observation = none := by
  classical
  unfold finish
  dsimp only
  cases hrecording : CoordinatorRecorderComplementBridge.run
      (recorderInput c observation) with
  | none => simp
  | some recorderOutput =>
      cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate
          r.payload r.pendingAtChoice c.sourceCutoff r.time row observation with
      | none => simp
      | some pendingAfter => simp

/-- Successful zero arrival is a real recorder output. It is not represented
by the failure branch of `finish`. -/
theorem finish_zero_arrival_is_success {r : Registers p eta}
    {row : CompleteRow p} (c : Continuation r row)
    (observation : Fin (D p + 1))
    {recorderOutput : CoordinatorRecordingOperation.Output p}
    {pendingAfter : Finset (ActiveRoundActions.Follower p.m)}
    (hrecorder : CoordinatorRecorderComplementBridge.run
      (recorderInput c observation) = some recorderOutput)
    (hzero : recorderOutput.rawArrival = 0)
    (hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate r.payload
      r.pendingAtChoice c.sourceCutoff r.time row observation = some pendingAfter) :
    ∃ out, finish c observation = .ok out ∧
      out.recorderOutput = recorderOutput ∧ out.pendingAfter = pendingAfter ∧
      out.recorderOutput.rawArrival = 0 := by
  let out : Output p eta := Output.mk r.priorClock c.startRoundResult r.payload
    r.time r.pendingAtChoice pendingAfter c.ownArm recorderOutput
  refine ⟨out, ?_, rfl, rfl, hzero⟩
  simp [finish, hrecorder, hconfirmation, out]

/-- The finish operation's recorder result is definitionally the accepted
recorder's raw checked output on the exact complement-extended input. -/
theorem finish_raw_output_eq_accepted {r : Registers p eta}
    {row : CompleteRow p} {c : Continuation r row}
    {observation : Fin (D p + 1)} {out : Output p eta}
    (h : finish c observation = .ok out) :
    CoordinatorRecordingOperation.run
      (CoordinatorRecorderComplementBridge.recorderInput
        (recorderInput c observation)) = some out.recorderOutput := by
  have hbridge := (finish_success_equations h).1
  simpa only [CoordinatorRecorderComplementBridge.run_eq_accepted] using hbridge

/-- On finish success the confirmation rule removes the selected pending
index exactly when the literal live DOWN, current-word hash, and positive-own-
feedback event occurs. -/
theorem finish_confirmation_removal_iff {r : Registers p eta}
    {row : CompleteRow p} {c : Continuation r row}
    {observation : Fin (D p + 1)} {out : Output p eta}
    (hfinish : finish c observation = .ok out) :
    let selected := PublicDiscreteDraws.selectedFollowerDraw p.two_le_m
      p.m_lt_K c.currentControl.1
    selected ∈ r.pendingAtChoice ∧ selected ∉ out.pendingAfter ↔
      CoordinatorLocalArmChoice.downConfirmationEvent r.payload r.pendingAtChoice
        c.sourceCutoff r.time c.currentControl observation := by
  dsimp only
  have hupdated := (finish_success_equations hfinish).2
  have hcurrent := c.currentControl_eq
  have hvalid := c.confirmationInputsValid
  let selected := PublicDiscreteDraws.selectedFollowerDraw p.two_le_m
    p.m_lt_K c.currentControl.1
  change selected ∈ r.pendingAtChoice ∧ selected ∉ out.pendingAfter ↔
    CoordinatorLocalArmChoice.downConfirmationEvent r.payload r.pendingAtChoice
      c.sourceCutoff r.time c.currentControl observation
  have hcore : CoordinatorLocalArmChoice.confirmationUpdateCore r.payload
      r.pendingAtChoice c.sourceCutoff r.time c.currentControl observation =
        some out.pendingAfter := by
    simpa [CoordinatorLocalArmChoice.confirmationUpdate, hcurrent] using hupdated
  by_cases hevent : CoordinatorLocalArmChoice.downConfirmationEvent r.payload
      r.pendingAtChoice c.sourceCutoff r.time c.currentControl observation
  · have hremove := CoordinatorLocalArmChoice.confirmationUpdateCore_removes
      r.payload r.pendingAtChoice c.sourceCutoff r.time c.currentControl
      observation hvalid hevent
    have hout : out.pendingAfter = r.pendingAtChoice.erase selected := by
      exact Option.some.inj (hcore.symm.trans hremove)
    have hmem : selected ∈ r.pendingAtChoice := hevent.2.2.2.1
    rw [hout]
    simp [hmem, hevent]
  · have hpreserve := CoordinatorLocalArmChoice.confirmationUpdateCore_preserves
      r.payload r.pendingAtChoice c.sourceCutoff r.time c.currentControl
      observation hvalid hevent
    have hout : out.pendingAfter = r.pendingAtChoice := by
      exact Option.some.inj (hcore.symm.trans hpreserve)
    rw [hout]
    simp [hevent]

/-- The typed own feedback is positive exactly when its denominator-`D`
integer coordinate is positive, as used by the literal confirmation test. -/
theorem finish_confirmation_positive_feedback_iff
    (observation : Fin (D p + 1)) :
    0 < CoordinatorLocalArmChoice.ownGridObservationValue observation ↔
      0 < observation.val :=
  CoordinatorLocalArmChoice.ownGridObservationValue_pos_iff observation

/-- If two complete rows have the same current control slice, the accepted
pre-choice arm is the same. No other time or row coordinate is consulted. -/
theorem prepare_arm_locality {r : Registers p eta} {row₁ row₂ : CompleteRow p}
    {c₁ : Continuation r row₁} {c₂ : Continuation r row₂}
    (_h₁ : prepare r row₁ = .ok c₁) (_h₂ : prepare r row₂ = .ok c₂)
    (hslice : row₁.2 r.time = row₂.2 r.time) : c₁.ownArm = c₂.ownArm := by
  have hchoice := CoordinatorLocalArmChoice.coordinatorArmChoice_eq_of_same_current_timeControl
    r.payload r.pendingAtChoice c₁.sourceCutoff r.time r.complementWeights
    row₁ row₂ hslice
  have h₁' : CoordinatorLocalArmChoice.coordinatorArmChoice r.payload
      r.pendingAtChoice c₁.sourceCutoff r.time r.complementWeights row₁ =
        some c₁.ownArm := by
    simpa [Continuation.sourceCutoff] using c₁.armChoice_eq
  have h₂' : CoordinatorLocalArmChoice.coordinatorArmChoice r.payload
      r.pendingAtChoice c₁.sourceCutoff r.time r.complementWeights row₂ =
        some c₂.ownArm := by
    simpa [Continuation.sourceCutoff] using c₂.armChoice_eq
  rw [h₁', h₂'] at hchoice
  exact Option.some.inj hchoice

/-- The complete checked recorder and confirmation outputs agree whenever the
current slice and own observation agree, for fixed retained registers. -/
theorem finish_current_slice_locality {r : Registers p eta}
    {row₁ row₂ : CompleteRow p}
    {c₁ : Continuation r row₁} {c₂ : Continuation r row₂}
    (h₁ : prepare r row₁ = .ok c₁) (h₂ : prepare r row₂ = .ok c₂)
    (hslice : row₁.2 r.time = row₂.2 r.time)
    (observation : Fin (D p + 1))
    (hout₁ : ∃ out₁, finish c₁ observation = .ok out₁)
    (hout₂ : ∃ out₂, finish c₂ observation = .ok out₂) :
    ∃ out₁ out₂, finish c₁ observation = .ok out₁ ∧
      finish c₂ observation = .ok out₂ ∧
      out₁.recorderOutput = out₂.recorderOutput ∧
      out₁.pendingAfter = out₂.pendingAfter ∧ out₁.ownArm = out₂.ownArm := by
  rcases hout₁ with ⟨out₁, hfinish₁⟩
  rcases hout₂ with ⟨out₂, hfinish₂⟩
  have harm : c₁.ownArm = c₂.ownArm :=
    prepare_arm_locality h₁ h₂ hslice
  have hrun₁ := (finish_success_equations hfinish₁).1
  have hrun₂ := (finish_success_equations hfinish₂).1
  have hlocal : CoordinatorRecorderComplementBridge.run
      (recorderInput c₁ observation) =
      CoordinatorRecorderComplementBridge.run (recorderInput c₂ observation) := by
    let base := CoordinatorRecorderComplementBridge.recorderInput
      (recorderInput c₁ observation)
    have hleftInput : CoordinatorRecorderComplementBridge.recorderInput
        (recorderInput c₁ observation) =
        CoordinatorRecordingMeasurability.inputAt base
          (row₁, (c₁.ownArm, observation)) := by
      rfl
    have hrightInput : CoordinatorRecorderComplementBridge.recorderInput
        (recorderInput c₂ observation) =
        CoordinatorRecordingMeasurability.inputAt base
          (row₂, (c₂.ownArm, observation)) := by
      dsimp [CoordinatorRecorderComplementBridge.recorderInput, recorderInput, base]
      rw [c₂.preChoiceMode_eq, c₁.preChoiceMode_eq]
      rfl
    have hsliceBase : row₁.2 base.time = row₂.2 base.time := by
      simpa [base, CoordinatorRecorderComplementBridge.recorderInput,
        CoordinatorRecorderComplementBridge.recorderInputWithWeights, recorderInput]
        using hslice
    have hrun := CoordinatorRecordingMeasurability.run_eq_of_current_slice_eq
      base (row₁, (c₁.ownArm, observation)) (row₂, (c₂.ownArm, observation))
      (by
        have hslice' := congrArg Prod.fst hsliceBase
        simpa [ContinuousLearningRows.sliceAt] using hslice')
      harm rfl
    have hleft := congrArg CoordinatorRecordingOperation.run hleftInput
    have hright := congrArg CoordinatorRecordingOperation.run hrightInput
    have hlocalAccepted := hleft.trans (hrun.trans hright.symm)
    simpa only [CoordinatorRecorderComplementBridge.run_eq_accepted] using
      hlocalAccepted
  have hrec : out₁.recorderOutput = out₂.recorderOutput := by
    apply Option.some.inj
    exact hrun₁.symm.trans (hlocal.trans hrun₂)
  have hconf := CoordinatorLocalArmChoice.confirmationUpdate_eq_of_same_current_timeControl
    r.payload r.pendingAtChoice c₁.sourceCutoff r.time row₁ row₂ observation hslice
  have hpending : out₁.pendingAfter = out₂.pendingAfter := by
    have hu₁ := (finish_success_equations hfinish₁).2
    have hu₂ := (finish_success_equations hfinish₂).2
    exact Option.some.inj (hu₁.symm.trans (hconf.trans hu₂))
  have hown : out₁.ownArm = out₂.ownArm :=
    (finish_success_arm hfinish₁).trans (harm.trans (finish_success_arm hfinish₂).symm)
  exact ⟨out₁, out₂, hfinish₁, hfinish₂, hrec, hpending, hown⟩

/-- A canonical positive typed observation used only to factor the confirmation
rule's dependence through the positivity bit. -/
private def positiveObservation (p : Parameters) : Fin (D p + 1) :=
  ⟨1, by have hD := D_pos p; omega⟩

private theorem positiveObservation_pos (p : Parameters) :
    0 < (positiveObservation p).val := by
  simp [positiveObservation]

/-- For fixed registers and current control, the confirmation update depends
on the typed observation only through its literal positive-feedback test. -/
theorem confirmationUpdate_eq_of_same_positive {r : Registers p eta}
    (row : CompleteRow p) (observation₁ observation₂ : Fin (D p + 1))
    (hpositive : (0 < observation₁.val) ↔ (0 < observation₂.val)) :
    CoordinatorLocalArmChoice.confirmationUpdate r.payload r.pendingAtChoice
      (cutoffFromClock p r.priorClock.u) r.time row observation₁ =
    CoordinatorLocalArmChoice.confirmationUpdate r.payload r.pendingAtChoice
      (cutoffFromClock p r.priorClock.u) r.time row observation₂ := by
  classical
  have hevent :
      CoordinatorLocalArmChoice.downConfirmationEvent r.payload r.pendingAtChoice
        (cutoffFromClock p r.priorClock.u) r.time (row.2 r.time) observation₁ ↔
      CoordinatorLocalArmChoice.downConfirmationEvent r.payload r.pendingAtChoice
        (cutoffFromClock p r.priorClock.u) r.time (row.2 r.time) observation₂ := by
    unfold CoordinatorLocalArmChoice.downConfirmationEvent
    constructor
    · rintro ⟨hlive, hnonempty, hslot, hmember, hhash, hfeedback⟩
      refine ⟨hlive, hnonempty, hslot, hmember, hhash, ?_⟩
      exact (CoordinatorLocalArmChoice.ownGridObservationValue_pos_iff
        observation₂).2 (hpositive.mp
          ((CoordinatorLocalArmChoice.ownGridObservationValue_pos_iff
            observation₁).1 hfeedback))
    · rintro ⟨hlive, hnonempty, hslot, hmember, hhash, hfeedback⟩
      refine ⟨hlive, hnonempty, hslot, hmember, hhash, ?_⟩
      exact (CoordinatorLocalArmChoice.ownGridObservationValue_pos_iff
        observation₁).2 (hpositive.mpr
          ((CoordinatorLocalArmChoice.ownGridObservationValue_pos_iff
            observation₂).1 hfeedback))
  by_cases hvalid : CoordinatorLocalArmChoice.ConfirmationInputsValid r.payload
      (cutoffFromClock p r.priorClock.u) r.time
  · simp [CoordinatorLocalArmChoice.confirmationUpdate,
      CoordinatorLocalArmChoice.confirmationUpdateCore, hvalid, hevent]
  · simp [CoordinatorLocalArmChoice.confirmationUpdate,
      CoordinatorLocalArmChoice.confirmationUpdateCore, hvalid]

/-- The observational projection of the checked prepare/finish flow. `none`
means a checked local failure; `some` retains the exact recorder output,
updated confirmation set, and pre-choice arm. -/
noncomputable def observedFlow (r : Registers p eta)
    (value : CompleteRow p × Fin (D p + 1)) :
    Option (CoordinatorRecordingOperation.Output p ×
      Finset (ActiveRoundActions.Follower p.m) × Fin p.K) :=
  match prepare r value.1 with
  | .error _ => none
  | .ok c =>
      match finish c value.2 with
      | .error _ => none
      | .ok out => some (out.recorderOutput, out.pendingAfter, out.ownArm)

/-- Exact bridge input produced after the arm has already been fixed. -/
noncomputable def flowRecorderInput (r : Registers p eta)
    (row : CompleteRow p) (arm : Fin p.K)
    (observation : Fin (D p + 1)) :
    CoordinatorRecorderComplementBridge.Input r.payload :=
  { currentWeights := r.complementWeights
    time := r.time
    gridBoundary := r.gridBoundary
    row := row
    ownArm := arm
    observation := observation
    mode := .live (decide (r.pendingAtChoice = ∅)) }

def zeroObservation (p : Parameters) : Fin (D p + 1) :=
  ⟨0, by have hD := D_pos p; omega⟩

def dummyCompleteRow (p : Parameters) : CompleteRow p :=
  ((fun _ _ => false), fun _ =>
    ((fun _ => ⟨0, by norm_num⟩), fun _ => (fun _ => 0, 0)))

/-- A fixed operation input used only to expose row and own arm/observation as
the measurable varying coordinates. Its replaced fields have no effect. -/
noncomputable def flowRecorderBase (r : Registers p eta) :
    CoordinatorRecordingOperation.Input p :=
  CoordinatorRecorderComplementBridge.recorderInput
    (flowRecorderInput r (dummyCompleteRow p) ⟨0, K_pos p⟩ (zeroObservation p))

/-- The already selected coordinator arm as a function of the complete row. -/
noncomputable def flowArmAt (r : Registers p eta) (row : CompleteRow p) : Fin p.K :=
  (CoordinatorLocalArmChoice.coordinatorArmChoice r.payload r.pendingAtChoice
    (cutoffFromClock p r.priorClock.u) r.time r.complementWeights row).getD
      ⟨0, K_pos p⟩

/-- The recorder result along the candidate complete-row/observation input. -/
noncomputable def flowRecorderAt (r : Registers p eta)
    (value : CompleteRow p × Fin (D p + 1)) :
    Option (CoordinatorRecordingOperation.Output p) :=
  CoordinatorRecordingOperation.run
    (CoordinatorRecordingMeasurability.inputAt (flowRecorderBase r)
      (value.1, (flowArmAt r value.1, value.2)))

/-- Confirmation is computed from the pre-choice pending set, current row,
and the separately supplied own observation. -/
noncomputable def flowConfirmationAt (r : Registers p eta)
    (value : CompleteRow p × Fin (D p + 1)) :
    Option (Finset (ActiveRoundActions.Follower p.m)) :=
  CoordinatorLocalArmChoice.confirmationUpdate r.payload r.pendingAtChoice
    (cutoffFromClock p r.priorClock.u) r.time value.1 value.2

/-- Measurability of the confirmation component in the complete current row
and own grid observation, with all incoming registers fixed. The factorization
uses only the accepted literal positivity test. -/
theorem measurable_flowConfirmationAt (r : Registers p eta) :
    Measurable (flowConfirmationAt r) := by
  classical
  let positive := positiveObservation p
  let zero := zeroObservation p
  let positiveRow : CompleteRow p →
      Option (Finset (ActiveRoundActions.Follower p.m)) := fun row =>
    CoordinatorLocalArmChoice.confirmationUpdate r.payload r.pendingAtChoice
      (cutoffFromClock p r.priorClock.u) r.time row positive
  let zeroRow : CompleteRow p →
      Option (Finset (ActiveRoundActions.Follower p.m)) := fun row =>
    CoordinatorLocalArmChoice.confirmationUpdate r.payload r.pendingAtChoice
      (cutoffFromClock p r.priorClock.u) r.time row zero
  have hpositiveRow : Measurable positiveRow := by
    simpa [positiveRow] using
      (CoordinatorLocalArmChoice.measurable_confirmationUpdate r.payload
        r.pendingAtChoice (cutoffFromClock p r.priorClock.u) r.time positive)
  have hzeroRow : Measurable zeroRow := by
    simpa [zeroRow] using
      (CoordinatorLocalArmChoice.measurable_confirmationUpdate r.payload
        r.pendingAtChoice (cutoffFromClock p r.priorClock.u) r.time zero)
  have hpositiveObs : MeasurableSet
      {value : CompleteRow p × Fin (D p + 1) | 0 < value.2.val} := by
    have hvalFin : Measurable (fun value : Fin (D p + 1) => value.val) :=
      measurable_of_finite _
    have hval : Measurable (fun value : CompleteRow p × Fin (D p + 1) =>
        value.2.val) := hvalFin.comp measurable_snd
    exact measurableSet_lt measurable_const hval
  have hpositiveMap : Measurable (fun value : CompleteRow p × Fin (D p + 1) =>
      positiveRow value.1) := hpositiveRow.comp measurable_fst
  have hzeroMap : Measurable (fun value : CompleteRow p × Fin (D p + 1) =>
      zeroRow value.1) := hzeroRow.comp measurable_fst
  have hfactored : Measurable (fun value : CompleteRow p × Fin (D p + 1) =>
      if 0 < value.2.val then positiveRow value.1 else zeroRow value.1) :=
    Measurable.ite hpositiveObs hpositiveMap hzeroMap
  have heq : flowConfirmationAt r = fun value : CompleteRow p × Fin (D p + 1) =>
      if 0 < value.2.val then positiveRow value.1 else zeroRow value.1 := by
    funext value
    by_cases hobs : 0 < value.2.val
    · have hsame := confirmationUpdate_eq_of_same_positive (r := r)
        value.1 value.2 positive
        (Iff.intro (fun _ => positiveObservation_pos p) (fun _ => hobs))
      simp [flowConfirmationAt, positiveRow, hobs, hsame]
    · have hzero : ¬ 0 < zero.val := by simp [zero, zeroObservation]
      have hsame : (0 < value.2.val) ↔ (0 < zero.val) := by
        constructor
        · exact False.elim ∘ hobs
        · exact False.elim ∘ hzero
      have heqzero := confirmationUpdate_eq_of_same_positive (r := r)
        value.1 value.2 zero hsame
      simp [flowConfirmationAt, zeroRow, hobs, heqzero]
  rw [heq]
  exact hfactored

/-- Pack raw recorder and confirmation results, preserving either failure. -/
def packFlowResult (value : Option (CoordinatorRecordingOperation.Output p) ×
    (Option (Finset (ActiveRoundActions.Follower p.m)) × Fin p.K)) :
    Option (CoordinatorRecordingOperation.Output p ×
      Finset (ActiveRoundActions.Follower p.m) × Fin p.K) :=
  match value.1, value.2.1 with
  | some recorderOutput, some pendingAfter =>
      some (recorderOutput, pendingAfter, value.2.2)
  | _, _ => none

/-- For registers satisfying the explicit preparation domain, the checked
flow is the accepted recorder run paired with the literal confirmation update
and the arm selected before observation. -/
theorem observedFlow_eq_packedRun {r : Registers p eta}
    (domain : PreparationDomain r)
    (value : CompleteRow p × Fin (D p + 1)) :
    observedFlow r value = packFlowResult
      (flowRecorderAt r value,
        (flowConfirmationAt r value, flowArmAt r value.1)) := by
  classical
  rcases prepare_success_of_domain domain value.1 with ⟨c, hprepare, _⟩
  have harmChoice : CoordinatorLocalArmChoice.coordinatorArmChoice r.payload
      r.pendingAtChoice (cutoffFromClock p r.priorClock.u) r.time
      r.complementWeights value.1 = some c.ownArm := c.armChoice_eq
  have harm : flowArmAt r value.1 = c.ownArm := by
    simp [flowArmAt, harmChoice]
  have hweights :
      CoordinatorRecorderComplementBridge.extendedCurrentWeights
        (flowRecorderInput r value.1 c.ownArm value.2) =
      CoordinatorRecorderComplementBridge.extendedCurrentWeights
        (flowRecorderInput r (dummyCompleteRow p) ⟨0, K_pos p⟩
          (zeroObservation p)) := by
    funext j
    by_cases hj : j ∈ r.payload.slowSet.val
    · rw [CoordinatorRecorderComplementBridge.extendedCurrentWeights_eq_anchor
        (flowRecorderInput r value.1 c.ownArm value.2) j hj,
        CoordinatorRecorderComplementBridge.extendedCurrentWeights_eq_anchor
          (flowRecorderInput r (dummyCompleteRow p) ⟨0, K_pos p⟩
            (zeroObservation p)) j hj]
    · let jFast : CanonicalFastSampling.FastArm r.payload.slowSet :=
        ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩⟩
      rw [CoordinatorRecorderComplementBridge.extendedCurrentWeights_eq_complement
        (flowRecorderInput r value.1 c.ownArm value.2) jFast,
        CoordinatorRecorderComplementBridge.extendedCurrentWeights_eq_complement
          (flowRecorderInput r (dummyCompleteRow p) ⟨0, K_pos p⟩
            (zeroObservation p)) jFast]
      rfl
  have hinput : CoordinatorRecorderComplementBridge.recorderInput
      (recorderInput c value.2) =
      CoordinatorRecordingMeasurability.inputAt (flowRecorderBase r)
        (value.1, (flowArmAt r value.1, value.2)) := by
    have hcInput : recorderInput c value.2 =
        flowRecorderInput r value.1 c.ownArm value.2 := by
      simp [recorderInput, flowRecorderInput, c.preChoiceMode_eq]
    rw [hcInput, harm]
    simp only [CoordinatorRecorderComplementBridge.recorderInput,
      CoordinatorRecorderComplementBridge.recorderInputWithWeights,
      CoordinatorRecordingMeasurability.inputAt, flowRecorderBase]
    rw [hweights]
    rfl
  have hrun : CoordinatorRecorderComplementBridge.run (recorderInput c value.2) =
      flowRecorderAt r value := by
    calc
      CoordinatorRecorderComplementBridge.run (recorderInput c value.2) =
          CoordinatorRecordingOperation.run
            (CoordinatorRecorderComplementBridge.recorderInput
              (recorderInput c value.2)) := by
        rw [CoordinatorRecorderComplementBridge.run_eq_accepted]
      _ = flowRecorderAt r value := by
        simpa [flowRecorderAt] using congrArg CoordinatorRecordingOperation.run hinput
  have hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate r.payload
      r.pendingAtChoice c.sourceCutoff r.time value.1 value.2 =
      flowConfirmationAt r value := rfl
  cases hrecording : flowRecorderAt r value with
  | none => simp [observedFlow, hprepare, finish, hrun, hrecording,
      packFlowResult]
  | some recorderOutput =>
      cases hpending : flowConfirmationAt r value with
      | none => simp [observedFlow, hprepare, finish, hrun, hconfirmation,
          hrecording, hpending, packFlowResult]
      | some pendingAfter =>
          simp [observedFlow, hprepare, finish, hrun, hconfirmation,
            hrecording, hpending, harm, packFlowResult]

/-- Measurability of the complete checked flow in the supplied complete row
and typed own observation for fixed registers satisfying `PreparationDomain`.
This is only a measurability statement; it gives no freshness or conditional
recording law. -/
theorem measurable_observedFlow {r : Registers p eta}
    (domain : PreparationDomain r) : Measurable (observedFlow r) := by
  classical
  have hchoice : Measurable
      (CoordinatorLocalArmChoice.coordinatorArmChoice r.payload r.pendingAtChoice
        (cutoffFromClock p r.priorClock.u) r.time r.complementWeights) :=
    CoordinatorLocalArmChoice.measurable_coordinatorArmChoice r.payload
      r.pendingAtChoice (cutoffFromClock p r.priorClock.u) r.time r.complementWeights
  have hget : Measurable (fun result : Option (Fin p.K) =>
      result.getD ⟨0, K_pos p⟩) := measurable_of_finite _
  have harm : Measurable (fun value : CompleteRow p × Fin (D p + 1) =>
      flowArmAt r value.1) := by
    change Measurable (fun value : CompleteRow p × Fin (D p + 1) =>
      (CoordinatorLocalArmChoice.coordinatorArmChoice r.payload r.pendingAtChoice
        (cutoffFromClock p r.priorClock.u) r.time r.complementWeights value.1).getD
          ⟨0, K_pos p⟩)
    exact (hget.comp hchoice).comp measurable_fst
  have hrecorder : Measurable (flowRecorderAt r) := by
    change Measurable (fun value : CompleteRow p × Fin (D p + 1) =>
      CoordinatorRecordingOperation.run
        (CoordinatorRecordingMeasurability.inputAt (flowRecorderBase r)
          (value.1, (flowArmAt r value.1, value.2))))
    exact (CoordinatorRecordingMeasurability.measurable_run (flowRecorderBase r)).comp
      (measurable_fst.prodMk (harm.prodMk measurable_snd))
  have hconfirmation : Measurable (flowConfirmationAt r) :=
    measurable_flowConfirmationAt r
  have hjoint : Measurable (fun value : CompleteRow p × Fin (D p + 1) =>
      (flowRecorderAt r value, (flowConfirmationAt r value, flowArmAt r value.1))) :=
    hrecorder.prodMk (hconfirmation.prodMk harm)
  have hpack : Measurable (packFlowResult (p := p)) := measurable_of_finite _
  have heq : observedFlow r = fun value =>
      packFlowResult (flowRecorderAt r value,
        (flowConfirmationAt r value, flowArmAt r value.1)) := by
    funext value
    exact observedFlow_eq_packedRun domain value
  rw [heq]
  exact hpack.comp hjoint

end Bandits.Support.CoordinatorLiveChoiceRecorderStep

end
