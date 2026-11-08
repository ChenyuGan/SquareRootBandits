/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public import Bandits.Support.FirstAssignmentLaunch
public import Bandits.Support.AssignmentStartPayload
public import Bandits.Support.LaterAssignmentStartOperation
public import Bandits.Support.AssignmentScoreReconstruction
public import Bandits.Support.CoordinatorPhaseClock
public import Bandits.Support.CoordinatorLiveChoiceRecorderStep
public import Bandits.Support.CoordinatorLiveServiceFinish

/-!
# Coordinator assignment register installation

This module installs the results of the existing first and later assignment
constructors into the existing live coordinator register carriers. It does
not choose an arm or run `StartRound` again.

The first case derives its checked first `StartRound` result from the accepted
initial-clock equation. The later case consumes an actual
`LaterAssignmentStartOperation.SuccessfulStart` and an explicit record of the
original successful `StartRound` call, including its local domain checks and
matching assignment instruction.

Sources: `sources/zip4/manuscript/06_interruptions.tex:37-61,123-189` and
`sources/zip4/manuscript/05_binary_transport.tex:62-70`.

These are internal local installations. They make no physical-run,
measurability, dispatch, or manuscript-closure claim. The future round
dispatcher must call the original clock operation once, pass its actual
result here, and then continue directly to the local arm-choice operation.
-/

@[expose] public section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.AssignmentStartPayload
open Bandits.Support.AssignmentScoreReconstruction

namespace Bandits.Support.CoordinatorAssignmentRegisterInstall

/-- The accepted constructor parameter bundle. -/
abbrev Parameters := ConstructorDimensions.Parameters
/-- The source learning-rate subtype used by the local assignment APIs. -/
abbrev LearningRate := ReferencePrelaunchFollower.LearningRate

variable {p : Parameters} {eta : LearningRate}

/-- The source proposal hazard is valid for a first launch from its actual
learning-rate cap. -/
theorem first_proposal_parameter_valid
    (s : FirstAssignmentLaunch.Input p eta) :
    CoordinatorPhaseClock.proposalParameterValid p eta.val := by
  have hmPos : 0 < (p.m : ℝ) := by
    exact_mod_cast ConstructorDimensions.m_pos p
  have hKle : (1 : ℝ) ≤ (p.K : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.K_pos p)
  have hKpos : 0 < (p.K : ℝ) := lt_of_lt_of_le (by norm_num) hKle
  have hLle : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast CanonicalRecordingRates.L_stab_ge_one p
  have hLpos : 0 < (CanonicalRecordingRates.L_stab p : ℝ) :=
    lt_of_lt_of_le (by norm_num) hLle
  have hKL : (1 : ℝ) ≤ (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) := by
    calc
      1 ≤ (p.K : ℝ) := hKle
      _ = (p.K : ℝ) * 1 := by ring
      _ ≤ (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) :=
        mul_le_mul_of_nonneg_left hLle hKpos.le
  have hmKL : (p.m : ℝ) ≤ (p.m : ℝ) *
      ((p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ)) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hKL hmPos.le
  have hden : 4 * (p.m : ℝ) ≤
      1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ) := by
    calc
      4 * (p.m : ℝ) ≤ 1024 * (p.m : ℝ) := by nlinarith [hmPos]
      _ ≤ 1024 * ((p.m : ℝ) *
          ((p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ))) := by
        have hmul := mul_le_mul_of_nonneg_left hmKL
          (by norm_num : 0 ≤ (1024 : ℝ))
        nlinarith [hmul]
      _ = 1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ) := by ring
  have hdenPos : 0 < 1024 * (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact mul_pos (mul_pos (mul_pos (by norm_num) hmPos) hKpos) hLpos
  have hhazard : 4 * (p.m : ℝ) * eta.val ≤ 1 := by
    have hcap : eta.val ≤
        (1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ))⁻¹ := by
      simpa only [one_div] using s.eta_le_source_cap
    calc
      4 * (p.m : ℝ) * eta.val ≤
          (4 * (p.m : ℝ)) /
            (1024 * (p.m : ℝ) * (p.K : ℝ) *
              (CanonicalRecordingRates.L_stab p : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hcap
          (by positivity)
      _ ≤ 1 := (div_le_iff₀ hdenPos).2 (by simpa only [one_mul] using hden)
  refine ⟨eta.property, ?_, hhazard⟩
  unfold FollowerCutoffScan.proposalHazard
  exact mul_pos (mul_pos (by norm_num) hmPos) eta.property

/-- The first start's clipped source boundary passes the checked clock domain. -/
theorem first_new_grid_boundary_valid
    (s : FirstAssignmentLaunch.Input p eta) :
    CoordinatorPhaseClock.newGridBoundaryValid p s.sigma
      (FollowerCutoffScan.gridBoundary p eta.val s.sigma) := by
  have h := FollowerCutoffScan.gridBoundary_bounds p eta.val eta.property
    s.eta_le_source_cap s.sigma
  simpa [CoordinatorPhaseClock.newGridBoundaryValid,
    FollowerCutoffScan.calendarRound] using h

/-- The actual checked first assignment result of the accepted `StartRound`
initial-clock equation. -/
noncomputable def firstStartRoundResult
    (s : FirstAssignmentLaunch.Input p eta) :
    CoordinatorPhaseClock.StartRoundResult p := {
  clock := {
    sigma := some s.sigma
    u := none
    g := FollowerCutoffScan.gridBoundary p eta.val s.sigma
    lastProposal := none
  }
  gridDomain := by
    simpa [CoordinatorPhaseClock.clockGridDomain,
      CoordinatorPhaseClock.newGridBoundaryValid,
      FollowerCutoffScan.calendarRound] using first_new_grid_boundary_valid s
  pending := Finset.univ
  ledgerCommand := none
  assignmentStart := some ⟨s.sigma, .first⟩
}

/-- The constructed first clock result is the result of one actual accepted
initial `StartRound` call. -/
theorem first_start_round_success
    (s : FirstAssignmentLaunch.Input p eta) :
    CoordinatorPhaseClock.startRound p eta.val s.sigma
      (CoordinatorPhaseClock.initialClock p) Finset.univ =
        .ok (firstStartRoundResult s) := by
  simpa [firstStartRoundResult] using
    CoordinatorPhaseClock.startRound_initial p eta.val s.sigma Finset.univ
      (first_proposal_parameter_valid s) (first_new_grid_boundary_valid s)

/-- Literal first-start coordinator registers on the selected slow set's
actual complement. -/
noncomputable def firstRegisters
    (s : FirstAssignmentLaunch.Input p eta) :
    CoordinatorLiveChoiceRecorderStep.Registers p eta := {
  payload := AssignmentStartPayload.Input.ofFirstAssignment s
  priorClock := (firstStartRoundResult s).clock
  pendingAtChoice := Finset.univ
  time := s.sigma
  gridBoundary := FollowerCutoffScan.gridBoundary p eta.val s.sigma
  complementScores := fun _ => 0
}

/-- The first-start installation retains the actual start and its derived
clock result while constructing the existing register carriers. -/
structure FirstInstallation (s : FirstAssignmentLaunch.Input p eta) where
  start : FirstAssignmentLaunch.Start p eta
  start_eq : start = s.start
  startRoundResult : CoordinatorPhaseClock.StartRoundResult p
  startRound_eq : CoordinatorPhaseClock.startRound p eta.val s.sigma
    (CoordinatorPhaseClock.initialClock p) Finset.univ = .ok startRoundResult
  registers : CoordinatorLiveChoiceRecorderStep.Registers p eta
  ownedRegisters : CoordinatorLiveServiceFinish.OwnedRegisters registers
  followerBaseScore : ActiveRoundActions.Follower p.m → ℕ

/-- Install the literal first assignment into the existing live registers. -/
noncomputable def installFirst
    (s : FirstAssignmentLaunch.Input p eta) : FirstInstallation s := {
  start := s.start
  start_eq := rfl
  startRoundResult := firstStartRoundResult s
  startRound_eq := first_start_round_success s
  registers := firstRegisters s
  ownedRegisters := {
    queue := fun _ => 0
    previousService := fun _ => 0
  }
  followerBaseScore := fun _ => 0
}

/-- The first installed payload is the accepted specialization of its actual
first-launch input. -/
theorem first_registers_payload
    (s : FirstAssignmentLaunch.Input p eta) :
    (installFirst s).registers.payload =
      AssignmentStartPayload.Input.ofFirstAssignment s := rfl

/-- The installed first clock is the clock returned by the checked start. -/
theorem first_registers_clock
    (s : FirstAssignmentLaunch.Input p eta) :
    (installFirst s).registers.priorClock =
      (firstStartRoundResult s).clock := rfl

/-- The first register time is the actual first-start coordinate. -/
theorem first_registers_time
    (s : FirstAssignmentLaunch.Input p eta) :
    (installFirst s).registers.time = s.start.sigma := rfl

/-- The first register boundary is the checked boundary for its start time. -/
theorem first_registers_grid_boundary
    (s : FirstAssignmentLaunch.Input p eta) :
    (installFirst s).registers.gridBoundary =
      FollowerCutoffScan.gridBoundary p eta.val s.sigma := rfl

/-- Every follower is pending immediately after the first assignment start. -/
theorem first_registers_pending
    (s : FirstAssignmentLaunch.Input p eta) :
    (installFirst s).registers.pendingAtChoice = Finset.univ := rfl

/-- The first installation initializes each owned complement score to zero. -/
theorem first_registers_complement_scores
    (s : FirstAssignmentLaunch.Input p eta)
    (j : CanonicalFastSampling.FastArm s.start.slowSet) :
    (installFirst s).registers.complementScores j = 0 := rfl

/-- The first installation initializes each owned complement queue to zero. -/
theorem first_owned_queue
    (s : FirstAssignmentLaunch.Input p eta)
    (j : CanonicalFastSampling.FastArm s.start.slowSet) :
    (installFirst s).ownedRegisters.queue j = 0 := rfl

/-- The first installation initializes each owned previous service to zero. -/
theorem first_owned_previous_service
    (s : FirstAssignmentLaunch.Input p eta)
    (j : CanonicalFastSampling.FastArm s.start.slowSet) :
    (installFirst s).ownedRegisters.previousService j = 0 := rfl

/-- Each retained first-start follower base score is zero. -/
theorem first_follower_base_score
    (s : FirstAssignmentLaunch.Input p eta)
    (i : ActiveRoundActions.Follower p.m) :
    (installFirst s).followerBaseScore i = 0 := rfl

/-- First retained follower scores agree with the actual start's base scores. -/
theorem first_follower_base_score_eq_start
    (s : FirstAssignmentLaunch.Input p eta)
    (i : ActiveRoundActions.Follower p.m) :
    (installFirst s).followerBaseScore i =
      s.start.baseScores (s.start.assignment.assigned i) := by
  rw [s.start_baseScores_zero]
  rfl

/-- The first payload preserves the full actual assigned-arm map. -/
theorem first_payload_assignment_eq_start
    (s : FirstAssignmentLaunch.Input p eta) :
    (installFirst s).registers.payload.assignment.assigned =
      s.start.assignment.assigned :=
  AssignmentStartPayload.Input.assignment_map_eq_first_start s

/-- The first payload retains the actual first-start anchor vector. -/
theorem first_payload_anchor_eq_start
    (s : FirstAssignmentLaunch.Input p eta) :
    (installFirst s).registers.payload.anchor = s.start.anchor :=
  AssignmentStartPayload.Input.anchor_eq_first_start s

/-- The first payload's anchor is one at every arm. -/
theorem first_payload_anchor_one
    (s : FirstAssignmentLaunch.Input p eta) (a : Fin p.K) :
    (installFirst s).registers.payload.anchor a = 1 := by
  rw [first_payload_anchor_eq_start]
  exact FirstAssignmentLaunch.Input.start_anchor_one s a

/-- The actual first start's current weights are all one. -/
theorem first_start_weight_one
    (s : FirstAssignmentLaunch.Input p eta) (a : Fin p.K) :
    s.start.weights a = 1 :=
  s.start_weights_one a

/-- The actual first start's frozen anchor is all ones. -/
theorem first_start_anchor_one
    (s : FirstAssignmentLaunch.Input p eta) (a : Fin p.K) :
    s.start.anchor a = 1 :=
  s.start_anchor_one a

/-- The specialized first payload keeps every actual recording rate. -/
theorem first_payload_rate_eq_start
    (s : FirstAssignmentLaunch.Input p eta) (a : Fin p.K) :
    (installFirst s).registers.payload.rate a = s.start.recordingRates a :=
  AssignmentStartPayload.Input.rate_eq_first_start s a

/-- The specialized exponent on each assigned arm is its actual first exponent. -/
theorem first_payload_exponent_eq_start
    (s : FirstAssignmentLaunch.Input p eta)
    (i : ActiveRoundActions.Follower p.m) :
    (installFirst s).registers.payload.exponent
        (s.start.assignment.assigned i) = s.exponent i := by
  exact AssignmentStartPayload.Input.exponent_eq_first s i

/-- The first payload retains the actual auxiliary arm. -/
theorem first_payload_auxiliary_eq_start
    (s : FirstAssignmentLaunch.Input p eta) :
    (installFirst s).registers.payload.assignment.auxiliary =
      s.start.assignment.auxiliary :=
  AssignmentStartPayload.Input.assignment_auxiliary_eq_first_start s

/-- The specialized first payload keeps the actual all-zero queues. -/
theorem first_payload_queues_eq_start
    (s : FirstAssignmentLaunch.Input p eta) :
    (installFirst s).registers.payload.queues = s.start.queues :=
  AssignmentStartPayload.Input.queues_eq_first_start s

/-- The installation retains the original complete `K + 1` input vector. -/
theorem first_start_coordinates
    (s : FirstAssignmentLaunch.Input p eta) :
    (installFirst s).start.coordinates = s.coordinates := by
  rw [(installFirst s).start_eq]
  exact s.start_coordinates

/-- Zero first complement scores induce unit current complement weights. -/
theorem first_complementWeight_one
    (s : FirstAssignmentLaunch.Input p eta)
    (j : CanonicalFastSampling.FastArm s.start.slowSet) :
    (installFirst s).registers.complementWeights j = 1 := by
  simp [CoordinatorLiveChoiceRecorderStep.Registers.complementWeights,
    firstRegisters, installFirst, ScoreWeights.scoreWeight]

/-- The first payload reuses each actual outgoing DOWN record. -/
theorem first_payload_down_record_eq_start
    (s : FirstAssignmentLaunch.Input p eta)
    (i : ActiveRoundActions.Follower p.m) :
    (installFirst s).registers.payload.downRecord i = s.start.outgoing i :=
  AssignmentStartPayload.Input.downRecord_eq_first_start s i

/-- The first payload reuses each actual encoded DOWN word. -/
theorem first_payload_down_word_eq_start
    (s : FirstAssignmentLaunch.Input p eta)
    (i : ActiveRoundActions.Follower p.m) :
    (installFirst s).registers.payload.downWord i = s.start.outgoingWords i :=
  AssignmentStartPayload.Input.downWord_eq_first_start s i

/-- Evidence that a later assignment result is paired with the exact original
successful `StartRound` result that supplied its instruction. All old-clock,
boundary, proposal, time, and call inputs remain visible to the caller. -/
structure LaterStartRoundEvidence
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row) where
  priorClock : CoordinatorPhaseClock.ClockRegisters p
  pending : Finset (Fin (p.m - 1))
  proposalParameterValid :
    CoordinatorPhaseClock.proposalParameterValid p eta.val
  priorClockValid :
    CoordinatorPhaseClock.clockRegistersValid p eta.val priorClock
  startTimeValid : CoordinatorPhaseClock.startRoundTimeValid p
    instruction.time priorClock
  result : CoordinatorPhaseClock.StartRoundResult p
  startRound_eq : CoordinatorPhaseClock.startRound p eta.val instruction.time
    priorClock pending = .ok result
  assignmentStart_eq : result.assignmentStart = some instruction
  priorSigma_eq : priorClock.sigma = some old.sigma
  priorGrid_eq_freezeAt : priorClock.g = output.localConsistency.oldFreezeAt

/-- An installation retains the actual successful later constructor's
complete sample vector and reconstruction. -/
structure LaterInstallation
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output) where
  registers : CoordinatorLiveChoiceRecorderStep.Registers p eta
  ownedRegisters : CoordinatorLiveServiceFinish.OwnedRegisters registers
  retainedBaseScore : ActiveRoundActions.Follower p.m → ℕ
  assignmentVector : CheckedAssignmentSample.AssignmentVector p
  reconstruction : AssignmentScoreReconstruction.ReconstructedStart ledger
    instruction

/-- Install the actual later assignment result on the complement of its new
payload's slow set. The score and queue coordinates come directly from the
checked reconstruction; previous service comes from its complete current
register vector. -/
noncomputable def installLater
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output) :
    LaterInstallation output clockData := {
  registers := {
    payload := output.payload
    priorClock := clockData.result.clock
    pendingAtChoice := clockData.result.pending
    time := instruction.time
    gridBoundary := clockData.result.clock.g
    complementScores := fun j =>
      AssignmentScoreReconstruction.sourceScore output.reconstruction j.1
  }
  ownedRegisters := {
    queue := fun j =>
      AssignmentScoreReconstruction.initialQueue output.reconstruction j.1
    previousService := fun j =>
      (output.reconstruction.registers.current j.1).lastService
  }
  retainedBaseScore := output.baseScore
  assignmentVector := output.assignmentVector
  reconstruction := output.reconstruction
}

/-- The source `StartRound` equations give the exact new-start frame and
classify the same instruction consumed by the later successful constructor. -/
theorem later_start_round_compatibility
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output) :
    instruction.kind = CoordinatorPhaseClock.classifyAssignmentStart
      clockData.priorClock.sigma instruction.time clockData.priorClock.g ∧
    clockData.result.clock.sigma = some instruction.time ∧
    clockData.result.clock.u = none ∧
    clockData.result.clock.g =
      FollowerCutoffScan.gridBoundary p eta.val instruction.time ∧
    clockData.result.clock.lastProposal = clockData.priorClock.lastProposal ∧
    clockData.result.pending = Finset.univ ∧
    clockData.result.ledgerCommand = none ∧
    CoordinatorPhaseClock.classifyAssignmentStart clockData.priorClock.sigma
      instruction.time clockData.priorClock.g =
        AssignmentScoreReconstruction.expectedLaterStartKind
          output.localConsistency.oldFreezeAt instruction.time ∧
    instruction.kind = AssignmentScoreReconstruction.expectedLaterStartKind
      output.localConsistency.oldFreezeAt instruction.time := by
  have hclock := CoordinatorPhaseClock.startRound_assignment_effect
    p eta.val instruction.time clockData.priorClock clockData.pending
    clockData.result instruction clockData.proposalParameterValid
    clockData.priorClockValid clockData.startTimeValid
    clockData.startRound_eq clockData.assignmentStart_eq
  rcases hclock with
    ⟨_, hkind, hσ, hu, hg, hproposal, hpending, hledger⟩
  have hreconstruction :=
    AssignmentScoreReconstruction.reconstructLaterStart_success_equations
      ledger instruction output.reconstruction output.reconstruction_eq
  rcases hreconstruction with ⟨hchecks, _, _, _, _, _, _, _, _, _, _⟩
  rcases hchecks with ⟨_, _, _, _, hkindExpected, _, _⟩
  have hclassifier :
      CoordinatorPhaseClock.classifyAssignmentStart clockData.priorClock.sigma
          instruction.time clockData.priorClock.g =
        AssignmentScoreReconstruction.expectedLaterStartKind
          output.localConsistency.oldFreezeAt instruction.time := by
    rw [clockData.priorSigma_eq, clockData.priorGrid_eq_freezeAt]
    by_cases hbefore : instruction.time.val + 1 <
        output.localConsistency.oldFreezeAt
    · have hnot : ¬ output.localConsistency.oldFreezeAt ≤
          instruction.time.val + 1 := by omega
      simp [CoordinatorPhaseClock.classifyAssignmentStart,
        AssignmentScoreReconstruction.expectedLaterStartKind,
        FollowerCutoffScan.calendarRound, hbefore, hnot]
    · have hafter : output.localConsistency.oldFreezeAt ≤
          instruction.time.val + 1 := by omega
      simp [CoordinatorPhaseClock.classifyAssignmentStart,
        AssignmentScoreReconstruction.expectedLaterStartKind,
        FollowerCutoffScan.calendarRound, hbefore, hafter]
  have hkindExpectedOld : instruction.kind =
      AssignmentScoreReconstruction.expectedLaterStartKind
        output.localConsistency.oldFreezeAt instruction.time := by
    rw [output.localConsistency.oldFreezeAt_eq]
    exact hkindExpected
  exact ⟨hkind, hσ, hu, hg, hproposal, hpending, hledger,
    hclassifier, hkindExpectedOld⟩

/-- The later installed payload is the exact successful constructor payload. -/
theorem later_registers_payload
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output) :
    (installLater output clockData).registers.payload = output.payload := rfl

/-- The later registers retain the clock from the original successful call. -/
theorem later_registers_clock
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output) :
    (installLater output clockData).registers.priorClock =
      clockData.result.clock := rfl

/-- The later register time is the actual assignment instruction time. -/
theorem later_registers_time
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output) :
    (installLater output clockData).registers.time = instruction.time := rfl

/-- The later register boundary is the boundary carried by the returned clock. -/
theorem later_registers_grid_boundary
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output) :
    (installLater output clockData).registers.gridBoundary =
      clockData.result.clock.g := rfl

/-- The later registers retain the pending set from the original call. -/
theorem later_registers_pending
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output) :
    (installLater output clockData).registers.pendingAtChoice =
      clockData.result.pending := rfl

/-- The accepted assignment branch resets the actual pending set to all
followers. -/
theorem later_registers_pending_full
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output) :
    (installLater output clockData).registers.pendingAtChoice = Finset.univ := by
  rw [later_registers_pending]
  rcases later_start_round_compatibility output clockData with
    ⟨_, _, _, _, _, hpending, _, _, _⟩
  exact hpending

/-- Each new complement score is the reconstruction's source score at that
arm. -/
theorem later_complement_score_eq_source_score
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output)
    (j : CanonicalFastSampling.FastArm output.payload.slowSet) :
    (installLater output clockData).registers.complementScores j =
      AssignmentScoreReconstruction.sourceScore output.reconstruction j.1 := rfl

/-- Each new complement queue is the reconstruction's initial queue. -/
theorem later_owned_queue_eq_initial_queue
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output)
    (j : CanonicalFastSampling.FastArm output.payload.slowSet) :
    (installLater output clockData).ownedRegisters.queue j =
      AssignmentScoreReconstruction.initialQueue output.reconstruction j.1 := rfl

/-- Previous service is restricted from the complete current-register vector. -/
theorem later_owned_previous_service_eq_current_register
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output)
    (j : CanonicalFastSampling.FastArm output.payload.slowSet) :
    (installLater output clockData).ownedRegisters.previousService j =
      (output.reconstruction.registers.current j.1).lastService := rfl

/-- The installed complement score equation follows from the checked
reconstruction equations. -/
theorem later_reconstruction_score_check
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output)
    (j : CanonicalFastSampling.FastArm output.payload.slowSet) :
    (installLater output clockData).registers.complementScores j =
      (output.reconstruction.registers.cutoff j.1).score + ledger.increment j.1 := by
  have hequations :=
    AssignmentScoreReconstruction.reconstructLaterStart_success_equations
      ledger instruction output.reconstruction output.reconstruction_eq
  rcases hequations with ⟨_, _, _, hscore, _, _, _, _, _, _, _⟩
  rw [later_complement_score_eq_source_score]
  exact hscore j.1

/-- The installed queue equation follows from the checked reconstruction
equations. -/
theorem later_reconstruction_queue_check
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output)
    (j : CanonicalFastSampling.FastArm output.payload.slowSet) :
    (installLater output clockData).ownedRegisters.queue j =
      (output.reconstruction.registers.current j.1).queue := by
  have hequations :=
    AssignmentScoreReconstruction.reconstructLaterStart_success_equations
      ledger instruction output.reconstruction output.reconstruction_eq
  rcases hequations with ⟨_, _, _, _, hqueue, _, _, _, _, _, _⟩
  rw [later_owned_queue_eq_initial_queue]
  exact hqueue j.1

/-- Every current register used by installation is the actual checked ledger
entry. -/
theorem later_current_register_eq_ledger
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (_clockData : LaterStartRoundEvidence output) (a : Fin p.K) :
    ledger.currentRegisters a = some (output.reconstruction.registers.current a) := by
  have hequations :=
    AssignmentScoreReconstruction.reconstructLaterStart_success_equations
      ledger instruction output.reconstruction output.reconstruction_eq
  rcases hequations with ⟨_, _, hcurrent, _, _, _, _, _, _, _, _⟩
  exact hcurrent a

/-- Newly assigned followers retain the successful constructor's exact base
scores. -/
theorem later_retained_base_score_eq_source
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output)
    (i : ActiveRoundActions.Follower p.m) :
    (installLater output clockData).retainedBaseScore i =
      AssignmentScoreReconstruction.sourceScore output.reconstruction
        (output.payload.assignment.assigned i) := by
  exact output.baseScore_eq_source i

/-- The full assignment vector is retained without changing any coordinate. -/
theorem later_assignment_vector_eq_source
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output) :
    (installLater output clockData).assignmentVector = output.assignmentVector := rfl

/-- The actual checked reconstruction is retained unchanged. -/
theorem later_reconstruction_eq_source
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output) :
    (installLater output clockData).reconstruction = output.reconstruction := rfl

/-- Each later outgoing DOWN record is the record in the exact installed
payload. -/
theorem later_payload_down_record_eq_source
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output)
    (i : ActiveRoundActions.Follower p.m) :
    (installLater output clockData).registers.payload.downRecord i =
      output.payload.downRecord i := rfl

/-- Each later outgoing DOWN word is the word in the exact installed payload. -/
theorem later_payload_down_word_eq_source
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output)
    (i : ActiveRoundActions.Follower p.m) :
    (installLater output clockData).registers.payload.downWord i =
      output.payload.downWord i := rfl

/-- The installation retains the original vector, projection, and checked
sampler result. -/
theorem later_sample_is_preserved
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output) :
    (installLater output clockData).assignmentVector = output.assignmentVector ∧
      output.assignmentVector = LaterAssignmentStartOperation.ownAssignmentVector
        row instruction.time ∧
      CheckedAssignmentSample.checkedAssignmentSample p output.law.mass
        output.law.anchor output.assignmentVector = .sampled output.outcome := by
  exact ⟨rfl, output.assignmentVector_eq_row_projection,
    output.checkedSample_eq⟩

private theorem allFin_apply_true {length : ℕ}
    {test : Fin length → Bool}
    (h : CoordinatorCollectionLedger.allFin length test = true)
    (i : Fin length) : test i = true := by
  unfold CoordinatorCollectionLedger.allFin at h
  rw [List.all_eq_true] at h
  exact h (test i) (List.mem_ofFn.mpr ⟨i, rfl⟩)

/-- The current-register last-service bound follows from the actual successful
reconstruction's valid-ledger and register-domain checks. -/
theorem current_register_last_service_le_of_success
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row) (a : Fin p.K) :
    (output.reconstruction.registers.current a).lastService ≤ D p := by
  have hequations :=
    AssignmentScoreReconstruction.reconstructLaterStart_success_equations
      ledger instruction output.reconstruction output.reconstruction_eq
  rcases hequations with
    ⟨hchecks, _, hcurrent, _, _, _, _, _, _, _, _⟩
  rcases hchecks with ⟨hvalid, _, _, _, _, _, _⟩
  have hledger := hvalid
  simp only [CoordinatorCollectionLedger.validLedgerCheck,
    Bool.and_eq_true] at hledger
  rcases hledger with ⟨hprefix, _⟩
  rcases hprefix with ⟨_, hregisterDomains⟩
  have hcurrentDomains :
      CoordinatorCollectionLedger.allFin p.K (fun b : Fin p.K =>
        match ledger.currentRegisters b with
        | none => true
        | some r => decide (r.queue ≤ p.T * D p) &&
            decide (r.lastService ≤ D p)) = true := by
    have h := hregisterDomains
    simp only [CoordinatorCollectionLedger.registerDomainsCheck,
      Bool.and_eq_true] at h
    exact h.1.1.1.1
  have hentry := allFin_apply_true hcurrentDomains a
  rw [hcurrent a] at hentry
  simp only [Bool.and_eq_true] at hentry
  exact of_decide_eq_true hentry.2

/-- Score, queue, and previous-service domains follow from actual reconstruction
checks. -/
theorem later_register_domains
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output) :
    (installLater output clockData).registers.scoreDomainValid ∧
      (installLater output clockData).ownedRegisters.queueDomainValid ∧
      (installLater output clockData).ownedRegisters.previousServiceDomainValid := by
  have hequations :=
    AssignmentScoreReconstruction.reconstructLaterStart_success_equations
      ledger instruction output.reconstruction output.reconstruction_eq
  rcases hequations with
    ⟨_, _, _, _, _, _, _, _, _, hscoreLe, hqueueLe⟩
  refine ⟨?_, ?_, ?_⟩
  · intro j
    exact hscoreLe j.1
  · intro j
    exact hqueueLe j.1
  · intro j
    exact current_register_last_service_le_of_success output j.1

/-- The exact payload queues agree with the reconstruction on all arms. -/
theorem later_payload_queue_eq_initial_queue
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output)
    (a : Fin p.K) :
    (installLater output clockData).registers.payload.queues a =
      AssignmentScoreReconstruction.initialQueue output.reconstruction a := by
  rw [later_registers_payload]
  exact output.payload_queues a

/-- A corrected later start retains the old payload's anchor. -/
theorem later_payload_anchor_corrected
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output)
    (hcorrected : instruction.kind = .corrected) :
    (installLater output clockData).registers.payload.anchor = old.anchor := by
  rcases LaterAssignmentStartOperation.successful_corrected_law_spec
      output hcorrected with
    ⟨_, _, _, _, hanchor, _⟩
  rw [later_registers_payload]
  exact hanchor

/-- A renewal later start installs the current reconstructed weight as anchor. -/
theorem later_payload_anchor_renewal
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output)
    (hrenewal : instruction.kind = .renewal) :
    (installLater output clockData).registers.payload.anchor =
      AssignmentScoreReconstruction.currentWeight output.reconstruction := by
  rcases LaterAssignmentStartOperation.successful_renewal_law_spec
      output hrenewal with
    ⟨_, hanchor, _⟩
  rw [later_registers_payload]
  exact hanchor

/-- The accepted start-round classification and the successful reconstruction
agree on a corrected start before the retained freeze boundary. -/
theorem later_corrected_branch
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output)
    (hcorrected : instruction.kind = .corrected) :
    instruction.time.val + 1 < output.localConsistency.oldFreezeAt ∧
      instruction.kind = CoordinatorPhaseClock.classifyAssignmentStart
        clockData.priorClock.sigma instruction.time clockData.priorClock.g ∧
      (installLater output clockData).registers.payload.anchor = old.anchor := by
  have hcompat := later_start_round_compatibility output clockData
  rcases LaterAssignmentStartOperation.successful_corrected_law_spec
      output hcorrected with
    ⟨hbefore, _, _, _, hanchor, _⟩
  exact ⟨hbefore, hcompat.1, by
    rw [later_registers_payload]
    exact hanchor⟩

/-- The accepted start-round classification and the successful reconstruction
agree on renewal at or after the retained freeze boundary. -/
theorem later_renewal_branch
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row)
    (clockData : LaterStartRoundEvidence output)
    (hrenewal : instruction.kind = .renewal) :
    output.localConsistency.oldFreezeAt ≤ instruction.time.val + 1 ∧
      instruction.kind = CoordinatorPhaseClock.classifyAssignmentStart
        clockData.priorClock.sigma instruction.time clockData.priorClock.g ∧
      (installLater output clockData).registers.payload.anchor =
        AssignmentScoreReconstruction.currentWeight output.reconstruction := by
  have hcompat := later_start_round_compatibility output clockData
  rcases LaterAssignmentStartOperation.successful_renewal_law_spec
      output hrenewal with
    ⟨hafter, hanchor, _⟩
  exact ⟨hafter, hcompat.1, by
    rw [later_registers_payload]
    exact hanchor⟩

end Bandits.Support.CoordinatorAssignmentRegisterInstall

end
