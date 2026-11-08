/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualCompleteHistoryRewardReadouts
public import Bandits.Support.ExpectedRoundedRegret

/-!
# Original physical payoff on the actual complete transcript

The literal original reward is evaluated at the times and simultaneous actions
of the existing source-initialized actual history, driven by the entrywise
rounded table. Every observation of this single transcript is identified with
the quantized original collision feedback. The original payoff itself is not
rounded. Whole-source Borel measurability uses actual time/action projections
of the retained initialization and mixed-suffix codes.

Sources: `sources/zip4/manuscript/01_introduction.tex:18-36`,
`sources/zip4/manuscript/07_public_setup.tex:55-114,127-164`,
`sources/zip4/manuscript/08_main_theorem.tex:163-168`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`, and
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`.

These are internal actual-transcript results. They establish no local-policy
representation, all-grid regret estimate, reference coupling, good event, or
manuscript closure. Public output precedes all original matrices and their
private expectations. All original continuous coordinates and private J remain.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.FiniteBanditModel
open Bandits.Support.ActualCompletePhysicalHistory
open Bandits.Support.BootstrapPrivateRoundStreams

namespace Bandits.Support.ActualCompleteOriginalRewardRounding

variable {p : ConstructorDimensions.Parameters} {rate : RateInput p} {C_star C_h : ℝ}

/-- Original, unrounded collision payoff on the literal actual physical records.
The table driving the actual observers is the existing floor-index grid table. -/
def sourceInitializedOriginalTotalReward (p : ConstructorDimensions.Parameters)
    (rate : RateInput p) (C_star C_h : ℝ) (original : RewardMatrix p.T p.K)
    (source : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  let history := sourceInitializedActualCompleteHistory p rate source
    (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original) C_star C_h
  ((physicalHistoryRecords history).map (fun record =>
    ∑ i : Fin p.m, playerFeedback record.actions (original.reward record.time) i)).sum

/-- Fix only the whole published output; retain all original private coordinates. -/
def fixedPublicSourceInitializedOriginalTotalReward (p : ConstructorDimensions.Parameters)
    (rate : RateInput p) (C_star C_h : ℝ) (original : RewardMatrix p.T p.K)
    (published : CompletePublicTable.PublishedOutput p)
    (privateCoordinates : ExtendedPrivateCoordinates p) : ℝ :=
  sourceInitializedOriginalTotalReward p rate C_star C_h original
    (published, privateCoordinates)

/-- Scalar quantization on every physical record, including exceptional play.
Both tags use their own actual simultaneous collision rule and calendar time. -/
theorem physicalHistoryRecord_originalFeedback_rounded
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    (original : RewardMatrix p.T p.K)
    (record : PhysicalHistoryRecord p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original))
    (i : Fin p.m) :
    RewardRounding.rounded (D p)
        (playerFeedback record.actions (original.reward record.time) i) =
      ((record.feedback i).val : ℝ) / (D p : ℝ) := by
  classical
  rw [RoundedLocalRollout.rounded_playerFeedback]
  cases record with
  | initialization record =>
      symm
      have h := ActualInitializationPhysicalRewards.physicalRoundRecordObservedReward_feedback
        record i
      have hvalue (t : Fin p.T) (a : Fin p.K) :
          ((RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original t a).val : ℝ) /
            (D p : ℝ) = RewardRounding.rounded (D p) (original.reward t a) :=
        RoundedLocalRollout.roundedRewardMatrixCode_value (D p) (D_pos p) original t a
      by_cases hf : collisionFreeFor record.result.actions i
      · simpa [PhysicalHistoryRecord.feedback, PhysicalHistoryRecord.actions,
          PhysicalHistoryRecord.time, playerFeedback, hf, hvalue] using h
      · simpa [PhysicalHistoryRecord.feedback, PhysicalHistoryRecord.actions,
          PhysicalHistoryRecord.time, playerFeedback, hf] using h
  | postlaunch record =>
      change playerFeedback record.actions
        (fun a => RewardRounding.rounded (D p) (original.reward record.time a)) i =
        ((ActualPostlaunchPhysicalStep.gridFeedback record.result.prepared i).val : ℝ) /
          (D p : ℝ)
      unfold ActualPostlaunchPhysicalStep.gridFeedback
      rw [record.input_rewards]
      change playerFeedback record.actions
        (fun a => RewardRounding.rounded (D p) (original.reward record.time a)) i =
        ((if collisionFreeFor record.actions i then
          RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original
            record.time (record.actions i) else 0).val : ℝ) / (D p : ℝ)
      by_cases hfree : collisionFreeFor record.actions i
      · simp only [playerFeedback, ite_eq_left hfree]
        rfl
      · simp [playerFeedback, hfree]

/-- The exact finite index passed to the actual observers is the floor index of
ORIGINAL physical feedback, with no supplied action/feedback identification. -/
theorem physicalHistoryRecord_originalFeedback_quantization
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    (original : RewardMatrix p.T p.K)
    (record : PhysicalHistoryRecord p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original))
    (i : Fin p.m) :
    RoundedLocalRollout.roundedIndex (D p) (D_pos p)
        (playerFeedback record.actions (original.reward record.time) i)
        (rewardMatrixFeedback_mem_Icc record.actions original record.time i) =
      record.feedback i := by
  have h := physicalHistoryRecord_originalFeedback_rounded original record i
  have hD : (D p : ℝ) ≠ 0 := (Nat.cast_pos.mpr (D_pos p)).ne'
  apply Fin.ext
  apply Nat.cast_injective (R := ℝ)
  exact (div_left_inj' hD).mp h

/-- The initialization coordinator's SAME accepted observation call, now with
its original-environment floor index displayed as the input. -/
theorem initialization_coordinator_original_observation
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    (original : RewardMatrix p.T p.K)
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)) :
    record.result.coordinator = BootstrapCoordinatorLocalRound.observe
      record.result.prepared.coordinator
      (RoundedLocalRollout.roundedIndex (D p) (D_pos p)
        (playerFeedback record.result.actions (original.reward record.time)
          (ActiveRoundActions.coordinator p.two_le_m))
        (rewardMatrixFeedback_mem_Icc record.result.actions original record.time
          (ActiveRoundActions.coordinator p.two_le_m))) := by
  have h := physicalHistoryRecord_originalFeedback_quantization original
    (.initialization record) (ActiveRoundActions.coordinator p.two_le_m)
  dsimp only [PhysicalHistoryRecord.actions, PhysicalHistoryRecord.time,
    PhysicalHistoryRecord.feedback] at h
  rw [h]
  rfl

/-- Every initialization follower consumes exactly its original-environment
quantized collision feedback in its retained actual transition. -/
theorem initialization_follower_original_observation
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    (original : RewardMatrix p.T p.K)
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original))
    (i : Fin (p.m - 1)) :
    ActualInitializationPhysicalStep.observeFollower rate record.block
      record.result.prepared.time record.result.prepared.source i
      (record.result.prepared.followers i)
      (RoundedLocalRollout.roundedIndex (D p) (D_pos p)
        (playerFeedback record.result.actions (original.reward record.time)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        (rewardMatrixFeedback_mem_Icc record.result.actions original record.time
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))) =
      .ok (record.result.followers i) := by
  have h := physicalHistoryRecord_originalFeedback_quantization original
    (.initialization record) (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  dsimp only [PhysicalHistoryRecord.actions, PhysicalHistoryRecord.time,
    PhysicalHistoryRecord.feedback] at h
  rw [h]
  exact record.result.followerTransition i

/-- Every mixed-suffix coordinator call uses the same quantized original
feedback, including its domain-error and dagger branches. -/
theorem postlaunch_coordinator_original_observation
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    (original : RewardMatrix p.T p.K)
    (record : MixedRoundRecord p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)) :
    record.result.coordinatorObservation = OrdinaryCoordinatorPhysicalInterface.observeLocal
      record.result.prepared.coordinator
      (RoundedLocalRollout.roundedIndex (D p) (D_pos p)
        (playerFeedback record.actions (original.reward record.time)
          (ActiveRoundActions.coordinator p.two_le_m))
        (rewardMatrixFeedback_mem_Icc record.actions original record.time
          (ActiveRoundActions.coordinator p.two_le_m))) := by
  have h := physicalHistoryRecord_originalFeedback_quantization original
    (.postlaunch record) (ActiveRoundActions.coordinator p.two_le_m)
  dsimp only [PhysicalHistoryRecord.actions, PhysicalHistoryRecord.time,
    PhysicalHistoryRecord.feedback] at h
  rw [h]
  exact record.result.coordinatorObservation_eq

/-- Every actual heterogeneous suffix follower consumes its own quantized
original feedback; no selected-row or successful ordinary-path premise occurs. -/
theorem postlaunch_follower_original_observation
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    (original : RewardMatrix p.T p.K)
    (record : MixedRoundRecord p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original))
    (i : Fin (p.m - 1)) :
    ActualInitializationPhysicalStep.observeFollower rate record.block
      record.input.time record.input.source i (record.result.prepared.followers i)
      (RoundedLocalRollout.roundedIndex (D p) (D_pos p)
        (playerFeedback record.actions (original.reward record.time)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        (rewardMatrixFeedback_mem_Icc record.actions original record.time
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))) =
      .ok (record.result.followers i) := by
  have h := physicalHistoryRecord_originalFeedback_quantization original
    (.postlaunch record) (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  dsimp only [PhysicalHistoryRecord.actions, PhysicalHistoryRecord.time,
    PhysicalHistoryRecord.feedback] at h
  rw [h]
  exact record.result.followerTransition i

/-- Preparation chooses the initialization actions before any feedback. Its
reward-table field is retained for subsequent physical feedback only. No
replacement execution or assumption of action equivalence is introduced. -/
theorem initialization_prepare_actions_independent_rewards
    (block : Fin (n_boot p)) (time : Fin p.T)
    (coordinator : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate block)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards rewards' : GridRewardTable p) :
    (ActualInitializationPhysicalStep.prepare rate block time coordinator followers
      source rewards).map ActualInitializationPhysicalStep.physicalActions =
    (ActualInitializationPhysicalStep.prepare rate block time coordinator followers
      source rewards').map ActualInitializationPhysicalStep.physicalActions := by
  classical
  unfold ActualInitializationPhysicalStep.prepare
  split <;> rfl

/-- Postlaunch preparation reads storage/source/time and no reward value. -/
theorem postlaunch_prepare_actions_independent_rewards {block : Fin (n_boot p)} {cursor : ℕ}
    (input : ActualPostlaunchPhysicalStep.PhysicalInput (p := p) (rate := rate) block cursor)
    (rewards' : GridRewardTable p) :
    ActualPostlaunchPhysicalStep.actionProfile
        (ActualPostlaunchPhysicalStep.prepare { input with rewards := rewards' }) =
      ActualPostlaunchPhysicalStep.actionProfile (ActualPostlaunchPhysicalStep.prepare input) := rfl

/-- The initialization call inputs are the recorded physical input, original
source, original time, and existing rounded table, all on the SAME step. -/
theorem initialization_original_physical_input
    {source : BootstrapPrivateRoundStreams.SourceInput p} (original : RewardMatrix p.T p.K)
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)) :
    ActualInitializationPhysicalStep.step rate record.block record.time
        record.coordinatorBefore record.followersBefore source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original) =
        .ok record.result ∧
      record.result.prepared.time = record.time ∧
      record.result.prepared.source = source ∧
      record.result.prepared.rewards =
        RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original := by
  have h := ActualInitializationHorizon.physicalRoundRecord_actual record
  exact ⟨h.1, record.result_time, h.2.1, h.2.2.1⟩

/-- The retained mixed result supplies ALL successor storage, including every
heterogeneous follower and the returned coordinator decoder bank. -/
theorem postlaunch_original_next_state
    {source : BootstrapPrivateRoundStreams.SourceInput p} (original : RewardMatrix p.T p.K)
    (record : MixedRoundRecord p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)) :
    record.result = ActualPostlaunchPhysicalStep.step record.input ∧
      record.input.source = source ∧
      record.input.rewards =
        RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original ∧
      record.result.nextState.coordinator = record.result.coordinatorObservation.configuration ∧
      record.result.nextState.upDecoderBank = record.result.coordinatorObservation.upDecoderBank ∧
      ∀ i, record.result.nextState.followers i = (record.result.followers i).next :=
  ⟨record.result_eq, record.input_source, record.input_rewards, rfl, rfl, fun _ => rfl⟩

/-- Adjacent retained records within every actual mixed block have consecutive
cursors and the FULL preceding result's next state as the next input state.
`HEq` only compares the existing indexed state types; no state is projected away. -/
theorem mixedBlockTrace_full_state_chain {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : GridRewardTable p} {block : Fin (n_boot p)} {cursor stop : ℕ}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate) block cursor}
    (trace : MixedBlockTrace p rate source rewards block cursor state stop) :
    trace.records.IsChain (fun before after => after.block = before.block ∧
      after.cursor = before.cursor + 1 ∧ HEq after.input.state before.result.nextState) := by
  induction trace with
  | done => exact .nil
  | step state input input_state input_source input_rewards result result_eq tail hlt ih =>
      cases tail with
      | done => exact .singleton _
      | step nextState nextInput next_input_state next_source next_rewards
          nextResult next_result_eq rest hnext =>
          exact .cons_cons ⟨rfl, rfl, heq_of_eq next_input_state⟩ ih

/-- A retained cross-boundary record uses the exact actual boundary adapter.
Coordinator storage is preserved, while each follower is the adapter's output
from that same completed block, including its original bootstrap carry. -/
theorem postlaunch_boundary_successor_chain
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    (record : PostlaunchCrossBoundaryRecord p rate source) :
    record.successorState = ActualPostlaunchPhysicalStep.crossSuccessorBoundary
        record.hasNext record.next_eq source record.state ∧
      record.successorState.coordinator = record.state.coordinator ∧
      record.successorState.upDecoderBank = record.state.upDecoderBank ∧
      ∀ i, record.successorState.followers i =
        ActualPostlaunchPhysicalStep.beginSuccessorFollower record.hasNext record.next_eq
          source record.state i := by
  rcases record with ⟨block, state, hnext, next, hnext_eq, successorState, hs⟩
  dsimp only at *
  subst next
  subst successorState
  exact ⟨rfl, rfl, rfl, fun _ => rfl⟩

/-- Actual complete chronology: precisely the absolute physical rounds
0,...,T-1, for every source and every original reward matrix. -/
theorem sourceInitializedOriginalHistory_chronology (p : ConstructorDimensions.Parameters)
    (rate : RateInput p) (C_star C_h : ℝ) (original : RewardMatrix p.T p.K)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let history := sourceInitializedActualCompleteHistory p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original) C_star C_h
    (physicalHistoryRecords history).length = p.T ∧
      (times history).map Fin.val = ActualInitializationHorizon.consecutiveNat 0 p.T :=
  ⟨(sourceInitializedActualCompleteHistory_lengths p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original) C_star C_h).1,
    sourceInitializedActualCompleteHistory_times_values p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original) C_star C_h⟩

/-- The actual initialization begins from its existing initial carry, with the
same constants, and no caller-supplied run or carry. -/
theorem sourceInitializedOriginalHistory_initial_carry (p : ConstructorDimensions.Parameters)
    (rate : RateInput p) (C_star C_h : ℝ) (original : RewardMatrix p.T p.K)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    initializationRecords (sourceInitializedActualCompleteHistory p rate source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original) C_star C_h) =
      (ActualInitializationHorizon.runFrom p rate source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        (ActualInitializationRun.firstBlock p)
        (ActualInitializationRun.initialCarry p rate C_star C_h)).records := rfl

/-- Every retained postlaunch block boundary contains exactly the accepted
actual follower outputs. No boundary record is omitted on an exceptional path. -/
theorem sourceInitializedOriginalHistory_boundaries (p : ConstructorDimensions.Parameters)
    (rate : RateInput p) (C_star C_h : ℝ) (original : RewardMatrix p.T p.K)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    ∀ boundary ∈ postlaunchBoundaryRecords (sourceInitializedActualCompleteHistory
      p rate source (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        C_star C_h), ∀ i,
      ActualInitializationPhysicalStep.boundaryFollower rate boundary.block
        (boundary.state.followers i) = .ok (boundary.outputs i) := by
  intro boundary _ i
  exact boundary.accepted i

/-- On a strict launch, the exact source-initialized adapter starts each
follower from the original terminal boundary output, with the next block's
original private draws. These are the actual launch typing conditions, not
an assumed common-launch event for unrelated histories. -/
theorem sourceInitializedOriginalLaunch_handoff (p : ConstructorDimensions.Parameters)
    (rate : RateInput p) (C_star C_h : ℝ) (original : RewardMatrix p.T p.K)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
      C_star C_h).terminalDisposition = .launched launch learnerSeed)
    (hbefore : launch.monitor.launchPosition < p.T) :
    ∀ i, (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original) C_star C_h
      launch learnerSeed hlaunch hbefore).state.followers i =
      ActualInitializationRun.beginFollowerBlock p rate
        (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock p rate source
          (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original) C_star C_h
          launch learnerSeed hlaunch hbefore) source i
        (ActualInitializationRun.followerCarryOfBoundaryOutput rate
          ((ActualInitializationHorizon.sourceInitializedRun p rate source
            (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
            C_star C_h).terminalHandoff.followers i)) := by
  intro i
  exact sourceInitializedLaunchSuccessorInput_followers p rate source
    (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original) C_star C_h
    launch learnerSeed hlaunch hbefore i

private theorem sum_players_list {α : Type*} (records : List α)
    (f : α → Fin p.m → ℝ) :
    (∑ i : Fin p.m, (records.map (fun r => f r i)).sum) =
      (records.map (fun r => ∑ i : Fin p.m, f r i)).sum := by
  induction records with
  | nil => simp
  | cons record records ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- A's existing grid total is the scaled grid feedback on the SAME complete
record spine used by the literal original total. -/
theorem gridTotalReward_eq_records {rewards : GridRewardTable p} (source : BootstrapPrivateRoundStreams.SourceInput p) :
    ActualCompleteHistoryRewardReadouts.sourceInitializedActualCompleteTotalReward
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) source =
      ((physicalHistoryRecords (sourceInitializedActualCompleteHistory
        p rate source rewards C_star C_h)).map (fun record =>
          ∑ i : Fin p.m, ((record.feedback i).val : ℝ) / (D p : ℝ))).sum := by
  unfold ActualCompleteHistoryRewardReadouts.sourceInitializedActualCompleteTotalReward
    totalObservedReward playerQuantizedObservationHistory playerGridFeedbackHistory feedbackHistory
  simp only [List.map_map, Function.comp_def]
  exact sum_players_list _ _

/-- Pathwise rounded reward is no larger than ORIGINAL physical reward. -/
theorem gridTotalReward_le_originalTotalReward (p : ConstructorDimensions.Parameters) (rate : RateInput p)
    (C_star C_h : ℝ) (original : RewardMatrix p.T p.K) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    ActualCompleteHistoryRewardReadouts.sourceInitializedActualCompleteTotalReward
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        source ≤ sourceInitializedOriginalTotalReward p rate C_star C_h original source := by
  rw [gridTotalReward_eq_records]
  unfold sourceInitializedOriginalTotalReward
  apply List.sum_le_sum
  intro record _
  apply Finset.sum_le_sum
  intro i _
  rw [← physicalHistoryRecord_originalFeedback_rounded]
  exact RewardRounding.rounded_le (D p) _ (D_pos p)
    (rewardMatrixFeedback_mem_Icc record.actions original record.time i).1

private theorem original_record_bounds {source : BootstrapPrivateRoundStreams.SourceInput p}
    (original : RewardMatrix p.T p.K)
    (record : PhysicalHistoryRecord p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)) :
    0 ≤ (∑ i : Fin p.m, playerFeedback record.actions (original.reward record.time) i) ∧
      (∑ i : Fin p.m, playerFeedback record.actions (original.reward record.time) i) ≤
        (p.m : ℝ) := by
  constructor
  · exact Finset.sum_nonneg fun i _ =>
      (rewardMatrixFeedback_mem_Icc record.actions original record.time i).1
  · calc
      _ ≤ ∑ _i : Fin p.m, (1 : ℝ) := Finset.sum_le_sum fun i _ =>
        (rewardMatrixFeedback_mem_Icc record.actions original record.time i).2
      _ = (p.m : ℝ) := by simp

/-- ORIGINAL physical payoff lies in `[0,mT]` on every complete physical path.
H's exact T count includes the boundary once and all later physical rounds. -/
theorem originalTotalReward_bounds (p : ConstructorDimensions.Parameters) (rate : RateInput p)
    (C_star C_h : ℝ) (original : RewardMatrix p.T p.K) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    0 ≤ sourceInitializedOriginalTotalReward p rate C_star C_h original source ∧
      sourceInitializedOriginalTotalReward p rate C_star C_h original source ≤
        (p.m : ℝ) * (p.T : ℝ) := by
  let history := sourceInitializedActualCompleteHistory p rate source
    (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original) C_star C_h
  have boundList : ∀ records : List (PhysicalHistoryRecord p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)),
      0 ≤ (records.map (fun r => ∑ i : Fin p.m,
        playerFeedback r.actions (original.reward r.time) i)).sum ∧
      (records.map (fun r => ∑ i : Fin p.m,
        playerFeedback r.actions (original.reward r.time) i)).sum ≤
          (records.length : ℝ) * (p.m : ℝ) := by
    intro records
    induction records with
    | nil => simp
    | cons record records ih =>
        obtain ⟨hn, hb⟩ := original_record_bounds original record
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
        exact ⟨add_nonneg hn ih.1, (add_le_add hb ih.2).trans_eq (by ring)⟩
  have h := boundList (physicalHistoryRecords history)
  have hcount := (sourceInitializedActualCompleteHistory_lengths p rate source
    (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original) C_star C_h).1
  rw [hcount] at h
  exact ⟨h.1, by simpa only [sourceInitializedOriginalTotalReward, history, mul_comm] using h.2⟩

/-! The following code readouts are analytic projections, not new dynamics.
Absent slots contribute the empty sum. Present error/dagger physical rounds
are never removed. Only the impossible unready initialization-code tag is
eliminated, using the proved action history of actual retained records. -/

private def originalRoundReadout (original : RewardMatrix p.T p.K)
    (entry : Fin p.T × ActionProfile p.m p.K) : ℝ :=
  ∑ i : Fin p.m, playerFeedback entry.2 (original.reward entry.1) i

private def optionalReadout {α : Type*} (read : α → ℝ) : Unit ⊕ α → ℝ :=
  Sum.elim (fun _ => 0) read

private theorem measurable_optionalReadout {α : Type*} [MeasurableSpace α]
    {read : α → ℝ} (hread : Measurable read) : Measurable (optionalReadout read) :=
  Measurable.sumElim measurable_const hread

private theorem measurable_sigma_sections {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] {γ : Type*} [MeasurableSpace γ]
    (f : Sigma β → γ)
    (hf : ∀ a, Measurable (fun x : β a => f ⟨a, x⟩)) : Measurable f := by
  intro t ht
  change MeasurableSet[(⨅ a, (inferInstance : MeasurableSpace (β a)).map (Sigma.mk a))]
    {x | f x ∈ t}
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  rw [MeasurableSpace.map_def]
  exact hf a ht

private theorem list_sum_congr {α : Type*} (records : List α) (f g : α → ℝ)
    (hfg : ∀ x ∈ records, f x = g x) : (records.map f).sum = (records.map g).sum := by
  induction records with
  | nil => rfl
  | cons x xs ih =>
      have hx := hfg x (by simp)
      have ht := ih (fun y hy => hfg y (by simp [hy]))
      simp only [List.map_cons, List.sum_cons, hx, ht]

private theorem list_map_pointwise {α β : Type*} (records : List α) (f g : α → β)
    (h : records.map f = records.map g) (x : α) (hx : x ∈ records) : f x = g x := by
  induction records with
  | nil => simp at hx
  | cons head tail ih =>
      injection h with hh ht
      rcases List.mem_cons.mp hx with heq | hmem
      · simpa [heq] using hh
      · exact ih ht hmem

private theorem list_sum_partition {α β : Type*} [Fintype β] [DecidableEq β]
    (records : List α) (key : α → β) (read : α → ℝ) :
    (records.map read).sum =
      ∑ b : β, ((records.filter (fun x => key x == b)).map read).sum := by
  classical
  induction records with
  | nil => simp
  | cons x xs ih =>
      have hfilter (b : β) :
          (((x :: xs).filter (fun y => key y == b)).map read).sum =
            (if key x == b then read x else 0) +
              ((xs.filter (fun y => key y == b)).map read).sum := by
        by_cases h : key x == b <;> simp [h]
      simp only [List.map_cons, List.sum_cons, ih, hfilter, Finset.sum_add_distrib]
      simp

private theorem list_sum_stream {α : Type*} (records : List α) (read : α → ℝ)
    (n : ℕ) (hlen : records.length ≤ n) :
    (records.map read).sum = ∑ cursor : Fin n, optionalReadout read
      ((ActualInitializationBlockFoldMeasurability.roundCodeListCoordinates records).2
        cursor.val) := by
  classical
  induction n generalizing records with
  | zero =>
      cases records with
      | nil => simp [optionalReadout,
          ActualInitializationBlockFoldMeasurability.roundCodeListCoordinates]
      | cons head tail => simp at hlen
  | succ n ih =>
      cases records with
      | nil => simp [optionalReadout,
          ActualInitializationBlockFoldMeasurability.roundCodeListCoordinates]
      | cons head tail =>
          have ht : tail.length ≤ n := by simp at hlen; omega
          rw [Fin.sum_univ_succ]
          simp only [List.map_cons, List.sum_cons, optionalReadout,
            ActualInitializationBlockFoldMeasurability.roundCodeListCoordinates]
          simp [List.getElem?_cons_succ, Fin.val_succ]
          exact ih tail ht

private def initializationCodeReadout (original : RewardMatrix p.T p.K)
    (code : ActualInitializationHorizonMeasurability.FullPhysicalRoundCode
      (p := p) (rate := rate)) : ℝ :=
  optionalReadout (fun x => originalRoundReadout original (x.1.1.2.1, x.2.1.1)) code.2

private theorem measurable_initializationCodeReadout (original : RewardMatrix p.T p.K) :
    Measurable (initializationCodeReadout (rate := rate) original) := by
  apply measurable_sigma_sections
  intro block
  apply measurable_optionalReadout
  exact (measurable_of_finite (originalRoundReadout original)).comp
    (measurable_fst.fst.snd.fst.prodMk measurable_snd.fst.fst)

/-- A successful initialization code retains its input's real calendar time.
This conditional codec lemma takes the explicit success equation; below that
equation is obtained by eliminating the impossible error tag of an actual record. -/
private theorem initialization_success_time (block : Fin (n_boot p))
    (x : ActualInitializationStepMeasurability.RoundInput p rate block C_star C_h)
    (successful : ActualInitializationStepMeasurability.SuccessfulRoundCode p rate block)
    (hs : ActualInitializationStepMeasurability.actualRoundOutputCode
      rate block C_star C_h x = .inr successful) : successful.1.1.2.1 = x.time := by
  classical
  by_cases hr : ActualInitializationRoundMeasurability.roundInputReady
      p rate block C_star C_h x
  · rw [ActualInitializationStepMeasurability.actualRoundOutputCode_eq_success_onReady
      rate block C_star C_h ⟨x, hr⟩] at hs
    have heq := Sum.inr.inj hs
    rw [← heq]
    rfl
  · have he := (ActualInitializationStepMeasurability.actualRoundOutputCode_and_step_eq_inputNotReady
      rate block C_star C_h x hr).1
    rw [he] at hs
    cases hs

private theorem initialization_record_action_code {rewards : GridRewardTable p}
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards)
    (hrecord : record ∈ (ActualInitializationHorizon.sourceInitializedRun
      p rate source rewards C_star C_h).records) :
    ActualInitializationHorizonObservation.fullActionEntry
      (ActualInitializationHorizonObservation.fullRecordCode
        (C_star := C_star) (C_h := C_h) record) = .inr record.result.actions := by
  have hcodes := ActualInitializationSourceObservation.sourceInitializedRunObservation_chronologicalRoundCodes
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) source
  have hactions := congrArg Prod.fst
    (ActualInitializationSourceObservation.sourceInitializedRunObservation_actionFeedbackHistory
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) source)
  change (ActualInitializationHorizonObservation.chronologicalRoundCodes
    (ActualInitializationRun.firstBlock p)
    (ActualInitializationSourceObservation.sourceInitializedRunObservation
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source).suffix).map
        ActualInitializationHorizonObservation.fullActionEntry = _ at hactions
  rw [hcodes] at hactions
  simp only [List.map_map, Function.comp_def] at hactions
  exact list_map_pointwise _ _ _ hactions record hrecord

/-- Every retained initialization record has a successful ready code with its
actual absolute time and simultaneous actions. Membership is an explicit
conditional helper input, discharged by the actual prefix in the Borel proof. -/
theorem initialization_record_time_actions_code {rewards : GridRewardTable p}
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards)
    (hrecord : record ∈ (ActualInitializationHorizon.sourceInitializedRun
      p rate source rewards C_star C_h).records) :
    ∃ successful : ActualInitializationStepMeasurability.SuccessfulRoundCode
        p rate record.block,
      ActualInitializationBlockFoldExact.physicalRoundCode C_star C_h record = .inr successful ∧
      successful.1.1.2.1 = record.time ∧ successful.2.1.1 = record.result.actions := by
  have ha := initialization_record_action_code (C_star := C_star) (C_h := C_h)
    source record hrecord
  unfold ActualInitializationHorizonObservation.fullRecordCode
    ActualInitializationHorizonObservation.fullActionEntry at ha
  cases hc : ActualInitializationBlockFoldExact.physicalRoundCode C_star C_h record with
  | inl error => simp only [hc, Sum.elim_inl] at ha; cases ha
  | inr successful =>
      simp only [hc, Sum.elim_inr] at ha
      exact ⟨successful, rfl, initialization_success_time record.block _ successful hc,
        Sum.inr.inj ha⟩

private theorem initializationCodeReadout_eq_record
    (original : RewardMatrix p.T p.K) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original))
    (hrecord : record ∈ (ActualInitializationHorizon.sourceInitializedRun p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        C_star C_h).records) :
    initializationCodeReadout (rate := rate) original
        (ActualInitializationHorizonObservation.fullRecordCode
          (C_star := C_star) (C_h := C_h) record) =
      originalRoundReadout original (record.time, record.result.actions) := by
  obtain ⟨successful, hc, ht, ha⟩ := initialization_record_time_actions_code
    (C_star := C_star) (C_h := C_h) source record hrecord
  simp only [initializationCodeReadout, ActualInitializationHorizonObservation.fullRecordCode,
    hc, optionalReadout, Sum.elim_inr, ht, ha]

private def initializationOriginalCodeSum (original : RewardMatrix p.T p.K)
    (source : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  ∑ block : Fin (n_boot p), ∑ cursor : Fin p.T,
    optionalReadout (initializationCodeReadout (rate := rate) original)
      ((ActualInitializationBlockFoldMeasurability.roundCodeListCoordinates
        (((ActualInitializationHorizon.sourceInitializedRun p rate source
          (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
            C_star C_h).records.filter (fun record => record.block == block)).map
          (ActualInitializationHorizonObservation.fullRecordCode
            (C_star := C_star) (C_h := C_h)))).2 cursor.val)

private theorem measurable_initializationOriginalCodeSum (original : RewardMatrix p.T p.K) :
    Measurable (initializationOriginalCodeSum (rate := rate)
      (C_star := C_star) (C_h := C_h) original) := by
  apply Finset.univ.measurable_fun_sum
  intro block _
  apply Finset.univ.measurable_fun_sum
  intro cursor _
  exact (measurable_optionalReadout (measurable_initializationCodeReadout original)).comp
    (ActualInitializationSourceObservation.measurable_sourceInitializedRun_round_stream
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
      block cursor.val)

private theorem initializationOriginal_eq_codeSum (original : RewardMatrix p.T p.K)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    (((ActualInitializationHorizon.sourceInitializedRun p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        C_star C_h).records).map (fun record =>
          originalRoundReadout original (record.time, record.result.actions))).sum =
      initializationOriginalCodeSum (rate := rate) (C_star := C_star) (C_h := C_h)
        original source := by
  classical
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source
    (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original) C_star C_h
  have hcount := ActualInitializationPhysicalRewards.sourceInitializationReward_record_count
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original) source
  have htotal : run.records.length ≤ p.T := hcount.trans_le (Nat.min_le_left _ _)
  rw [list_sum_partition run.records (fun r => r.block)]
  unfold initializationOriginalCodeSum
  apply Finset.sum_congr rfl
  intro block _
  let records := run.records.filter (fun r => r.block == block)
  have hlen : records.length ≤ p.T := (List.length_filter_le _ _).trans htotal
  have hread : (records.map (fun r =>
      originalRoundReadout original (r.time, r.result.actions))).sum =
      (records.map (fun r => initializationCodeReadout (rate := rate) original
        (ActualInitializationHorizonObservation.fullRecordCode
          (C_star := C_star) (C_h := C_h) r))).sum := by
    apply list_sum_congr
    intro record hmem
    exact (initializationCodeReadout_eq_record original source record
      (List.mem_of_mem_filter hmem)).symm
  rw [hread]
  simpa only [List.map_map, Function.comp_def, records, run] using
    (list_sum_stream (records.map (ActualInitializationHorizonObservation.fullRecordCode
      (C_star := C_star) (C_h := C_h)))
      (initializationCodeReadout (rate := rate) original) p.T
      (by simpa only [List.length_map] using hlen))

private def suffixCodeReadout (original : RewardMatrix p.T p.K)
    (code : ActualPostlaunchSuffixMeasurability.StepCodeObservation p rate) : ℝ :=
  originalRoundReadout original
    (OrdinaryCoordinatorLocalMeasurability.calendarTime code.2.1.1.1.1,
      ActualPostlaunchBlockMeasurability.stepCodeActions code.2)

private theorem measurable_suffixCodeReadout (original : RewardMatrix p.T p.K) :
    Measurable (suffixCodeReadout (rate := rate) original) := by
  apply measurable_sigma_sections
  intro block
  exact (measurable_of_finite (originalRoundReadout original)).comp
    (measurable_fst.fst.fst.fst.snd.snd.snd.prodMk
      (ActualPostlaunchBlockMeasurability.measurable_stepCodeActions
        (p := p) (rate := rate) (block := block)))

private theorem suffixCodeReadout_eq_record (original : RewardMatrix p.T p.K)
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    (record : MixedRoundRecord p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)) :
    suffixCodeReadout original
        (ActualPostlaunchSuffixMeasurability.recordStepCodeObservation record) =
      originalRoundReadout original (record.time, record.actions) := by
  have hfull := ActualPostlaunchSuffixMeasurability.recordStepCodeObservation_reconstructs_full
    record
  have ha : ActualPostlaunchBlockMeasurability.stepCodeActions
      (ActualPostlaunchStepMeasurability.stepCode record.input) = record.actions := by
    calc
      _ = ActualPostlaunchPhysicalStep.actionProfile
          (ActualPostlaunchPhysicalStep.step record.input).prepared := hfull.1.2.2.1
      _ = record.actions := by rw [← record.result_eq]; rfl
  have ht : OrdinaryCoordinatorLocalMeasurability.calendarTime
      (ActualPostlaunchStepMeasurability.stepCode record.input).1.1.1.1 = record.time := rfl
  simp only [suffixCodeReadout, ActualPostlaunchSuffixMeasurability.recordStepCodeObservation,
    ha, ht]

private abbrev SuffixCoordinates := ActualPostlaunchSuffixMeasurability.LengthIndexObservation
  (ActualPostlaunchSuffixMeasurability.StepCodeObservation p rate)

private def suffixLengthReadout (original : RewardMatrix p.T p.K)
    (coordinates : SuffixCoordinates (p := p) (rate := rate)) : ℝ :=
  ∑ cursor : Fin coordinates.1,
    optionalReadout (suffixCodeReadout original) (coordinates.2 cursor.val)

private def suffixOriginalReadout (original : RewardMatrix p.T p.K)
    (coordinates : Unit ⊕ SuffixCoordinates (p := p) (rate := rate)) : ℝ :=
  optionalReadout (suffixLengthReadout original) coordinates

private theorem measurable_suffixOriginalReadout (original : RewardMatrix p.T p.K) :
    Measurable (suffixOriginalReadout (rate := rate) original) := by
  apply measurable_optionalReadout
  apply measurable_from_prod_countable_right
  intro length
  dsimp only [suffixLengthReadout]
  apply Finset.univ.measurable_fun_sum
  intro cursor _
  exact (measurable_optionalReadout (measurable_suffixCodeReadout original)).comp
    (measurable_pi_apply cursor.val)

private theorem suffixOriginalReadout_eq_records (original : RewardMatrix p.T p.K)
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    (history : CompleteHistory p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original) C_star C_h) :
    suffixOriginalReadout original
        (ActualSourceCompleteSuffixObservation.suffixStepCodeCoordinatesOfCompleteHistory history) =
      ((postlaunchRecords history).map (fun record =>
        originalRoundReadout original (record.time, record.actions))).sum := by
  cases history with
  | launchedBefore launch learnerSeed hlaunch hbefore suffix =>
      rw [ActualSourceCompleteSuffixObservation.suffixStepCodeCoordinatesOfCompleteHistory_eq_records]
      simp only [suffixOriginalReadout, optionalReadout, Sum.elim_inr, suffixLengthReadout]
      calc
        _ = ((suffix.records.map
            ActualPostlaunchSuffixMeasurability.recordStepCodeObservation).map
              (suffixCodeReadout original)).sum := by
          symm
          exact list_sum_stream _ _ _ le_rfl
        _ = (suffix.records.map (fun record =>
            originalRoundReadout original (record.time, record.actions))).sum := by
          simp only [List.map_map, Function.comp_def]
          apply list_sum_congr
          intro record _
          exact suffixCodeReadout_eq_record original record
  | launchedAtHorizon launch learnerSeed hlaunch hat =>
      simp [suffixOriginalReadout, optionalReadout,
        ActualSourceCompleteSuffixObservation.suffixStepCodeCoordinatesOfCompleteHistory_eq_records,
        postlaunchRecords]
  | exhausted live hexhausted =>
      simp [suffixOriginalReadout, optionalReadout,
        ActualSourceCompleteSuffixObservation.suffixStepCodeCoordinatesOfCompleteHistory_eq_records,
        postlaunchRecords]

/-- Exact Borel readout decomposition of the literal original payoff. The
initialization boundary is in the prefix; neither empty-suffix constructor
creates another physical time or action. -/
private theorem originalTotalReward_eq_codeReadouts (original : RewardMatrix p.T p.K)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    sourceInitializedOriginalTotalReward p rate C_star C_h original source =
      initializationOriginalCodeSum (rate := rate) (C_star := C_star) (C_h := C_h)
          original source +
        suffixOriginalReadout original
          (ActualSourceCompleteSuffixObservation.suffixStepCodeCoordinatesOfCompleteHistory
            (sourceInitializedActualCompleteHistory p rate source
              (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
                C_star C_h)) := by
  rw [suffixOriginalReadout_eq_records]
  unfold sourceInitializedOriginalTotalReward physicalHistoryRecords
  simp only [List.map_append, List.map_map, List.sum_append, Function.comp_def,
    PhysicalHistoryRecord.time, PhysicalHistoryRecord.actions]
  rw [← initializationOriginal_eq_codeSum]
  rfl

/-- Whole-source Borel measurability on the inherited continuous source space.
Only finite time/action payoff evaluation is discrete; no continuous coordinate
or stored-real fibre receives a replacement measurable structure. -/
theorem measurable_originalTotalReward (p : ConstructorDimensions.Parameters) (rate : RateInput p)
    (C_star C_h : ℝ) (original : RewardMatrix p.T p.K) :
    Measurable (sourceInitializedOriginalTotalReward p rate C_star C_h original) := by
  have hp := measurable_initializationOriginalCodeSum (rate := rate)
    (C_star := C_star) (C_h := C_h) original
  have hs := (measurable_suffixOriginalReadout (rate := rate) original).comp
    (ActualSourceCompleteSuffixObservation.measurable_sourceInitializedActualCompleteHistory_stepCodeCoordinates
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original))
  have heq : sourceInitializedOriginalTotalReward p rate C_star C_h original =
      (fun source => initializationOriginalCodeSum (rate := rate)
        (C_star := C_star) (C_h := C_h) original source +
        suffixOriginalReadout original
          (ActualSourceCompleteSuffixObservation.suffixStepCodeCoordinatesOfCompleteHistory
            (sourceInitializedActualCompleteHistory p rate source
              (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
                C_star C_h))) := by
    funext source
    exact originalTotalReward_eq_codeReadouts original source
  rw [heq]
  exact hp.add hs

/-- Every fixed-public section is Borel on the FULL extended private space. -/
theorem measurable_fixedPublicOriginalTotalReward (p : ConstructorDimensions.Parameters)
    (rate : RateInput p) (C_star C_h : ℝ) (original : RewardMatrix p.T p.K)
    (published : CompletePublicTable.PublishedOutput p) :
    Measurable (fixedPublicSourceInitializedOriginalTotalReward p rate C_star C_h
      original published) :=
  (measurable_originalTotalReward p rate C_star C_h original).comp
    (measurable_const.prodMk measurable_id)

private theorem integrable_nonneg_bounded {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    {B : ℝ} (hn : ∀ x, 0 ≤ f x) (hb : ∀ x, f x ≤ B) : Integrable f μ := by
  refine (integrable_const B).mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (hn x)]
  exact hb x

/-- Integrability under the EXACT original source input probability law. -/
theorem integrable_originalTotalReward (p : ConstructorDimensions.Parameters) (rate : RateInput p)
    (C_star C_h : ℝ) (original : RewardMatrix p.T p.K) :
    Integrable (sourceInitializedOriginalTotalReward p rate C_star C_h original)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  exact integrable_nonneg_bounded (measurable_originalTotalReward p rate C_star C_h original)
    (fun source => (originalTotalReward_bounds p rate C_star C_h original source).1)
    (fun source => (originalTotalReward_bounds p rate C_star C_h original source).2)

/-- Integrability at each fixed published output under the EXACT original
extended private law, with J and every continuous private stream retained. -/
theorem integrable_fixedPublicOriginalTotalReward (p : ConstructorDimensions.Parameters)
    (rate : RateInput p) (C_star C_h : ℝ) (original : RewardMatrix p.T p.K)
    (published : CompletePublicTable.PublishedOutput p) :
    Integrable (fixedPublicSourceInitializedOriginalTotalReward p rate C_star C_h
      original published) (BootstrapPrivateRoundStreams.extendedPrivateLaw p) := by
  exact integrable_nonneg_bounded
    (measurable_fixedPublicOriginalTotalReward p rate C_star C_h original published)
    (fun e => (originalTotalReward_bounds p rate C_star C_h original (published, e)).1)
    (fun e => (originalTotalReward_bounds p rate C_star C_h original (published, e)).2)

/-- Pathwise regret transfer for the real best fixed m-set comparator. There
is no policy, coupling, event, or all-grid estimate among the hypotheses. -/
theorem sourceInitializedOriginalRegret_rounding_le (p : ConstructorDimensions.Parameters)
    (rate : RateInput p) (C_star C_h : ℝ) (original : RewardMatrix p.T p.K)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    bestFixedMSetComparator (m_pos p) (Nat.le_of_lt p.m_lt_K) original -
        sourceInitializedOriginalTotalReward p rate C_star C_h original source ≤
      bestFixedMSetComparator (m_pos p) (Nat.le_of_lt p.m_lt_K)
          (RoundedLocalRollout.roundedRewardMatrix (D p) (D_pos p) original) -
        ActualCompleteHistoryRewardReadouts.sourceInitializedActualCompleteTotalReward
          (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
          (rewards := RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
          source + (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) := by
  have hc := RoundedLocalRollout.bestFixedMSetComparator_rounding_le
    (m_pos p) (Nat.le_of_lt p.m_lt_K) (D p) (D_pos p) original
  have hr := gridTotalReward_le_originalTotalReward p rate C_star C_h original source
  linarith only [hc, hr]

/-- Fix the whole published output, THEN quantify over all original matrices,
with each matrix preceding its private integral. This is a rounding transfer,
not an all-grid estimate. The law is the actual extended private law. -/
theorem fixedPublicOriginalExpectedRegret_rounding_le (p : ConstructorDimensions.Parameters)
    (rate : RateInput p) (C_star C_h : ℝ)
    (published : CompletePublicTable.PublishedOutput p) :
    ∀ original : RewardMatrix p.T p.K,
      bestFixedMSetComparator (m_pos p) (Nat.le_of_lt p.m_lt_K) original -
          (∫ e, fixedPublicSourceInitializedOriginalTotalReward p rate C_star C_h
            original published e ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p) ≤
        bestFixedMSetComparator (m_pos p) (Nat.le_of_lt p.m_lt_K)
            (RoundedLocalRollout.roundedRewardMatrix (D p) (D_pos p) original) -
          (∫ e, ActualCompleteHistoryRewardReadouts.fixedPublicSourceInitializedActualCompleteTotalReward
            (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
            (rewards := RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
            published e ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p) +
          (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) := by
  intro original
  have hc := RoundedLocalRollout.bestFixedMSetComparator_rounding_le
    (m_pos p) (Nat.le_of_lt p.m_lt_K) (D p) (D_pos p) original
  have hi := integral_mono
    (ActualCompleteHistoryRewardReadouts.integrable_fixedPublicSourceInitializedActualCompleteTotalReward
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original) published)
    (integrable_fixedPublicOriginalTotalReward p rate C_star C_h original published)
    (fun e => gridTotalReward_le_originalTotalReward p rate C_star C_h original (published, e))
  linarith only [hc, hi]

end Bandits.Support.ActualCompleteOriginalRewardRounding

end
