/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualFollowerFiniteHistoryReplay
public import Bandits.Support.ActualBoundedCoordinatorDecision

import Lean.Elab.Tactic.Omega

/-!
# The actual follower on bounded original-feedback histories

For each finite prefix, this module reads the follower's actual arm and its
original collision-filtered reward from the existing complete physical record.
It codes those bounded real observations with the existing floor map and feeds
the already proved follower replay and decision. At the horizon it also retains
the existing boundary output and final bootstrap numerator update.

Mathematical evidence: `sources/zip4/manuscript/01_introduction.tex:18-36`,
`sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`, and
`sources/zip4/manuscript/08_main_theorem.tex:163-168`.

These are deterministic internal readout and reconstruction results. They do
not prove joint measurability of this bounded composition, an all-player
rollout law, a source section, a regret estimate, or a manuscript theorem.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.FiniteBanditModel
open Bandits.Support.ActualCompletePhysicalHistory
open Bandits.Support.FiniteBoundedLocalHistoryCode

namespace Bandits.Support.ActualBoundedFollowerDecision

abbrev Parameters := ActualFollowerFiniteHistoryReplay.Parameters
abbrev RateInput := ActualFollowerFiniteHistoryReplay.RateInput
abbrev SourceInput (p : Parameters) := ActualFollowerFiniteHistoryReplay.SourceInput p
abbrev Published (p : Parameters) := ActualFollowerFiniteHistoryReplay.Published p
abbrev Own (p : Parameters) := ActualFollowerFiniteHistoryReplay.Own p
abbrev BoundedHistory := FiniteBoundedLocalHistoryCode.BoundedHistory
abbrev HistoryCode := FiniteBoundedLocalHistoryCode.HistoryCode

variable {p : Parameters}

/-- The full bounded real history of one follower, read at its own coordinate
from each existing actual physical record. -/
def actualBoundedFollowerHistory (rate : RateInput p)
    (C_star C_h : ℝ) (original : RewardMatrix p.T p.K)
    (source : SourceInput p) (i : Fin (p.m - 1)) (n : ℕ) (hn : n ≤ p.T) :
    BoundedHistory p n := fun j =>
  let t : Fin p.T := ⟨j.val, lt_of_lt_of_le j.isLt hn⟩
  let record := ActualBoundedCoordinatorDecision.actualCoordinatorPhysicalRecordAt
    rate source original C_star C_h t
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m i
  (record.actions player,
    ⟨playerFeedback record.actions (original.reward record.time) player,
      rewardMatrixFeedback_mem_Icc record.actions original record.time player⟩)

/-- The actual complete physical record selected by a history index has that
same calendar time. The shared role-independent lookup proves this fact. -/
theorem actual_bounded_follower_history_record_time (rate : RateInput p)
    (C_star C_h : ℝ) (original : RewardMatrix p.T p.K)
    (source : SourceInput p) (n : ℕ) (hn : n ≤ p.T)
    (j : Fin n) :
    (ActualBoundedCoordinatorDecision.actualCoordinatorPhysicalRecordAt rate source
      original C_star C_h ⟨j.val, lt_of_lt_of_le j.isLt hn⟩).time.val = j.val := by
  exact congrArg Fin.val
    (ActualBoundedCoordinatorDecision.actualCoordinatorPhysicalRecordAt_time
      rate source original C_star C_h ⟨j.val, lt_of_lt_of_le j.isLt hn⟩)

/-- The existing finite floor code of the actual bounded follower history. -/
def actualBoundedFollowerHistoryCode (rate : RateInput p)
    (C_star C_h : ℝ) (original : RewardMatrix p.T p.K)
    (source : SourceInput p) (i : Fin (p.m - 1)) (n : ℕ) (hn : n ≤ p.T) :
    HistoryCode p n :=
  FiniteBoundedLocalHistoryCode.Q p
    (actualBoundedFollowerHistory rate C_star C_h original source i n hn)

/-- Quantizing the actual original-reward history gives exactly the follower's
existing strict-past arm and grid-feedback history, without a realizability
premise or a feedback-equality hypothesis. -/
theorem actual_bounded_follower_history_code_eq_source_follower_history_code
    (rate : RateInput p) (C_star C_h : ℝ)
    (original : RewardMatrix p.T p.K) (source : SourceInput p)
    (i : Fin (p.m - 1)) (n : ℕ) (hn : n ≤ p.T) :
    actualBoundedFollowerHistoryCode rate C_star C_h original source i n hn =
      ActualFollowerFiniteHistoryReplay.sourceFollowerHistoryCode p rate source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        C_star C_h i n hn := by
  funext j
  let t : Fin p.T := ⟨j.val, lt_of_lt_of_le j.isLt hn⟩
  let record := ActualBoundedCoordinatorDecision.actualCoordinatorPhysicalRecordAt
    rate source original C_star C_h t
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m i
  have hrecordTime : record.time = t := by
    simpa only [record, t] using
      ActualBoundedCoordinatorDecision.actualCoordinatorPhysicalRecordAt_time
        rate source original C_star C_h t
  have hfeedback :=
    ActualCompleteOriginalRewardRounding.physicalHistoryRecord_originalFeedback_quantization
      (rate := rate) original record player
  have hfeedbackAtT :
      RoundedLocalRollout.roundedIndex (D p) (D_pos p)
        (playerFeedback record.actions (original.reward t) player)
        (rewardMatrixFeedback_mem_Icc record.actions original t player) =
      record.feedback player := by
    simpa only [hrecordTime] using hfeedback
  change (record.actions player,
      FiniteBoundedLocalHistoryCode.q p
        ⟨playerFeedback record.actions (original.reward record.time) player,
          rewardMatrixFeedback_mem_Icc record.actions original record.time player⟩) =
    ((ActualFollowerFiniteHistoryReplay.sourceFollowerHistoryCode p rate source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        C_star C_h i n hn j).1,
      (ActualFollowerFiniteHistoryReplay.sourceFollowerHistoryCode p rate source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        C_star C_h i n hn j).2)
  have hgridArm :
      (ActualFollowerFiniteHistoryReplay.sourceFollowerHistoryCode p rate source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        C_star C_h i n hn j).1 = record.actions player := by
    dsimp only [ActualFollowerFiniteHistoryReplay.sourceFollowerHistoryCode,
      ActualFollowerFiniteHistoryReplay.sourceFollowerArm,
      ActualFollowerCalendarContinuity.actualHistory,
      ActualCompletePhysicalHistory.playerArmHistory,
      ActualCompletePhysicalHistory.actionHistory,
      ActualBoundedCoordinatorDecision.actualOriginalHistory,
      ActualBoundedCoordinatorDecision.actualCoordinatorPhysicalRecordAt, record, t]
    simp only [ActualCompletePhysicalHistory.physicalHistoryRecords,
      List.getElem_map]
    rfl
  have hgridFeedback :
      (ActualFollowerFiniteHistoryReplay.sourceFollowerHistoryCode p rate source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        C_star C_h i n hn j).2 = record.feedback player := by
    dsimp only [ActualFollowerFiniteHistoryReplay.sourceFollowerHistoryCode,
      ActualFollowerFiniteHistoryReplay.sourceFollowerGridFeedback,
      ActualFollowerCalendarContinuity.actualHistory,
      ActualCompletePhysicalHistory.playerGridFeedbackHistory,
      ActualCompletePhysicalHistory.feedbackHistory,
      ActualBoundedCoordinatorDecision.actualOriginalHistory,
      ActualBoundedCoordinatorDecision.actualCoordinatorPhysicalRecordAt, record, t]
    simp only [ActualCompletePhysicalHistory.physicalHistoryRecords,
      List.getElem_map]
    rfl
  rw [hgridArm, hgridFeedback]
  apply Prod.ext
  · rfl
  · change FiniteBoundedLocalHistoryCode.q p
        ⟨playerFeedback record.actions (original.reward record.time) player,
          rewardMatrixFeedback_mem_Icc record.actions original record.time player⟩ =
        record.feedback player
    rw [hrecordTime]
    simpa only [FiniteBoundedLocalHistoryCode.q] using hfeedbackAtT

/-- Restricting the actual original history along `Fin.castLE` restricts the
same physical readout. -/
theorem actual_bounded_follower_history_cast_le (rate : RateInput p)
    (C_star C_h : ℝ) (original : RewardMatrix p.T p.K)
    (source : SourceInput p) (i : Fin (p.m - 1))
    {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ p.T) :
    actualBoundedFollowerHistory rate C_star C_h original source i m
        (Nat.le_trans hmn hn) =
      fun j : Fin m => actualBoundedFollowerHistory rate C_star C_h original source i n hn
        (Fin.castLE hmn j) := by
  funext j
  simp only [actualBoundedFollowerHistory, Fin.val_castLE]

/-- The finite code has the same `Fin.castLE` prefix law, using the existing
quantizer's restriction theorem. -/
theorem actual_bounded_follower_history_code_cast_le (rate : RateInput p)
    (C_star C_h : ℝ) (original : RewardMatrix p.T p.K)
    (source : SourceInput p) (i : Fin (p.m - 1))
    {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ p.T) :
    actualBoundedFollowerHistoryCode rate C_star C_h original source i m
        (Nat.le_trans hmn hn) =
      fun j : Fin m => actualBoundedFollowerHistoryCode rate C_star C_h original source i n hn
        (Fin.castLE hmn j) := by
  unfold actualBoundedFollowerHistoryCode
  rw [actual_bounded_follower_history_cast_le]
  exact FiniteBoundedLocalHistoryCode.Q_castLE p hmn
    (actualBoundedFollowerHistory rate C_star C_h original source i n hn)

/-- The follower's decision input retains the entire published table, its
literal original own coordinates, and the bounded strict-past history. -/
abbrev DecisionInput (p : Parameters) (t : Fin p.T) :=
  Published p × (Own p × BoundedHistory p t.val)

/-- The source-free follower decision is the existing grid decision composed
with the existing floor code on the supplied bounded real history. -/
def followerBoundedDecision (rate : RateInput p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (input : DecisionInput p t) : Fin p.K :=
  ActualFollowerFiniteHistoryReplay.followerGridDecision rate C_star C_h i
    input.1 input.2.1 t (FiniteBoundedLocalHistoryCode.Q p input.2.2)

/-- The corresponding complete follower storage before round `t`, obtained
only by composing the existing replay with the bounded-history floor code. -/
def followerBoundedReplayBefore (rate : RateInput p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (pub : Published p) (own : Own p) (t : Fin p.T)
    (history : BoundedHistory p t.val) :
    ActualInitializationPhysicalStep.FollowerState p rate
      (ActualFollowerCalendarContinuity.calendarBlockIndex t) :=
  ActualFollowerFiniteHistoryReplay.followerReplayBefore rate C_star C_h i pub own t
    (FiniteBoundedLocalHistoryCode.Q p history)

/-- The existing whole terminal boundary code after coding a bounded history
of exactly `T` actual rounds. -/
def followerBoundedTerminalCode (rate : RateInput p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (pub : Published p) (own : Own p)
    (history : BoundedHistory p p.T) :
    ActualInitializationFollowerBoundaryMeasurability.BoundaryOutputCode p rate :=
  ActualFollowerFiniteHistoryReplay.followerTerminalCode rate C_star C_h i pub own
    (FiniteBoundedLocalHistoryCode.Q p history)

/-- The separate last bootstrap numerator observable, including a terminal
declaration whose ordinary boundary carry discards those weights. -/
def followerBoundedTerminalUpdatedNumerators (rate : RateInput p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (pub : Published p) (own : Own p)
    (history : BoundedHistory p p.T) : Option (Fin p.K → ℕ) :=
  ActualFollowerFiniteHistoryReplay.followerTerminalUpdatedNumerators rate C_star C_h i pub own
    (FiniteBoundedLocalHistoryCode.Q p history)

/-- On the actual original history, the bounded before-replay is the existing
complete calendar follower storage, with no matching-prefix or safety premise. -/
theorem source_initialized_follower_bounded_replay_before
    (rate : RateInput p) (C_star C_h : ℝ)
    (original : RewardMatrix p.T p.K) (source : SourceInput p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    followerBoundedReplayBefore rate C_star C_h i source.1
      (ActualFollowerFiniteHistoryReplay.ownProjection p source i) t
      (actualBoundedFollowerHistory rate C_star C_h original source i t.val t.isLt.le) =
    ActualFollowerCalendarContinuity.calendarFollowerBefore rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
      C_star C_h i t := by
  change ActualFollowerFiniteHistoryReplay.followerReplayBefore rate C_star C_h i source.1
      (ActualFollowerFiniteHistoryReplay.ownProjection p source i) t
      (actualBoundedFollowerHistoryCode rate C_star C_h original source i t.val t.isLt.le) = _
  rw [actual_bounded_follower_history_code_eq_source_follower_history_code]
  exact ActualFollowerFiniteHistoryReplay.source_initialized_follower_before_replay
    rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
      C_star C_h i t

/-- For every actual round, the source-free bounded decision returns the
already recorded follower arm on the same original reward matrix. -/
theorem source_initialized_follower_bounded_decision
    (rate : RateInput p) (C_star C_h : ℝ)
    (original : RewardMatrix p.T p.K) (source : SourceInput p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    followerBoundedDecision rate C_star C_h i t
      (source.1,
        (ActualFollowerFiniteHistoryReplay.ownProjection p source i,
          actualBoundedFollowerHistory rate C_star C_h original source i t.val t.isLt.le)) =
    ActualFollowerFiniteHistoryReplay.sourceFollowerArm p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
      C_star C_h i t := by
  change ActualFollowerFiniteHistoryReplay.followerGridDecision rate C_star C_h i source.1
      (ActualFollowerFiniteHistoryReplay.ownProjection p source i) t
      (actualBoundedFollowerHistoryCode rate C_star C_h original source i t.val t.isLt.le) = _
  rw [actual_bounded_follower_history_code_eq_source_follower_history_code]
  exact (ActualFollowerFiniteHistoryReplay.source_initialized_follower_replay
    rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
      C_star C_h i t).2

/-- At the complete horizon, decoding the bounded terminal code gives the
existing terminal follower output, including the `T = 1` case. -/
theorem source_initialized_follower_bounded_terminal
    (rate : RateInput p) (C_star C_h : ℝ)
    (original : RewardMatrix p.T p.K) (source : SourceInput p)
    (i : Fin (p.m - 1)) :
    ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode p rate
      (followerBoundedTerminalCode rate C_star C_h i source.1
        (ActualFollowerFiniteHistoryReplay.ownProjection p source i)
        (actualBoundedFollowerHistory rate C_star C_h original source i p.T (Nat.le_refl _))) =
    ActualFollowerCalendarContinuity.terminalFollowerOutput rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
      C_star C_h i := by
  change ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode p rate
      (ActualFollowerFiniteHistoryReplay.followerTerminalCode rate C_star C_h i source.1
        (ActualFollowerFiniteHistoryReplay.ownProjection p source i)
        (actualBoundedFollowerHistoryCode rate C_star C_h original source i p.T
          (Nat.le_refl _))) = _
  rw [actual_bounded_follower_history_code_eq_source_follower_history_code]
  exact ActualFollowerFiniteHistoryReplay.source_initialized_follower_terminal_replay
    rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
      C_star C_h i

/-- The full bounded terminal history also retains the existing final
bootstrap numerator update, even if terminal carry conversion drops it. -/
theorem source_initialized_follower_bounded_terminal_updated_numerators
    (rate : RateInput p) (C_star C_h : ℝ)
    (original : RewardMatrix p.T p.K) (source : SourceInput p)
    (i : Fin (p.m - 1)) :
    let last : Fin p.T := ⟨p.T - 1, by have := p.one_le_T; omega⟩
    followerBoundedTerminalUpdatedNumerators rate C_star C_h i source.1
      (ActualFollowerFiniteHistoryReplay.ownProjection p source i)
      (actualBoundedFollowerHistory rate C_star C_h original source i p.T (Nat.le_refl _)) =
      match ActualFollowerCalendarContinuity.calendarFollowerAfter rate source
          (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
          C_star C_h i last with
      | .bootstrap startup => some (BootstrapObservedFollower.updatedNumerators p
          (ActualFollowerCalendarContinuity.calendarBlockIndex last) startup)
      | .declared _ _ _ => none := by
  change ActualFollowerFiniteHistoryReplay.followerTerminalUpdatedNumerators rate C_star C_h i
      source.1 (ActualFollowerFiniteHistoryReplay.ownProjection p source i)
      (actualBoundedFollowerHistoryCode rate C_star C_h original source i p.T (Nat.le_refl _)) = _
  rw [actual_bounded_follower_history_code_eq_source_follower_history_code]
  exact ActualFollowerFiniteHistoryReplay.source_initialized_follower_terminal_updatedNumerators
    rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
      C_star C_h i

end Bandits.Support.ActualBoundedFollowerDecision

end
