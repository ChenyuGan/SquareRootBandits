/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualCompleteCoordinatorOwnHistory
public import Bandits.Support.FiniteBoundedLocalHistoryCode
public import Bandits.Support.ActualCompleteOriginalRewardRounding

/-!
# The actual coordinator on bounded original-reward histories

This module reads the coordinator's observations from the existing complete
actual physical history. At each calendar time it pairs that record's actual
coordinator arm with collision-filtered feedback evaluated on the original
reward table at the same record time. The existing finite floor code then
feeds the complete coordinator replay and decision.

The construction uses the actual complete chronology and retains its
initialization and postlaunch record tags. Its storage includes the existing
configuration and decoder bank. No new physical run, state representation,
off-horizon extension, or additional random coordinate is introduced.

Sources, relative to `sources/zip4/manuscript/`:
`01_introduction.tex:18-36`, `07_public_setup.tex:55-114`,
`06_interruptions.tex:240-296`,
`appendix_a_local_protocol.tex:6-14,28-79`, and
`appendix_b_communication.tex:94-131`.

These are internal finite coordinator results. They do not assert follower or
all-state local-policy membership, sampled-private factorization, a
Real-history/all-Nat interface, or a regret bound. The original scalar J and
target coordinates remain in the existing coordinator own-coordinate input.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.FiniteBanditModel
open Bandits.Support.ActualCompletePhysicalHistory
open Bandits.Support.ActualInitializationCoordinatorOwnHistory
open Bandits.Support.ActiveRoundActions

namespace Bandits.Support.ActualBoundedCoordinatorDecision

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActualCompleteCoordinatorOwnHistory.RateInput
abbrev SourceInput := ActualCompleteCoordinatorOwnHistory.SourceInput
abbrev OwnCoordinates := ActualCompleteCoordinatorOwnHistory.OwnCoordinates
abbrev BoundedHistory := FiniteBoundedLocalHistoryCode.BoundedHistory
abbrev HistoryCode := FiniteBoundedLocalHistoryCode.HistoryCode

/-- Inputs for the coordinator's bounded finite-time decision. The published
output and the complete original coordinator coordinates are retained. -/
abbrev DecisionInput (p : Parameters) (t : Fin p.T) :=
  CompletePublicTable.PublishedOutput p ×
    (OwnCoordinates p × BoundedHistory p t.val)

variable {p : Parameters}

/-- The existing complete actual history driven by the literal floor-coded
whole original reward matrix. This alias adds no transition or record. -/
abbrev actualOriginalHistory (rate : RateInput p)
    (source : SourceInput p) (original : RewardMatrix p.T p.K)
    (C_star C_h : ℝ) :=
  ActualCompleteCoordinatorOwnHistory.actualHistory rate source
    (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
    C_star C_h

/-- The physical record already stored at a calendar index of the existing
actual complete history. The full-horizon length theorem justifies the lookup. -/
def actualCoordinatorPhysicalRecordAt (rate : RateInput p)
    (source : SourceInput p) (original : RewardMatrix p.T p.K)
    (C_star C_h : ℝ) (t : Fin p.T) :
    PhysicalHistoryRecord p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original) :=
  (physicalHistoryRecords (actualOriginalHistory rate source original C_star C_h))[t.val]'(by
    rw [(ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
      p rate source (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
      C_star C_h).1]
    exact t.isLt)

private theorem consecutiveNat_get (start count i : ℕ) (hi : i < count) :
    (ActualInitializationHorizon.consecutiveNat start count)[i]'(by
      rw [ActualInitializationHorizon.consecutiveNat_length]
      exact hi) = start + i := by
  induction count generalizing start i with
  | zero => omega
  | succ count ih =>
      cases i with
      | zero => rfl
      | succ i =>
          change (ActualInitializationHorizon.consecutiveNat (start + 1) count)[i]'(by
            rw [ActualInitializationHorizon.consecutiveNat_length]
            omega) = start + (i + 1)
          rw [ih (start + 1) i (by omega)]
          omega

/-- The index used above is the actual physical record at exactly calendar
time `t`. This follows from the public complete-history chronology and length,
including both tags and all terminal cases. -/
theorem actualCoordinatorPhysicalRecordAt_time (rate : RateInput p)
    (source : SourceInput p) (original : RewardMatrix p.T p.K)
    (C_star C_h : ℝ) (t : Fin p.T) :
    (actualCoordinatorPhysicalRecordAt rate source original C_star C_h t).time = t := by
  apply Fin.ext
  have hlength :=
    (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
      p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
      C_star C_h).1
  change (physicalHistoryRecords
    (actualOriginalHistory rate source original C_star C_h)).length = p.T at hlength
  have hchronology :=
    ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_times_values
      p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
      C_star C_h
  have hindexed := congrArg (fun values : List ℕ => values[t.val]?) hchronology
  have hrecordIndex : t.val <
      (physicalHistoryRecords (actualOriginalHistory rate source original C_star C_h)).length := by
    rw [hlength]
    exact t.isLt
  have hcalendarIndex :
      t.val < (ActualInitializationHorizon.consecutiveNat 0 p.T).length := by
    rw [ActualInitializationHorizon.consecutiveNat_length]
    exact t.isLt
  have htime :
      ((physicalHistoryRecords
        (actualOriginalHistory rate source original C_star C_h))[t.val]'hrecordIndex).time.val = t.val := by
    simpa only [ActualCompletePhysicalHistory.times, List.getElem?_map,
      List.getElem?_eq_getElem hrecordIndex, Option.map_some,
      List.getElem?_eq_getElem hcalendarIndex,
      consecutiveNat_get 0 p.T t.val t.isLt, Nat.zero_add,
      Option.some.injEq] using hindexed
  simpa only [actualCoordinatorPhysicalRecordAt, actualOriginalHistory] using htime

/-- At each `j : Fin n`, read the actual record at calendar index `j.val`,
then pair its actual coordinator action with original collision feedback at
that very record's calendar time. The subtype uses the existing proved
feedback bound. There is no default branch or representative choice. -/
def actualBoundedCoordinatorHistory (rate : RateInput p)
    (C_star C_h : ℝ) (original : RewardMatrix p.T p.K)
    (source : SourceInput p) (n : ℕ) (hn : n ≤ p.T) :
    BoundedHistory p n := fun j =>
  let t : Fin p.T := ⟨j.val, lt_of_lt_of_le j.isLt hn⟩
  let record : PhysicalHistoryRecord p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original) :=
    actualCoordinatorPhysicalRecordAt rate source original C_star C_h t
  (record.actions (ActiveRoundActions.coordinator p.two_le_m),
    ⟨playerFeedback record.actions (original.reward record.time)
        (ActiveRoundActions.coordinator p.two_le_m),
      rewardMatrixFeedback_mem_Icc record.actions original record.time
        (ActiveRoundActions.coordinator p.two_le_m)⟩)

/-- Every actual lookup used in the bounded readout exists and is the record
whose calendar time is the corresponding `j.val`. -/
theorem actualBoundedCoordinatorHistory_record_time
    (rate : RateInput p) (C_star C_h : ℝ)
    (original : RewardMatrix p.T p.K) (source : SourceInput p)
    (n : ℕ) (hn : n ≤ p.T) (j : Fin n) :
    (actualCoordinatorPhysicalRecordAt rate source original C_star C_h
      ⟨j.val, lt_of_lt_of_le j.isLt hn⟩).time.val = j.val := by
  have htime := actualCoordinatorPhysicalRecordAt_time rate source original C_star C_h
    ⟨j.val, lt_of_lt_of_le j.isLt hn⟩
  exact congrArg Fin.val htime

/-- The literal finite floor code of the bounded original history above. -/
def coordinatorBoundedHistoryCode (rate : RateInput p)
    (C_star C_h : ℝ) (original : RewardMatrix p.T p.K)
    (source : SourceInput p) (n : ℕ) (hn : n ≤ p.T) :
    HistoryCode p n :=
  FiniteBoundedLocalHistoryCode.Q p
    (actualBoundedCoordinatorHistory rate C_star C_h original source n hn)

/-- The actual bounded replay is the existing grid replay applied to the
literal code of a bounded original-reward history. -/
def coordinatorBoundedReplay (rate : RateInput p)
    (C_star C_h : ℝ) (source : SourceInput p) (n : ℕ) (hn : n ≤ p.T)
    (history : BoundedHistory p n) :
    ActualCompleteCoordinatorOwnHistory.CoordinatorStorage p rate :=
  ActualCompleteCoordinatorOwnHistory.coordinatorGridReplay rate source.1
    (ActualInitializationCoordinatorOwnHistory.ownCoordinates source)
    C_star C_h n hn (FiniteBoundedLocalHistoryCode.Q p history)

/-- Literal composition of the complete grid decision with the existing
bounded-history floor code. It keeps the whole published table and the
coordinator's existing own coordinates unchanged. -/
def coordinatorBoundedDecision (rate : RateInput p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (input : DecisionInput p t) : Fin p.K :=
  ActualCompleteCoordinatorOwnHistory.coordinatorGridDecision rate C_star C_h t
    (input.1, (input.2.1,
      FiniteBoundedLocalHistoryCode.Q p input.2.2))

/-- The Q-code of the actual original coordinator readout is exactly the
existing complete replay's own arm/grid-feedback history. The feedback
identity is the admitted all-record original collision quantization theorem. -/
theorem actualBoundedHistoryCode_eq_sourceGridHistory
    (rate : RateInput p) (C_star C_h : ℝ)
    (original : RewardMatrix p.T p.K) (source : SourceInput p)
    (n : ℕ) (hn : n ≤ p.T) :
    coordinatorBoundedHistoryCode rate C_star C_h original source n hn =
      ActualCompleteCoordinatorOwnHistory.sourceGridHistory rate source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        C_star C_h n hn := by
  funext j
  let t : Fin p.T := ⟨j.val, lt_of_lt_of_le j.isLt hn⟩
  let record : PhysicalHistoryRecord p rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original) :=
    actualCoordinatorPhysicalRecordAt rate source original C_star C_h t
  have hrecordTime : record.time = t := by
    simpa only [record] using
      actualCoordinatorPhysicalRecordAt_time rate source original C_star C_h t
  have hfeedback :=
    ActualCompleteOriginalRewardRounding.physicalHistoryRecord_originalFeedback_quantization
      (rate := rate) original record (ActiveRoundActions.coordinator p.two_le_m)
  rw [hrecordTime] at hfeedback
  have hgridArm :
      (ActualCompleteCoordinatorOwnHistory.sourceGridHistory rate source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        C_star C_h n hn j).1 =
        record.actions (ActiveRoundActions.coordinator p.two_le_m) := by
    dsimp only [ActualCompleteCoordinatorOwnHistory.sourceGridHistory,
      ActualCompleteCoordinatorOwnHistory.actualHistory,
      actualOriginalHistory, ActualCompletePhysicalHistory.playerArmHistory,
      ActualCompletePhysicalHistory.actionHistory, record, actualCoordinatorPhysicalRecordAt]
    simp only [ActualCompletePhysicalHistory.physicalHistoryRecords,
      List.getElem_map]
    rfl
  have hgridFeedback :
      (ActualCompleteCoordinatorOwnHistory.sourceGridHistory rate source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        C_star C_h n hn j).2 =
        record.feedback (ActiveRoundActions.coordinator p.two_le_m) := by
    dsimp only [ActualCompleteCoordinatorOwnHistory.sourceGridHistory,
      ActualCompleteCoordinatorOwnHistory.actualFeedback,
      ActualInitializationCoordinatorOwnHistory.sourceOwnFeedbackPrefix,
      ActualCompleteCoordinatorOwnHistory.actualHistory,
      actualOriginalHistory,
      ActualCompletePhysicalHistory.playerGridFeedbackHistory,
      ActualCompletePhysicalHistory.feedbackHistory, record, actualCoordinatorPhysicalRecordAt]
    simp only [ActualCompletePhysicalHistory.physicalHistoryRecords,
      List.getElem_map]
    rfl
  change
    ((record.actions (ActiveRoundActions.coordinator p.two_le_m)),
      FiniteBoundedLocalHistoryCode.q p
        ⟨playerFeedback record.actions (original.reward record.time)
            (ActiveRoundActions.coordinator p.two_le_m),
          rewardMatrixFeedback_mem_Icc record.actions original record.time
            (ActiveRoundActions.coordinator p.two_le_m)⟩) =
      ((ActualCompleteCoordinatorOwnHistory.sourceGridHistory rate source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        C_star C_h n hn j).1,
      (ActualCompleteCoordinatorOwnHistory.sourceGridHistory rate source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        C_star C_h n hn j).2)
  rw [hrecordTime]
  exact Prod.ext hgridArm.symm (hfeedback.trans hgridFeedback.symm)

/-- The bounded readout restricts by the existing `Fin.castLE` prefix map. -/
theorem actualBoundedCoordinatorHistory_castLE
    (rate : RateInput p) (C_star C_h : ℝ)
    (original : RewardMatrix p.T p.K) (source : SourceInput p)
    {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ p.T) :
    actualBoundedCoordinatorHistory rate C_star C_h original source m
        (Nat.le_trans hmn hn) =
      fun j : Fin m => actualBoundedCoordinatorHistory rate C_star C_h original source n hn
        (Fin.castLE hmn j) := by
  funext j
  simp only [actualBoundedCoordinatorHistory, Fin.val_castLE]

/-- Its finite code commutes with the same prefix cast by Q's proved law. -/
theorem coordinatorBoundedHistoryCode_castLE
    (rate : RateInput p) (C_star C_h : ℝ)
    (original : RewardMatrix p.T p.K) (source : SourceInput p)
    {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ p.T) :
    coordinatorBoundedHistoryCode rate C_star C_h original source m
        (Nat.le_trans hmn hn) =
      fun j : Fin m => coordinatorBoundedHistoryCode rate C_star C_h original source n hn
        (Fin.castLE hmn j) := by
  unfold coordinatorBoundedHistoryCode
  rw [actualBoundedCoordinatorHistory_castLE]
  exact FiniteBoundedLocalHistoryCode.Q_castLE p hmn
    (actualBoundedCoordinatorHistory rate C_star C_h original source n hn)

/-- Joint Borel measurability in the whole published output, existing
coordinator own coordinates, and the entire bounded original history. -/
theorem measurable_coordinatorBoundedDecision (rate : RateInput p)
    (C_star C_h : ℝ) (t : Fin p.T) :
    Measurable (fun input : DecisionInput p t =>
      coordinatorBoundedDecision rate C_star C_h t input) := by
  have hcode : Measurable
      (fun input : DecisionInput p t =>
        FiniteBoundedLocalHistoryCode.Q p input.2.2) := by
    exact (FiniteBoundedLocalHistoryCode.Q_measurable p).comp
      (measurable_snd.comp measurable_snd)
  have hinput : Measurable
      (fun input : DecisionInput p t =>
        (input.1, (input.2.1,
          FiniteBoundedLocalHistoryCode.Q p input.2.2))) := by
    exact measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).prodMk hcode)
  change Measurable (fun input : DecisionInput p t =>
    ActualCompleteCoordinatorOwnHistory.coordinatorGridDecision rate C_star C_h t
      (input.1, (input.2.1,
        FiniteBoundedLocalHistoryCode.Q p input.2.2)))
  exact (ActualCompleteCoordinatorOwnHistory.measurable_coordinatorGridDecision
    rate C_star C_h t).comp hinput

/-- On every original source and reward table, the bounded decision returns
the current action in the same retained physical-history position. -/
theorem sourceInitialized_coordinatorBoundedDecision
    (rate : RateInput p) (C_star C_h : ℝ)
    (original : RewardMatrix p.T p.K) (source : SourceInput p)
    (t : Fin p.T) :
    coordinatorBoundedDecision rate C_star C_h t
      (source.1,
        (ActualInitializationCoordinatorOwnHistory.ownCoordinates source,
          actualBoundedCoordinatorHistory rate C_star C_h original source
            t.val t.isLt.le)) =
      (ActualCompleteCoordinatorOwnHistory.sourceOwnArms rate source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        C_star C_h)[t.val]'(by
          change t.val < (ActualCompletePhysicalHistory.playerArmHistory
            (actualOriginalHistory rate source original C_star C_h)
            (ActiveRoundActions.coordinator p.two_le_m)).length
          rw [ActualCompletePhysicalHistory.playerArmHistory,
            List.length_map,
            (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
              p rate source
              (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
              C_star C_h).2.1]
          exact t.isLt) := by
  change ActualCompleteCoordinatorOwnHistory.coordinatorGridDecision rate C_star C_h t
      (source.1,
        (ActualInitializationCoordinatorOwnHistory.ownCoordinates source,
          coordinatorBoundedHistoryCode rate C_star C_h original source
            t.val t.isLt.le)) = _
  rw [actualBoundedHistoryCode_eq_sourceGridHistory rate C_star C_h original source
    t.val t.isLt.le]
  exact ActualCompleteCoordinatorOwnHistory.sourceInitialized_coordinatorGridDecision
    rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
      C_star C_h t

/-- At each strict-past length, the actual bounded original readout reconstructs
the complete before-storage of the existing physical history. At `T`, this
is the existing terminal storage and no action is produced. -/
theorem coordinatorBoundedReplay_actual_reconstruction
    (rate : RateInput p) (C_star C_h : ℝ)
    (original : RewardMatrix p.T p.K) (source : SourceInput p)
    (n : ℕ) (hn : n ≤ p.T) :
    coordinatorBoundedReplay rate C_star C_h source n hn
        (actualBoundedCoordinatorHistory rate C_star C_h original source n hn) =
      ActualCompleteCoordinatorOwnHistory.actualBeforeStorage rate source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        C_star C_h n hn := by
  change ActualCompleteCoordinatorOwnHistory.coordinatorGridReplay rate source.1
      (ActualInitializationCoordinatorOwnHistory.ownCoordinates source) C_star C_h n hn
      (coordinatorBoundedHistoryCode rate C_star C_h original source n hn) = _
  rw [actualBoundedHistoryCode_eq_sourceGridHistory rate C_star C_h original source n hn]
  exact ActualCompleteCoordinatorOwnHistory.sourceInitialized_coordinatorGridReplay
    rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
      C_star C_h n hn

/-- Equality of bounded original strict-past histories supplies the
quantized-past premise for the existing two-source replay-locality theorem.
Thus both the reconstructed storage and, below `T`, the actual current arm
agree with only whole-public, coordinator-own, and produced-history equality. -/
theorem sourceInitialized_coordinatorBounded_original_history_locality
    (rate : RateInput p) (C_star C_h : ℝ)
    (source : SourceInput p) (original : RewardMatrix p.T p.K)
    (other : SourceInput p) (otherOriginal : RewardMatrix p.T p.K)
    (n : ℕ) (hn : n ≤ p.T)
    (hpublic : source.1 = other.1)
    (hown : ActualInitializationCoordinatorOwnHistory.ownCoordinates source =
      ActualInitializationCoordinatorOwnHistory.ownCoordinates other)
    (hpast : actualBoundedCoordinatorHistory rate C_star C_h original source n hn =
      actualBoundedCoordinatorHistory rate C_star C_h otherOriginal other n hn) :
    ActualCompleteCoordinatorOwnHistory.actualBeforeStorage rate source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        C_star C_h n hn =
      ActualCompleteCoordinatorOwnHistory.actualBeforeStorage rate other
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) otherOriginal)
        C_star C_h n hn ∧
    (∀ ht : n < p.T,
      coordinatorBoundedDecision rate C_star C_h ⟨n, ht⟩
        (source.1,
          (ActualInitializationCoordinatorOwnHistory.ownCoordinates source,
            actualBoundedCoordinatorHistory rate C_star C_h original source n hn)) =
      coordinatorBoundedDecision rate C_star C_h ⟨n, ht⟩
        (other.1,
          (ActualInitializationCoordinatorOwnHistory.ownCoordinates other,
            actualBoundedCoordinatorHistory rate C_star C_h otherOriginal other n hn))) := by
  have hcode := congrArg (FiniteBoundedLocalHistoryCode.Q p) hpast
  change coordinatorBoundedHistoryCode rate C_star C_h original source n hn =
      coordinatorBoundedHistoryCode rate C_star C_h otherOriginal other n hn at hcode
  rw [actualBoundedHistoryCode_eq_sourceGridHistory rate C_star C_h original source n hn,
    actualBoundedHistoryCode_eq_sourceGridHistory rate C_star C_h otherOriginal other n hn]
    at hcode
  have hgridFeedback :
      ActualCompleteCoordinatorOwnHistory.actualFeedback rate source
          (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
          C_star C_h n hn =
        ActualCompleteCoordinatorOwnHistory.actualFeedback rate other
          (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) otherOriginal)
          C_star C_h n hn := by
    funext j
    exact congrArg Prod.snd (congrFun hcode j)
  have hpastGrid :
      (ActualCompleteCoordinatorOwnHistory.sourceOwnFeedback rate source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        C_star C_h).take n =
      (ActualCompleteCoordinatorOwnHistory.sourceOwnFeedback rate other
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) otherOriginal)
        C_star C_h).take n := by
    calc
      _ = List.ofFn (ActualCompleteCoordinatorOwnHistory.actualFeedback rate source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        C_star C_h n hn) := by
          symm
          exact ActualInitializationCoordinatorOwnHistory.sourceOwnFeedbackPrefix_list
            rate source
            (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
            C_star C_h n hn
      _ = List.ofFn (ActualCompleteCoordinatorOwnHistory.actualFeedback rate other
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) otherOriginal)
        C_star C_h n hn) := congrArg List.ofFn hgridFeedback
      _ = _ :=
        ActualInitializationCoordinatorOwnHistory.sourceOwnFeedbackPrefix_list
          rate other
          (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) otherOriginal)
          C_star C_h n hn
  have hlocal :=
    ActualCompleteCoordinatorOwnHistory.sourceInitialized_coordinator_own_history
      rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
      C_star C_h other
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) otherOriginal)
      n hn hpublic hown hpastGrid
  refine ⟨hlocal.1, ?_⟩
  intro ht
  have hdecision := sourceInitialized_coordinatorBoundedDecision rate C_star C_h
    original source ⟨n, ht⟩
  have hotherDecision := sourceInitialized_coordinatorBoundedDecision rate C_star C_h
    otherOriginal other ⟨n, ht⟩
  have harms := (hlocal.2.2 ht).1
  exact hdecision.trans (harms.trans hotherDecision.symm)

end Bandits.Support.ActualBoundedCoordinatorDecision

end
