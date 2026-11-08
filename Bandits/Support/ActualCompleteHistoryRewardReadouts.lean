/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualSourceCompleteSuffixObservation
public import Bandits.Support.ActualInitializationPhysicalRewards

/-!
# Actual complete-horizon reward readouts

The total reward is read from H's existing per-player quantized-feedback
history on the original source-initialized complete history. Its postlaunch
suffix is observed through G's retained actual S step codes. The original
continuous published table, all original private coordinates including the
private index `J`, the whole reward table, and the same unrestricted constants
are retained throughout.

Mathematical evidence: `sources/zip4/manuscript/01_introduction.tex:18-36`,
`sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`, and
`sources/zip4/manuscript/08_main_theorem.tex:67-75`.

These are internal actual-reward measurability, bound, and integrability
results. They establish no policy locality, coupling, exceptional-event
estimate, expectation comparison, source theorem, or regret bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.CompletePublicTable

namespace Bandits.Support.ActualCompleteHistoryRewardReadouts

abbrev Parameters := ActualCompletePhysicalHistory.Parameters
abbrev RateInput := ActualCompletePhysicalHistory.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev GridRewardTable := ActualCompletePhysicalHistory.GridRewardTable

variable {p : Parameters} {rate : RateInput p} {C_star C_h : ℝ}
  {rewards : GridRewardTable p}

/-- The real reward read from one actual whole grid-feedback vector. -/
def actualFeedbackVectorReward (feedback : Fin p.m → Fin (D p + 1)) : ℝ :=
  ∑ player : Fin p.m, ((feedback player).val : ℝ) / (D p : ℝ)

/-- One physical history record's sum of the existing collision-filtered,
quantized player feedbacks, scaled by the source denominator. -/
private def physicalHistoryRecordObservedReward {source : SourceInput p}
    (record : ActualCompletePhysicalHistory.PhysicalHistoryRecord
      p rate source rewards) : ℝ :=
  actualFeedbackVectorReward (p := p) record.feedback

/-- The actual full-horizon reward read from each player's existing H
quantized-feedback observation history on H's literal source-initialized
complete history. -/
def sourceInitializedActualCompleteTotalReward (source : SourceInput p) : ℝ :=
  ∑ player : Fin p.m,
    ActualCompletePhysicalHistory.totalObservedReward
      (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
        p rate source rewards C_star C_h) player

private def stepCodeObservedReward
    (code : ActualPostlaunchSuffixMeasurability.StepCodeObservation p rate) : ℝ :=
  actualFeedbackVectorReward (p := p)
    (ActualPostlaunchBlockMeasurability.stepCodeFeedback code.2)

private def roundCodeSlotObservedReward {α : Type*} (read : α → ℝ)
    (code : Unit ⊕ α) : ℝ :=
  Sum.elim (fun _ => 0) read code

private def stepCodeSlotObservedReward
    (code : Unit ⊕ ActualPostlaunchSuffixMeasurability.StepCodeObservation p rate) : ℝ :=
  roundCodeSlotObservedReward stepCodeObservedReward code

private abbrev StepCodeLengthIndexObservation :=
  ActualPostlaunchSuffixMeasurability.LengthIndexObservation
    (ActualPostlaunchSuffixMeasurability.StepCodeObservation p rate)

private def stepCodeLengthIndexObservedReward
    (coordinates : StepCodeLengthIndexObservation (p := p) (rate := rate)) : ℝ :=
  ∑ cursor : Fin coordinates.1,
    stepCodeSlotObservedReward (coordinates.2 cursor.val)

private def suffixStepCodeObservedReward
    (coordinates : Unit ⊕ StepCodeLengthIndexObservation (p := p) (rate := rate)) : ℝ :=
  Sum.elim (fun _ => 0) stepCodeLengthIndexObservedReward coordinates

private theorem sum_players_list_feedback
    (rounds : List (Fin p.m → Fin (D p + 1))) :
    (∑ player : Fin p.m,
      (rounds.map fun feedback => ((feedback player).val : ℝ) / (D p : ℝ)).sum) =
      (rounds.map actualFeedbackVectorReward).sum := by
  induction rounds with
  | nil => simp
  | cons feedback rounds ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih,
        actualFeedbackVectorReward]

private theorem list_map_sum_congr {α : Type*} (rounds : List α)
    (f g : α → ℝ) (hfg : ∀ x ∈ rounds, f x = g x) :
    (rounds.map f).sum = (rounds.map g).sum := by
  induction rounds with
  | nil => rfl
  | cons x xs ih =>
      have hx := hfg x (by simp)
      have htail := ih (fun y hy => hfg y (by simp [hy]))
      simp only [List.map_cons, List.sum_cons, hx, htail]

/-- The actual total is exactly the initialization reward plus the sum of the
whole feedback vector on every retained postlaunch physical record. This
includes both no-suffix constructors, whose actual suffix list is empty. -/
theorem sourceInitializedActualCompleteTotalReward_eq_initialization_add_postlaunch
    (source : SourceInput p) :
    sourceInitializedActualCompleteTotalReward (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) source =
      ActualInitializationPhysicalRewards.sourceInitializationReward
          (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
          (rewards := rewards) source +
        ((ActualCompletePhysicalHistory.postlaunchRecords
          (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
            p rate source rewards C_star C_h)).map
          (fun record => actualFeedbackVectorReward (p := p) record.feedback)).sum := by
  let history := ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
    p rate source rewards C_star C_h
  have hprojection := fun player =>
    ActualCompletePhysicalHistory.playerQuantizedObservationHistory_projection
      p rate source rewards C_star C_h history player
  unfold sourceInitializedActualCompleteTotalReward
  change (∑ player : Fin p.m,
      (ActualCompletePhysicalHistory.playerQuantizedObservationHistory history player).sum) = _
  simp_rw [hprojection]
  simp_rw [List.sum_append]
  rw [Finset.sum_add_distrib]
  rw [sum_players_list_feedback (p := p)
    (ActualInitializationRun.PhysicalRoundRecord.feedback
      (ActualCompletePhysicalHistory.initializationRecords history))]
  rw [sum_players_list_feedback (p := p)
    ((ActualCompletePhysicalHistory.postlaunchRecords history).map
      ActualCompletePhysicalHistory.MixedRoundRecord.feedback)]
  change
    ((ActualInitializationRun.PhysicalRoundRecord.feedback
        (ActualCompletePhysicalHistory.initializationRecords history)).map
      actualFeedbackVectorReward).sum +
      (((ActualCompletePhysicalHistory.postlaunchRecords history).map
        ActualCompletePhysicalHistory.MixedRoundRecord.feedback).map
      actualFeedbackVectorReward).sum = _
  have hinit :
      ((ActualInitializationRun.PhysicalRoundRecord.feedback
        (ActualCompletePhysicalHistory.initializationRecords history)).map
          actualFeedbackVectorReward).sum =
        ActualInitializationPhysicalRewards.sourceInitializationReward
          (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
          (rewards := rewards) source := by
    unfold ActualInitializationPhysicalRewards.sourceInitializationReward
    simp only [ActualInitializationRun.PhysicalRoundRecord.feedback, List.map_map,
      Function.comp_def, ActualCompletePhysicalHistory.initializationRecords]
    apply list_map_sum_congr
    intro record _
    rfl
  rw [hinit]
  simp only [List.map_map, Function.comp_def]
  simp only [history]

private theorem list_map_sum_eq_roundListCoordinates_sum {α : Type*}
    (rounds : List α) (read : α → ℝ) (n : ℕ) (hlen : rounds.length ≤ n) :
    (rounds.map read).sum =
      ∑ cursor : Fin n,
        roundCodeSlotObservedReward read
          ((ActualPostlaunchBlockMeasurability.roundListCoordinates rounds).2 cursor.val) := by
  classical
  induction n generalizing rounds with
  | zero =>
      cases rounds with
      | nil => simp [roundCodeSlotObservedReward,
          ActualPostlaunchBlockMeasurability.roundListCoordinates]
      | cons head tail => simp at hlen
  | succ n ih =>
      cases rounds with
      | nil => simp [roundCodeSlotObservedReward,
          ActualPostlaunchBlockMeasurability.roundListCoordinates]
      | cons head tail =>
          have htail : tail.length ≤ n := by simp at hlen; omega
          rw [Fin.sum_univ_succ]
          simp only [List.map_cons, List.sum_cons, roundCodeSlotObservedReward,
            ActualPostlaunchBlockMeasurability.roundListCoordinates]
          rw [ih tail htail]
          rfl

private theorem measurable_sigma_sections_local {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] {γ : Type*} [MeasurableSpace γ]
    (f : Sigma β → γ)
    (hf : ∀ a, Measurable (fun x : β a => f ⟨a, x⟩)) : Measurable f := by
  intro s hs
  change MeasurableSet[
      (⨅ a, (inferInstance : MeasurableSpace (β a)).map (Sigma.mk a))]
    {x | f x ∈ s}
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  rw [MeasurableSpace.map_def]
  exact hf a hs

private theorem measurable_stepCodeObservedReward :
    Measurable (stepCodeObservedReward (p := p) (rate := rate)) := by
  apply measurable_sigma_sections_local
  intro block
  change Measurable (fun code : ActualPostlaunchStepMeasurability.StepCode
      p rate block =>
    ∑ player : Fin p.m,
      ((ActualPostlaunchBlockMeasurability.stepCodeFeedback code player).val : ℝ) /
        (D p : ℝ))
  apply Finset.univ.measurable_fun_sum
  intro player _
  exact (measurable_of_finite fun grid : Fin (D p + 1) =>
    ((grid.val : ℝ) / (D p : ℝ))).comp
      ((measurable_pi_apply player).comp
        (ActualPostlaunchBlockMeasurability.measurable_stepCodeFeedback
          (p := p) (rate := rate) (block := block)))

private theorem measurable_roundCodeSlotObservedReward {α : Type*}
    [MeasurableSpace α] {read : α → ℝ} (hread : Measurable read) :
    Measurable (roundCodeSlotObservedReward read) :=
  Measurable.sumElim measurable_const hread

private theorem measurable_stepCodeLengthIndexObservedReward :
    Measurable (stepCodeLengthIndexObservedReward (p := p) (rate := rate)) := by
  apply measurable_from_prod_countable_right
  intro length
  change Measurable (fun stream : ℕ →
    Unit ⊕ ActualPostlaunchSuffixMeasurability.StepCodeObservation p rate =>
      ∑ cursor : Fin length, stepCodeSlotObservedReward (stream cursor.val))
  apply Finset.univ.measurable_fun_sum
  intro cursor _
  exact (measurable_roundCodeSlotObservedReward measurable_stepCodeObservedReward).comp
    (measurable_pi_apply cursor.val)

private theorem measurable_suffixStepCodeObservedReward :
    Measurable (suffixStepCodeObservedReward (p := p) (rate := rate)) :=
  Measurable.sumElim measurable_const measurable_stepCodeLengthIndexObservedReward

private theorem stepCodeObservedReward_eq_record {source : SourceInput p}
    (record : ActualCompletePhysicalHistory.MixedRoundRecord p rate source rewards) :
    stepCodeObservedReward (ActualPostlaunchSuffixMeasurability.recordStepCodeObservation
      record) = actualFeedbackVectorReward (p := p) record.feedback := by
  have hfull := ActualPostlaunchSuffixMeasurability.recordStepCodeObservation_reconstructs_full
    record
  have hfeedback :
      ActualPostlaunchBlockMeasurability.stepCodeFeedback
        (ActualPostlaunchSuffixMeasurability.recordStepCodeObservation record).2 =
        record.feedback := by
    change ActualPostlaunchBlockMeasurability.stepCodeFeedback
        (ActualPostlaunchStepMeasurability.stepCode record.input) = _
    calc
      ActualPostlaunchBlockMeasurability.stepCodeFeedback
          (ActualPostlaunchStepMeasurability.stepCode record.input) =
          ActualPostlaunchPhysicalStep.physicalFeedback
            (ActualPostlaunchPhysicalStep.step record.input).prepared :=
        hfull.1.2.2.2.1
      _ = ActualPostlaunchPhysicalStep.physicalFeedback record.result.prepared := by
        rw [← record.result_eq]
      _ = record.feedback := rfl
  simp only [stepCodeObservedReward, hfeedback]

private theorem suffixStepCodeObservedReward_eq_records {source : SourceInput p}
    (history : ActualCompletePhysicalHistory.CompleteHistory
      p rate source rewards C_star C_h) :
    suffixStepCodeObservedReward
        (_root_.Bandits.Support.ActualSourceCompleteSuffixObservation.suffixStepCodeCoordinatesOfCompleteHistory
          history) =
      ((ActualCompletePhysicalHistory.postlaunchRecords history).map
        (fun record => actualFeedbackVectorReward (p := p) record.feedback)).sum := by
  cases history with
  | launchedBefore launch learnerSeed hlaunch hbefore suffix =>
      have hcoordinates :=
        _root_.Bandits.Support.ActualSourceCompleteSuffixObservation.suffixStepCodeCoordinatesOfCompleteHistory_eq_records
          (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
          (rewards := rewards)
          (.launchedBefore launch learnerSeed hlaunch hbefore suffix)
      simp only [suffixStepCodeObservedReward, hcoordinates, Sum.elim_inr,
        stepCodeLengthIndexObservedReward]
      calc
        (∑ cursor : Fin (suffix.records.map
            ActualPostlaunchSuffixMeasurability.recordStepCodeObservation).length,
            roundCodeSlotObservedReward stepCodeObservedReward
              ((ActualPostlaunchBlockMeasurability.roundListCoordinates
                (suffix.records.map
                  ActualPostlaunchSuffixMeasurability.recordStepCodeObservation)).2
                cursor.val)) =
            (suffix.records.map
              (fun record => stepCodeObservedReward
                (ActualPostlaunchSuffixMeasurability.recordStepCodeObservation record))).sum := by
          symm
          simpa only [List.map_map, Function.comp_def] using
            list_map_sum_eq_roundListCoordinates_sum
            (suffix.records.map ActualPostlaunchSuffixMeasurability.recordStepCodeObservation)
            stepCodeObservedReward _ le_rfl
        _ = (suffix.records.map
            (fun record => actualFeedbackVectorReward (p := p) record.feedback)).sum := by
          apply list_map_sum_congr
          intro record _
          exact stepCodeObservedReward_eq_record record
  | launchedAtHorizon launch learnerSeed hlaunch hat =>
      simp [suffixStepCodeObservedReward,
        _root_.Bandits.Support.ActualSourceCompleteSuffixObservation.suffixStepCodeCoordinatesOfCompleteHistory_eq_records,
        ActualCompletePhysicalHistory.postlaunchRecords]
  | exhausted live hexhausted =>
      simp [suffixStepCodeObservedReward,
        _root_.Bandits.Support.ActualSourceCompleteSuffixObservation.suffixStepCodeCoordinatesOfCompleteHistory_eq_records,
        ActualCompletePhysicalHistory.postlaunchRecords]

/-- The complete actual readout is the initialization readout plus the
readout of G's exact optional S-code suffix. The public code projection and
record reconstruction identify every feedback vector, including in the
shortened terminal block; launch at `T` and exhaustion contribute zero. -/
private theorem sourceInitializedActualCompleteTotalReward_eq_initialization_add_suffixCode
    (source : SourceInput p) :
    sourceInitializedActualCompleteTotalReward (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) source =
      ActualInitializationPhysicalRewards.sourceInitializationReward
          (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
          (rewards := rewards) source +
        suffixStepCodeObservedReward (p := p) (rate := rate)
          (_root_.Bandits.Support.ActualSourceCompleteSuffixObservation.suffixStepCodeCoordinatesOfCompleteHistory
            (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
              p rate source rewards C_star C_h)) := by
  rw [sourceInitializedActualCompleteTotalReward_eq_initialization_add_postlaunch]
  exact congrArg (fun value =>
    ActualInitializationPhysicalRewards.sourceInitializationReward
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) source + value)
      (suffixStepCodeObservedReward_eq_records
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards)
        (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
          p rate source rewards C_star C_h)).symm

/-- Borel measurability of the full actual total reward on the complete
original source `PublishedOutput × ExtendedPrivateCoordinates`. -/
theorem measurable_sourceInitializedActualCompleteTotalReward :
    Measurable (sourceInitializedActualCompleteTotalReward (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)) := by
  have hsuffix : Measurable (fun source : SourceInput p =>
      suffixStepCodeObservedReward (p := p) (rate := rate)
        (_root_.Bandits.Support.ActualSourceCompleteSuffixObservation.suffixStepCodeCoordinatesOfCompleteHistory
          (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
            p rate source rewards C_star C_h))) :=
    measurable_suffixStepCodeObservedReward.comp
      (_root_.Bandits.Support.ActualSourceCompleteSuffixObservation.measurable_sourceInitializedActualCompleteHistory_stepCodeCoordinates
          (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
          (rewards := rewards))
  have hEq :
      (fun source : SourceInput p =>
        sourceInitializedActualCompleteTotalReward (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) (rewards := rewards) source) =
      (fun source => ActualInitializationPhysicalRewards.sourceInitializationReward
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) source) +
        (fun source => suffixStepCodeObservedReward (p := p) (rate := rate)
          (_root_.Bandits.Support.ActualSourceCompleteSuffixObservation.suffixStepCodeCoordinatesOfCompleteHistory
            (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
              p rate source rewards C_star C_h))) := by
    funext source
    exact sourceInitializedActualCompleteTotalReward_eq_initialization_add_suffixCode
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) source
  have hmeasureRight := (ActualInitializationPhysicalRewards.measurable_sourceInitializationReward
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards)).add
    hsuffix
  simpa only [← hEq] using hmeasureRight

private theorem actualFeedbackVectorReward_bounds
    (feedback : Fin p.m → Fin (D p + 1)) :
    0 ≤ actualFeedbackVectorReward (p := p) feedback ∧
      actualFeedbackVectorReward (p := p) feedback ≤ (p.m : ℝ) := by
  have hD : (0 : ℝ) < (D p : ℝ) := Nat.cast_pos.mpr (D_pos p)
  constructor
  · unfold actualFeedbackVectorReward
    apply Finset.sum_nonneg
    intro player _
    exact div_nonneg (Nat.cast_nonneg _) hD.le
  · unfold actualFeedbackVectorReward
    calc
      (∑ player : Fin p.m, ((feedback player).val : ℝ) / (D p : ℝ)) ≤
          ∑ _player : Fin p.m, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro player _
        have hval : (feedback player).val ≤ D p := by
          have hlt := (feedback player).isLt
          omega
        calc
          ((feedback player).val : ℝ) / (D p : ℝ) ≤
              (D p : ℝ) / (D p : ℝ) :=
            div_le_div_of_nonneg_right (by exact_mod_cast hval) hD.le
          _ = 1 := div_self (ne_of_gt hD)
      _ = (p.m : ℝ) := by simp

private theorem physicalHistoryRecordObservedReward_bounds {source : SourceInput p}
    (record : ActualCompletePhysicalHistory.PhysicalHistoryRecord
      p rate source rewards) :
    0 ≤ physicalHistoryRecordObservedReward (p := p) record ∧
      physicalHistoryRecordObservedReward (p := p) record ≤ (p.m : ℝ) :=
  actualFeedbackVectorReward_bounds (p := p) record.feedback

private theorem physicalHistoryRecordsReward_bounds {source : SourceInput p}
    (records : List (ActualCompletePhysicalHistory.PhysicalHistoryRecord
      p rate source rewards)) :
    0 ≤ (records.map (physicalHistoryRecordObservedReward (p := p))).sum ∧
      (records.map (physicalHistoryRecordObservedReward (p := p))).sum ≤
        (records.length : ℝ) * (p.m : ℝ) := by
  induction records with
  | nil => simp
  | cons record records ih =>
      rcases physicalHistoryRecordObservedReward_bounds (p := p) record with
        ⟨hrecord_nonneg, hrecord_bound⟩
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
      constructor
      · exact add_nonneg hrecord_nonneg ih.1
      · calc
          physicalHistoryRecordObservedReward (p := p) record +
              (records.map (physicalHistoryRecordObservedReward (p := p))).sum ≤
              (p.m : ℝ) + (records.length : ℝ) * (p.m : ℝ) :=
            add_le_add hrecord_bound ih.2
          _ = ((records.length : ℝ) + 1) * (p.m : ℝ) := by ring

/-- Pointwise the actual reward lies between zero and `mT` on every original
source input, including all actual exceptional paths. The exact record count
is H's full-horizon count, so the prefix boundary is counted once and every
retained shortened-suffix round is included. -/
theorem sourceInitializedActualCompleteTotalReward_bounds (source : SourceInput p) :
    0 ≤ sourceInitializedActualCompleteTotalReward (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) source ∧
      sourceInitializedActualCompleteTotalReward (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) source ≤
          (p.m : ℝ) * (p.T : ℝ) := by
  let history := ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
    p rate source rewards C_star C_h
  have hcount : (ActualCompletePhysicalHistory.physicalHistoryRecords history).length = p.T := by
    simpa [history] using
      (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
        p rate source rewards C_star C_h).1
  have hrecords := physicalHistoryRecordsReward_bounds (p := p)
    (source := source) (ActualCompletePhysicalHistory.physicalHistoryRecords history)
  have hreward : sourceInitializedActualCompleteTotalReward (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source =
      ((ActualCompletePhysicalHistory.physicalHistoryRecords history).map
        (physicalHistoryRecordObservedReward (p := p))).sum := by
    unfold sourceInitializedActualCompleteTotalReward
    change (∑ player : Fin p.m,
      (ActualCompletePhysicalHistory.playerQuantizedObservationHistory history player).sum) = _
    simp_rw [ActualCompletePhysicalHistory.playerQuantizedObservationHistory_projection
      p rate source rewards C_star C_h history]
    simp_rw [List.sum_append]
    rw [Finset.sum_add_distrib]
    rw [sum_players_list_feedback (p := p)
      (ActualInitializationRun.PhysicalRoundRecord.feedback
        (ActualCompletePhysicalHistory.initializationRecords history))]
    rw [sum_players_list_feedback (p := p)
      ((ActualCompletePhysicalHistory.postlaunchRecords history).map
        ActualCompletePhysicalHistory.MixedRoundRecord.feedback)]
    simp [ActualCompletePhysicalHistory.physicalHistoryRecords,
      physicalHistoryRecordObservedReward,
      ActualCompletePhysicalHistory.PhysicalHistoryRecord.feedback,
      ActualInitializationRun.PhysicalRoundRecord.feedback,
      ActualCompletePhysicalHistory.initializationRecords,
      ActualCompletePhysicalHistory.postlaunchRecords,
      actualFeedbackVectorReward, List.map_append, List.map_map, Function.comp_def]
  rw [hreward]
  rw [hcount] at hrecords
  exact ⟨hrecords.1, by simpa [hcount, mul_comm] using hrecords.2⟩

/-- Fixing the whole published output leaves all original private coordinates,
including the scalar selecting `J`, variable in the actual total. -/
def fixedPublicSourceInitializedActualCompleteTotalReward
    (published : CompletePublicTable.PublishedOutput p)
    (privateCoordinates : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) : ℝ :=
  sourceInitializedActualCompleteTotalReward (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) (rewards := rewards)
    (published, privateCoordinates)

/-- Every fixed-public section of the whole-source actual reward is Borel on
the full original extended private-coordinate space. -/
theorem measurable_fixedPublicSourceInitializedActualCompleteTotalReward
    (published : CompletePublicTable.PublishedOutput p) :
    Measurable (fixedPublicSourceInitializedActualCompleteTotalReward
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) published) :=
  (measurable_sourceInitializedActualCompleteTotalReward (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) (rewards := rewards)).comp
      (measurable_const.prodMk measurable_id)

private theorem integrable_of_nonneg_bounded {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) {B : ℝ}
    (hnonneg : ∀ x, 0 ≤ f x) (hbound : ∀ x, f x ≤ B) : Integrable f μ := by
  refine (integrable_const B).mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]
  exact hbound x

/-- The whole-source actual reward is integrable under the actual source input
probability law. -/
theorem integrable_sourceInitializedActualCompleteTotalReward :
    Integrable (sourceInitializedActualCompleteTotalReward (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards))
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  refine integrable_of_nonneg_bounded
    (measurable_sourceInitializedActualCompleteTotalReward (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards))
    (B := (p.m : ℝ) * (p.T : ℝ)) ?_ ?_
  · intro source
    exact (sourceInitializedActualCompleteTotalReward_bounds (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source).1
  · intro source
    exact (sourceInitializedActualCompleteTotalReward_bounds (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source).2

/-- Every fixed-public full-private section is integrable under the actual
extended private probability law, with the private coordinator index retained
inside the expectation. -/
theorem integrable_fixedPublicSourceInitializedActualCompleteTotalReward
    (published : CompletePublicTable.PublishedOutput p) :
    Integrable (fixedPublicSourceInitializedActualCompleteTotalReward
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) published)
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p) := by
  refine integrable_of_nonneg_bounded
    (measurable_fixedPublicSourceInitializedActualCompleteTotalReward
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) published)
    (B := (p.m : ℝ) * (p.T : ℝ)) ?_ ?_
  · intro privateCoordinates
    exact (sourceInitializedActualCompleteTotalReward_bounds (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)
      (published, privateCoordinates)).1
  · intro privateCoordinates
    exact (sourceInitializedActualCompleteTotalReward_bounds (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)
      (published, privateCoordinates)).2

end Bandits.Support.ActualCompleteHistoryRewardReadouts

end
