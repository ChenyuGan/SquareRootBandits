/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionCalendarServiceLaw

/-!
# Round-end observation for first replacement collection service

This module adapts the existing literal first-replacement calendar service to
PhaseServiceWaiting. It preserves the complete original source input and
source law, and establishes the actual source-prefix round-end filtration.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open MeasureTheory
open ConstructorDimensions
open ReferenceSourcePrefixHistoryFiltration
open scoped Classical

namespace Bandits.Support.ReferenceFirstReplacementCollectionRoundEndObservation

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)
variable (control0 : ContinuousLearningRows.TimeControl p)

/-- The literal Boolean version of the actual replacement collection service. -/
def x (i : Fin (p.m - 1)) (n : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Bool :=
  decide (ReferenceFirstReplacementCollectionActualCalendarTasks.service
    rate rewards C_star C_h control0 n i z = 1)

/-- The real observation is the existing natural-valued service on the whole
natural calendar, including absent and post-horizon rounds. -/
theorem observation_eq_service (i : Fin (p.m - 1)) (n : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    PhaseServiceWaiting.observation (x rate rewards C_star C_h control0) i n z =
      (ReferenceFirstReplacementCollectionActualCalendarTasks.service
        rate rewards C_star C_h control0 n i z : ℝ) := by
  have hle := ReferenceFirstReplacementCollectionActualCalendarTasks.service_le_one
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) n i z
  by_cases hs : ReferenceFirstReplacementCollectionActualCalendarTasks.service
      rate rewards C_star C_h control0 n i z = 1
  · simp [PhaseServiceWaiting.observation, x, hs]
  · have hz : ReferenceFirstReplacementCollectionActualCalendarTasks.service
        rate rewards C_star C_h control0 n i z = 0 := by omega
    simp [PhaseServiceWaiting.observation, x, hz]

/-- The actual replacement service factors through the source prefix through
its physical round. For dates beyond the horizon both sides retain the literal
zero extension. -/
theorem service_end_factor (i : Fin (p.m - 1)) (n : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    (ReferenceFirstReplacementCollectionActualCalendarTasks.service
      rate rewards C_star C_h control0 n i z : ℝ) =
      (ReferenceFirstReplacementCollectionActualCalendarTasks.service
        rate rewards C_star C_h control0 n i
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (n + 1) z) : ℝ) := by
  by_cases hn : p.T ≤ n
  · have hz := ReferenceFirstReplacementCollectionActualCalendarTasks.services_of_horizon_le
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0) n i z hn
    have hp := ReferenceFirstReplacementCollectionActualCalendarTasks.services_of_horizon_le
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0) n i
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (n + 1) z) hn
    simp [hz.2.2, hp.2.2]
  · have hn' : n < p.T := Nat.lt_of_not_ge hn
    let t : Fin p.T := ⟨n, hn'⟩
    let pref := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (n + 1) z
    have hstage :
        ReferenceFirstReplacementCollectionPredictableStages.taskStage
            rate rewards C_star C_h control0 n i z =
          ReferenceFirstReplacementCollectionPredictableStages.taskStage
            rate rewards C_star C_h control0 n i pref := by
      calc
        _ = ReferenceFirstReplacementCollectionPredictableStages.taskStage
              rate rewards C_star C_h control0 n i
              (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) :=
          ReferenceFirstReplacementCollectionPredictableStages.taskStage_factor
            (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
            (control0 := control0) n i z
        _ = ReferenceFirstReplacementCollectionPredictableStages.taskStage
              rate rewards C_star C_h control0 n i
              (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n pref) := by
          rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
            control0 n (n + 1) (by omega) z]
        _ = ReferenceFirstReplacementCollectionPredictableStages.taskStage
              rate rewards C_star C_h control0 n i pref :=
          (ReferenceFirstReplacementCollectionPredictableStages.taskStage_factor
            (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
            (control0 := control0) n i pref).symm
    have hOld :
        ReferenceFirstReplacementCollectionPredictableStages.OLD
            rate rewards C_star C_h control0 n i z ↔
          ReferenceFirstReplacementCollectionPredictableStages.OLD
            rate rewards C_star C_h control0 n i pref := by
      change _ = some ReferenceFirstReplacementCollectionPredictableStages.TaskStage.old ↔
        _ = some ReferenceFirstReplacementCollectionPredictableStages.TaskStage.old
      rw [hstage]
    have hFormed :
        ReferenceFirstReplacementCollectionPredictableStages.FORMED
            rate rewards C_star C_h control0 n i z ↔
          ReferenceFirstReplacementCollectionPredictableStages.FORMED
            rate rewards C_star C_h control0 n i pref := by
      change _ = some ReferenceFirstReplacementCollectionPredictableStages.TaskStage.formed ↔
        _ = some ReferenceFirstReplacementCollectionPredictableStages.TaskStage.formed
      rw [hstage]
    obtain ⟨hDown, hUp⟩ :=
      ReferenceFirstCollectionRoundEndObservation.actual_readouts_end_factor
        (rate := rate) rewards C_star C_h control0 i t z
    have hDown' :
        ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
            (rate := rate) rewards C_star C_h i t z =
          ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
            (rate := rate) rewards C_star C_h i t pref := by
      simpa only [t, pref] using hDown
    have hUp' :
        ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
            (rate := rate) rewards C_star C_h i t z =
          ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
            (rate := rate) rewards C_star C_h i t pref := by
      simpa only [t, pref] using hUp
    have hDownInd :
        ({y | ReferenceFirstReplacementCollectionPredictableStages.OLD
            rate rewards C_star C_h control0 n i y}.indicator
          (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
            (rate := rate) rewards C_star C_h i t)) z =
        ({y | ReferenceFirstReplacementCollectionPredictableStages.OLD
            rate rewards C_star C_h control0 n i y}.indicator
          (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
            (rate := rate) rewards C_star C_h i t)) pref := by
      by_cases ho : ReferenceFirstReplacementCollectionPredictableStages.OLD
          rate rewards C_star C_h control0 n i z
      · have hpref := hOld.mp ho
        simp [ho, hpref, hDown']
      · have hpref : ¬ ReferenceFirstReplacementCollectionPredictableStages.OLD
            rate rewards C_star C_h control0 n i pref :=
          fun hpref => ho (hOld.mpr hpref)
        simp [ho, hpref]
    have hUpInd :
        ({y | ReferenceFirstReplacementCollectionPredictableStages.FORMED
            rate rewards C_star C_h control0 n i y}.indicator
          (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
            (rate := rate) rewards C_star C_h i t)) z =
        ({y | ReferenceFirstReplacementCollectionPredictableStages.FORMED
            rate rewards C_star C_h control0 n i y}.indicator
          (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
            (rate := rate) rewards C_star C_h i t)) pref := by
      by_cases ho : ReferenceFirstReplacementCollectionPredictableStages.FORMED
          rate rewards C_star C_h control0 n i z
      · have hpref := hFormed.mp ho
        simp [ho, hpref, hUp']
      · have hpref : ¬ ReferenceFirstReplacementCollectionPredictableStages.FORMED
            rate rewards C_star C_h control0 n i pref :=
          fun hpref => ho (hFormed.mpr hpref)
        simp [ho, hpref]
    have hservice :=
      ReferenceFirstReplacementCollectionCalendarServiceLaw.service_eq_masked_readouts
        rate rewards C_star C_h control0 t i
    have hz := congrFun hservice z
    have hpref := congrFun hservice pref
    change (ReferenceFirstReplacementCollectionActualCalendarTasks.service
      rate rewards C_star C_h control0 n i z : ℝ) = _
    simp only [t] at hz hpref
    rw [hz, hpref]
    exact congrArg₂ (fun a b : ℝ => a + b) hDownInd hUpInd

/-- Strong measurability in the actual source-prefix filtration through the
end of round n. Post-horizon observations are the literal zero extension. -/
theorem observation_stronglyMeasurable (i : Fin (p.m - 1)) (n : ℕ) :
    StronglyMeasurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 2)]
      (PhaseServiceWaiting.observation (x rate rewards C_star C_h control0) i n) := by
  by_cases hn : n < p.T
  · let t : Fin p.T := ⟨n, hn⟩
    rw [show n + 2 = (n + 1) + 1 by omega,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
    have hmeas :=
      (ReferenceFirstReplacementCollectionCalendarServiceLaw.measurable_service
        rate rewards C_star C_h control0 t i).comp
        (comap_measurable
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (n + 1)))
    have hfactor :
        PhaseServiceWaiting.observation (x rate rewards C_star C_h control0) i n =
          (fun z => (ReferenceFirstReplacementCollectionActualCalendarTasks.service
            rate rewards C_star C_h control0 n i z : ℝ)) ∘
            ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (n + 1) := by
      funext z
      rw [observation_eq_service (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) i n z,
        service_end_factor (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) (control0 := control0) i n z]
      rfl
    rw [hfactor]
    simpa only [t] using hmeas.stronglyMeasurable
  · have hzero :
        PhaseServiceWaiting.observation (x rate rewards C_star C_h control0) i n =
          fun _ => (0 : ℝ) := by
      funext z
      rw [observation_eq_service (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) i n z]
      have hz := ReferenceFirstReplacementCollectionActualCalendarTasks.services_of_horizon_le
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (control0 := control0) n i z (Nat.le_of_not_gt hn)
      simp [hz.2.2]
    rw [hzero]
    exact stronglyMeasurable_const

/-- Inclusive binary waiting observes exactly the existing replacement
service count, with pending-task membership enforced at every calendar date. -/
theorem N_eq_taskCount (H : ℕ) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    PhaseServiceWaiting.N
        (ReferenceFirstReplacementCollectionPendingFoundation.P_repl
          rate rewards C_star C_h control0)
        (x rate rewards C_star C_h control0) i H z =
      ReferenceFirstReplacementCollectionActualCalendarTasks.taskCount
        rate rewards C_star C_h control0 H i z := by
  unfold PhaseServiceWaiting.N
    ReferenceFirstReplacementCollectionActualCalendarTasks.taskCount
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hmem : i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl
      rate rewards C_star C_h control0 n z
  · have hle := ReferenceFirstReplacementCollectionActualCalendarTasks.service_le_one
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0) n i z
    by_cases hpos : ReferenceFirstReplacementCollectionActualCalendarTasks.service
        rate rewards C_star C_h control0 n i z = 1
    · simp [x, hmem, hpos]
    · have hzero : ReferenceFirstReplacementCollectionActualCalendarTasks.service
          rate rewards C_star C_h control0 n i z = 0 := by omega
      simp [x, hmem, hzero]
  · have hzero :=
      (ReferenceFirstReplacementCollectionActualCalendarTasks.services_of_not_pending
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (control0 := control0) n i z hmem).2.2
    simp [x, hmem, hzero]

private theorem taskCount_eq_zero_of_empty
    (H : ℕ) (i : Fin (p.m - 1)) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hEmpty : ∀ n, ReferenceFirstReplacementCollectionPendingFoundation.P_repl
      rate rewards C_star C_h control0 n z = ∅) :
    ReferenceFirstReplacementCollectionActualCalendarTasks.taskCount
      rate rewards C_star C_h control0 H i z = 0 := by
  unfold ReferenceFirstReplacementCollectionActualCalendarTasks.taskCount
  apply Finset.sum_eq_zero
  intro n hn
  have hmem : i ∉ ReferenceFirstReplacementCollectionPendingFoundation.P_repl
      rate rewards C_star C_h control0 n z := by
    rw [hEmpty n]
    simp
  exact (ReferenceFirstReplacementCollectionActualCalendarTasks.services_of_not_pending
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) n i z hmem).2.2

private theorem taskCount_le_quota_of_empty
    (i : Fin (p.m - 1)) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hEmpty : ∀ n, ReferenceFirstReplacementCollectionPendingFoundation.P_repl
      rate rewards C_star C_h control0 n z = ∅) :
    ReferenceFirstReplacementCollectionActualCalendarTasks.taskCount
      rate rewards C_star C_h control0 p.T i z ≤ 4 * AffineBatchDecoder.quota p := by
  rw [taskCount_eq_zero_of_empty (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) (control0 := control0) p.T i z hEmpty]
  exact Nat.zero_le _

/-- The first replacement collection has the literal inclusive quota 4Q on
all original source inputs, including every absent and failed-run branch. -/
theorem N_le_four_quota (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    PhaseServiceWaiting.N
        (ReferenceFirstReplacementCollectionPendingFoundation.P_repl
          rate rewards C_star C_h control0)
        (x rate rewards C_star C_h control0) i p.T z ≤
      4 * AffineBatchDecoder.quota p := by
  rw [N_eq_taskCount (rate := rate) (rewards := rewards) (C_star := C_star)
    (C_h := C_h) (control0 := control0) p.T i z]
  have h := ReferenceFirstReplacementCollectionActualCalendarTasks.complete_first_replacement_actual_calendar_tasks
    rate rewards C_star C_h control0 z
  dsimp only at h
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none =>
    have hEmpty : ∀ n, ReferenceFirstReplacementCollectionPendingFoundation.P_repl
        rate rewards C_star C_h control0 n z = ∅ := by
      simpa only [hb] using h
    exact taskCount_le_quota_of_empty (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (control0 := control0) i z hEmpty
  | some birth =>
    rw [hb] at h
    dsimp only at h
    cases hbirth : birth.output.preparation.coordinator <;>
      try
        (have hEmpty : ∀ n, ReferenceFirstReplacementCollectionPendingFoundation.P_repl
            rate rewards C_star C_h control0 n z = ∅ := by
          simpa only [hb, hbirth] using h
         exact taskCount_le_quota_of_empty (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) (control0 := control0) i z hEmpty)
    rename_i old ledger clock cutoff outcome
    rw [hbirth] at h
    cases outcome <;>
      try
        (have hEmpty : ∀ n, ReferenceFirstReplacementCollectionPendingFoundation.P_repl
            rate rewards C_star C_h control0 n z = ∅ := by
          simpa only [hb, hbirth] using h
         exact taskCount_le_quota_of_empty (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) (control0 := control0) i z hEmpty)
    rename_i core consistent started hstart instruction hinstruction output hconsistent
      clockData installed selectedBirth
    dsimp only [ReferenceActivePhysicalStep.collectionInput] at h
    cases hc : R[c]? with
    | none =>
      have hEmpty : ∀ n, ReferenceFirstReplacementCollectionPendingFoundation.P_repl
          rate rewards C_star C_h control0 n z = ∅ := by
        simpa only [hb, hbirth, hc] using h
      exact taskCount_le_quota_of_empty (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) i z hEmpty
    | some cut =>
      rw [hc] at h
      dsimp only at h
      cases hcut : cut.output.preparation.coordinator <;>
        try
          (have hEmpty : ∀ n, ReferenceFirstReplacementCollectionPendingFoundation.P_repl
              rate rewards C_star C_h control0 n z = ∅ := by
            simpa only [hb, hbirth, hc, hcut] using h
           exact taskCount_le_quota_of_empty (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) (control0 := control0) i z hEmpty)
      rename_i registers owned base outcome
      rw [hcut] at h
      cases outcome <;>
        try
          (have hEmpty : ∀ n, ReferenceFirstReplacementCollectionPendingFoundation.P_repl
              rate rewards C_star C_h control0 n z = ∅ := by
            simpa only [hb, hbirth, hc, hcut] using h
           exact taskCount_le_quota_of_empty (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) (control0 := control0) i z hEmpty)
      rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
      dsimp only at h
      exact (h.2.2.2.2 i p.T).2.2.2.2.2

end Bandits.Support.ReferenceFirstReplacementCollectionRoundEndObservation

end
