/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteCoordinatorPhaseExhaustion
public import Bandits.Support.ReferenceGeneratedInheritedDownWrongCompletionWitness

/-!
# Coordinator support on the original generated DOWN calendar

The full generated run is the complete physical suffix of the same source.
Coordinator phase exhaustion therefore applies at each original generated
record. This removes the no-selection branch for actual DOWN cuts without
asserting presence of an expected word or follower success.

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,246-299,355-390`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-84`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42,67-100`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceGeneratedDownBatchCalendar
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.ReferenceGeneratedInheritedDownWrongCompletionWitness

namespace Bandits.Support.ReferenceCompleteCoordinatorDiagnosticSupport

variable {p : ConstructorDimensions.Parameters}

/-- The launch-source subtype retains the exact physical start of its original
source, including all original row and private coordinates. -/
theorem generatedSource_physicalStart
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs) :
    physicalStart rate x.val rewards C_star C_h = s := by
  exact x.property.2

/-- Exact full-run transport. The public bounded-run theorem is used with the
actual generated seed, and its take is removed using the actual suffix length.
No suffix, source coordinate, or physical continuation is discarded. -/
theorem generatedSourceRun_records_eq_completeSuffixRecords
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs) :
    (generatedSourceRun rate rewards C_star C_h s hs x).records =
      completeSuffixRecords rate x.val rewards C_star C_h := by
  have hfiberMem : x.val ∈
      ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
        (rate := rate) rewards C_star C_h s := by
    change _ ∧ _
    exact x.property
  let fiber : ReferenceGeneratedDownAmbiguityMeasurability.GeneratedLaunchFiber
      (rate := rate) rewards C_star C_h s := ⟨x.val, hfiberMem⟩
  have hseed := generatedSourceSeed_spec rate rewards C_star C_h s hs x
  have hpayload := correctedLaunch_eq_some_payload rate x.val rewards C_star C_h
    (ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunch_ne_none
      (rate := rate) rewards C_star C_h s fiber)
  have hpayloadEq :
      correctedLaunchPayload rate x.val rewards C_star C_h
        (ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunch_ne_none
          (rate := rate) rewards C_star C_h s fiber) =
        generatedSourceSeed rate rewards C_star C_h s hs x :=
    Option.some.inj (hpayload.symm.trans hseed.1)
  have hinput :
      ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput
          (rate := rate) rewards C_star C_h s fiber =
        generatedSourceRunInput rate rewards C_star C_h s hs x := by
    apply Subtype.ext
    rw [ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput_val,
      generatedSourceRunInput]
    simp [fiber, hpayloadEq]
  have hsuffix :=
    ReferenceGeneratedDownAmbiguityMeasurability.generatedRun_records_eq_completeSuffixRecords_take
      (rate := rate) rewards C_star C_h s (p.T - s) (by omega) fiber
  rw [hinput] at hsuffix
  have hlength : (completeSuffixRecords rate x.val rewards C_star C_h).length =
      p.T - s := by
    rw [completeSuffixRecords_length,
      generatedSource_physicalStart rate rewards C_star C_h s hs x]
  have htake : (completeSuffixRecords rate x.val rewards C_star C_h).take (p.T - s) =
      completeSuffixRecords rate x.val rewards C_star C_h := by
    rw [← hlength, List.take_length]
  simpa only [generatedSourceRun, fiber, htake] using hsuffix

/-- The bounded generated record is the record at the same index in the full
original complete suffix. Its index bound comes from the actual source start.
-/
theorem generatedSourceRecordAt_eq_completeSuffixRecord
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs)
    (n : Fin (p.T - s)) :
    ∃ hbound : n.val < (completeSuffixRecords rate x.val rewards C_star C_h).length,
      (completeSuffixRecords rate x.val rewards C_star C_h)[n.val]'hbound =
        generatedSourceRecordAt rate rewards C_star C_h s hs x n := by
  have hbound : n.val < (completeSuffixRecords rate x.val rewards C_star C_h).length := by
    rw [completeSuffixRecords_length,
      generatedSource_physicalStart rate rewards C_star C_h s hs x]
    exact n.isLt
  have hrecord := generatedSourceRecordAt_getElem? rate rewards C_star C_h s hs x n
  rw [generatedSourceRun_records_eq_completeSuffixRecords,
    List.getElem?_eq_getElem hbound] at hrecord
  exact ⟨hbound, Option.some.inj hrecord⟩

/-- Coordinator support at every original generated record, with no supplied
validity, success, survival, or trace-equality premise. -/
theorem generated_coordinator_diagnostic_support
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs)
    (n : Fin (p.T - s)) :
    let r := generatedSourceRecordAt rate rewards C_star C_h s hs x n
    r.input.state.coordinator ≠ .dagger ∧
      r.output.preparation.coordinator.selection ≠ none ∧
      r.output.coordinator.failure = none ∧
      r.output.next.coordinator ≠ .first ∧
      r.output.next.coordinator ≠ .dagger := by
  obtain ⟨hbound, hrecord⟩ := generatedSourceRecordAt_eq_completeSuffixRecord
    rate rewards C_star C_h s hs x n
  have hsupport :=
    (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
      rate rewards C_star C_h x.val).1 ⟨n.val, hbound⟩
  exact hrecord ▸ hsupport

/-- At any actual follower DOWN cut, the obsolete current no-selection branch
is impossible. The cut and follower diagnostics are retained unchanged; this
makes no assertion about the cut's expected word or its acceptance outcome. -/
theorem generated_down_cut_no_selection_impossible
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs)
    (n : Fin (p.T - s)) (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : ((generatedSourceRecordAt rate rewards C_star C_h s hs x n).output.followers i).down =
      some cut) :
    ((generatedSourceRecordAt rate rewards C_star C_h s hs x n).output.followers i).down =
        some cut ∧
      ¬ ((generatedSourceRecordAt rate rewards C_star C_h s hs x n).output.preparation.coordinator.selection =
        none) := by
  exact ⟨hcut, (generated_coordinator_diagnostic_support
    rate rewards C_star C_h s hs x n).2.1⟩

/-- The coordinator failure projection of the actual full evidence list is
uniformly absent. No follower diagnostic is modified or erased by this fact.
-/
theorem completeSuffixEvidence_coordinator_failure
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    (completeSuffixEvidence rate source rewards C_star C_h).map
        (fun evidence => evidence.coordinator.failure) =
      List.replicate (completeSuffixRecords rate source rewards C_star C_h).length none := by
  have hfailure : ∀ r ∈ completeSuffixRecords rate source rewards C_star C_h,
      r.output.coordinator.failure = none := by
    intro r hr
    obtain ⟨j, hj, hrecord⟩ := List.mem_iff_getElem.mp hr
    have hsupport :=
      (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
        rate rewards C_star C_h source).1 ⟨j, hj⟩
    dsimp only at hsupport
    exact hrecord ▸ hsupport.2.2.1
  change ((completeSuffixRecords rate source rewards C_star C_h).map
    ReferenceActivePhysicalHorizon.RoundRecord.evidence).map _ = _
  rw [List.map_map]
  have hmap :
      (completeSuffixRecords rate source rewards C_star C_h).map
        (fun r => r.evidence.coordinator.failure) =
      (completeSuffixRecords rate source rewards C_star C_h).map (fun _ => none) := by
    apply List.map_congr_left
    intro r hr
    exact hfailure r hr
  simp only [Function.comp_def, hmap, List.map_const']

/-- The same absence statement through the existing literal diagnostic map,
whose second components remain the original complete follower diagnostics. -/
theorem completeSuffixDiagnostics_coordinator_failure
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    (completeSuffixDiagnostics rate source rewards C_star C_h).map
        (fun diagnostic => diagnostic.1.failure) =
      List.replicate (completeSuffixRecords rate source rewards C_star C_h).length none := by
  simpa only [completeSuffixDiagnostics, List.map_map, Function.comp_def] using
    completeSuffixEvidence_coordinator_failure rate rewards C_star C_h source

/-- No launch has no physical suffix and no active terminal state. -/
theorem no_launch_empty_suffix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none) :
    completeSuffixRecords rate source rewards C_star C_h = [] ∧
      completeTerminalState rate source rewards C_star C_h = none := by
  exact ⟨(no_launch_complete_history rate source rewards C_star C_h hlaunch).2.1,
    (no_launch_complete_history rate source rewards C_star C_h hlaunch).2.2.1⟩

/-- A launch at T also has an empty suffix, but retains its actual active
terminal state. This is distinct from the no-launch branch. -/
theorem launch_at_T_empty_suffix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (active : ReferenceActivePhysicalStep.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active)
    (hterminal : physicalStart rate source rewards C_star C_h = p.T) :
    completeSuffixRecords rate source rewards C_star C_h = [] ∧
      completeTerminalState rate source rewards C_star C_h = some active := by
  exact ⟨(terminal_crossing_complete_history
    rate source rewards C_star C_h active hlaunch hterminal).1,
    (terminal_crossing_complete_history
      rate source rewards C_star C_h active hlaunch hterminal).2.1⟩

end Bandits.Support.ReferenceCompleteCoordinatorDiagnosticSupport
