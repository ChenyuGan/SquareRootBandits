/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCorrectedInitializationLaunch

import Lean.Elab.Tactic.Omega

/-!
# Complete original-source corrected physical history

Sources: `sources/zip4/manuscript/07_public_setup.tex:93-164`,
`sources/zip4/manuscript/06_interruptions.tex:235-297,355-426`,
`sources/zip4/manuscript/08_main_theorem.tex:29-42,67-75`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.

For the original complete source, whole reward table, shared constants and
accepted capped rate, this module projects the generated initialization
boundary and concatenates its actual history with the existing active
physical-horizon run. The launch option distinguishes exhaustion from a
crossing at time `T`; the latter still has an active state and an empty suffix.
Every suffix record, diagnostic and terminal state is the literal output of
the existing horizon fold. This is deterministic history construction only:
it proves no law, measurability, ordinary-actual coupling or regret claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ActualReferenceInitializationBlock
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceCorrectedInitializationLaunch

namespace Bandits.Support.ReferenceCompletePhysicalHistory

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev State := ReferenceActivePhysicalStep.State
abbrev RoundRecord (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev RoundEvidence (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate)

variable {p : Parameters}

/-- The exact existing reference input generated from the whole source. -/
def generatedInput (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : ReferenceInitializationRun.Input p :=
  ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate

/-- The complete generated initialization output, retained as the prefix
provenance for the entire construction. -/
def generatedBoundary (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : ReferenceInitializationRun.Boundary p :=
  ReferenceInitializationRun.output (generatedInput rate source rewards C_star C_h)

/-- An optional projection of a generated boundary's own entry at a root
physical coordinate. `none` records that the initializer has not generated
that coordinate. -/
def generatedBoundaryOwnEntry (boundary : ReferenceInitializationRun.Boundary p)
    (player : Fin p.m) (time : Fin p.T) :
    Option (Fin p.K × ReferencePrelaunchFollower.Observation p) :=
  if htime : time.val < ReferenceInitializationRun.elapsed p boundary.completed then
    some (boundary.history player ⟨time.val, htime⟩)
  else
    none

theorem generatedBoundaryOwnEntry_eq_some
    (boundary : ReferenceInitializationRun.Boundary p)
    (player : Fin p.m) (time : Fin p.T)
    (htime : time.val < ReferenceInitializationRun.elapsed p boundary.completed) :
    generatedBoundaryOwnEntry boundary player time =
      some (boundary.history player ⟨time.val, htime⟩) := by
  simp [generatedBoundaryOwnEntry, htime]

theorem generatedBoundaryOwnEntry_eq_cast
    (boundary : ReferenceInitializationRun.Boundary p)
    (player : Fin p.m) (time : Fin p.T)
    (hstart : ReferenceInitializationRun.elapsed p boundary.completed = p.T) :
    generatedBoundaryOwnEntry boundary player time =
      some (boundary.history player (Fin.cast hstart.symm time)) := by
  rw [generatedBoundaryOwnEntry_eq_some boundary player time (by rw [hstart]; exact time.isLt)]
  apply congrArg (fun index : Fin (ReferenceInitializationRun.elapsed p boundary.completed) =>
    some (boundary.history player index))
  apply Fin.ext
  rfl

/-- The source-generated physical start, including the terminal sentinel case.
-/
def physicalStart (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : ℕ :=
  ReferenceInitializationRun.elapsed p
    (generatedBoundary rate source rewards C_star C_h).completed

theorem physicalStart_le_T (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    physicalStart rate source rewards C_star C_h ≤ p.T := by
  exact ReferenceInitializationRun.elapsed_le_T p
    (generatedBoundary rate source rewards C_star C_h).completed

theorem correctedLaunch_none_start_eq_T (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none) :
    physicalStart rate source rewards C_star C_h = p.T := by
  have hcross := (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
    rate source rewards C_star C_h).mp hlaunch
  have hsource := ReferenceCorrectedInitializationLaunch.correctedLaunch_no_crossing_source
    rate source rewards C_star C_h (by simpa [generatedInput, generatedBoundary] using hcross)
  simpa [physicalStart, generatedBoundary, generatedInput] using hsource.2.1

/-- The active mode follows from this source-generated `some` launch.  The
launch equation identifies the existential state with the actual option
payload, so no state is chosen independently. -/
theorem activeMode_of_launch_eq_some (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (active : State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active) :
    ReferenceActivePhysicalHorizon.allActiveAtStart active
      (physicalStart rate source rewards C_star C_h) := by
  have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h).isSome = true := by
    rw [hlaunch]
    rfl
  have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate source rewards C_star C_h).mp hsome
  obtain ⟨actual, hactual, hmode⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_all_active_at_start
      rate source rewards C_star C_h hc
  have hstate : active = actual := Option.some.inj (hlaunch.symm.trans hactual)
  subst actual
  simpa [physicalStart, generatedBoundary, generatedInput] using hmode

/-- The actual option payload, projected only under proof that the accepted
corrected launch is present. -/
def correctedLaunchPayload (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h ≠ none) : State p rate :=
  let launch := ReferenceCorrectedInitializationLaunch.correctedLaunch
    rate source rewards C_star C_h
  launch.get (Option.ne_none_iff_isSome.mp hnone)

theorem correctedLaunch_eq_some_payload (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h ≠ none) :
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
      some (correctedLaunchPayload rate source rewards C_star C_h hnone) := by
  unfold correctedLaunchPayload
  exact Option.eq_some_of_isSome (Option.ne_none_iff_isSome.mp hnone)

/-- The literal existing active-horizon computation for the actual launch
payload. The only proof arguments are derived from the corrected launch and
its generated elapsed time. -/
def correctedSuffixRun (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h ≠ none) :
    ReferenceActivePhysicalHorizon.Run
      (correctedLaunchPayload rate source rewards C_star C_h hnone) :=
  let active := correctedLaunchPayload rate source rewards C_star C_h hnone
  let hlaunch := correctedLaunch_eq_some_payload rate source rewards C_star C_h hnone
  ReferenceActivePhysicalHorizon.run active source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    (physicalStart rate source rewards C_star C_h)
    (p.T - physicalStart rate source rewards C_star C_h)
    (by
      have hs := physicalStart_le_T rate source rewards C_star C_h
      omega)
    (activeMode_of_launch_eq_some rate source rewards C_star C_h active hlaunch)

theorem correctedSuffixRun_record_count (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h ≠ none) :
    (correctedSuffixRun rate source rewards C_star C_h hnone).records.length =
      p.T - physicalStart rate source rewards C_star C_h := by
  exact ReferenceActivePhysicalHorizon.run_record_count
    (correctedLaunchPayload rate source rewards C_star C_h hnone) source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    (physicalStart rate source rewards C_star C_h)
    (p.T - physicalStart rate source rewards C_star C_h) (by
      have hs := physicalStart_le_T rate source rewards C_star C_h
      omega)
    (activeMode_of_launch_eq_some rate source rewards C_star C_h
      (correctedLaunchPayload rate source rewards C_star C_h hnone)
      (correctedLaunch_eq_some_payload rate source rewards C_star C_h hnone))

/-- Suffix records are empty exactly when the launch option is `none`; on a
`some` branch they are the complete chronological records of the literal
existing horizon run. -/
def completeSuffixRecords (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : List (RoundRecord p rate) :=
  if hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none then
    []
  else
    (correctedSuffixRun rate source rewards C_star C_h hnone).records

/-- The terminal state projection retains absence of a launch as `none` and
otherwise is the literal final state of the canonical active horizon. -/
def completeTerminalState (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : Option (State p rate) :=
  if hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none then
    none
  else
    some (correctedSuffixRun rate source rewards C_star C_h hnone).finalState

/-- Full suffix evidence keeps actual states, timestamps, actions, complete
grid feedback, own observations and both coordinator and follower diagnostics.
It intentionally projects away the unused whole-row field in each raw
`RoundRecord.input`; raw records need not be equal when unselected rows differ.
-/
def completeSuffixEvidence (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : List (RoundEvidence p rate) :=
  (completeSuffixRecords rate source rewards C_star C_h).map
    ReferenceActivePhysicalHorizon.RoundRecord.evidence

/-- The retained diagnostics as a direct projection of full suffix evidence.
-/
def completeSuffixDiagnostics (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : List (CoordinatorObservation p rate ×
      (Fin (p.m - 1) → FollowerObservation p rate)) :=
  (completeSuffixEvidence rate source rewards C_star C_h).map
    (fun evidence => (evidence.coordinator, evidence.followers))

/-- A complete own history is the generated prefix followed by the actual
selected-row physical suffix. The no-launch branch uses the source proof that
the generated boundary already reaches `T`; no default observation is used.
-/
def completeOwnHistory (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (player : Fin p.m) : LocalHistory p p.T :=
  if hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none then
    let hstart := correctedLaunch_none_start_eq_T rate source rewards C_star C_h hnone
    fun t =>
      (generatedBoundary rate source rewards C_star C_h).history player
        (Fin.cast hstart.symm t)
  else
    let start := physicalStart rate source rewards C_star C_h
    let execution := correctedSuffixRun rate source rewards C_star C_h hnone
    fun t =>
      if ht : t.val < start then
        (generatedBoundary rate source rewards C_star C_h).history player
          ⟨t.val, ht⟩
      else
        let offset : Fin (p.T - start) := ⟨t.val - start, by
          have htT := t.isLt
          have hstart := physicalStart_le_T rate source rewards C_star C_h
          have hge : start ≤ t.val := Nat.le_of_not_gt ht
          omega⟩
        let record : RoundRecord p rate := execution.records.get ⟨offset.val, by
          rw [correctedSuffixRun_record_count rate source rewards C_star C_h hnone]
          exact offset.isLt⟩
        record.ownEntries player

/-- Every prefix coordinate is exactly the same generated initialization
entry, with the natural inclusion of `Fin physicalStart` into `Fin T`. -/
theorem completeOwnHistory_prefix (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (player : Fin p.m)
    (time : Fin p.T)
    (htime : time.val < physicalStart rate source rewards C_star C_h) :
    completeOwnHistory rate source rewards C_star C_h player time =
      (generatedBoundary rate source rewards C_star C_h).history player
        ⟨time.val, htime⟩ := by
  by_cases hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none
  · have hstart := correctedLaunch_none_start_eq_T rate source rewards C_star C_h hnone
    simp only [completeOwnHistory, dite_eq_left hnone]
    apply congrArg ((generatedBoundary rate source rewards C_star C_h).history player)
    apply Fin.ext
    rfl
  · simp [completeOwnHistory, hnone, htime]

/-- The active suffix coordinate at offset `k` is the own entry of exactly the
`k`th retained physical round record. -/
theorem completeOwnHistory_suffix (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (player : Fin p.m) (active : State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active)
    (k : Fin (p.T - physicalStart rate source rewards C_star C_h)) :
    completeOwnHistory rate source rewards C_star C_h player
      ⟨physicalStart rate source rewards C_star C_h + k.val,
        by have hs := physicalStart_le_T rate source rewards C_star C_h; omega⟩ =
      ((correctedSuffixRun rate source rewards C_star C_h
          (by rw [hlaunch]; simp)).records.get
        ⟨k.val, by
          rw [correctedSuffixRun_record_count rate source rewards C_star C_h
            (by rw [hlaunch]; simp)]
          exact k.isLt⟩).ownEntries player := by
  have htime : ¬ physicalStart rate source rewards C_star C_h + k.val <
      physicalStart rate source rewards C_star C_h := by omega
  have hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h ≠ none := by rw [hlaunch]; simp
  simp [completeOwnHistory, hnone, htime]

/-- The suffix records retain precisely the physical calendar interval
`[start,T)`: no record uses the terminal sentinel, and the first calendar
coordinate is the start itself when the interval is nonempty. -/
theorem completeSuffixRecords_time_values (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    (completeSuffixRecords rate source rewards C_star C_h).map
      (fun record => record.input.time.val) =
      ReferenceActivePhysicalHorizon.calendar (physicalStart rate source rewards C_star C_h)
        (p.T - physicalStart rate source rewards C_star C_h) := by
  by_cases hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none
  · have hstart := correctedLaunch_none_start_eq_T rate source rewards C_star C_h hnone
    simp [completeSuffixRecords, hnone, hstart, ReferenceActivePhysicalHorizon.calendar]
  · simpa [completeSuffixRecords, hnone, correctedSuffixRun,
      ReferenceActivePhysicalHorizon.calendar] using
      (ReferenceActivePhysicalHorizon.run_time_values
        (correctedLaunchPayload rate source rewards C_star C_h hnone) source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (physicalStart rate source rewards C_star C_h)
        (p.T - physicalStart rate source rewards C_star C_h) (by
          have hs := physicalStart_le_T rate source rewards C_star C_h
          omega)
        (activeMode_of_launch_eq_some rate source rewards C_star C_h
          (correctedLaunchPayload rate source rewards C_star C_h hnone)
          (correctedLaunch_eq_some_payload rate source rewards C_star C_h hnone)))

/-- The suffix list has exactly its interval length; adjoining it to the
generated prefix accounts for all `T` coordinates once. -/
theorem completeSuffixRecords_length (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    (completeSuffixRecords rate source rewards C_star C_h).length =
      p.T - physicalStart rate source rewards C_star C_h := by
  by_cases hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none
  · have hstart := correctedLaunch_none_start_eq_T rate source rewards C_star C_h hnone
    simp [completeSuffixRecords, hnone, hstart]
  · simpa [completeSuffixRecords, hnone] using
      correctedSuffixRun_record_count rate source rewards C_star C_h hnone

private theorem activeHorizonRun_eq_of_initial_eq
    {rate : RateInput p}
    (active active' : State p (rate := rate))
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active start)
    (hmode' : ReferenceActivePhysicalHorizon.allActiveAtStart active' start)
    (hactive : active = active') :
    (ReferenceActivePhysicalHorizon.run active rows selected rewards start count hspan hmode).finalState =
        (ReferenceActivePhysicalHorizon.run active' rows selected rewards start count hspan hmode').finalState ∧
      (ReferenceActivePhysicalHorizon.run active rows selected rewards start count hspan hmode).records =
        (ReferenceActivePhysicalHorizon.run active' rows selected rewards start count hspan hmode').records := by
  cases hactive
  have hm : hmode = hmode' := Subsingleton.elim _ _
  subst hmode'
  exact ⟨rfl, rfl⟩

/-- On the active option branch, the retained suffix records are exactly the
records of the existing physical horizon run from this launch state, using
the original complete row table, selected row and reward table through `T`.
-/
theorem completeSuffixRecords_on_launch (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (active : State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active) :
    completeSuffixRecords rate source rewards C_star C_h =
      (ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (physicalStart rate source rewards C_star C_h)
        (p.T - physicalStart rate source rewards C_star C_h)
        (by
          have hs := physicalStart_le_T rate source rewards C_star C_h
          omega)
        (activeMode_of_launch_eq_some rate source rewards C_star C_h active hlaunch)).records := by
  have hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h ≠ none := by rw [hlaunch]; simp
  have hpayload : correctedLaunchPayload rate source rewards C_star C_h hnone = active :=
    Option.some.inj ((correctedLaunch_eq_some_payload rate source rewards C_star C_h hnone).symm.trans hlaunch)
  have hspan : physicalStart rate source rewards C_star C_h +
      (p.T - physicalStart rate source rewards C_star C_h) ≤ p.T := by
    have hs := physicalStart_le_T rate source rewards C_star C_h
    omega
  have hmodePayload := activeMode_of_launch_eq_some rate source rewards C_star C_h
    (correctedLaunchPayload rate source rewards C_star C_h hnone)
    (correctedLaunch_eq_some_payload rate source rewards C_star C_h hnone)
  have hrun := activeHorizonRun_eq_of_initial_eq
    (correctedLaunchPayload rate source rewards C_star C_h hnone) active source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    (physicalStart rate source rewards C_star C_h)
    (p.T - physicalStart rate source rewards C_star C_h) hspan hmodePayload
    (activeMode_of_launch_eq_some rate source rewards C_star C_h active hlaunch) hpayload
  simp only [completeSuffixRecords, dite_eq_right hnone]
  calc
    (correctedSuffixRun rate source rewards C_star C_h hnone).records =
        (ReferenceActivePhysicalHorizon.run
          (correctedLaunchPayload rate source rewards C_star C_h hnone) source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          (physicalStart rate source rewards C_star C_h)
          (p.T - physicalStart rate source rewards C_star C_h) hspan hmodePayload).records := by
            rfl
    _ = (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          (physicalStart rate source rewards C_star C_h)
          (p.T - physicalStart rate source rewards C_star C_h) hspan
          (activeMode_of_launch_eq_some rate source rewards C_star C_h active hlaunch)).records := hrun.2

/-- The active terminal option is exactly the final state of the same
existing physical horizon run characterized by `completeSuffixRecords_on_launch`.
-/
theorem completeTerminalState_on_launch (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (active : State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active) :
    completeTerminalState rate source rewards C_star C_h =
      some (ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (physicalStart rate source rewards C_star C_h)
        (p.T - physicalStart rate source rewards C_star C_h)
        (by
          have hs := physicalStart_le_T rate source rewards C_star C_h
          omega)
        (activeMode_of_launch_eq_some rate source rewards C_star C_h active hlaunch)).finalState := by
  have hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h ≠ none := by rw [hlaunch]; simp
  have hpayload : correctedLaunchPayload rate source rewards C_star C_h hnone = active :=
    Option.some.inj ((correctedLaunch_eq_some_payload rate source rewards C_star C_h hnone).symm.trans hlaunch)
  have hspan : physicalStart rate source rewards C_star C_h +
      (p.T - physicalStart rate source rewards C_star C_h) ≤ p.T := by
    have hs := physicalStart_le_T rate source rewards C_star C_h
    omega
  have hmodePayload := activeMode_of_launch_eq_some rate source rewards C_star C_h
    (correctedLaunchPayload rate source rewards C_star C_h hnone)
    (correctedLaunch_eq_some_payload rate source rewards C_star C_h hnone)
  have hrun := activeHorizonRun_eq_of_initial_eq
    (correctedLaunchPayload rate source rewards C_star C_h hnone) active source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    (physicalStart rate source rewards C_star C_h)
    (p.T - physicalStart rate source rewards C_star C_h) hspan hmodePayload
    (activeMode_of_launch_eq_some rate source rewards C_star C_h active hlaunch) hpayload
  simp only [completeTerminalState, dite_eq_right hnone]
  calc
    some (correctedSuffixRun rate source rewards C_star C_h hnone).finalState =
        some (ReferenceActivePhysicalHorizon.run
          (correctedLaunchPayload rate source rewards C_star C_h hnone) source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          (physicalStart rate source rewards C_star C_h)
          (p.T - physicalStart rate source rewards C_star C_h) hspan hmodePayload).finalState := by
            rfl
    _ = some (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          (physicalStart rate source rewards C_star C_h)
          (p.T - physicalStart rate source rewards C_star C_h) hspan
          (activeMode_of_launch_eq_some rate source rewards C_star C_h active hlaunch)).finalState :=
            congrArg some hrun.1

/-- The run's evidence projection retains its actual states, action profile,
grid feedback, own observations, and full coordinator/follower diagnostics.
-/
theorem completeSuffixEvidence_on_launch (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (active : State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active) :
    completeSuffixEvidence rate source rewards C_star C_h =
      ((ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (physicalStart rate source rewards C_star C_h)
        (p.T - physicalStart rate source rewards C_star C_h)
        (by
          have hs := physicalStart_le_T rate source rewards C_star C_h
          omega)
        (activeMode_of_launch_eq_some rate source rewards C_star C_h active hlaunch)).records.map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence) := by
  change (completeSuffixRecords rate source rewards C_star C_h).map
      ReferenceActivePhysicalHorizon.RoundRecord.evidence = _
  exact congrArg (fun records => records.map
    ReferenceActivePhysicalHorizon.RoundRecord.evidence)
      (completeSuffixRecords_on_launch rate source rewards C_star C_h active hlaunch)

/-- The diagnostic projection is the coordinator and follower diagnostic
pair from every actual evidence record in the canonical run. -/
theorem completeSuffixDiagnostics_on_launch (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (active : State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active) :
    completeSuffixDiagnostics rate source rewards C_star C_h =
      ((ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (physicalStart rate source rewards C_star C_h)
        (p.T - physicalStart rate source rewards C_star C_h)
        (by
          have hs := physicalStart_le_T rate source rewards C_star C_h
          omega)
        (activeMode_of_launch_eq_some rate source rewards C_star C_h active hlaunch)).records.map
          (fun record => (record.evidence.coordinator, record.evidence.followers))) := by
  change (completeSuffixEvidence rate source rewards C_star C_h).map
      (fun evidence => (evidence.coordinator, evidence.followers)) = _
  rw [completeSuffixEvidence_on_launch rate source rewards C_star C_h active hlaunch]
  simp only [List.map_map, Function.comp_def]

/-- The records above are connected from this source-generated active state
to that same run's endpoint, so every literal transition and exceptional path
is retained in order. -/
theorem completeSuffix_connected_on_launch (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (active : State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active) :
    ReferenceActivePhysicalHorizon.Connected active
      (completeSuffixRecords rate source rewards C_star C_h)
      (ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (physicalStart rate source rewards C_star C_h)
        (p.T - physicalStart rate source rewards C_star C_h)
        (by
          have hs := physicalStart_le_T rate source rewards C_star C_h
          omega)
        (activeMode_of_launch_eq_some rate source rewards C_star C_h active hlaunch)).finalState := by
  rw [completeSuffixRecords_on_launch rate source rewards C_star C_h active hlaunch]
  exact (ReferenceActivePhysicalHorizon.run active source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    (physicalStart rate source rewards C_star C_h)
    (p.T - physicalStart rate source rewards C_star C_h)
    (by
      have hs := physicalStart_le_T rate source rewards C_star C_h
      omega)
    (activeMode_of_launch_eq_some rate source rewards C_star C_h active hlaunch)).connected

/-- The accepted active horizon preserves every source-generated activation
while it executes the entire physical suffix. -/
theorem completeSuffix_activations_preserved_on_launch (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (active : State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active) :
    (ReferenceActivePhysicalHorizon.run active source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      (physicalStart rate source rewards C_star C_h)
      (p.T - physicalStart rate source rewards C_star C_h)
      (by
        have hs := physicalStart_le_T rate source rewards C_star C_h
        omega)
      (activeMode_of_launch_eq_some rate source rewards C_star C_h active hlaunch)).finalState.activations =
        active.activations :=
  (ReferenceActivePhysicalHorizon.run active source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    (physicalStart rate source rewards C_star C_h)
    (p.T - physicalStart rate source rewards C_star C_h)
    (by
      have hs := physicalStart_le_T rate source rewards C_star C_h
      omega)
    (activeMode_of_launch_eq_some rate source rewards C_star C_h active hlaunch)).activations_preserved

/-- No crossing retains the existing initializer's `T+1` launch sentinel. -/
theorem no_launch_sentinel_round (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none) :
    ReferenceInitializationRun.launchRound
      (generatedInput rate source rewards C_star C_h) = p.T + 1 := by
  have hcross := (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
    rate source rewards C_star C_h).mp hlaunch
  have hsource := ReferenceCorrectedInitializationLaunch.correctedLaunch_no_crossing_source
    rate source rewards C_star C_h (by simpa [generatedInput, generatedBoundary] using hcross)
  simpa [generatedInput] using hsource.2.2.1

/-- A terminal crossing has the same `T+1` sentinel as exhaustion while its
launch option and terminal active state remain present. -/
theorem terminal_crossing_sentinel_round (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (active : State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active)
    (hterminal : physicalStart rate source rewards C_star C_h = p.T) :
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h ≠ none ∧
      ReferenceInitializationRun.launchRound
        (generatedInput rate source rewards C_star C_h) = p.T + 1 := by
  have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h).isSome = true := by rw [hlaunch]; rfl
  have hcross := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate source rewards C_star C_h).mp hsome
  have hterminal' : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = p.T := by
    simpa [physicalStart, generatedBoundary, generatedInput] using hterminal
  simpa [generatedInput] using
    ReferenceCorrectedInitializationLaunch.correctedLaunch_terminal_crossing
      rate source rewards C_star C_h hcross hterminal'

/-- On exhaustion, the complete history is exactly the generated initializer
through physical round `T`, and there is no active terminal state. -/
theorem no_launch_complete_history (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none) :
    physicalStart rate source rewards C_star C_h = p.T ∧
    completeSuffixRecords rate source rewards C_star C_h = [] ∧
    completeTerminalState rate source rewards C_star C_h = none ∧
    (∀ player time,
      completeOwnHistory rate source rewards C_star C_h player time =
        (generatedBoundary rate source rewards C_star C_h).history player
        (Fin.cast (correctedLaunch_none_start_eq_T rate source rewards C_star C_h hlaunch).symm time)) := by
  have hstart := correctedLaunch_none_start_eq_T rate source rewards C_star C_h hlaunch
  refine ⟨hstart, ?_, ?_, ?_⟩
  · simp [completeSuffixRecords, hlaunch]
  · simp [completeTerminalState, hlaunch]
  · intro player time
    simp [completeOwnHistory, hlaunch]

/-- At a crossing exactly at `T`, the computed active option remains present,
but its physical suffix is empty and its terminal state is the launch state.
The full history is still the generated prefix. -/
theorem terminal_crossing_complete_history (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (active : State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active)
    (hterminal : physicalStart rate source rewards C_star C_h = p.T) :
    completeSuffixRecords rate source rewards C_star C_h = [] ∧
    completeTerminalState rate source rewards C_star C_h = some active ∧
    (∀ player time,
      completeOwnHistory rate source rewards C_star C_h player time =
        (generatedBoundary rate source rewards C_star C_h).history player
          (Fin.cast hterminal.symm time)) := by
  have hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h ≠ none := by rw [hlaunch]; simp
  have hpayload : correctedLaunchPayload rate source rewards C_star C_h hnone = active :=
    Option.some.inj ((correctedLaunch_eq_some_payload rate source rewards C_star C_h hnone).symm.trans hlaunch)
  have hcount := correctedSuffixRun_record_count rate source rewards C_star C_h hnone
  have hzero : p.T - physicalStart rate source rewards C_star C_h = 0 := by omega
  have hrecordsRun : (correctedSuffixRun rate source rewards C_star C_h hnone).records = [] :=
    List.eq_nil_of_length_eq_zero (by simpa [hzero] using hcount)
  have hmodeT : ReferenceActivePhysicalHorizon.allActiveAtStart active p.T := by
    rw [← hterminal]
    exact activeMode_of_launch_eq_some rate source rewards C_star C_h active hlaunch
  have hfinal := ReferenceActivePhysicalHorizon.run_zero_final active source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards p.T (by omega)
    hmodeT
  have hfinal' : (correctedSuffixRun rate source rewards C_star C_h hnone).finalState = active := by
    cases hpayload
    simpa [correctedSuffixRun, hterminal] using hfinal
  refine ⟨?_, ?_, ?_⟩
  · simpa [completeSuffixRecords, hnone] using hrecordsRun
  · simp only [completeTerminalState, dite_eq_right hnone]
    exact congrArg some hfinal'
  · intro player time
    have htime : time.val < physicalStart rate source rewards C_star C_h := by
      rw [hterminal]
      exact time.isLt
    have hprefix := completeOwnHistory_prefix rate source rewards C_star C_h player time
      htime
    calc
      completeOwnHistory rate source rewards C_star C_h player time =
          (generatedBoundary rate source rewards C_star C_h).history player
            ⟨time.val, htime⟩ := hprefix
      _ = (generatedBoundary rate source rewards C_star C_h).history player
          (Fin.cast hterminal.symm time) := by
            congr 1

/-- The already accepted failure-provenance equation for the generated
boundary. This module retains that original event and does not define a second
initialization-failure event. -/
theorem generated_failure_provenance (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    (∃ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.initializationFailure
        (generatedInput rate source rewards C_star C_h)
        (generatedBoundary rate source rewards C_star C_h) i = true) ↔
      InitializationFailureProvenance.operationalInitializationFailure
        (generatedInput rate source rewards C_star C_h) := by
  simpa [generatedInput, generatedBoundary] using
    ReferenceCorrectedInitializationLaunch.correctedLaunch_failure_provenance
      rate source rewards C_star C_h

private theorem generatedInput_eq_of_source_data (rate : RateInput p)
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p))
    (hids : source.1.1 = source'.1.1)
    (hprivate : source.2 = source'.2)
    (hq : ActualInitializationPhysicalStep.selectedRowIndex p source = q)
    (hrow : source.1.2 q = source'.1.2 q) :
    generatedInput rate source rewards C_star C_h =
      generatedInput rate source' rewards C_star C_h := by
  have hJ : source.2.1.2 = source'.2.1.2 :=
    congrArg (fun z : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p => z.1.2)
      hprivate
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source =
      ActualInitializationPhysicalStep.selectedRowIndex p source' := by
    unfold ActualInitializationPhysicalStep.selectedRowIndex
    exact congrArg (PrivateSourceStreams.coordinatorIndex p) hJ
  have hselectedRow :
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) =
        source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source') := by
    have hselected' : ActualInitializationPhysicalStep.selectedRowIndex p source' = q :=
      hselected.symm.trans hq
    rw [hq, hselected']
    exact hrow
  unfold generatedInput ActualReferenceInitializationBlock.referenceInput
  simp only [ReferenceInitializationRun.Input.mk.injEq]
  exact ⟨hids, hselectedRow, trivial, hprivate, trivial, trivial, trivial⟩

private theorem ordinary_eq_of_input_boundary_eq
    (x x' : ReferenceInitializationRun.Input p)
    (b b' : ReferenceInitializationRun.Boundary p)
    (i : ActiveRoundActions.Follower p.m)
    (hx : x = x') (hb : b = b') :
    Eq.mp (congrArg (fun z : ReferenceInitializationRun.Input p =>
          ReferencePrelaunchFollower.State p z.eta) hx)
        (ReferenceInitializationRun.ordinary x b i) =
      ReferenceInitializationRun.ordinary x' b' i := by
  cases hx
  cases hb
  rfl

/-- Equality of the original ID array, all original private coordinates
(including the source `J` scalar), and the complete selected row gives the
literal generated-prefix and launch equalities. -/
theorem generatedInput_and_launch_eq_of_source_data (rate : RateInput p)
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p))
    (hids : source.1.1 = source'.1.1)
    (hprivate : source.2 = source'.2)
    (hq : ActualInitializationPhysicalStep.selectedRowIndex p source = q)
    (hrow : source.1.2 q = source'.1.2 q) :
    generatedInput rate source rewards C_star C_h =
        generatedInput rate source' rewards C_star C_h ∧
      generatedBoundary rate source rewards C_star C_h =
        generatedBoundary rate source' rewards C_star C_h ∧
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
        ReferenceCorrectedInitializationLaunch.correctedLaunch rate source' rewards C_star C_h := by
  have hx := generatedInput_eq_of_source_data rate source source' rewards C_star C_h q
    hids hprivate hq hrow
  refine ⟨hx, ?_, ?_⟩
  · exact congrArg ReferenceInitializationRun.output hx
  · have hx' : ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate =
        ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate := by
      simpa [generatedInput] using hx
    have hordinary : ∀ i : ActiveRoundActions.Follower p.m,
        ReferenceInitializationRun.ordinary
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)) i =
          ReferenceInitializationRun.ordinary
            (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)) i := by
      intro i
      have hordinaryEq := ordinary_eq_of_input_boundary_eq
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
        (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate))
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate))
        i hx' rfl
      have htransport :
          Eq.mp (congrArg (fun z : ReferenceInitializationRun.Input p =>
            ReferencePrelaunchFollower.State p z.eta) hx')
              (ReferenceInitializationRun.ordinary
                (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
                (ReferenceInitializationRun.output
                  (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)) i) =
            ReferenceInitializationRun.ordinary
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
              (ReferenceInitializationRun.output
                (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)) i := by
        have hproof :
            congrArg (fun z : ReferenceInitializationRun.Input p =>
              ReferencePrelaunchFollower.State p z.eta) hx' = rfl := Subsingleton.elim _ _
        rw [hproof]
        rfl
      rw [htransport] at hordinaryEq
      simpa [ActualReferenceInitializationBlock.referenceInput] using hordinaryEq
    have hordinaryFun := funext hordinary
    unfold ReferenceCorrectedInitializationLaunch.correctedLaunch
    simp [hx', hordinaryFun]

/-- Selected-row dependence of the complete own-history projection. All
unselected complete rows and every original private coordinate stay present;
only equality of the actual selected row is used. -/
theorem completeOwnHistory_eq_of_source_data (rate : RateInput p)
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p))
    (hids : source.1.1 = source'.1.1)
    (hprivate : source.2 = source'.2)
    (hq : ActualInitializationPhysicalStep.selectedRowIndex p source = q)
    (hrow : source.1.2 q = source'.1.2 q) (player : Fin p.m) :
    completeOwnHistory rate source rewards C_star C_h player =
      completeOwnHistory rate source' rewards C_star C_h player := by
  obtain ⟨hx, hboundary, hlaunch⟩ := generatedInput_and_launch_eq_of_source_data
    rate source source' rewards C_star C_h q hids hprivate hq hrow
  by_cases hnoneL : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none
  · have hnoneR : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source' rewards C_star C_h = none := by rw [← hlaunch, hnoneL]
    have hstartL := correctedLaunch_none_start_eq_T rate source rewards C_star C_h hnoneL
    have hstartR := correctedLaunch_none_start_eq_T rate source' rewards C_star C_h hnoneR
    funext time
    have hsourceEntry := congrArg
      (fun boundary => generatedBoundaryOwnEntry boundary player time) hboundary
    have hleft : generatedBoundaryOwnEntry
        (generatedBoundary rate source rewards C_star C_h) player time =
        some (completeOwnHistory rate source rewards C_star C_h player time) := by
      simpa [completeOwnHistory, hnoneL, generatedBoundary] using
        generatedBoundaryOwnEntry_eq_cast
          (generatedBoundary rate source rewards C_star C_h) player time hstartL
    have hright : generatedBoundaryOwnEntry
        (generatedBoundary rate source' rewards C_star C_h) player time =
        some (completeOwnHistory rate source' rewards C_star C_h player time) := by
      simpa [completeOwnHistory, hnoneR, generatedBoundary] using
        generatedBoundaryOwnEntry_eq_cast
          (generatedBoundary rate source' rewards C_star C_h) player time hstartR
    rw [hleft, hright] at hsourceEntry
    exact Option.some.inj hsourceEntry
  · have hnoneR : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source' rewards C_star C_h ≠ none := by
      intro h
      apply hnoneL
      rw [hlaunch, h]
    let activeL := correctedLaunchPayload rate source rewards C_star C_h hnoneL
    let activeR := correctedLaunchPayload rate source' rewards C_star C_h hnoneR
    have hactive : activeL = activeR := Option.some.inj
      ((correctedLaunch_eq_some_payload rate source rewards C_star C_h hnoneL).symm.trans
        (hlaunch.trans (correctedLaunch_eq_some_payload rate source' rewards C_star C_h hnoneR)))
    have hpayloadEq : correctedLaunchPayload rate source rewards C_star C_h hnoneL =
        correctedLaunchPayload rate source' rewards C_star C_h hnoneR := by
      change activeL = activeR
      exact hactive
    have hstart : physicalStart rate source rewards C_star C_h =
        physicalStart rate source' rewards C_star C_h :=
      congrArg (fun b : ReferenceInitializationRun.Boundary p =>
        ReferenceInitializationRun.elapsed p b.completed) hboundary
    let leftRun := correctedSuffixRun rate source rewards C_star C_h hnoneL
    let rightRun := correctedSuffixRun rate source' rewards C_star C_h hnoneR
    have hlaunchL := correctedLaunch_eq_some_payload rate source rewards C_star C_h hnoneL
    have hmode := activeMode_of_launch_eq_some rate source rewards C_star C_h activeL hlaunchL
    have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source =
        ActualInitializationPhysicalStep.selectedRowIndex p source' := by
      change PrivateSourceStreams.coordinatorIndex p source.2.1.2 =
        PrivateSourceStreams.coordinatorIndex p source'.2.1.2
      rw [hprivate]
    have hselected' : ActualInitializationPhysicalStep.selectedRowIndex p source' = q :=
      hselected.symm.trans hq
    have hspanL : physicalStart rate source rewards C_star C_h +
        (p.T - physicalStart rate source rewards C_star C_h) ≤ p.T := by
      have hs := physicalStart_le_T rate source rewards C_star C_h
      omega
    have hruns := ReferenceActivePhysicalHorizon.run_rows_eq activeL source.1.2 source'.1.2
      q rewards (physicalStart rate source rewards C_star C_h)
      (p.T - physicalStart rate source rewards C_star C_h) (by
        have hs := physicalStart_le_T rate source rewards C_star C_h
        omega) hmode hrow
    have hrows : leftRun.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence =
        rightRun.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
      have hrunL : leftRun = ReferenceActivePhysicalHorizon.run activeL source.1.2 q rewards
          (physicalStart rate source rewards C_star C_h)
          (p.T - physicalStart rate source rewards C_star C_h) hspanL hmode := by
        dsimp only [leftRun, correctedSuffixRun]
        rw [hq]
      have hlaunchR := correctedLaunch_eq_some_payload rate source' rewards C_star C_h hnoneR
      have hmodeR := activeMode_of_launch_eq_some rate source' rewards C_star C_h activeR hlaunchR
      have hmodeR' : ReferenceActivePhysicalHorizon.allActiveAtStart activeR
          (physicalStart rate source rewards C_star C_h) := by
        rw [hstart]
        exact hmodeR
      have hrunR : rightRun = ReferenceActivePhysicalHorizon.run activeR source'.1.2 q rewards
          (physicalStart rate source rewards C_star C_h)
          (p.T - physicalStart rate source rewards C_star C_h) hspanL hmodeR' := by
        dsimp only [rightRun, correctedSuffixRun, activeR]
        simp only [hselected', ← hstart]
      have hrunState := activeHorizonRun_eq_of_initial_eq activeR activeL source'.1.2 q rewards
        (physicalStart rate source rewards C_star C_h)
        (p.T - physicalStart rate source rewards C_star C_h) hspanL
        hmodeR' hmode hactive.symm
      calc
        leftRun.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence =
            (ReferenceActivePhysicalHorizon.run activeL source.1.2 q rewards
              (physicalStart rate source rewards C_star C_h)
              (p.T - physicalStart rate source rewards C_star C_h) hspanL hmode).records.map
                ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
                  exact congrArg (fun run => run.records.map
                    ReferenceActivePhysicalHorizon.RoundRecord.evidence) hrunL
        _ = (ReferenceActivePhysicalHorizon.run activeL source'.1.2 q rewards
              (physicalStart rate source rewards C_star C_h)
              (p.T - physicalStart rate source rewards C_star C_h) hspanL hmode).records.map
                ReferenceActivePhysicalHorizon.RoundRecord.evidence := hruns.2
        _ = (ReferenceActivePhysicalHorizon.run activeR source'.1.2 q rewards
              (physicalStart rate source rewards C_star C_h)
              (p.T - physicalStart rate source rewards C_star C_h) hspanL hmodeR').records.map
                ReferenceActivePhysicalHorizon.RoundRecord.evidence :=
                  congrArg (fun records => records.map
                    ReferenceActivePhysicalHorizon.RoundRecord.evidence) hrunState.2.symm
        _ = rightRun.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
                  exact congrArg (fun run => run.records.map
                    ReferenceActivePhysicalHorizon.RoundRecord.evidence) hrunR.symm
    have hcountL := correctedSuffixRun_record_count rate source rewards C_star C_h hnoneL
    have hcountR := correctedSuffixRun_record_count rate source' rewards C_star C_h hnoneR
    funext time
    by_cases htime : time.val < physicalStart rate source rewards C_star C_h
    · have htimeR : time.val < physicalStart rate source' rewards C_star C_h := by
        rw [← hstart]
        exact htime
      have hsourceEntry := congrArg
        (fun boundary => generatedBoundaryOwnEntry boundary player time) hboundary
      have hleft := generatedBoundaryOwnEntry_eq_some
        (generatedBoundary rate source rewards C_star C_h) player time htime
      have hright := generatedBoundaryOwnEntry_eq_some
        (generatedBoundary rate source' rewards C_star C_h) player time htimeR
      rw [hleft, hright] at hsourceEntry
      have hprefix := Option.some.inj hsourceEntry
      simpa [completeOwnHistory, hnoneL, hnoneR, htime, htimeR] using hprefix
    · let offset : Fin (p.T - physicalStart rate source rewards C_star C_h) :=
        ⟨time.val - physicalStart rate source rewards C_star C_h, by
          have hT := time.isLt
          omega⟩
      have hcoordinate : time =
          ⟨physicalStart rate source rewards C_star C_h + offset.val, by
            have hT := time.isLt
            omega⟩ := by
        apply Fin.ext
        simp [offset]
        omega
      have hidxL : offset.val < leftRun.records.length := by
        rw [hcountL]
        exact offset.isLt
      have hidxR : offset.val < rightRun.records.length := by
        rw [hcountR]
        have hs := physicalStart_le_T rate source' rewards C_star C_h
        have ht := time.isLt
        omega
      have hmapGet? := congrArg
        (fun records : List (RoundEvidence p rate) => records[offset.val]?) hrows
      rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using hidxL),
        List.getElem?_eq_getElem (by simpa only [List.length_map] using hidxR)] at hmapGet?
      have hmapGet := Option.some.inj hmapGet?
      have hentry : (leftRun.records.get ⟨offset.val, hidxL⟩).ownEntries player =
          (rightRun.records.get ⟨offset.val, hidxR⟩).ownEntries player := by
        have he := congrArg (fun evidence : RoundEvidence p rate => evidence.ownEntries player) hmapGet
        simpa only [List.get_eq_getElem, List.getElem_map,
          ReferenceActivePhysicalHorizon.RoundRecord.evidence,
          ReferenceActivePhysicalHorizon.RoundRecord.ownEntries] using he
      rw [hcoordinate]
      have htimeR : ¬ time.val < physicalStart rate source' rewards C_star C_h := by
        rw [← hstart]
        exact htime
      simpa [completeOwnHistory, hnoneL, hnoneR, htime, htimeR,
        leftRun, rightRun, offset, Nat.add_sub_cancel_left, ← hactive, ← hstart] using hentry

/-- The selected-row invariant also gives equality of the literal terminal
state projection and the complete suffix evidence/diagnostics. Evidence keeps
all used data and actual diagnostics; raw records with different unused whole
tables are not asserted equal. -/
theorem terminal_and_suffix_eq_of_source_data (rate : RateInput p)
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p))
    (hids : source.1.1 = source'.1.1)
    (hprivate : source.2 = source'.2)
    (hq : ActualInitializationPhysicalStep.selectedRowIndex p source = q)
    (hrow : source.1.2 q = source'.1.2 q) :
    completeTerminalState rate source rewards C_star C_h =
        completeTerminalState rate source' rewards C_star C_h ∧
      completeSuffixEvidence rate source rewards C_star C_h =
        completeSuffixEvidence rate source' rewards C_star C_h ∧
      completeSuffixDiagnostics rate source rewards C_star C_h =
        completeSuffixDiagnostics rate source' rewards C_star C_h := by
  obtain ⟨hx, hboundary, hlaunch⟩ := generatedInput_and_launch_eq_of_source_data
    rate source source' rewards C_star C_h q hids hprivate hq hrow
  by_cases hnoneL : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none
  · have hnoneR : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source' rewards C_star C_h = none := by rw [← hlaunch, hnoneL]
    have hterm : completeTerminalState rate source rewards C_star C_h =
        completeTerminalState rate source' rewards C_star C_h := by
      simp [completeTerminalState, hnoneL, hnoneR]
    have hevidence : completeSuffixEvidence rate source rewards C_star C_h =
        completeSuffixEvidence rate source' rewards C_star C_h := by
      simp [completeSuffixEvidence, completeSuffixRecords, hnoneL, hnoneR]
    refine ⟨hterm, hevidence, ?_⟩
    exact congrArg (fun entries => entries.map (fun e => (e.coordinator, e.followers))) hevidence
  · have hnoneR : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source' rewards C_star C_h ≠ none := by
      intro h
      apply hnoneL
      rw [hlaunch, h]
    let activeL := correctedLaunchPayload rate source rewards C_star C_h hnoneL
    let activeR := correctedLaunchPayload rate source' rewards C_star C_h hnoneR
    have hactive : activeL = activeR := Option.some.inj
      ((correctedLaunch_eq_some_payload rate source rewards C_star C_h hnoneL).symm.trans
        (hlaunch.trans (correctedLaunch_eq_some_payload rate source' rewards C_star C_h hnoneR)))
    have hpayloadEq : correctedLaunchPayload rate source rewards C_star C_h hnoneL =
        correctedLaunchPayload rate source' rewards C_star C_h hnoneR := by
      change activeL = activeR
      exact hactive
    have hstart : physicalStart rate source rewards C_star C_h =
        physicalStart rate source' rewards C_star C_h :=
      congrArg (fun b : ReferenceInitializationRun.Boundary p =>
        ReferenceInitializationRun.elapsed p b.completed) hboundary
    let leftRun := correctedSuffixRun rate source rewards C_star C_h hnoneL
    let rightRun := correctedSuffixRun rate source' rewards C_star C_h hnoneR
    have hmode := activeMode_of_launch_eq_some rate source rewards C_star C_h activeL
      (correctedLaunch_eq_some_payload rate source rewards C_star C_h hnoneL)
    have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source =
        ActualInitializationPhysicalStep.selectedRowIndex p source' := by
      change PrivateSourceStreams.coordinatorIndex p source.2.1.2 =
        PrivateSourceStreams.coordinatorIndex p source'.2.1.2
      rw [hprivate]
    have hselected' : ActualInitializationPhysicalStep.selectedRowIndex p source' = q :=
      hselected.symm.trans hq
    have hspanL : physicalStart rate source rewards C_star C_h +
        (p.T - physicalStart rate source rewards C_star C_h) ≤ p.T := by
      have hs := physicalStart_le_T rate source rewards C_star C_h
      omega
    have hruns := ReferenceActivePhysicalHorizon.run_rows_eq activeL source.1.2 source'.1.2
      q rewards (physicalStart rate source rewards C_star C_h)
      (p.T - physicalStart rate source rewards C_star C_h) (by
        have hs := physicalStart_le_T rate source rewards C_star C_h
        omega) hmode hrow
    have hrunL : leftRun = ReferenceActivePhysicalHorizon.run activeL source.1.2 q rewards
        (physicalStart rate source rewards C_star C_h)
        (p.T - physicalStart rate source rewards C_star C_h) hspanL hmode := by
      dsimp only [leftRun, correctedSuffixRun]
      rw [hq]
    have hlaunchR := correctedLaunch_eq_some_payload rate source' rewards C_star C_h hnoneR
    have hmodeR := activeMode_of_launch_eq_some rate source' rewards C_star C_h activeR hlaunchR
    have hmodeR' : ReferenceActivePhysicalHorizon.allActiveAtStart activeR
        (physicalStart rate source rewards C_star C_h) := by
      rw [hstart]
      exact hmodeR
    have hrunR : rightRun = ReferenceActivePhysicalHorizon.run activeR source'.1.2 q rewards
        (physicalStart rate source rewards C_star C_h)
        (p.T - physicalStart rate source rewards C_star C_h) hspanL hmodeR' := by
      dsimp only [rightRun, correctedSuffixRun, activeR]
      simp only [hselected', ← hstart]
    have hrunState := activeHorizonRun_eq_of_initial_eq activeR activeL source'.1.2 q rewards
      (physicalStart rate source rewards C_star C_h)
      (p.T - physicalStart rate source rewards C_star C_h) hspanL
      hmodeR' hmode hactive.symm
    have hfinal : leftRun.finalState = rightRun.finalState := by
      calc
        leftRun.finalState = (ReferenceActivePhysicalHorizon.run activeL source.1.2 q rewards
            (physicalStart rate source rewards C_star C_h)
            (p.T - physicalStart rate source rewards C_star C_h) hspanL hmode).finalState :=
              congrArg (fun run => run.finalState) hrunL
        _ = (ReferenceActivePhysicalHorizon.run activeL source'.1.2 q rewards
            (physicalStart rate source rewards C_star C_h)
            (p.T - physicalStart rate source rewards C_star C_h) hspanL hmode).finalState := hruns.1
        _ = (ReferenceActivePhysicalHorizon.run activeR source'.1.2 q rewards
            (physicalStart rate source rewards C_star C_h)
            (p.T - physicalStart rate source rewards C_star C_h) hspanL hmodeR').finalState :=
              hrunState.1.symm
        _ = rightRun.finalState := congrArg (fun run => run.finalState) hrunR.symm
    have hterm : completeTerminalState rate source rewards C_star C_h =
        completeTerminalState rate source' rewards C_star C_h := by
      simp only [completeTerminalState, dite_eq_right hnoneL, dite_eq_right hnoneR]
      exact congrArg some hfinal
    have hevidence : completeSuffixEvidence rate source rewards C_star C_h =
        completeSuffixEvidence rate source' rewards C_star C_h := by
      simp only [completeSuffixEvidence, completeSuffixRecords,
        dite_eq_right hnoneL, dite_eq_right hnoneR]
      calc
        leftRun.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence =
            (ReferenceActivePhysicalHorizon.run activeL source.1.2 q rewards
              (physicalStart rate source rewards C_star C_h)
              (p.T - physicalStart rate source rewards C_star C_h) hspanL hmode).records.map
                ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
                  exact congrArg (fun run => run.records.map
                    ReferenceActivePhysicalHorizon.RoundRecord.evidence) hrunL
        _ = (ReferenceActivePhysicalHorizon.run activeL source'.1.2 q rewards
              (physicalStart rate source rewards C_star C_h)
              (p.T - physicalStart rate source rewards C_star C_h) hspanL hmode).records.map
                ReferenceActivePhysicalHorizon.RoundRecord.evidence := hruns.2
        _ = (ReferenceActivePhysicalHorizon.run activeR source'.1.2 q rewards
              (physicalStart rate source rewards C_star C_h)
              (p.T - physicalStart rate source rewards C_star C_h) hspanL hmodeR').records.map
                ReferenceActivePhysicalHorizon.RoundRecord.evidence :=
                  congrArg (fun records => records.map
                    ReferenceActivePhysicalHorizon.RoundRecord.evidence) hrunState.2.symm
        _ = rightRun.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
                  exact congrArg (fun run => run.records.map
                    ReferenceActivePhysicalHorizon.RoundRecord.evidence) hrunR.symm
    refine ⟨hterm, hevidence, ?_⟩
    exact congrArg (fun entries => entries.map (fun e => (e.coordinator, e.followers))) hevidence

end Bandits.Support.ReferenceCompletePhysicalHistory
