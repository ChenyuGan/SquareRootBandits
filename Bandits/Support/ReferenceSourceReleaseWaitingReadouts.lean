/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLocalReleaseWaitingPaths

import Lean.Elab.Tactic.Omega

/-!
# Original-source release-waiting readouts

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-88,180-240,293-348`,
`sources/zip4/manuscript/06_interruptions.tex:435-492`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This module reconstructs the existing retained launch and observes its actual
full-calendar records on the original source carrier. It proves ambient Borel
readout facts only; it constructs no stopping-time law or conditional service
estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceSourceReleaseWaitingReadouts

variable {p : ConstructorDimensions.Parameters}

/-- The source-event carrier already owned by the public waiting-path root. -/
abbrev SourceEvent (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) :=
  ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s

/-- The actual selected-row fiber of the original source event. -/
abbrev SourceFiber (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (q : Fin (M p)) :=
  {z : SourceEvent rate rewards C_star C_h s //
    ActualInitializationPhysicalStep.selectedRowIndex p z.val = q}

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (s : ℕ)

/-- Reconstruct the retained launch from its actual source witnesses. -/
def retainedLaunchOfSource (q : Fin (M p)) (t : Fin p.T) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : SourceFiber rate rewards C_star C_h s q) :
    ReferenceRetainedReleasePhaseObservation.LaunchStart
      rate rewards C_star C_h q t s hs control0 :=
  ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
    rate rewards C_star C_h q t s hs control0 z.val.val z.property
    z.val.property.1 z.val.property.2

/-- The actual selected-row control removed by the fixed-time split. -/
def sourceCurrentControl (q : Fin (M p)) (t : Fin p.T)
    (z : SourceFiber rate rewards C_star C_h s q) :
    ContinuousLearningRows.TimeControl p :=
  (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.val.val).1

private theorem replace_selected_suffix_after_current_control
    (source : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T)
    (control0 : ContinuousLearningRows.TimeControl p) :
    ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source control0)
        t (fun _ => control0) =
      ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
        source t (fun _ => control0) := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext row
      by_cases hrow : row = ActualInitializationPhysicalStep.selectedRowIndex p source
      · subst row
        dsimp only [ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix,
          ActualInitializationPhysicalStep.selectedRowIndex,
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
          ReferenceFixedTimeSourceControlCoupling.replaceSourceControl]
        simp only [Function.update_self]
        apply Prod.ext
        · rfl
        · funext v
          by_cases hv : v.val < t.val
          · have hvne : v ≠ t := by
              intro h
              subst v
              omega
            change (if v.val < t.val then
              Function.update (source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t control0 v
              else control0) =
              (if v.val < t.val then
                (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v
              else control0)
            rw [if_pos hv, if_pos hv]
            exact Function.update_of_ne hvne _ _
          · change (if v.val < t.val then
              Function.update (source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t control0 v
              else control0) =
              (if v.val < t.val then
                (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v
              else control0)
            rw [if_neg hv, if_neg hv]
      · dsimp only [ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix,
          ActualInitializationPhysicalStep.selectedRowIndex,
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
          ReferenceFixedTimeSourceControlCoupling.replaceSourceControl]
        have hrow' : row ≠ PrivateSourceStreams.coordinatorIndex p source.2.1.2 := by
          intro h
          apply hrow
          exact h
        simp only [Function.update_of_ne hrow']
  · rfl

/-- The source-to-retained launch map is Borel on each true selected-row fiber. -/
theorem source_to_retained_launch_measurable
    (q : Fin (M p)) (t : Fin p.T) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (retainedLaunchOfSource rate rewards C_star C_h s q t hs control0) := by
  let Fiber := SourceFiber rate rewards C_star C_h s q
  have hsource : Measurable (fun z : Fiber =>
      (z.val.val : BootstrapPrivateRoundStreams.SourceInput p)) :=
    measurable_subtype_coe.comp measurable_subtype_coe
  have hsplit : Measurable (fun z : Fiber =>
      ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.val.val) :=
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).measurable.comp hsource
  have hvalue : Measurable (fun z : Fiber =>
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.val.val).2) :=
    measurable_snd.comp hsplit
  have hmem (z : Fiber) :
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.val.val).2 ∈
        ReferenceRetainedBoundaryMeasurability.retainedLaunchStartSet
          rate rewards C_star C_h q t s control0 :=
    ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource_mem
      rate rewards C_star C_h q t s hs control0 z.val.val z.property
      z.val.property.1 z.val.property.2
  have hmap : Measurable (fun z : Fiber =>
      retainedLaunchOfSource rate rewards C_star C_h s q t hs control0 z) := by
    have hEq : (fun z : Fiber =>
        retainedLaunchOfSource rate rewards C_star C_h s q t hs control0 z) =
        fun z => ⟨(ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
          z.val.val).2, hmem z⟩ := by
      funext z
      apply Subtype.ext
      exact ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource_val
        rate rewards C_star C_h q t s hs control0 z.val.val z.property
        z.val.property.1 z.val.property.2
    rw [hEq]
    exact hvalue.subtype_mk (h := hmem)
  exact hmap

/-- The current source control is Borel on each actual selected-row fiber. -/
theorem source_current_control_measurable
    (q : Fin (M p)) (t : Fin p.T) :
    Measurable (sourceCurrentControl rate rewards C_star C_h s q t) := by
  have hsource : Measurable (fun z : SourceFiber rate rewards C_star C_h s q =>
      (z.val.val : BootstrapPrivateRoundStreams.SourceInput p)) :=
    measurable_subtype_coe.comp measurable_subtype_coe
  exact measurable_fst.comp
    ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).measurable.comp hsource)

/-- The retained launch keeps the actual fixed-time remainder, and splitting
the actual control together with that remainder reconstructs the whole source. -/
theorem source_launch_reconstruction
    (q : Fin (M p)) (t : Fin p.T) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : SourceFiber rate rewards C_star C_h s q) :
    (retainedLaunchOfSource rate rewards C_star C_h s q t hs control0 z).val =
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.val.val).2 ∧
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
        (sourceCurrentControl rate rewards C_star C_h s q t z,
          (retainedLaunchOfSource rate rewards C_star C_h s q t hs control0 z).val) =
      z.val.val ∧
    ReferenceReleaseStrictPastFactor.launchSource rate rewards C_star C_h q t s hs control0
        (ReferenceReleaseStrictPastFactor.normalize rate rewards C_star C_h q t s hs control0
          (retainedLaunchOfSource rate rewards C_star C_h s q t hs control0 z)) =
      ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
        z.val.val t (fun _ => control0) := by
  have hval :=
    ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource_val
      rate rewards C_star C_h q t s hs control0 z.val.val z.property
      z.val.property.1 z.val.property.2
  have hselected :
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z.val.val = q := by
    calc
      _ = ActualInitializationPhysicalStep.selectedRowIndex p z.val.val :=
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
          p z.val.val
      _ = q := z.property
  have hlaunch :
      ReferenceReleaseStrictPastFactor.launchSource rate rewards C_star C_h q t s hs
          control0 (retainedLaunchOfSource rate rewards C_star C_h s q t hs control0 z) =
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z.val.val control0 := by
    change (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
        (control0,
          (ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
            rate rewards C_star C_h q t s hs control0 z.val.val z.property
            z.val.property.1 z.val.property.2).val) = _
    rw [ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource_val]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
      p q t z.val.val control0 hselected
  refine ⟨hval, ?_, ?_⟩
  · change (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
      ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.val.val).1,
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.val.val).2) = _
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_reconstruct
      p q t z.val.val
  · rw [ReferenceReleaseStrictPastFactor.launchSource_normalize]
    change ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
      (ReferenceReleaseStrictPastFactor.launchSource rate rewards C_star C_h q t s hs control0
        (retainedLaunchOfSource rate rewards C_star C_h s q t hs control0 z)) t
        (fun _ => control0) = _
    rw [hlaunch]
    exact replace_selected_suffix_after_current_control z.val.val t control0

private theorem roundInput_ext
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {left right : ReferenceActivePhysicalStep.RoundInput p rate}
    (hstate : left.state = right.state) (hrows : left.rows = right.rows)
    (hselected : left.selected = right.selected) (htime : left.time = right.time)
    (hrewards : left.rewards = right.rewards) : left = right := by
  cases left
  cases right
  simp_all

private theorem horizon_run_finalState_congr_initial
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial initial' : ReferenceActivePhysicalStep.State p rate)
    (hinitial : initial = initial')
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hmode' : ReferenceActivePhysicalHorizon.allActiveAtStart initial' start) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).finalState =
      (ReferenceActivePhysicalHorizon.run initial' rows selected rewards start count hspan hmode').finalState := by
  cases hinitial
  have hmodeEq : hmode = hmode' := Subsingleton.elim _ _
  cases hmodeEq
  rfl

private theorem horizon_run_finalState_congr_selected
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected selected' : Fin (M p))
    (hselected : selected = selected')
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).finalState =
      (ReferenceActivePhysicalHorizon.run initial rows selected' rewards start count hspan hmode).finalState := by
  cases hselected
  rfl

private theorem retained_boundary_state_eq_source_run
    (q : Fin (M p)) (t : Fin p.T) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : SourceFiber rate rewards C_star C_h s q) :
    (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
      rate rewards C_star C_h q t s hs control0
      (retainedLaunchOfSource rate rewards C_star C_h s q t hs control0 z)).state =
      (ReferenceActivePhysicalHorizon.run
        (ReferenceLocalReleaseGateChronology.sourceSeed rate z.val.val rewards C_star C_h
          z.val.property.1)
        z.val.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val.val)
        rewards s (t.val - s) (by omega)
        (by simpa only [z.val.property.2] using
          (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
            rate z.val.val rewards C_star C_h z.val.property.1).2.1)).finalState := by
  let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.val.val
  let control := split.1
  let remainder := split.2
  have hrem : remainder ∈
      ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t := by
    change PrivateSourceStreams.coordinatorIndex p remainder.2.1.2 = q
    dsimp only [remainder, split]
    rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_private]
    change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z.val.val = q
    rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact z.property
  have hstart : remainder ∈
      ReferenceInitializationControlRemainder.launchStartRemainderEvent
        rate rewards C_star C_h q t s control := by
    dsimp only [remainder, split, control]
    exact (ReferenceInitializationControlRemainder.launchStartRemainderEvent_iff_source
      rate rewards C_star C_h q t control z.val.val z.property s hs).2
        ⟨z.val.property.1, z.val.property.2⟩
  let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control remainder hrem s hs hstart
  have hseedSpec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control remainder hrem s hs hstart
  have hsplitSource :
      ReferenceGeneratedActivePrefixFactor.splitSource q t control remainder = z.val.val := by
    change (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
        (control, remainder) = z.val.val
    dsimp only [control, remainder, split]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_reconstruct p q t z.val.val
  have hseedLaunch :
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate z.val.val rewards C_star C_h =
        some seed := by
    rw [← hsplitSource]
    exact hseedSpec.1
  have hseedEq : seed = ReferenceLocalReleaseGateChronology.sourceSeed
      rate z.val.val rewards C_star C_h z.val.property.1 :=
    Option.some.inj (hseedLaunch.symm.trans
      (ReferenceLocalReleaseGateChronology.sourceSeed_launch
        rate z.val.val rewards C_star C_h z.val.property.1))
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart seed s := hseedSpec.2.1
  have hsourceMode : ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceLocalReleaseGateChronology.sourceSeed rate z.val.val rewards C_star C_h
        z.val.property.1) s :=
    by
      simpa only [z.val.property.2] using
        (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
          rate z.val.val rewards C_star C_h z.val.property.1).2.1
  have hrunEq :
      (ReferenceActivePhysicalHorizon.run seed z.val.val.1.2 q rewards s (t.val - s)
          (by omega) hmode).finalState =
        (ReferenceActivePhysicalHorizon.run
          (ReferenceLocalReleaseGateChronology.sourceSeed rate z.val.val rewards C_star C_h
            z.val.property.1)
          z.val.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val.val)
          rewards s (t.val - s) (by omega) hsourceMode).finalState := by
    exact (horizon_run_finalState_congr_initial seed
      (ReferenceLocalReleaseGateChronology.sourceSeed rate z.val.val rewards C_star C_h
        z.val.property.1) hseedEq z.val.val.1.2 q rewards s (t.val - s) (by omega)
      hmode hsourceMode).trans
      (horizon_run_finalState_congr_selected
        (ReferenceLocalReleaseGateChronology.sourceSeed rate z.val.val rewards C_star C_h
          z.val.property.1)
        z.val.val.1.2 q (ActualInitializationPhysicalStep.selectedRowIndex p z.val.val)
        z.property.symm rewards s (t.val - s) (by omega) hsourceMode)
  let x := retainedLaunchOfSource rate rewards C_star C_h s q t hs control0 z
  let j : Fin (t.val - s + 1) := ⟨t.val - s, by omega⟩
  have hcode :
      ReferenceReleaseStrictPastFactor.phaseFactor rate rewards C_star C_h q t s hs
          control0 x j =
        ReferenceActivePhysicalStepMeasurability.encodeState
          ((ReferenceActivePhysicalHorizon.run seed z.val.val.1.2 q rewards s (t.val - s)
            (by omega) hmode).finalState) := by
    exact ReferenceReleaseStrictPastFactor.phaseFactor_source_specialization
      rate rewards C_star C_h q t s hs control0 z.val.val z.property
      z.val.property.1 z.val.property.2 j
  have hphase :
      ReferenceActivePhysicalStepMeasurability.encodeState
          (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
            rate rewards C_star C_h q t s hs control0 x).state =
        ReferenceReleaseStrictPastFactor.phaseFactor rate rewards C_star C_h q t s hs
          control0 x j := by
    rw [ReferenceReleaseStrictPastFactor.phaseFactor_eq rate rewards C_star C_h q t s hs
      control0 x control0]
    rfl
  have hencoded :
      ReferenceActivePhysicalStepMeasurability.encodeState
          (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
            rate rewards C_star C_h q t s hs control0 x).state =
        ReferenceActivePhysicalStepMeasurability.encodeState
          ((ReferenceActivePhysicalHorizon.run
            (ReferenceLocalReleaseGateChronology.sourceSeed rate z.val.val rewards C_star C_h
              z.val.property.1)
            z.val.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val.val)
            rewards s (t.val - s) (by omega)
            (by simpa only [z.val.property.2] using
              (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
                rate z.val.val rewards C_star C_h z.val.property.1).2.1)).finalState) := by
    calc
      _ = ReferenceReleaseStrictPastFactor.phaseFactor rate rewards C_star C_h q t s hs
            control0 x j := hphase
      _ = ReferenceActivePhysicalStepMeasurability.encodeState
            ((ReferenceActivePhysicalHorizon.run seed z.val.val.1.2 q rewards s (t.val - s)
              (by omega) hmode).finalState) := hcode
      _ = _ := congrArg
        ReferenceActivePhysicalStepMeasurability.encodeState
        hrunEq
  have hstate := congrArg ReferenceActivePhysicalStepMeasurability.decodeState hencoded
  simpa only [ReferenceActivePhysicalStepMeasurability.decodeState_encodeState] using hstate

private theorem retained_next_input_eq_source_record
    (q : Fin (M p)) (t : Fin p.T) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : SourceFiber rate rewards C_star C_h s q) :
    ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
      rate rewards C_star C_h q t s hs control0
      (retainedLaunchOfSource rate rewards C_star C_h s q t hs control0 z)
      (sourceCurrentControl rate rewards C_star C_h s q t z) =
    (ReferenceAssignmentPayloadChronology.actualRunRecordAt
      (ReferenceLocalReleaseGateChronology.sourceSeed rate z.val.val rewards C_star C_h
        z.val.property.1)
      z.val.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val.val)
      rewards s (t.val - s) (by omega)
      (by simpa only [z.val.property.2] using
        (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
          rate z.val.val rewards C_star C_h z.val.property.1).2.1)).input := by
  have hnext := ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput_eq_of_source
    rate rewards C_star C_h q t s hs control0 z.val.val z.property
    z.val.property.1 z.val.property.2
  have hstate := retained_boundary_state_eq_source_run
    rate rewards C_star C_h s q t hs control0 z
  have hrecordInput :
      ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate
          (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
            rate rewards C_star C_h q t s hs control0
            (retainedLaunchOfSource rate rewards C_star C_h s q t hs control0 z)) z.val.val =
        (ReferenceAssignmentPayloadChronology.actualRunRecordAt
          (ReferenceLocalReleaseGateChronology.sourceSeed rate z.val.val rewards C_star C_h
            z.val.property.1)
          z.val.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val.val)
          rewards s (t.val - s) (by omega)
          (by simpa only [z.val.property.2] using
            (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
              rate z.val.val rewards C_star C_h z.val.property.1).2.1)).input := by
    apply roundInput_ext
    · exact hstate
    · rfl
    · exact ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
        p z.val.val
    · apply Fin.ext
      change t.val = s + (t.val - s)
      omega
    · rfl
  exact hnext.trans hrecordInput

/-- The whole original calendar record at the current round is the literal
physical record of the retained next input. -/
theorem source_calendar_record_eq_retained_next_input
    (q : Fin (M p)) (t : Fin p.T) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : SourceFiber rate rewards C_star C_h s q) :
    ReferenceLocalReleaseCalendarCounts.calendarRecord rate z.val.val rewards C_star C_h
      z.val.property.1 s (p.T - s) z.val.property.2 (by omega) t.val =
    some (ReferencePhysicalReleaseObservability.recordOfInput
      (ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
        rate rewards C_star C_h q t s hs control0
        (retainedLaunchOfSource rate rewards C_star C_h s q t hs control0 z)
        (sourceCurrentControl rate rewards C_star C_h s q t z))) := by
  let sourceRun := ReferenceLocalReleaseGateChronology.sourceRun rate z.val.val rewards C_star C_h
    z.val.property.1 s (p.T - s) z.val.property.2 (by omega)
  let active := (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
    rate z.val.val rewards C_star C_h z.val.property.1).2.1
  let index : Fin (p.T - s) := ⟨t.val - s, by omega⟩
  let actual := ReferenceAssignmentPayloadChronology.actualRunRecordAt
    (ReferenceLocalReleaseGateChronology.sourceSeed rate z.val.val rewards C_star C_h
      z.val.property.1)
    z.val.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val.val)
    rewards s index.val (by omega)
    (by simpa only [z.val.property.2] using active)
  have hrun := ReferenceLocalReleaseGateChronology.run_record_at
    (ReferenceLocalReleaseGateChronology.sourceSeed rate z.val.val rewards C_star C_h
      z.val.property.1)
    z.val.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val.val)
    rewards s
    (by simpa only [z.val.property.2] using active) (p.T - s) (by omega) index
  have hmem : actual ∈ sourceRun.records := by
    dsimp only [actual, sourceRun, ReferenceLocalReleaseGateChronology.sourceRun]
    rw [← hrun]
    exact List.getElem_mem (by
      rw [ReferenceActivePhysicalHorizon.run_record_count]
      exact index.isLt)
  have htime : actual.input.time.val = t.val := by
    dsimp only [actual, ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt, index]
    omega
  have hcalendar :
      ReferenceLocalReleaseCalendarCounts.calendarRecord rate z.val.val rewards C_star C_h
        z.val.property.1 s (p.T - s) z.val.property.2 (by omega) t.val = some actual :=
    (ReferenceLocalReleaseCalendarCounts.calendarRecord_eq_some_iff
      rate z.val.val rewards C_star C_h z.val.property.1 s (p.T - s) z.val.property.2
      (by omega) t.val actual).2 ⟨hmem, htime⟩
  have hinput := retained_next_input_eq_source_record
    rate rewards C_star C_h s q t hs control0 z
  rw [hcalendar]
  congr 1
  rw [hinput]
  rfl

theorem source_calendar_record_eq_actual_run_record
    (q : Fin (M p)) (t : Fin p.T) (hs : s ≤ t.val)
    (z : SourceFiber rate rewards C_star C_h s q) (k : ℕ)
    (hk : s ≤ k) (hkt : k ≤ t.val) :
    ReferenceLocalReleaseCalendarCounts.calendarRecord rate z.val.val rewards C_star C_h
      z.val.property.1 s (p.T - s) z.val.property.2 (by omega) k =
    some (ReferenceAssignmentPayloadChronology.actualRunRecordAt
      (ReferenceLocalReleaseGateChronology.sourceSeed rate z.val.val rewards C_star C_h
        z.val.property.1)
      z.val.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val.val)
      rewards s (k - s) (by omega)
      (by simpa only [z.val.property.2] using
        (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
          rate z.val.val rewards C_star C_h z.val.property.1).2.1)) := by
  let sourceRun := ReferenceLocalReleaseGateChronology.sourceRun rate z.val.val rewards C_star C_h
    z.val.property.1 s (p.T - s) z.val.property.2 (by omega)
  let index : Fin (p.T - s) := ⟨k - s, by omega⟩
  let actual := ReferenceAssignmentPayloadChronology.actualRunRecordAt
    (ReferenceLocalReleaseGateChronology.sourceSeed rate z.val.val rewards C_star C_h
      z.val.property.1)
    z.val.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val.val)
    rewards s index.val (by omega)
    (by simpa only [z.val.property.2] using
      (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
        rate z.val.val rewards C_star C_h z.val.property.1).2.1)
  have hrun := ReferenceLocalReleaseGateChronology.run_record_at
    (ReferenceLocalReleaseGateChronology.sourceSeed rate z.val.val rewards C_star C_h
      z.val.property.1)
    z.val.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val.val)
    rewards s
    (by simpa only [z.val.property.2] using
      (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
        rate z.val.val rewards C_star C_h z.val.property.1).2.1)
    (p.T - s) (by omega) index
  have hmem : actual ∈ sourceRun.records := by
    dsimp only [actual, sourceRun, ReferenceLocalReleaseGateChronology.sourceRun]
    rw [← hrun]
    exact List.getElem_mem (by
      rw [ReferenceActivePhysicalHorizon.run_record_count]
      exact index.isLt)
  have htime : actual.input.time.val = k := by
    dsimp only [actual, ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt, index]
    omega
  exact (ReferenceLocalReleaseCalendarCounts.calendarRecord_eq_some_iff
    rate z.val.val rewards C_star C_h z.val.property.1 s (p.T - s) z.val.property.2
    (by omega) k actual).2 ⟨hmem, htime⟩

/-- The original full-span calendar entry at an earlier current round is the
same O entry read by R on the retained launch's original-source factor. -/
theorem source_calendar_entry_factor
    (q : Fin (M p)) (t : Fin p.T) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : SourceFiber rate rewards C_star C_h s q)
    (b k : ℕ) (hk : s ≤ k) (hkt : k ≤ t.val)
    (j : Fin (t.val - s + 1)) (hj : j.val = k - s) :
    ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val.val rewards C_star C_h
      z.val.property.1 s (p.T - s) z.val.property.2 (by omega) b k =
    some (ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h q t s hs
      control0 b (retainedLaunchOfSource rate rewards C_star C_h s q t hs control0 z) j) := by
  let actual := ReferenceAssignmentPayloadChronology.actualRunRecordAt
    (ReferenceLocalReleaseGateChronology.sourceSeed rate z.val.val rewards C_star C_h
      z.val.property.1)
    z.val.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val.val)
    rewards s (k - s) (by omega)
    (by simpa only [z.val.property.2] using
      (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
        rate z.val.val rewards C_star C_h z.val.property.1).2.1)
  have hcalendar := source_calendar_record_eq_actual_run_record
    rate rewards C_star C_h s q t hs z k hk hkt
  have hsourceRecord :
      ReferenceLocalReleasePendingHistory.sourceRecord rate z.val.val rewards C_star C_h
        z.val.property.1 s (t.val - s + 1) z.val.property.2 (by omega) j.val j.isLt = actual := by
    have hrun := ReferenceLocalReleaseGateChronology.run_record_at
      (ReferenceLocalReleaseGateChronology.sourceSeed rate z.val.val rewards C_star C_h
        z.val.property.1)
      z.val.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val.val)
      rewards s
      (by simpa only [z.val.property.2] using
        (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
          rate z.val.val rewards C_star C_h z.val.property.1).2.1)
      (t.val - s + 1) (by omega) j
    simpa only [ReferenceLocalReleasePendingHistory.sourceRecord,
      ReferenceLocalReleaseGateChronology.sourceRun, hj] using hrun
  have hsourceRecord' :
      (ReferenceLocalReleaseGateChronology.sourceRun rate z.val.val rewards C_star C_h
        z.val.property.1 s (t.val - s + 1) z.val.property.2 (by omega)).records[j.val]'(by
          simp only [ReferenceLocalReleaseGateChronology.sourceRun,
            ReferenceActivePhysicalHorizon.run_record_count]
          exact j.isLt) = actual := by
    simpa only [ReferenceLocalReleasePendingHistory.sourceRecord] using hsourceRecord
  have hfactor := ReferenceLocalReleaseGateChronology.releaseEntries_original_source_record
    rate rewards C_star C_h q t s hs control0 z.val.val z.property
    z.val.property.1 z.val.property.2 b
  have hfactorJ := hfactor j
  have hfactorActual :
      ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h q t s hs
        control0 b (retainedLaunchOfSource rate rewards C_star C_h s q t hs control0 z) j =
      ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate b actual.input.time
        (ReferenceActivePhysicalStepMeasurability.encodeState actual.input.state) := by
    simpa only [retainedLaunchOfSource, hsourceRecord'] using hfactorJ
  have hentry :
      ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val.val rewards C_star C_h
        z.val.property.1 s (p.T - s) z.val.property.2 (by omega) b k =
      some (ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate b actual.input.time
        (ReferenceActivePhysicalStepMeasurability.encodeState actual.input.state)) := by
    rw [ReferenceLocalReleaseCalendarCounts.calendarEntry, hcalendar]
    rfl
  rw [hentry, hfactorActual.symm]

/-- R's normalization preserves the same original-calendar entry, with no
baseline-source substitution. -/
theorem source_calendar_entry_factor_normalize
    (q : Fin (M p)) (t : Fin p.T) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : SourceFiber rate rewards C_star C_h s q)
    (b k : ℕ) (hk : s ≤ k) (hkt : k ≤ t.val)
    (j : Fin (t.val - s + 1)) (hj : j.val = k - s) :
    ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val.val rewards C_star C_h
      z.val.property.1 s (p.T - s) z.val.property.2 (by omega) b k =
    some (ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h q t s hs
      control0 b (ReferenceReleaseStrictPastFactor.normalize rate rewards C_star C_h q t s hs
        control0 (retainedLaunchOfSource rate rewards C_star C_h s q t hs control0 z)) j) := by
  rw [source_calendar_entry_factor rate rewards C_star C_h s q t hs control0 z
    b k hk hkt j hj]
  exact congrArg (fun f => some (f j))
    (ReferenceReleaseStrictPastFactor.releaseEntries_normalize
      rate rewards C_star C_h q t s hs control0 b
      (retainedLaunchOfSource rate rewards C_star C_h s q t hs control0 z))

abbrev FollowerReadouts (rate : ReferenceActivePhysicalStep.RateInput p) :=
  Fin (p.m - 1) → Option Bool × Option Bool × Option Bool

/-- The full original-source calendar observation at `(b,k)`: the actual
optional stored payload, O entry, C gate, W pending projection, and every
follower's raw UP, DATA, and release flags. -/
abbrev CalendarReadouts (rate : ReferenceActivePhysicalStep.RateInput p) :=
  Option (ReferenceActivePhysicalStep.Payload rate) ×
    (Option (Bool × Option (Finset (Fin (p.m - 1)))) ×
      (Option Bool ×
        (Option (Finset (Fin (p.m - 1))) × FollowerReadouts rate)))

/-- The literal tuple of original-source calendar projections. Its first
component is the optional whole stored payload of the actual record. -/
def sourceCalendarReadouts (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s ≤ p.T) (b : ℕ)
    (z : SourceEvent rate rewards C_star C_h s) (k : ℕ) : CalendarReadouts rate :=
  ((ReferenceLocalReleaseCalendarCounts.calendarRecord rate z.val rewards C_star C_h
      z.property.1 s (p.T - s) z.property.2 (by omega) k).bind fun record =>
        ReferenceAssignmentPayloadPersistence.storedPayload record.input.state.coordinator,
    (ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val rewards C_star C_h
      z.property.1 s (p.T - s) z.property.2 (by omega) b k,
     (ReferenceLocalReleaseCalendarCounts.calendarGate rate z.val rewards C_star C_h
        z.property.1 s (p.T - s) z.property.2 (by omega) b k,
      (ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h s hs b z k,
       fun i =>
        (ReferenceLocalReleaseWaitingPaths.calendarUpReadout rate rewards C_star C_h s hs b z i k,
         ReferenceLocalReleaseWaitingPaths.calendarDataReadout rate rewards C_star C_h s hs b z i k,
         ReferenceLocalReleaseWaitingPaths.calendarReleaseReadout rate rewards C_star C_h s hs b z i k)))))

private def pendingOfLocalEntry
    (entry : Bool × Option (Finset (Fin (p.m - 1)))) : Option (Finset (Fin (p.m - 1))) :=
  entry.2

private def retainedInputCalendarReadouts
    (rate : ReferenceActivePhysicalStep.RateInput p) (b : ℕ) (t : Fin p.T)
    (input : ReferenceActivePhysicalStep.RoundInput p rate) : CalendarReadouts rate :=
  let code := ReferenceActivePhysicalStepMeasurability.encodeState input.state
  let payload := ReferenceRetainedReleasePhaseObservation.localStoredPayload code
  let entry := ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate b t code
  (payload,
    (some entry,
     (some (ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b t code),
      (pendingOfLocalEntry entry,
       fun i =>
        ((payload.map fun M => ReferencePhysicalReleaseQuota.upFlag M
            (ReferencePhysicalReleaseObservability.recordOfInput input) i),
         (payload.map fun M => ReferencePhysicalReleaseQuota.dataFlag M
            (ReferencePhysicalReleaseObservability.recordOfInput input) i),
         (payload.map fun M => ReferencePhysicalReleaseQuota.releaseFlag M
            (ReferencePhysicalReleaseObservability.recordOfInput input) i))))))

private theorem retained_next_input_measurable_on_source_fiber
    (q : Fin (M p)) (t : Fin p.T) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (fun z : SourceFiber rate rewards C_star C_h s q =>
      ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
        rate rewards C_star C_h q t s hs control0
        (retainedLaunchOfSource rate rewards C_star C_h s q t hs control0 z)
        (sourceCurrentControl rate rewards C_star C_h s q t z)) := by
  let launch := retainedLaunchOfSource rate rewards C_star C_h s q t hs control0
  let control := sourceCurrentControl rate rewards C_star C_h s q t
  let boundary := fun z : SourceFiber rate rewards C_star C_h s q =>
    ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
      rate rewards C_star C_h q t s hs control0 (launch z)
  let source := fun z : SourceFiber rate rewards C_star C_h s q =>
    ReferenceGeneratedActivePrefixFactor.splitSource q t (control z) (launch z).val
  have hlaunch : Measurable launch :=
    source_to_retained_launch_measurable rate rewards C_star C_h s q t hs control0
  have hcontrol : Measurable control :=
    source_current_control_measurable rate rewards C_star C_h s q t
  have hboundary : Measurable boundary :=
    (ReferenceRetainedBoundaryMeasurability.measurable_retainedIncomingBoundary
      rate rewards C_star C_h q t s hs control0).comp hlaunch
  have hsource : Measurable source := by
    change Measurable (fun z : SourceFiber rate rewards C_star C_h s q =>
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
        (control z, (launch z).val))
    exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm.measurable.comp
      (hcontrol.prodMk (measurable_subtype_coe.comp hlaunch))
  have hstate : Measurable (fun z : SourceFiber rate rewards C_star C_h s q =>
      (boundary z).state) :=
    ReferenceActivePhysicalStepMeasurability.measurable_state.comp hboundary
  have hrows : Measurable (fun z : SourceFiber rate rewards C_star C_h s q =>
      (source z).1.2) :=
    measurable_snd.comp (measurable_fst.comp hsource)
  have hselected : Measurable (fun z : SourceFiber rate rewards C_star C_h s q =>
      BootstrapPrivateRoundStreams.sourceCoordinatorIndex p (source z)) :=
    (BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p).comp hsource
  have htime : Measurable (fun z : SourceFiber rate rewards C_star C_h s q =>
      (boundary z).time) :=
    ReferenceActivePhysicalStepMeasurability.measurable_time.comp hboundary
  have hrewards : Measurable (fun z : SourceFiber rate rewards C_star C_h s q =>
      (boundary z).rewards) :=
    ReferenceActivePhysicalStepMeasurability.measurable_rewards.comp hboundary
  let coordinates : SourceFiber rate rewards C_star C_h s q →
      ReferenceActivePhysicalStepMeasurability.RoundCoordinates p rate := fun z =>
    ((boundary z).state,
      ((source z).1.2,
        (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p (source z),
          ((boundary z).time, (boundary z).rewards))))
  have hcoordinates : Measurable coordinates :=
    hstate.prodMk (hrows.prodMk (hselected.prodMk (htime.prodMk hrewards)))
  have hencoded : Measurable (fun z =>
      ReferenceActivePhysicalStepMeasurability.encodeRoundInput
        (ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate
          (boundary z) (source z))) := by
    exact hcoordinates.subtype_mk
  have hround : Measurable (fun z : SourceFiber rate rewards C_star C_h s q =>
      ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate
        (boundary z) (source z)) := by
    apply measurable_comap_iff.mpr
    exact hencoded
  have heq : (fun z : SourceFiber rate rewards C_star C_h s q =>
      ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
        rate rewards C_star C_h q t s hs control0 (launch z) (control z)) =
      fun z => ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate
        (boundary z) (source z) := by
    funext z
    exact ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput_eq_roundInputAtSource
      rate rewards C_star C_h q t s hs control0 (launch z) (control z)
  rw [heq]
  exact hround

private theorem measurable_retained_input_calendar_readouts
    (q : Fin (M p)) (t : Fin p.T) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) (b : ℕ) :
    Measurable (fun z : SourceFiber rate rewards C_star C_h s q =>
      retainedInputCalendarReadouts rate b t
        (ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
          rate rewards C_star C_h q t s hs control0
          (retainedLaunchOfSource rate rewards C_star C_h s q t hs control0 z)
          (sourceCurrentControl rate rewards C_star C_h s q t z))) := by
  let input : SourceFiber rate rewards C_star C_h s q →
      ReferenceActivePhysicalStep.RoundInput p rate := fun z =>
    ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
      rate rewards C_star C_h q t s hs control0
      (retainedLaunchOfSource rate rewards C_star C_h s q t hs control0 z)
      (sourceCurrentControl rate rewards C_star C_h s q t z)
  have hin : Measurable input :=
    retained_next_input_measurable_on_source_fiber rate rewards C_star C_h s q t hs control0
  let code : SourceFiber rate rewards C_star C_h s q →
      ReferenceActivePhysicalStepMeasurability.StateCode p rate :=
    fun z => ReferenceActivePhysicalStepMeasurability.encodeState (input z).state
  have hcode : Measurable code :=
    ReferenceActivePhysicalStepMeasurability.measurable_encodeState.comp
      (ReferenceActivePhysicalStepMeasurability.measurable_state.comp hin)
  have hpayload : Measurable (fun z =>
      ReferenceRetainedReleasePhaseObservation.localStoredPayload (code z)) :=
    (ReferenceReleaseStrictPastFactor.measurable_localStoredPayload rate).comp hcode
  have hentry : Measurable (fun z =>
      ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate b t (code z)) :=
    (ReferenceReleaseStrictPastFactor.measurable_localReleaseEntry rate b t).comp hcode
  have hgate : Measurable (fun z =>
      ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b t (code z)) :=
    (ReferenceRetainedReleasePhaseObservation.measurable_localReleaseGate rate b t).comp hcode
  have hpending : Measurable (fun z =>
      pendingOfLocalEntry (ReferenceRetainedReleasePhaseObservation.localReleaseEntry
        rate b t (code z))) := by
    exact (measurable_snd.comp hentry)
  have hflag (i : Fin (p.m - 1))
      (flag : ReferenceActivePhysicalStep.Payload rate →
        ReferenceLocalReleaseCalendarCounts.Record (p := p) (rate := rate) →
        Fin (p.m - 1) → Bool)
      (hflag : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
          ReferenceActivePhysicalStep.RoundInput p rate =>
            flag z.1 (ReferencePhysicalReleaseObservability.recordOfInput z.2) i)) :
      Measurable (fun z : SourceFiber rate rewards C_star C_h s q =>
        (ReferenceRetainedReleasePhaseObservation.localStoredPayload (code z)).map
          fun M => flag M (ReferencePhysicalReleaseObservability.recordOfInput (input z)) i) := by
    exact ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
      (fun z : ReferenceActivePhysicalStep.Payload rate ×
          SourceFiber rate rewards C_star C_h s q =>
        flag z.1 (ReferencePhysicalReleaseObservability.recordOfInput (input z.2)) i)
      (hflag.comp (measurable_fst.prodMk (hin.comp measurable_snd)))
      (fun z => ReferenceRetainedReleasePhaseObservation.localStoredPayload (code z))
      hpayload
  have hflags : Measurable (fun z : SourceFiber rate rewards C_star C_h s q =>
      fun i =>
        ((ReferenceRetainedReleasePhaseObservation.localStoredPayload (code z)).map
          fun M => ReferencePhysicalReleaseQuota.upFlag M
            (ReferencePhysicalReleaseObservability.recordOfInput (input z)) i,
         (ReferenceRetainedReleasePhaseObservation.localStoredPayload (code z)).map
          fun M => ReferencePhysicalReleaseQuota.dataFlag M
            (ReferencePhysicalReleaseObservability.recordOfInput (input z)) i,
         (ReferenceRetainedReleasePhaseObservation.localStoredPayload (code z)).map
          fun M => ReferencePhysicalReleaseQuota.releaseFlag M
            (ReferencePhysicalReleaseObservability.recordOfInput (input z)) i)) := by
    apply measurable_pi_iff.mpr
    intro i
    have hup := hflag i ReferencePhysicalReleaseQuota.upFlag
      (ReferencePhysicalReleaseObservability.measurable_upFlag i)
    have hdata := hflag i ReferencePhysicalReleaseQuota.dataFlag
      (ReferencePhysicalReleaseObservability.measurable_dataFlag i)
    have hrelease := hflag i ReferencePhysicalReleaseQuota.releaseFlag
      (ReferencePhysicalReleaseObservability.measurable_releaseFlag i)
    exact hup.prodMk (hdata.prodMk hrelease)
  have hsomeEntry : Measurable (some :
      (Bool × Option (Finset (Fin (p.m - 1)))) →
        Option (Bool × Option (Finset (Fin (p.m - 1))))) := by
    apply measurable_comap_iff.mpr
    exact measurable_inl
  have hsomeGate : Measurable (some : Bool → Option Bool) := by
    apply measurable_comap_iff.mpr
    exact measurable_inl
  exact hpayload.prodMk
    ((hsomeEntry.comp hentry).prodMk ((hsomeGate.comp hgate).prodMk (hpending.prodMk hflags)))

private def selectedFiberCover
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (q : Fin (M p)) :
    Set (SourceEvent rate rewards C_star C_h s × (ℕ × ℕ)) :=
  {x | ActualInitializationPhysicalStep.selectedRowIndex p x.1.val = q}

private theorem measurable_source_selected_row
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) :
    Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
      ActualInitializationPhysicalStep.selectedRowIndex p z.val) := by
  have hsource : Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
      BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z.val) :=
    (BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p).comp
      (measurable_subtype_coe : Measurable
        (fun z : SourceEvent rate rewards C_star C_h s => z.val))
  have heq : (fun z : SourceEvent rate rewards C_star C_h s =>
      ActualInitializationPhysicalStep.selectedRowIndex p z.val) =
      fun z => BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z.val := by
    funext z
    exact (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
      p z.val).symm
  rw [heq]
  exact hsource

private theorem selected_fiber_cover_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (q : Fin (M p)) :
    MeasurableSet (selectedFiberCover rate rewards C_star C_h s q) := by
  change MeasurableSet {x : SourceEvent rate rewards C_star C_h s × (ℕ × ℕ) |
    ActualInitializationPhysicalStep.selectedRowIndex p x.1.val = q}
  exact (measurableSet_singleton q).preimage
    ((measurable_source_selected_row rate rewards C_star C_h s).comp measurable_fst)

/-- Joint Borel measurability on the actual crossing/elapsed source event and
both countable calendar coordinates. The proof glues over the actual finite
selected-row fibers and reconstructs each current input from the original
source. -/
theorem measurable_source_calendar_readouts
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s ≤ p.T)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (fun z : SourceEvent rate rewards C_star C_h s × (ℕ × ℕ) =>
      sourceCalendarReadouts rate rewards C_star C_h s hs z.2.1 z.1 z.2.2) := by
  let event := SourceEvent rate rewards C_star C_h s
  let cover := selectedFiberCover rate rewards C_star C_h s
  let readout := sourceCalendarReadouts rate rewards C_star C_h s hs
  have hfiber (q : Fin (M p)) : Measurable (fun z : SourceFiber rate rewards C_star C_h s q ×
      (ℕ × ℕ) => readout z.2.1 z.1.val z.2.2) := by
    apply measurable_from_prod_countable_left
    intro bk
    by_cases hstart : s ≤ bk.2
    · by_cases hround : bk.2 < p.T
      · let t : Fin p.T := ⟨bk.2, hround⟩
        have hs' : s ≤ t.val := by simpa only [t] using hstart
        let input : SourceFiber rate rewards C_star C_h s q →
            ReferenceActivePhysicalStep.RoundInput p rate := fun z =>
          ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
            rate rewards C_star C_h q t s hs' control0
            (retainedLaunchOfSource rate rewards C_star C_h s q t hs'
              control0 z)
            (sourceCurrentControl rate rewards C_star C_h s q t z)
        have hinput : Measurable input := by
          exact retained_next_input_measurable_on_source_fiber rate rewards C_star C_h
            s q t hs' control0
        have hrecord := source_calendar_record_eq_retained_next_input
          rate rewards C_star C_h s q t hs' control0
        have heq : (fun z : SourceFiber rate rewards C_star C_h s q =>
            readout bk.1 z.val bk.2) = fun z =>
              retainedInputCalendarReadouts rate bk.1 t (input z) := by
          funext z
          dsimp only [readout, sourceCalendarReadouts, input]
          have hrecordZ := hrecord z
          have hactual := source_calendar_record_eq_actual_run_record rate rewards C_star C_h
            s q t hs' z t.val hs' le_rfl
          have hrecordEq := Option.some.inj (hactual.symm.trans hrecordZ)
          have hactualTime :
              (ReferenceAssignmentPayloadChronology.actualRunRecordAt
                (ReferenceLocalReleaseGateChronology.sourceSeed rate z.val.val rewards C_star C_h
                  z.val.property.1)
                z.val.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val.val)
                rewards s (t.val - s) (by omega)
                (by simpa only [z.val.property.2] using
                  (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
                    rate z.val.val rewards C_star C_h z.val.property.1).2.1)).input.time.val = t.val := by
            dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
              ReferenceActivePhysicalHorizon.roundInputAt]
            omega
          have hinputTime : (input z).time.val = t.val := by
            calc
              (input z).time.val =
                  (ReferenceAssignmentPayloadChronology.actualRunRecordAt
                    (ReferenceLocalReleaseGateChronology.sourceSeed rate z.val.val rewards C_star C_h
                      z.val.property.1)
                    z.val.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val.val)
                    rewards s (t.val - s) (by omega)
                    (by simpa only [z.val.property.2] using
                      (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
                        rate z.val.val rewards C_star C_h z.val.property.1).2.1)).input.time.val := by
                exact congrArg
                  (fun r : ReferenceLocalReleaseCalendarCounts.Record (p := p) (rate := rate) =>
                    r.input.time.val) hrecordEq |>.symm
              _ = t.val := hactualTime
          have hinputTime' : (input z).time = t := Fin.ext hinputTime
          simp only [ReferenceLocalReleaseWaitingPaths.calendarPendingReadout,
            ReferenceLocalReleaseWaitingPaths.calendarUpReadout,
            ReferenceLocalReleaseWaitingPaths.calendarDataReadout,
            ReferenceLocalReleaseWaitingPaths.calendarReleaseReadout,
            ReferenceLocalReleaseCalendarCounts.calendarEntry,
            ReferenceLocalReleaseCalendarCounts.calendarGate,
            ReferenceLocalReleaseCalendarCounts.calendarPending,
            ReferenceLocalReleaseCalendarCounts.calendarUpFlag,
            ReferenceLocalReleaseCalendarCounts.calendarDataFlag,
            ReferenceLocalReleaseCalendarCounts.calendarReleaseFlag,
            ReferenceLocalReleaseCalendarCounts.calendarFlag]
          repeat rw [hrecordZ]
          simp only [Option.bind_some, Option.map_some,
            ReferencePhysicalReleaseObservability.recordOfInput]
          rw [hinputTime']
          simp only [
            retainedInputCalendarReadouts,
            ReferenceRetainedReleasePhaseObservation.localStoredPayload_eq_decoded,
            ReferenceActivePhysicalStepMeasurability.decodeState_encodeState]
          let code := ReferenceActivePhysicalStepMeasurability.encodeState
            (ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
              rate rewards C_star C_h q t s hs' control0
              (retainedLaunchOfSource rate rewards C_star C_h s q t hs' control0 z)
              (sourceCurrentControl rate rewards C_star C_h s q t z)).state
          cases hgate : ReferenceRetainedReleasePhaseObservation.localReleaseGate
              rate bk.1 t code with
          | false =>
              simp [code, hgate, pendingOfLocalEntry,
                ReferenceRetainedReleasePhaseObservation.localReleaseEntry,
                ReferencePhysicalReleaseObservability.recordOfInput]
          | true =>
              cases hpayload : ReferenceRetainedReleasePhaseObservation.localStoredPayload code with
              | none =>
                  simp [code, hgate, hpayload, pendingOfLocalEntry,
                    ReferenceRetainedReleasePhaseObservation.localReleaseEntry,
                    ReferencePhysicalReleaseObservability.recordOfInput]
              | some payload =>
                  simp [code, hgate, hpayload, pendingOfLocalEntry,
                    ReferenceRetainedReleasePhaseObservation.localReleaseEntry,
                    ReferencePhysicalReleaseObservability.recordOfInput]
        rw [heq]
        exact measurable_retained_input_calendar_readouts rate rewards C_star C_h
          s q t hs' control0 bk.1
      · have hlookup : ∀ z : SourceFiber rate rewards C_star C_h s q,
            ReferenceLocalReleaseCalendarCounts.calendarRecord rate z.val.val rewards C_star C_h
              z.val.property.1 s (p.T - s) z.val.property.2 (by omega) bk.2 = none := by
          intro z
          unfold ReferenceLocalReleaseCalendarCounts.calendarRecord
          have hbranch : ¬ (s ≤ bk.2 ∧ bk.2 < s + (p.T - s)) := by omega
          simp [hbranch]
        have heq : (fun z : SourceFiber rate rewards C_star C_h s q =>
            readout bk.1 z.val bk.2) = fun _ =>
              ((none : Option (ReferenceActivePhysicalStep.Payload rate)),
               (none, (none, (none, fun _ => (none, none, none))))) := by
          funext z
          dsimp only [readout, sourceCalendarReadouts]
          simp only [hlookup z, Option.bind_none,
            ReferenceLocalReleaseWaitingPaths.calendarPendingReadout,
            ReferenceLocalReleaseWaitingPaths.calendarUpReadout,
            ReferenceLocalReleaseWaitingPaths.calendarDataReadout,
            ReferenceLocalReleaseWaitingPaths.calendarReleaseReadout,
            ReferenceLocalReleaseCalendarCounts.calendarEntry,
            ReferenceLocalReleaseCalendarCounts.calendarGate,
            ReferenceLocalReleaseCalendarCounts.calendarPending,
            ReferenceLocalReleaseCalendarCounts.calendarUpFlag,
            ReferenceLocalReleaseCalendarCounts.calendarDataFlag,
            ReferenceLocalReleaseCalendarCounts.calendarReleaseFlag,
            ReferenceLocalReleaseCalendarCounts.calendarFlag]
          rfl
        rw [heq]
        exact measurable_const
    · have hlookup : ∀ z : SourceFiber rate rewards C_star C_h s q,
          ReferenceLocalReleaseCalendarCounts.calendarRecord rate z.val.val rewards C_star C_h
            z.val.property.1 s (p.T - s) z.val.property.2 (by omega) bk.2 = none := by
        intro z
        unfold ReferenceLocalReleaseCalendarCounts.calendarRecord
        have hbranch : ¬ (s ≤ bk.2 ∧ bk.2 < s + (p.T - s)) := by omega
        simp [hbranch]
      have heq : (fun z : SourceFiber rate rewards C_star C_h s q =>
          readout bk.1 z.val bk.2) = fun _ =>
            ((none : Option (ReferenceActivePhysicalStep.Payload rate)),
             (none, (none, (none, fun _ => (none, none, none))))) := by
        funext z
        dsimp only [readout, sourceCalendarReadouts]
        simp only [hlookup z, Option.bind_none,
          ReferenceLocalReleaseWaitingPaths.calendarPendingReadout,
          ReferenceLocalReleaseWaitingPaths.calendarUpReadout,
          ReferenceLocalReleaseWaitingPaths.calendarDataReadout,
          ReferenceLocalReleaseWaitingPaths.calendarReleaseReadout,
          ReferenceLocalReleaseCalendarCounts.calendarEntry,
          ReferenceLocalReleaseCalendarCounts.calendarGate,
          ReferenceLocalReleaseCalendarCounts.calendarPending,
          ReferenceLocalReleaseCalendarCounts.calendarUpFlag,
          ReferenceLocalReleaseCalendarCounts.calendarDataFlag,
          ReferenceLocalReleaseCalendarCounts.calendarReleaseFlag,
          ReferenceLocalReleaseCalendarCounts.calendarFlag]
        rfl
      rw [heq]
      exact measurable_const
  let branch (q : Fin (M p)) :
      {x : event × (ℕ × ℕ) // x ∈ cover q} → CalendarReadouts rate := fun x =>
    readout x.val.2.1 x.val.1 x.val.2.2
  have hbranch : ∀ q, Measurable (branch q) := by
    intro q
    let toFiber : {x : event × (ℕ × ℕ) // x ∈ cover q} →
        SourceFiber rate rewards C_star C_h s q × (ℕ × ℕ) := fun x =>
      (⟨x.val.1, x.property⟩, x.val.2)
    have hfirst : Measurable (fun x : {x : event × (ℕ × ℕ) // x ∈ cover q} => x.val.1) :=
      measurable_fst.comp measurable_subtype_coe
    have hsourceFiber : Measurable (fun x : {x : event × (ℕ × ℕ) // x ∈ cover q} =>
        (⟨x.val.1, x.property⟩ : SourceFiber rate rewards C_star C_h s q)) :=
      hfirst.subtype_mk (h := fun x => x.property)
    have hparams : Measurable (fun x : {x : event × (ℕ × ℕ) // x ∈ cover q} => x.val.2) :=
      measurable_snd.comp measurable_subtype_coe
    have htoFiber : Measurable toFiber := hsourceFiber.prodMk hparams
    exact (hfiber q).comp htoFiber
  have hcompat : ∀ (q q' : Fin (M p)) (x : event × (ℕ × ℕ))
      (hq : x ∈ cover q) (hq' : x ∈ cover q'),
      branch q ⟨x, hq⟩ = branch q' ⟨x, hq'⟩ := by
    intro q q' x hq hq'
    have hqq : q = q' := hq.symm.trans hq'
    subst q'
    rfl
  have hcover : (⋃ q, cover q) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨ActualInitializationPhysicalStep.selectedRowIndex p x.1.val, rfl⟩
  have hlift : Measurable (Set.liftCover cover branch hcompat hcover) :=
    measurable_liftCover cover (fun q => selected_fiber_cover_measurable
      rate rewards C_star C_h s q) branch hbranch hcompat hcover
  have heq : (fun z : event × (ℕ × ℕ) => readout z.2.1 z.1 z.2.2) =
      Set.liftCover cover branch hcompat hcover := by
    funext z
    let q := ActualInitializationPhysicalStep.selectedRowIndex p z.1.val
    have hz : z ∈ cover q := rfl
    rw [Set.liftCover_of_mem (S := cover) (f := branch) (hf := hcompat)
      (hS := hcover) (i := q) hz]
  rw [heq]
  exact hlift

/-- The original-source zero-based gate support used by the waiting-path
consumer. It is exactly C's finite filter of actual calendar gate readouts. -/
def sourceCalendarGateSupport
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s b : ℕ)
    (z : SourceEvent rate rewards C_star C_h s) : Finset ℕ :=
  let hs : s ≤ p.T := by
    rw [← z.property.2]
    exact ReferenceInitializationRun.elapsed_le_T p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed
  ReferenceLocalReleaseCalendarCounts.calendarGateSupport rate z.val rewards C_star C_h
    z.property.1 s (p.T - s) z.property.2 (by omega) b

private def sourceOneBasedGateSupport
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s b : ℕ)
    (z : SourceEvent rate rewards C_star C_h s) : Finset ℕ :=
  Finset.image (fun k : ℕ => k + 1)
    (sourceCalendarGateSupport rate rewards C_star C_h s b z)

private theorem measurable_calendar_gate_readout
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s ≤ p.T)
    (control0 : ContinuousLearningRows.TimeControl p) (b k : ℕ) :
    Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
      ReferenceLocalReleaseCalendarCounts.calendarGate rate z.val rewards C_star C_h
        z.property.1 s (p.T - s) z.property.2 (by omega) b k) := by
  have hjoint := measurable_source_calendar_readouts rate rewards C_star C_h s hs control0
  have hparameters : Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
      (z, (b, k))) := measurable_id.prodMk measurable_const
  have hreadout := hjoint.comp hparameters
  exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hreadout))

private theorem measurableSet_option_singleton {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (a : Option α) :
    MeasurableSet[LaterAssignmentStartMeasurability.optionMeasurableSpace] ({a} : Set (Option α)) := by
  let e := Equiv.optionEquivSumPUnit α
  have he : @Measurable (Option α) (α ⊕ PUnit)
      LaterAssignmentStartMeasurability.optionMeasurableSpace inferInstance e := comap_measurable _
  have hset : ({a} : Set (Option α)) = e ⁻¹' {e a} := by
    ext x
    exact ⟨fun h => congrArg e h, fun h => e.injective h⟩
  rw [hset]
  apply he
  cases h : e a with
  | inl value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inl_image (β := PUnit)
  | inr value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inr_image (α := α)

local instance {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] :
    @MeasurableSingletonClass (Option α) LaterAssignmentStartMeasurability.optionMeasurableSpace :=
  ⟨measurableSet_option_singleton⟩

/-- The zero-based finite calendar gate support is Borel on the original
source event. Its membership is read from the actual local gate, independently
of the pending set. -/
theorem measurable_source_calendar_gate_support
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s b : ℕ) (hs : s ≤ p.T)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (sourceCalendarGateSupport rate rewards C_star C_h s b ·) := by
  apply measurable_finset_iff.mpr
  intro k
  have hgate := measurable_calendar_gate_readout rate rewards C_star C_h s hs control0 b k
  have hgateSet : MeasurableSet {z : SourceEvent rate rewards C_star C_h s |
      ReferenceLocalReleaseCalendarCounts.calendarGate rate z.val rewards C_star C_h
        z.property.1 s (p.T - s) z.property.2 (by omega) b k = some true} :=
    (measurableSet_singleton (some true)).preimage hgate
  have hdescription :
      {z : SourceEvent rate rewards C_star C_h s |
        k ∈ sourceCalendarGateSupport rate rewards C_star C_h s b z} =
      {z | k < p.T} ∩ {z |
        ReferenceLocalReleaseCalendarCounts.calendarGate rate z.val rewards C_star C_h
          z.property.1 s (p.T - s) z.property.2 (by omega) b k = some true} := by
    ext z
    simp [sourceCalendarGateSupport,
      ReferenceLocalReleaseCalendarCounts.calendarGateSupport,
      Finset.mem_filter, Finset.mem_range]
  apply measurableSet_setOfPred.mp
  rw [hdescription]
  have hlt : MeasurableSet {z : SourceEvent rate rewards C_star C_h s | k < p.T} := by
    by_cases hk : k < p.T <;> simp [hk]
  exact hlt.inter hgateSet

private theorem measurable_source_one_based_gate_support
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s b : ℕ) (hs : s ≤ p.T)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (sourceOneBasedGateSupport rate rewards C_star C_h s b ·) := by
  apply measurable_finset_iff.mpr
  intro v
  have hmem (k : ℕ) : MeasurableSet {z : SourceEvent rate rewards C_star C_h s |
      k ∈ sourceCalendarGateSupport rate rewards C_star C_h s b z} := by
    have hgate := measurable_calendar_gate_readout rate rewards C_star C_h s hs control0 b k
    have hgateSet : MeasurableSet {z : SourceEvent rate rewards C_star C_h s |
        ReferenceLocalReleaseCalendarCounts.calendarGate rate z.val rewards C_star C_h
          z.property.1 s (p.T - s) z.property.2 (by omega) b k = some true} :=
      (measurableSet_singleton (some true)).preimage hgate
    have hdescription :
        {z : SourceEvent rate rewards C_star C_h s |
          k ∈ sourceCalendarGateSupport rate rewards C_star C_h s b z} =
        {z | k < p.T} ∩ {z |
          ReferenceLocalReleaseCalendarCounts.calendarGate rate z.val rewards C_star C_h
            z.property.1 s (p.T - s) z.property.2 (by omega) b k = some true} := by
      ext z
      simp [sourceCalendarGateSupport,
        ReferenceLocalReleaseCalendarCounts.calendarGateSupport,
        Finset.mem_filter, Finset.mem_range]
    rw [hdescription]
    have hlt : MeasurableSet {z : SourceEvent rate rewards C_star C_h s | k < p.T} := by
      by_cases hk : k < p.T <;> simp [hk]
    exact hlt.inter hgateSet
  have hdescription :
      {z : SourceEvent rate rewards C_star C_h s |
        v ∈ sourceOneBasedGateSupport rate rewards C_star C_h s b z} =
      ⋃ k : ℕ, {z | k ∈ sourceCalendarGateSupport rate rewards C_star C_h s b z ∧ k + 1 = v} := by
    ext z
    simp only [sourceOneBasedGateSupport, Finset.mem_image, Set.mem_iUnion,
      Set.mem_setOf_eq]
  apply measurableSet_setOfPred.mp
  rw [hdescription]
  exact MeasurableSet.iUnion fun k => (hmem k).inter (by
    by_cases hk : k + 1 = v
    · exact measurableSet_setOfPred.mpr measurable_const
    · exact measurableSet_setOfPred.mpr measurable_const)

private theorem source_one_based_gate_support_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s b : ℕ) (hs : s ≤ p.T)
    (z : SourceEvent rate rewards C_star C_h s) :
    sourceOneBasedGateSupport rate rewards C_star C_h s b z =
      ReferenceLocalReleaseGateChronology.gateSupport b
        (ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch rate rewards C_star C_h s hs z).records := by
  simpa [sourceOneBasedGateSupport, sourceCalendarGateSupport,
    ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch] using
    ReferenceLocalReleaseCalendarCounts.calendarGateSupport_image rate z.val rewards C_star C_h
      z.property.1 s (p.T - s) z.property.2 (by omega) b

/-- The actual zero-based calendar gate support, together with the existing
one-based source gate endpoints, is jointly Borel on the original source
event. -/
theorem measurable_source_gate_support_and_endpoints
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s b : ℕ) (hs : s ≤ p.T)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
      (sourceCalendarGateSupport rate rewards C_star C_h s b z,
        (ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs b z,
         ReferenceLocalReleaseWaitingPaths.localGateBeta rate rewards C_star C_h s hs b z))) := by
  let S : SourceEvent rate rewards C_star C_h s → Finset ℕ := fun z =>
    ReferenceLocalReleaseGateChronology.gateSupport b
      (ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch rate rewards C_star C_h s hs z).records
  have hcalendarSupport := measurable_source_calendar_gate_support
    rate rewards C_star C_h s b hs control0
  have hOneBased := measurable_source_one_based_gate_support
    rate rewards C_star C_h s b hs control0
  have hS : Measurable S := by
    change Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
      ReferenceLocalReleaseGateChronology.gateSupport b
        (ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch rate rewards C_star C_h s hs z).records)
    have heq : (fun z : SourceEvent rate rewards C_star C_h s => S z) =
        sourceOneBasedGateSupport rate rewards C_star C_h s b := by
      funext z
      exact (source_one_based_gate_support_eq rate rewards C_star C_h s b hs z).symm
    rw [heq]
    exact hOneBased
  let alpha : SourceEvent rate rewards C_star C_h s → ℕ := fun z =>
    if h : (S z).Nonempty then (S z).min' h else p.T + 1
  let beta : SourceEvent rate rewards C_star C_h s → ℕ := fun z =>
    if h : (S z).Nonempty then (S z).max' h + 1 else p.T + 1
  have hAlphaEq :
      (fun z => ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h
        s hs b z) = alpha := by
    rfl
  have hBetaEq :
      (fun z => ReferenceLocalReleaseWaitingPaths.localGateBeta rate rewards C_star C_h
        s hs b z) = beta := by
    rfl
  have hAlpha : Measurable alpha := by
    have hfinite : Measurable (fun A : Finset ℕ =>
        if h : A.Nonempty then A.min' h else p.T + 1) := measurable_of_countable _
    exact hfinite.comp hS
  have hBeta : Measurable beta := by
    have hfinite : Measurable (fun A : Finset ℕ =>
        if h : A.Nonempty then A.max' h + 1 else p.T + 1) := measurable_of_countable _
    exact hfinite.comp hS
  have hpair : Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
      (ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs b z,
       ReferenceLocalReleaseWaitingPaths.localGateBeta rate rewards C_star C_h s hs b z)) := by
    have heq : (fun z : SourceEvent rate rewards C_star C_h s =>
        (ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs b z,
         ReferenceLocalReleaseWaitingPaths.localGateBeta rate rewards C_star C_h s hs b z)) =
        fun z => (alpha z, beta z) := by
      funext z
      exact Prod.ext (congrFun hAlphaEq z) (congrFun hBetaEq z)
    rw [heq]
    exact hAlpha.prodMk hBeta
  exact hcalendarSupport.prodMk hpair

private theorem measurable_source_calendar_readouts_fixed
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s ≤ p.T)
    (control0 : ContinuousLearningRows.TimeControl p) (b k : ℕ) :
    Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
      sourceCalendarReadouts rate rewards C_star C_h s hs b z k) := by
  have hjoint := measurable_source_calendar_readouts rate rewards C_star C_h s hs control0
  have hparameters : Measurable (fun z : SourceEvent rate rewards C_star C_h s => (z, (b, k))) :=
    measurable_id.prodMk measurable_const
  exact hjoint.comp hparameters

/-- The three existing raw source observations are jointly Borel at each
fixed follower and calendar coordinate. The tuple keeps absence-defaulting
separate from the gate and pending readouts. -/
theorem measurable_source_waiting_observations
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s ≤ p.T)
    (control0 : ContinuousLearningRows.TimeControl p) (b k : ℕ)
    (i : Fin (p.m - 1)) :
    Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
      (ReferenceLocalReleaseWaitingPaths.upObservation rate rewards C_star C_h s hs b i k z,
        (ReferenceLocalReleaseWaitingPaths.dataObservation rate rewards C_star C_h s hs b i k z,
         ReferenceLocalReleaseWaitingPaths.releaseObservation rate rewards C_star C_h s hs b i k z))) := by
  have htuple := measurable_source_calendar_readouts_fixed
    rate rewards C_star C_h s hs control0 b k
  have hvector : Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
      (sourceCalendarReadouts rate rewards C_star C_h s hs b z k).2.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp htuple)))
  have htriple (i : Fin (p.m - 1)) : Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
      (sourceCalendarReadouts rate rewards C_star C_h s hs b z k).2.2.2.2 i) :=
    (measurable_pi_iff.mp hvector) i
  have hgetD : Measurable (fun x : Option Bool => x.getD false) := measurable_of_countable _
  have hflags : Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
      (((sourceCalendarReadouts rate rewards C_star C_h s hs b z k).2.2.2.2 i).1.getD false,
        (((sourceCalendarReadouts rate rewards C_star C_h s hs b z k).2.2.2.2 i).2.1.getD false,
         ((sourceCalendarReadouts rate rewards C_star C_h s hs b z k).2.2.2.2 i).2.2.getD false))) := by
    have hup := hgetD.comp (measurable_fst.comp (htriple i))
    have hdata := hgetD.comp (measurable_fst.comp (measurable_snd.comp (htriple i)))
    have hrelease := hgetD.comp (measurable_snd.comp (measurable_snd.comp (htriple i)))
    exact hup.prodMk (hdata.prodMk hrelease)
  have heq : (fun z : SourceEvent rate rewards C_star C_h s =>
      (ReferenceLocalReleaseWaitingPaths.upObservation rate rewards C_star C_h s hs b i k z,
        (ReferenceLocalReleaseWaitingPaths.dataObservation rate rewards C_star C_h s hs b i k z,
         ReferenceLocalReleaseWaitingPaths.releaseObservation rate rewards C_star C_h s hs b i k z))) =
      fun z => (((sourceCalendarReadouts rate rewards C_star C_h s hs b z k).2.2.2.2 i).1.getD false,
        (((sourceCalendarReadouts rate rewards C_star C_h s hs b z k).2.2.2.2 i).2.1.getD false,
         ((sourceCalendarReadouts rate rewards C_star C_h s hs b z k).2.2.2.2 i).2.2.getD false)) := by
    funext z
    rfl
  rw [heq]
  exact hflags

/-- Borel measurability of the existing pending set restricted by an
arbitrary measurable one-based endpoint. No stopping-time or endpoint-bound
property is used. -/
theorem measurable_source_pending_theta
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s ≤ p.T)
    (control0 : ContinuousLearningRows.TimeControl p) (b k : ℕ)
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (htheta : Measurable theta) :
    Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
      ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs b theta k z) := by
  have htuple := measurable_source_calendar_readouts_fixed
    rate rewards C_star C_h s hs control0 b k
  have hpendingOption : Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
      (sourceCalendarReadouts rate rewards C_star C_h s hs b z k).2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp htuple)))
  have hgetD : Measurable (fun x : Option (Finset (Fin (p.m - 1))) => x.getD ∅) :=
    measurable_of_countable _
  have hcut : MeasurableSet {z : SourceEvent rate rewards C_star C_h s | k + 1 < theta z} :=
    measurableSet_lt measurable_const htheta
  have hrestricted : Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
      if k + 1 < theta z then (sourceCalendarReadouts rate rewards C_star C_h s hs b z k).2.2.2.1.getD ∅
      else ∅) :=
    Measurable.ite hcut (hgetD.comp hpendingOption) measurable_const
  have heq : (fun z : SourceEvent rate rewards C_star C_h s =>
      ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs b theta k z) =
    fun z => if k + 1 < theta z then
      (sourceCalendarReadouts rate rewards C_star C_h s hs b z k).2.2.2.1.getD ∅ else ∅ := by
    funext z
    rfl
  rw [heq]
  exact hrestricted

private theorem measurable_source_waiting_count
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s ≤ p.T)
    (control0 : ContinuousLearningRows.TimeControl p) (b : ℕ)
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (hpending : ∀ k, Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
      ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs b theta k z))
    (X : Fin (p.m - 1) → ℕ → SourceEvent rate rewards C_star C_h s → Bool)
    (hX : ∀ i k, Measurable (fun z : SourceEvent rate rewards C_star C_h s => X i k z))
    (i : Fin (p.m - 1)) (v : ℕ) :
    Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
      PhaseServiceWaiting.N (ReferenceLocalReleaseWaitingPaths.pendingTheta
        rate rewards C_star C_h s hs b theta) X i v z) := by
  change Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
    ∑ k ∈ Finset.range v,
      if i ∈ ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs b theta k z ∧
          X i k z then 1 else 0)
  apply Finset.measurable_fun_sum
  intro k hk
  have hP := hpending k
  have hmember : Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
      i ∈ ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs b theta k z) :=
    (measurable_finset_iff.mp hP) i
  have hmemberSet : MeasurableSet {z : SourceEvent rate rewards C_star C_h s |
      i ∈ ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs b theta k z} :=
    measurableSet_setOfPred.mpr hmember
  have hsuccessSet : MeasurableSet {z : SourceEvent rate rewards C_star C_h s | X i k z = true} :=
    (measurableSet_singleton true).preimage (hX i k)
  exact Measurable.ite (hmemberSet.inter hsuccessSet) measurable_const measurable_const

/-- All three literal phase service counts are Borel on the original source
event for an arbitrary measurable endpoint function. -/
theorem measurable_source_waiting_counts
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s ≤ p.T)
    (control0 : ContinuousLearningRows.TimeControl p) (b : ℕ)
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (htheta : Measurable theta) (i : Fin (p.m - 1)) (v : ℕ) :
    Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
      (PhaseServiceWaiting.N (ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs b theta)
        (fun j k z => ReferenceLocalReleaseWaitingPaths.upObservation rate rewards C_star C_h s hs b j k z) i v z,
       (PhaseServiceWaiting.N (ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs b theta)
          (fun j k z => ReferenceLocalReleaseWaitingPaths.dataObservation rate rewards C_star C_h s hs b j k z) i v z,
        PhaseServiceWaiting.N (ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs b theta)
          (fun j k z => ReferenceLocalReleaseWaitingPaths.releaseObservation rate rewards C_star C_h s hs b j k z) i v z))) := by
  have hpending (k : ℕ) : Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
      ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs b theta k z) :=
    measurable_source_pending_theta rate rewards C_star C_h s hs control0 b k theta htheta
  have hobservations (j : Fin (p.m - 1)) (k : ℕ) :=
    measurable_source_waiting_observations rate rewards C_star C_h s hs control0 b k j
  have hup (j : Fin (p.m - 1)) (k : ℕ) := measurable_fst.comp (hobservations j k)
  have hdata (j : Fin (p.m - 1)) (k : ℕ) :=
    measurable_fst.comp (measurable_snd.comp (hobservations j k))
  have hrelease (j : Fin (p.m - 1)) (k : ℕ) :=
    measurable_snd.comp (measurable_snd.comp (hobservations j k))
  have hNu := measurable_source_waiting_count rate rewards C_star C_h s hs control0 b theta hpending
    (fun j k z => ReferenceLocalReleaseWaitingPaths.upObservation rate rewards C_star C_h s hs b j k z)
    hup i v
  have hNd := measurable_source_waiting_count rate rewards C_star C_h s hs control0 b theta hpending
    (fun j k z => ReferenceLocalReleaseWaitingPaths.dataObservation rate rewards C_star C_h s hs b j k z)
    hdata i v
  have hNr := measurable_source_waiting_count rate rewards C_star C_h s hs control0 b theta hpending
    (fun j k z => ReferenceLocalReleaseWaitingPaths.releaseObservation rate rewards C_star C_h s hs b j k z)
    hrelease i v
  exact hNu.prodMk (hNd.prodMk hNr)

/-- The existing local phase start and endpoint are Borel for any measurable
one-based endpoint function. No endpoint range or stopping-time hypothesis is
needed. -/
theorem measurable_source_local_phase_endpoints
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s ≤ p.T)
    (control0 : ContinuousLearningRows.TimeControl p) (b : ℕ)
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (htheta : Measurable theta) :
    Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
      (ReferenceLocalReleaseWaitingPaths.localPhaseSigma rate rewards C_star C_h s hs b theta z,
       ReferenceLocalReleaseWaitingPaths.localPhaseEndpoint rate rewards C_star C_h s hs b theta z)) := by
  have hendpoints := measurable_source_gate_support_and_endpoints
    rate rewards C_star C_h s b hs control0
  have hab := measurable_snd.comp hendpoints
  let phaseMap : ((ℕ × ℕ) × ℕ) → (ℕ × ℕ) := fun x =>
    let alpha := x.1.1
    let beta := min x.1.2 x.2
    if alpha < beta then (alpha, beta) else (p.T + 1, p.T + 1)
  have hmap : Measurable phaseMap := measurable_of_countable _
  have hcoordinates : Measurable (fun z : SourceEvent rate rewards C_star C_h s =>
      ((ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs b z,
        ReferenceLocalReleaseWaitingPaths.localGateBeta rate rewards C_star C_h s hs b z), theta z)) :=
    hab.prodMk htheta
  have heq : (fun z : SourceEvent rate rewards C_star C_h s =>
      (ReferenceLocalReleaseWaitingPaths.localPhaseSigma rate rewards C_star C_h s hs b theta z,
       ReferenceLocalReleaseWaitingPaths.localPhaseEndpoint rate rewards C_star C_h s hs b theta z)) =
      fun z => phaseMap ((ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs b z,
        ReferenceLocalReleaseWaitingPaths.localGateBeta rate rewards C_star C_h s hs b z), theta z) := by
    funext z
    have hcondition :
      (ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs b z <
        min (ReferenceLocalReleaseWaitingPaths.localGateBeta rate rewards C_star C_h s hs b z)
          (theta z)) ↔
        ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs b z <
          ReferenceLocalReleaseWaitingPaths.localGateBeta rate rewards C_star C_h s hs b z ∧
        ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs b z <
          theta z := by omega
    simp [phaseMap, ReferenceLocalReleaseWaitingPaths.localPhaseSigma,
      ReferenceLocalReleaseWaitingPaths.localPhaseEndpoint, hcondition]
    by_cases h : ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs b z <
        ReferenceLocalReleaseWaitingPaths.localGateBeta rate rewards C_star C_h s hs b z ∧
        ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs b z < theta z <;>
      simp [h]
  rw [heq]
  exact hmap.comp hcoordinates

end Bandits.Support.ReferenceSourceReleaseWaitingReadouts

end noncomputable section
