/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveStoppedQueueComparison
public import Bandits.Support.ReferenceTotalSourceDisintegration
public import Bandits.Support.ReferenceContinuingSavedIncrementMoments

/-!
# The actual retained first-live continuing recording branch

This module identifies a literal continuing DATA preparation on the original
retained source fibre and prepares its actual recording and saved-observation
inputs for the fixed-prefix laws. The branch is computed from the existing
corrected launch, physical horizon, and PREPARE functions; it introduces no
replacement source, physical state, or recorder schema.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:376-408`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

The exports here are internal fixed-prefix producers. They do not establish an
adaptive history law, integrate a source cylinder, prove the first-launch
sampler law, or close a manuscript theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceGeneratedActivePrefixFactor
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceRetainedBoundaryMeasurability
open Bandits.Support.ReferenceContinuingDataCandidateLogging
open Bandits.Support.ReferenceContinuingLiveSlicePreparation
open Bandits.Support.ReferenceContinuingRecordingFastPair
open Bandits.Support.ReferenceContinuingRecordingFastLaw
open Bandits.Support.ReferenceContinuingSavedIncrementMoments
open Bandits.Support.ReferenceCollectionPhaseHistory

namespace Bandits.Support.ReferenceFirstLiveRecordingSourceBranch

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl
variable {p : Parameters}

private theorem roundInput_ext {rate : RateInput p}
    {left right : ReferenceActivePhysicalStep.RoundInput p rate}
    (hstate : left.state = right.state) (hrows : left.rows = right.rows)
    (hselected : left.selected = right.selected) (htime : left.time = right.time)
    (hrewards : left.rewards = right.rewards) : left = right := by
  cases left
  cases right
  simp_all

private theorem horizonRun_eq_of_selected_eq {rate : RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (left right : Fin (M p))
    (rewards : RewardTable p) (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hselected : left = right) :
    ReferenceActivePhysicalHorizon.run initial rows left rewards start count hspan hmode =
      ReferenceActivePhysicalHorizon.run initial rows right rewards start count hspan hmode := by
  cases hselected
  rfl

abbrev SourceRemainder (p : Parameters) (q : Fin (M p)) (t : Fin p.T) :=
  ReferenceRetainedBoundaryMeasurability.Remainder p q t
abbrev RetainedBranch (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) :=
    ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
    rate rewards C_star C_h q t s hs control0

private theorem retainedBranch_parts
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0) :
    x.1 ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t ∧
      x.1 ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
        rate rewards C_star C_h q t s control0 := by
  have hx := x.2
  change x.1 ∈ ReferenceRetainedBoundaryMeasurability.retainedLaunchStartSet
    rate rewards C_star C_h q t s control0 at hx
  simpa [ReferenceRetainedBoundaryMeasurability.retainedLaunchStartSet,
    Set.mem_inter_iff] using hx

/-- The original-source crossing and elapsed-start facts carried by `X`.
The selected coordinator row, all other rows, the original private arrays,
and the whole reward table remain those of the retained source. -/
theorem retainedSourceFacts
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0) :
    let z := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true ∧
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s :=
  ReferenceRetainedBoundaryMeasurability.retainedLaunchStart_source_facts
    rate rewards C_star C_h q t s hs control0 x.1
    (retainedBranch_parts rate rewards C_star C_h q t s hs control0 x).1
    (retainedBranch_parts rate rewards C_star C_h q t s hs control0 x).2

/-- The actual corrected first-live seed on the retained source. In
particular, the original carried follower buffers are retained verbatim. -/
def actualRetainedSeed
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0) :=
  ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate
    (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1)
    rewards C_star C_h (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).1

/-- The actual current input at the end of the retained physical prefix. Its
body is the existing horizon `candidateInput`, with the actual launch seed,
original source row, original selected row, and whole reward table. -/
def actualCurrentInput
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0) :
    ReferenceActivePhysicalStep.RoundInput p rate :=
  ReferenceContinuingDataCandidateLogging.candidateInput
    (ReferenceFirstLaunchNumericalCell.launchState rate
      (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1)
      rewards C_star C_h (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).1)
    (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1).1.2
    q
    rewards
    s
    (t.val - s)
    (by have h := (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).2
        omega)
    (by
      have hmode := (actualRetainedSeed rate rewards C_star C_h q t s hs control0 x).activeAtStart
      rcases retainedSourceFacts rate rewards C_star C_h q t s hs control0 x with
        ⟨_, helapsed⟩
      simpa only [helapsed] using hmode)

/-- The actual physical first-live run through the current round. It uses the
same actual launch seed as `actualCurrentInput`; the current row is included
in this `n + 1` run, while its continuous control remains the original one. -/
def actualRetainedPrefixRun
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0) :=
  ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate
    (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1)
    rewards C_star C_h (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).1
    (t.val - s + 1)
    (by have h := (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).2
        omega)

def actualCurrentRecord
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0) :
    ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
  ⟨actualCurrentInput rate rewards C_star C_h q t s hs control0 x,
    ReferenceActivePhysicalStep.step
      (actualCurrentInput rate rewards C_star C_h q t s hs control0 x), rfl⟩

private theorem actualRetainedPrefixRun_records_append
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0) :
    (actualRetainedPrefixRun rate rewards C_star C_h q t s hs control0 x).records =
      (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstLaunchNumericalCell.launchState rate
          (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1)
          rewards C_star C_h (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).1)
        (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1).1.2 q rewards
        s (t.val - s) (by omega)
        (by
          rcases retainedSourceFacts rate rewards C_star C_h q t s hs control0 x with
            ⟨_, helapsed⟩
          simpa only [helapsed] using
            (actualRetainedSeed rate rewards C_star C_h q t s hs control0 x).activeAtStart)).records ++
      [actualCurrentRecord rate rewards C_star C_h q t s hs control0 x] := by
  let z := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h
    (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).1
  have hparts := retainedBranch_parts rate rewards C_star C_h q t s hs control0 x
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p z = q := by
    calc
      ActualInitializationPhysicalStep.selectedRowIndex p z =
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z :=
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
          p z).symm
      _ = q := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
        p q t control0 x.1 hparts.1
  let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
    rcases retainedSourceFacts rate rewards C_star C_h q t s hs control0 x with
      ⟨_, helapsed⟩
    simpa only [helapsed] using
      (actualRetainedSeed rate rewards C_star C_h q t s hs control0 x).activeAtStart
  have hspan : s + ((t.val - s) + 1) ≤ p.T := by omega
  have hrun : actualRetainedPrefixRun rate rewards C_star C_h q t s hs control0 x =
      ReferenceActivePhysicalHorizon.run initial z.1.2 q rewards s
        (t.val - s + 1) hspan hmode := by
    rcases retainedSourceFacts rate rewards C_star C_h q t s hs control0 x with
      ⟨_, helapsed⟩
    simp [actualRetainedPrefixRun, ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
      z, initial, helapsed, hselected]
  have hsucc := ReferenceActivePhysicalHorizon.run_successor initial z.1.2 q rewards s
    (t.val - s) (by omega) hmode
  have hrecords := congrArg ReferenceActivePhysicalHorizon.Run.records hsucc
  have hone := ReferenceActivePhysicalHorizon.calendarEntries_one s
    (s + (t.val - s)) (by omega) (by omega)
  have hrecordsAppend :
      (ReferenceActivePhysicalHorizon.run initial z.1.2 q rewards s
        (t.val - s + 1) hspan hmode).records =
        (ReferenceActivePhysicalHorizon.run initial z.1.2 q rewards s
          (t.val - s) (by omega) hmode).records ++
          [actualCurrentRecord rate rewards C_star C_h q t s hs control0 x] := by
    calc
      _ = (ReferenceActivePhysicalHorizon.foldCalendar initial z.1.2 q rewards s
          (s + (t.val - s)) 1 (by omega) (by omega) hmode
          (ReferenceActivePhysicalHorizon.run initial z.1.2 q rewards s
            (t.val - s) (by omega) hmode)).records := hrecords
      _ = _ := by
        rw [ReferenceActivePhysicalHorizon.foldCalendar, hone]
        simp only [List.foldl_cons, List.foldl_nil]
        simp [ReferenceActivePhysicalHorizon.foldRound,
          ReferenceActivePhysicalHorizon.roundInputAt,
          actualCurrentRecord, actualCurrentInput,
          ReferenceContinuingDataCandidateLogging.candidateInput,
          z, initial, hmode, hselected]
  rw [hrun]
  exact hrecordsAppend

/-- Initialization identifies the generated horizon input with B0's actual
incoming boundary. The launch identity is obtained from the same nonempty
`correctedLaunch` option used by A and N. -/
theorem actualCurrentInput_eq_retainedIncomingBoundary
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0) :
    actualCurrentInput rate rewards C_star C_h q t s hs control0 x =
      ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x := by
  let z := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  let active := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h
    (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).1
  have hparts := retainedBranch_parts rate rewards C_star C_h q t s hs control0 x
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p z = q := by
    calc
      ActualInitializationPhysicalStep.selectedRowIndex p z =
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z :=
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
          p z).symm
      _ = q := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
        p q t control0 x.1 hparts.1
  let generated := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control0 x.1 hparts.1 s hs hparts.2
  have hlaunchA := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate z rewards C_star C_h (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).1
  have hlaunchG := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control0 x.1 hparts.1 s hs hparts.2).1
  have hseed : generated = active := Option.some.inj (hlaunchG.symm.trans hlaunchA)
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active s := by
    have hmode' := (actualRetainedSeed rate rewards C_star C_h q t s hs control0 x).activeAtStart
    rcases retainedSourceFacts rate rewards C_star C_h q t s hs control0 x with
      ⟨_, helapsed⟩
    simpa only [helapsed] using hmode'
  have hrun :
      ReferenceActivePhysicalHorizon.run active z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (t.val - s)
          (by omega) hmode =
      ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
        rate rewards C_star C_h q t control0 x.1 hparts.1 s (t.val - s) hs hparts.2 (by omega) := by
    simp only [ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor]
    cases hseed
    rfl
  have hrunQ :
      ReferenceActivePhysicalHorizon.run active z.1.2 q rewards s (t.val - s)
        (by omega) hmode =
      ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
        rate rewards C_star C_h q t control0 x.1 hparts.1 s (t.val - s) hs hparts.2 (by omega) := by
    rw [horizonRun_eq_of_selected_eq active z.1.2 q
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (t.val - s)
      (by omega) hmode hselected.symm]
    exact hrun
  apply roundInput_ext
  · change (ReferenceActivePhysicalHorizon.run active z.1.2 q rewards s (t.val - s)
          (by omega) hmode).finalState =
      (ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
        rate rewards C_star C_h q t control0 x.1 hparts.1 s (t.val - s) hs hparts.2 (by omega)).finalState
    exact congrArg ReferenceActivePhysicalHorizon.Run.finalState hrunQ
  · rfl
  · exact hselected.symm
  · change (⟨s + (t.val - s), by omega⟩ : Fin p.T) = t
    apply Fin.ext
    simp only [Fin.val_mk]
    omega
  · rfl

/-- The retained incoming boundary remains the actual current input under
every replacement of its whole current time-control coordinate. This is the
original-source bridge used to feed C's and F's fixed-prefix producers. -/
theorem actualCurrentInput_control_eq_retainedGeneratedNextInput
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 u : TimeControl p)
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0) :
    ReferenceContinuingLiveSlicePreparation.inputAtControl
      (actualCurrentInput rate rewards C_star C_h q t s hs control0 x) u =
    ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
      rate rewards C_star C_h q t s hs control0 x u := by
  let beta := ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
    rate rewards C_star C_h q t s hs control0 x
  let z0 := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  let zu := ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1
  have hparts := retainedBranch_parts rate rewards C_star C_h q t s hs control0 x
  let e := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
  have hsourceIndex :
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z0 = q := by
    rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p q t control0 x.1 hparts.1
  have hsplitRemainder :
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z0).2 = x.1 := by
    have hsplit := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).apply_symm_apply
      (control0, x.1)
    exact congrArg Prod.snd hsplit
  have hsourceReplace : zu =
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z0 u := by
    change (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
        (u, x.1) =
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z0 u
    rw [← hsplitRemainder]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
      p q t z0 u hsourceIndex
  have hbase : ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate beta z0 = beta := by
    apply roundInput_ext
    · rfl
    · rfl
    · change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z0 = beta.selected
      calc
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z0 = q := hsourceIndex
        _ = beta.selected := by
          symm
          exact ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_selected_eq_q
            rate rewards C_star C_h q t s hs control0 x
    · rfl
    · rfl
  have hwith :
      ReferenceContinuingLiveSlicePreparation.inputAtControl beta u =
        ReferenceLaterOptionalControlResampling.withControl beta u := by
    cases beta
    rfl
  have htime : beta.time = t := by
    simp [beta, ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary]
  have hchange := ReferenceFixedTimeSourceControlCoupling.roundInputAtSource_replaceSourceControl
    p rate beta z0 u
  rw [htime] at hchange
  calc
    ReferenceContinuingLiveSlicePreparation.inputAtControl
        (actualCurrentInput rate rewards C_star C_h q t s hs control0 x) u =
      ReferenceContinuingLiveSlicePreparation.inputAtControl beta u := by
        simpa only [actualCurrentInput_eq_retainedIncomingBoundary]
    _ = ReferenceLaterOptionalControlResampling.withControl beta u := hwith
    _ = ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate beta zu := by
      rw [hsourceReplace]
      rw [← hbase]
      exact hchange.symm
    _ = ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
        rate rewards C_star C_h q t s hs control0 x u := by
      symm
      exact ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput_eq_roundInputAtSource
        rate rewards C_star C_h q t s hs control0 x u

/-- The computed continuing branch on the actual current PREPARE and the
actual `n + 1` physical prefix. Every earlier cutoff test is evaluated on the
existing physical records; the current pending set and clock come from the
actual continuing constructor. -/
def continuingRecordingBranch
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0) : Prop :=
  let n := t.val - s
  n > 0 ∧
    (∀ record ∈ (actualRetainedPrefixRun rate rewards C_star C_h q t s hs control0 x).records.take n,
      ReferenceCollectionPhaseHistory.cutoffChosen record.input = false) ∧
    (match (ReferenceActivePhysicalStep.prepare
      (actualCurrentInput rate rewards C_star C_h q t s hs control0 x)).coordinator with
    | .live _ _ _ (.continuingChosen dispatched _ _ _) =>
        dispatched.startResult.pending.Nonempty ∧
          t.val + 1 < dispatched.startResult.clock.g
    | _ => False)

/-- The computed unoccupied-follower branch, using the same actual current
PREPARE state as `continuingRecordingBranch`. -/
def continuingRecordingFollowerBranch
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (i : Fin (p.m - 1))
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0) : Prop :=
  continuingRecordingBranch rate rewards C_star C_h q t s hs control0 x ∧
    match ((ReferenceActivePhysicalStep.prepare
      (actualCurrentInput rate rewards C_star C_h q t s hs control0 x)).followers.followers i).configuration with
    | .ordinary state _ => state.status = .unoccupied
    | .dagger => False

private theorem continuingBranch_current_data
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0)
    (hbranch : continuingRecordingBranch rate rewards C_star C_h q t s hs control0 x) :
    ∃ r owned base d hsStart c arm,
      (ReferenceActivePhysicalStep.prepare
        (actualCurrentInput rate rewards C_star C_h q t s hs control0 x)).coordinator =
        .live r owned base (.continuingChosen d hsStart c arm) ∧
      d.startResult.pending.Nonempty ∧ t.val + 1 < d.startResult.clock.g := by
  rcases hbranch with ⟨_, _, hcurrent⟩
  cases hcoord : (ReferenceActivePhysicalStep.prepare
      (actualCurrentInput rate rewards C_star C_h q t s hs control0 x)).coordinator with
  | first out => simp [hcoord] at hcurrent
  | live r owned base outcome =>
      cases outcome with
      | continuingChosen d hsStart c arm =>
          simp [hcoord] at hcurrent
          exact ⟨r, owned, base, d, hsStart, c, arm, rfl, hcurrent.1, hcurrent.2⟩
      | _ => simp [hcoord] at hcurrent
  | collection payload ledger clock cutoff outcome => simp [hcoord] at hcurrent
  | invalidCollectionCutoff => simp [hcoord] at hcurrent
  | dagger => simp [hcoord] at hcurrent

private theorem continuingBranch_current_not_cutoff
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0)
    (hbranch : continuingRecordingBranch rate rewards C_star C_h q t s hs control0 x) :
    ReferenceCollectionPhaseHistory.cutoffChosen
      (actualCurrentInput rate rewards C_star C_h q t s hs control0 x) = false := by
  obtain ⟨r, owned, base, d, hsStart, c, arm, hcoord, _, _⟩ :=
    continuingBranch_current_data rate rewards C_star C_h q t s hs control0 x hbranch
  simp [ReferenceCollectionPhaseHistory.cutoffChosen, hcoord]

private theorem takeWhile_append_of_all {α : Type*} (predicate : α → Bool)
    (left right : List α) (hall : ∀ a ∈ left, predicate a = true) :
    List.takeWhile predicate (left ++ right) =
      left ++ List.takeWhile predicate right := by
  induction left with
  | nil => simp
  | cons head tail ih =>
      have hhead : predicate head = true := hall head (by simp)
      have htail : ∀ a ∈ tail, predicate a = true := by
        intro a ha
        exact hall a (by simp [ha])
      simp only [List.cons_append, List.takeWhile_cons_of_pos hhead, ih htail]

private theorem actualRetainedPrefixRun_current_in_firstLiveWindow
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0)
    (hbranch : continuingRecordingBranch rate rewards C_star C_h q t s hs control0 x) :
    ∃ hn : t.val - s < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (actualRetainedPrefixRun rate rewards C_star C_h q t s hs control0 x).records).length,
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (actualRetainedPrefixRun rate rewards C_star C_h q t s hs control0 x).records)[t.val - s]'hn =
        actualCurrentRecord rate rewards C_star C_h q t s hs control0 x := by
  let n := t.val - s
  let z := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h
    (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).1
  let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
    rcases retainedSourceFacts rate rewards C_star C_h q t s hs control0 x with
      ⟨_, helapsed⟩
    simpa only [helapsed] using
      (actualRetainedSeed rate rewards C_star C_h q t s hs control0 x).activeAtStart
  let preRun := ReferenceActivePhysicalHorizon.run initial z.1.2 q rewards s n
    (by omega) hmode
  have hrecords := actualRetainedPrefixRun_records_append rate rewards C_star C_h
    q t s hs control0 x
  have hrecords' :
      (actualRetainedPrefixRun rate rewards C_star C_h q t s hs control0 x).records =
        preRun.records ++ [actualCurrentRecord rate rewards C_star C_h q t s hs control0 x] := by
    simpa [preRun] using hrecords
  have hprefixLength : preRun.records.length = n := by
    dsimp [preRun, n]
    exact ReferenceActivePhysicalHorizon.run_record_count initial z.1.2 q rewards s
      (t.val - s) (by omega) hmode
  have htake :
      (actualRetainedPrefixRun rate rewards C_star C_h q t s hs control0 x).records.take n =
        preRun.records := by
    rw [hrecords']
    rw [List.take_append_of_le_length (by omega : n ≤ preRun.records.length)]
    exact List.take_of_length_le (by omega : preRun.records.length ≤ n)
  have hpast := hbranch.2.1
  have hall : ∀ record ∈ preRun.records ++
      [actualCurrentRecord rate rewards C_star C_h q t s hs control0 x],
      (!ReferenceCollectionPhaseHistory.cutoffChosen record.input) = true := by
    intro record hrecord
    rcases List.mem_append.mp hrecord with hprefixRecord | hcurrentRecord
    · have hcut := hpast record (by rw [htake]; exact hprefixRecord)
      simp [hcut]
    · simp only [List.mem_singleton] at hcurrentRecord
      rcases hcurrentRecord with rfl
      have hcurrent := continuingBranch_current_not_cutoff rate rewards C_star C_h
        q t s hs control0 x hbranch
      change (!ReferenceCollectionPhaseHistory.cutoffChosen
        (actualCurrentInput rate rewards C_star C_h q t s hs control0 x)) = true
      simp [hcurrent]
  simp only [ReferenceFirstLiveConfirmationHistory.firstLiveWindow]
  rw [hrecords']
  have hwindow := takeWhile_append_of_all
    (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
      !ReferenceCollectionPhaseHistory.cutoffChosen record.input)
    preRun.records
    [actualCurrentRecord rate rewards C_star C_h q t s hs control0 x]
    (by
      intro record hrecord
      apply hall record
      exact List.mem_append.mpr (Or.inl hrecord))
  have hcurrent := continuingBranch_current_not_cutoff rate rewards C_star C_h
    q t s hs control0 x hbranch
  have hcurrentTake : List.takeWhile
      (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
        !ReferenceCollectionPhaseHistory.cutoffChosen record.input)
      [actualCurrentRecord rate rewards C_star C_h q t s hs control0 x] =
        [actualCurrentRecord rate rewards C_star C_h q t s hs control0 x] := by
    simp [hcurrent, actualCurrentRecord]
  simp only [hwindow, hcurrentTake]
  refine ⟨by simp [hprefixLength, n], ?_⟩
  simp [hprefixLength, n]

private theorem actual_current_prepared_followers
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0)
    (hbranch : continuingRecordingBranch rate rewards C_star C_h q t s hs control0 x) :
    ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
      ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
        ∀ i, ((ReferenceActivePhysicalStep.prepare
          (actualCurrentInput rate rewards C_star C_h q t s hs control0 x)).followers.followers i).configuration =
            .ordinary (states i) (memories i) := by
  let z := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  rcases retainedSourceFacts rate rewards C_star C_h q t s hs control0 x with
    ⟨hc, helapsed⟩
  let n := t.val - s
  have hspan : s + (n + 1) ≤ p.T := by dsimp [n]; omega
  have hNspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed +
        (n + 1) ≤ p.T := by rw [helapsed]; exact hspan
  have hwindowIndex := actualRetainedPrefixRun_current_in_firstLiveWindow
    rate rewards C_star C_h q t s hs control0 x hbranch
  have hparts := retainedBranch_parts rate rewards C_star C_h q t s hs control0 x
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p z = q := by
    calc
      ActualInitializationPhysicalStep.selectedRowIndex p z =
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z :=
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
          p z).symm
      _ = q := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
        p q t control0 x.1 hparts.1
  have hrun : actualRetainedPrefixRun rate rewards C_star C_h q t s hs control0 x =
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate z rewards C_star C_h hc
        (n + 1) hNspan := by
    simp [actualRetainedPrefixRun,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
      actualRetainedSeed, z, n]
  let hwindowControl : ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (actualRetainedPrefixRun rate rewards C_star C_h q t s hs control0 x).records =
    ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z rewards C_star C_h hc
      (n + 1) hNspan := by
    exact congrArg (fun run : ReferenceActivePhysicalHorizon.Run _ =>
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow run.records) hrun
  let k : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z rewards C_star C_h hc
      (n + 1) hNspan).length :=
    ⟨n, by simpa [hwindowControl] using hwindowIndex.1⟩
  have hrecord :
      (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z rewards C_star C_h hc
        (n + 1) hNspan)[k.val] =
          actualCurrentRecord rate rewards C_star C_h q t s hs control0 x := by
    simpa only [k, hwindowControl] using hwindowIndex.2
  obtain ⟨cell, _, _, _, _⟩ :=
    ReferenceFirstWindowNumericalStream.actual_first_live_source_cell rate z rewards C_star C_h
      hc (n + 1) hNspan k
  refine ⟨cell.states, cell.memories, ?_⟩
  intro i
  have hordinary := cell.ordinary i
  have hconfigurationEq := congrArg
    (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
      (record.output.preparation.followers.followers i).configuration) hrecord
  rw [hconfigurationEq] at hordinary
  simpa [actualCurrentRecord, ReferenceActivePhysicalStep.step] using hordinary

/-- F's actual whole-control producer is fed by the branch's own corrected
launch seed, the original selected source row and reward table, and the
ordinary states extracted from N's actual first-live cell at the current
record. No seed, state, or PREPARE conclusion is an input hypothesis. -/
theorem actual_continuing_recording_inputs
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0)
    (hbranch : continuingRecordingBranch rate rewards C_star C_h q t s hs control0 x) :
    let z := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
    let n := t.val - s
    let hspan : s + (n + 1) ≤ p.T := by
      have ht := t.isLt
      dsimp [n]
      omega
    let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h
      (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).1
    let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z rewards C_star C_h
      (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).1
    let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
      have helapsedZ : ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s := by
        simpa [z] using
          (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).2
      change ReferenceActivePhysicalHorizon.allActiveAtStart
        (ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h
          (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).1) s
      simpa only [helapsedZ] using seed.activeAtStart
    let candidate := ReferenceContinuingDataCandidateLogging.candidateInput initial z.1.2 q
      rewards s n hspan hmode
    ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
      ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
      ∃ ho : ∀ i, ((ReferenceActivePhysicalStep.prepare candidate).followers.followers i).configuration =
        .ordinary (states i) (memories i),
      ∃ r owned base d hsStart c arm,
        ∃ hcoord : (ReferenceActivePhysicalStep.prepare candidate).coordinator =
          .live r owned base (.continuingChosen d hsStart c arm),
        ∃ henabled : candidate.time.val + 1 < d.startResult.clock.g,
          d.startResult.pending.Nonempty ∧
          (∀ u : TimeControl p, ∃ c_u arm_u,
            (ReferenceActivePhysicalStep.prepare
              (ReferenceContinuingLiveSlicePreparation.inputAtControl candidate u)).coordinator =
              .live r owned base (.continuingChosen d hsStart c_u arm_u)) ∧
          (∀ u : TimeControl p,
            PublicDiscreteDraws.slotDraw u.1 = PublicDiscreteDraws.dataSlot →
            ∀ i, ((ReferenceActivePhysicalStep.prepare
              (ReferenceContinuingLiveSlicePreparation.inputAtControl candidate u)).followers.followers i).configuration =
                .ordinary (states i) (memories i)) ∧
          initial.coordinator = .first ∧
          (∀ i, initial.followers i = .ordinary (seed.followers i) (seed.memory i)) ∧
          (∀ i, ReferencePrelaunchFollower.acceptedStart (seed.followers i) = 0) ∧
          (∀ i, (seed.followers i).S = 0) ∧
          (∀ i, (seed.followers i).delta = 0) ∧
          (∀ i, (seed.followers i).backlog = 0) ∧
          (∀ i, (seed.followers i).lastDown = none) ∧
          (∀ i, (seed.followers i).status = .unoccupied) ∧
          (∀ i, ActiveFollowerLifecycle.localStateDomainValid (seed.followers i)) ∧
          (∀ i, ActiveFollowerLifecycle.localBufferValid (seed.followers i)) ∧
          (∀ i, (seed.followers i).buffer.Pairwise
            (fun a b => a.calendarRound < b.calendarRound)) ∧
          (∀ i saved, saved ∈ (seed.followers i).buffer → saved.calendarRound ≤ s) ∧
          (∀ i, ActiveFollowerLifecycle.downDecoderStateValid (seed.followers i)) ∧
          ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
  classical
  intro z n hspan initial seed
  have helapsedZ : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s := by
    simpa [z] using
      (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).2
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
    simpa only [helapsedZ] using seed.activeAtStart
  let candidate := ReferenceContinuingDataCandidateLogging.candidateInput initial z.1.2 q
    rewards s n hspan hmode
  obtain ⟨states, memories, hoActual⟩ :=
    actual_current_prepared_followers rate rewards C_star C_h q t s hs control0 x hbranch
  obtain ⟨r, owned, base, d, hsStart, c, arm, hcoordActual, hpending, henabledActual⟩ :=
    continuingBranch_current_data rate rewards C_star C_h q t s hs control0 x hbranch
  have hcoord : (ReferenceActivePhysicalStep.prepare candidate).coordinator =
      .live r owned base (.continuingChosen d hsStart c arm) := by
    simpa [candidate, actualCurrentInput, z, n] using hcoordActual
  have ho : ∀ i, ((ReferenceActivePhysicalStep.prepare candidate).followers.followers i).configuration =
      .ordinary (states i) (memories i) := by
    intro i
    simpa [candidate, actualCurrentInput, z, n] using hoActual i
  have htime : candidate.time.val = t.val := by
    change s + n = t.val
    omega
  have henabled : candidate.time.val + 1 < d.startResult.clock.g := by
    simpa [htime] using henabledActual
  have hcontrols := ReferenceContinuingLiveSlicePreparation.continuing_cut_at_control
    candidate r owned base d hsStart c arm hcoord
  have hdata := ReferenceContinuingLiveSlicePreparation.data_preparation_at_control
    candidate states memories ho
  have hseedStamps : ∀ i saved, saved ∈ (seed.followers i).buffer →
      saved.calendarRound ≤ s := by
    intro i saved hsaved
    have h := seed.bufferStamps i saved hsaved
    rw [helapsedZ] at h
    exact h
  refine ⟨states, memories, ho, r, owned, base, d, hsStart, c, arm,
    hcoord, henabled, hpending, hcontrols, hdata,
    seed.coordinatorFirst, seed.configuration, seed.acceptedStart_zero, seed.S_zero,
    seed.delta_zero, seed.backlog_zero, seed.lastDown_none, seed.unoccupied,
    seed.localStateDomain, seed.bufferValid, seed.chronologicalBuffer,
    hseedStamps, seed.decoderValid, hmode⟩

/-- On the computed continuing branch, the actual source marker is the
recorder source selected by the existing physical preparation. Its owner,
assigned arm, feedback and typed observation are read from that same record. -/
theorem actual_continuing_source_marker_eq
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0)
    (hbranch : continuingRecordingBranch rate rewards C_star C_h q t s hs control0 x) :
    let z := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
    let n := t.val - s
    let hspan : s + (n + 1) ≤ p.T := by
      have ht := t.isLt
      dsimp [n]
      omega
    let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h
      (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).1
    let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z rewards C_star C_h
      (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).1
    let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
      have helapsedZ : ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s := by
        simpa [z] using
          (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).2
      change ReferenceActivePhysicalHorizon.allActiveAtStart
        (ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h
          (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).1) s
      simpa only [helapsedZ] using seed.activeAtStart
    let candidate := ReferenceContinuingDataCandidateLogging.candidateInput initial z.1.2 q
      rewards s n hspan hmode
    ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
      ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
      ∃ r owned base d hsStart c arm,
      (ReferenceActivePhysicalStep.prepare candidate).coordinator =
        .live r owned base (.continuingChosen d hsStart c arm) ∧
      (∀ i, ((ReferenceActivePhysicalStep.prepare candidate).followers.followers i).configuration =
        .ordinary (states i) (memories i)) ∧
      let W := ReferenceContinuingLiveSlicePreparation.liveSliceWeights r candidate.time
      let snapshot := ReferenceContinuingLiveSlicePreparation.liveSliceSnapshot
        r owned base candidate.time d states
      ∀ u : TimeControl p,
        let y := ReferenceContinuingLiveSlicePreparation.inputAtControl candidate u
        let record := ReferenceContinuingDataCandidateLogging.candidateRecord initial z.1.2 q
          rewards s n hspan hmode u
        let source := CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec
            ((y.row.2 y.time).1))
        ∀ arm : Fin p.K,
          ReferenceContinuingRecordingFastPair.candidatePhysicalMarker initial z.1.2 q
              rewards s n hspan hmode r.payload true u = some arm →
            ∃ selected_u : ReferenceActivePhysicalStep.Selection y,
              (ReferenceActivePhysicalStep.prepare y).coordinator.selection = some selected_u ∧
              selected_u.view.payload = r.payload ∧
              selected_u.started = d.startResult ∧
              (∀ i, ((ReferenceActivePhysicalStep.prepare y).followers.followers i).configuration =
                .ordinary (states i) (memories i)) ∧
              PublicDiscreteDraws.slotDraw u.1 = PublicDiscreteDraws.dataSlot ∧
              SnapshotRecordingKernel.owns p (.live r.payload.assignment snapshot) source arm ∧
              record.output.preparation.arms.actions source = arm ∧
              record.output.preparation.feedback.feedback source = rewards candidate.time arm ∧
              (record.output.preparation.feedback.observations source).val.val =
                ((rewards candidate.time arm).val : ℝ) / (D p : ℝ) := by
  classical
  intro z n hspan initial seed
  have helapsedZ : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s := by
    simpa [z] using
      (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).2
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
    simpa only [helapsedZ] using seed.activeAtStart
  let candidate := ReferenceContinuingDataCandidateLogging.candidateInput initial z.1.2 q
    rewards s n hspan hmode
  obtain ⟨states, memories, ho, r, owned, base, d, hsStart, c, arm, hcoord,
      henabled, hpending, hcontrols, hdata, hfirst, hseed, haccepted, hS, hdelta,
      hbacklog, hlastDown, hunoccupied, hlocal, hvalid, hpairwise, htime,
      hdecoder, hmodeActual⟩ :=
    actual_continuing_recording_inputs rate rewards C_star C_h q t s hs control0 x hbranch
  have hphysical :=
    ReferenceContinuingRecordingPhysicalReward.prefix_continuing_recording_physical_reward
      initial z.1.2 q rewards s n hspan hmode seed.followers seed.memory hfirst hseed
      hunoccupied hvalid hpairwise htime r owned base d hsStart c arm hcoord states memories
      ho henabled
  rcases hphysical with ⟨_, hmarkers⟩
  refine ⟨states, memories, r, owned, base, d, hsStart, c, arm, hcoord, ho, ?_⟩
  dsimp only [candidate]
  intro u
  rcases hmarkers u with ⟨hmarker, _⟩
  intro arm hselected
  rcases hmarker arm hselected with
    ⟨selected_u, hselection, hpayload, hstarted, hfollowers, hslot, howns,
      haction, hfeedback, hobservation, _⟩
  exact ⟨selected_u, hselection, hpayload, hstarted, hfollowers, hslot, howns,
    haction, hfeedback, hobservation⟩

/-- The actual saved contribution of an unoccupied follower is measurable as
the current complete control varies. The unoccupied condition is read from
the same computed PREPARE branch; no buffer or contribution is supplied. -/
theorem measurable_current_saved_contribution_on_branch
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p) (i : Fin (p.m - 1))
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0)
    (hbranch : continuingRecordingFollowerBranch
      rate rewards C_star C_h q t s hs control0 i x) :
    let z := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
    let n := t.val - s
    let hspan : s + (n + 1) ≤ p.T := by
      have ht := t.isLt
      dsimp [n]
      omega
    let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h
      (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).1
    let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z rewards C_star C_h
      (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).1
    let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
      have helapsedZ : ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s := by
        simpa [z] using
          (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).2
      change ReferenceActivePhysicalHorizon.allActiveAtStart
        (ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h
          (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).1) s
      simpa only [helapsedZ] using seed.activeAtStart
    let candidate := ReferenceContinuingDataCandidateLogging.candidateInput initial z.1.2 q
      rewards s n hspan hmode
    ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
      ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
      ∃ r owned base d hsStart c arm,
        (ReferenceActivePhysicalStep.prepare candidate).coordinator =
          .live r owned base (.continuingChosen d hsStart c arm) ∧
        (∀ j, ((ReferenceActivePhysicalStep.prepare candidate).followers.followers j).configuration =
          .ordinary (states j) (memories j)) ∧
        candidate.time.val + 1 < d.startResult.clock.g ∧
        (states i).status = .unoccupied ∧
        Measurable (fun u : TimeControl p =>
          ReferenceContinuingSavedIncrementMoments.normalizedCurrentSavedContribution
            (ReferenceContinuingDataCandidateLogging.candidateRecord initial z.1.2 q
              rewards s n hspan hmode u) r.payload i) := by
  classical
  rcases hbranch with ⟨hcontinuing, hcurrent⟩
  intro z n hspan initial seed
  have helapsedZ : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s := by
    simpa [z] using
      (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).2
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
    simpa only [helapsedZ] using seed.activeAtStart
  let candidate := ReferenceContinuingDataCandidateLogging.candidateInput initial z.1.2 q
    rewards s n hspan hmode
  obtain ⟨states, memories, ho, r, owned, base, d, hsStart, c, arm, hcoord,
      henabled, hpending, hcontrols, hdata, hfirst, hseed, haccepted, hS, hdelta,
      hbacklog, hlastDown, hseedUnoccupied, hlocal, hvalid, hpairwise, htime,
      hdecoder, hmodeActual⟩ :=
    actual_continuing_recording_inputs rate rewards C_star C_h q t s hs control0 x hcontinuing
  have hcurrentUnoccupied : (states i).status = .unoccupied := by
    have hcurrentCandidate :
        match ((ReferenceActivePhysicalStep.prepare candidate).followers.followers i).configuration with
        | .ordinary state _ => state.status = .unoccupied
        | .dagger => False := by
      simpa [candidate, actualCurrentInput, z, n] using hcurrent
    rw [ho i] at hcurrentCandidate
    exact hcurrentCandidate
  have hmoments :=
    ReferenceContinuingSavedIncrementMoments.actual_continuing_saved_increment_moments
      initial z.1.2 q rewards s n hspan hmode seed.followers seed.memory hfirst hseed
      hseedUnoccupied hvalid hpairwise htime r owned base d hsStart c arm hcoord states memories
      ho henabled i hcurrentUnoccupied
  rcases hmoments with ⟨_, _, hmeasurable, _, _, _, _, _, _, _, _, _⟩
  refine ⟨states, memories, r, owned, base, d, hsStart, c, arm,
    hcoord, ho, henabled, hcurrentUnoccupied, ?_⟩
  simpa only [candidate] using hmeasurable

/-- The literal current continuing PREPARE constructor produces C's stable
registers, owned registers, pending set, payload, cutoff weights and clock
under every current complete-control replacement. No altered source or
second state is introduced. -/
theorem actual_continuing_cut_at_control
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0)
    (hbranch : continuingRecordingBranch rate rewards C_star C_h q t s hs control0 x) :
    ∃ r owned base d hsStart c arm,
      (ReferenceActivePhysicalStep.prepare
        (actualCurrentInput rate rewards C_star C_h q t s hs control0 x)).coordinator =
        .live r owned base (.continuingChosen d hsStart c arm) ∧
      d.startResult.pending.Nonempty ∧ t.val + 1 < d.startResult.clock.g ∧
      ∀ u : TimeControl p, ∃ c_u arm_u,
        (ReferenceActivePhysicalStep.prepare
          (ReferenceContinuingLiveSlicePreparation.inputAtControl
            (actualCurrentInput rate rewards C_star C_h q t s hs control0 x) u)).coordinator =
          .live r owned base (.continuingChosen d hsStart c_u arm_u) := by
  obtain ⟨r, owned, base, d, hsStart, c, arm, hcoord, hpending, henabled⟩ :=
    continuingBranch_current_data rate rewards C_star C_h q t s hs control0 x hbranch
  have hcontrols := ReferenceContinuingLiveSlicePreparation.continuing_cut_at_control
    (actualCurrentInput rate rewards C_star C_h q t s hs control0 x)
    r owned base d hsStart c arm hcoord
  exact ⟨r, owned, base, d, hsStart, c, arm, hcoord, hpending, henabled, hcontrols⟩

/-- The original-source prefix seed agrees with the corrected launch state
used by A. This is a source identity, not an independently supplied seed. -/
theorem actualRetainedSeed_launchState
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0) :
    (ReferenceFirstLaunchNumericalCell.launchState rate
      (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1)
      rewards C_star C_h (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).1).coordinator = .first :=
  (actualRetainedSeed rate rewards C_star C_h q t s hs control0 x).coordinatorFirst

end Bandits.Support.ReferenceFirstLiveRecordingSourceBranch

end
