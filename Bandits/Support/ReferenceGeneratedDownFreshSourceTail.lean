/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedDownQthDecomposition
public import Bandits.Support.ReferenceGeneratedDownPrefixPositiveHalf

import Lean.Elab.Tactic.Omega

/-!
# Original-source fresh-reset DOWN recurrence and tail

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:112-146`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

Each event is a literal pullback of D's generated DOWN predicate to the
original complete source. The zero event is the real launch-stratum reset.
The finite recurrence is unconditional under the original source law; it is
not a conditional batch-history or decoder-coverage theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal
open scoped Classical
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceGeneratedDownBatchCalendar
open Bandits.Support.ReferenceGeneratedDownQthCalendar
open Bandits.Support.ReferenceGeneratedDownQthDecomposition
open Bandits.Support.ReferenceGeneratedDownPrefixEvent
open Bandits.Support.ReferenceGeneratedDownPrefixPositiveHalf

namespace Bandits.Support.ReferenceGeneratedDownFreshSourceTail

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceGeneratedDownBatchCalendar.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev Candidate (p : Parameters) :=
  AffineChannelLaw.Word (AffineBatchDecoder.width p)

variable {p : Parameters} {rate : RateInput p}

/- The zero case remains D's actual reset event on the launch stratum. -/
def generatedDownFreshSourceEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaT : alpha < p.T) (candidate : Candidate p) (q : ℕ) :
    Set (SourceInput p) :=
  {source | ∃ x : ReferenceGeneratedDownQthCalendar.LaunchSource
      rate rewards C_star C_h s hs,
    x.1 = source ∧
      generatedDownD rate rewards C_star C_h s q hs i alpha halpha halphaT candidate x}

private abbrev FreshCellIndex (p : Parameters) (alpha : ℕ) :=
  Fin (M p) × {r : Fin p.T // alpha ≤ r.val}

private def freshPositiveCell
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (candidate : Candidate p) (q : ℕ) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (cell : FreshCellIndex p alpha) : Set (SourceInput p) :=
  downPrefixPositiveSourceEvent (rate := rate) rewards C_star C_h cell.1 cell.2.1 s
    hs (Nat.le_trans (Nat.le_of_lt halpha) cell.2.2) i alpha halpha cell.2.2
      candidate q hq hqQ control0

private def freshHashOneCell
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (candidate : Candidate p) (q : ℕ) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (cell : FreshCellIndex p alpha) : Set (SourceInput p) :=
  downPrefixPositiveHashOneSourceEvent (rate := rate) rewards C_star C_h cell.1
    cell.2.1 s hs (Nat.le_trans (Nat.le_of_lt halpha) cell.2.2) i alpha halpha
    cell.2.2 candidate q hq hqQ control0

private def freshPositiveUnion
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (candidate : Candidate p) (q : ℕ) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) : Set (SourceInput p) :=
  ⋃ cell : FreshCellIndex p alpha,
    freshPositiveCell (rate := rate) rewards C_star C_h s hs i alpha halpha candidate q
      hq hqQ control0 cell

private def freshHashOneUnion
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (candidate : Candidate p) (q : ℕ) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) : Set (SourceInput p) :=
  ⋃ cell : FreshCellIndex p alpha,
    freshHashOneCell (rate := rate) rewards C_star C_h s hs i alpha halpha candidate q
      hq hqQ control0 cell

private theorem roundInput_ext
    {left right : ReferenceActivePhysicalStep.RoundInput p rate}
    (hstate : left.state = right.state) (hrows : left.rows = right.rows)
    (hselected : left.selected = right.selected) (htime : left.time = right.time)
    (hrewards : left.rewards = right.rewards) : left = right := by
  cases left
  cases right
  simp_all

private theorem generatedCurrentDownRecord_input_eq_sourcePrefixInput
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (_halpha : s < alpha)
    (j : Fin (M p)) (r : Fin p.T) (hsr : s ≤ r.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (branch : GeneratedDownBranch (rate := rate) rewards C_star C_h j r i s) :
    (generatedCurrentDownRecord (rate := rate) rewards C_star C_h j r i s hsr
      control0 branch).input =
      ReferenceDownCompletedAmbiguityMeasurability.prefixInput s (r.val - s) (by omega)
        (generatedSourceRunInput rate rewards C_star C_h s hs
          ⟨branch.1, branch.2.2.1, branch.2.2.2⟩) := by
  let sourceLaunch : ReferenceGeneratedDownQthCalendar.LaunchSource
      rate rewards C_star C_h s hs :=
    ⟨branch.1, branch.2.2.1, branch.2.2.2⟩
  let retained0 := ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
    (rate := rate) rewards C_star C_h j r (0, i) s hsr control0 branch
  let actualControl : ContinuousLearningRows.TimeControl p :=
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p j r branch.1).1
  let retainedActual := ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
    (rate := rate) rewards C_star C_h j r (0, i) s hsr actualControl branch
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p branch.1 = j :=
    ReferenceGeneratedAffineHashHalf.selectedRowIndex_of_generatedLaunchBranch
      (rate := rate) rewards C_star C_h j r (0, i) s branch
  have hsplitSelected :
      ActualInitializationPhysicalStep.selectedRowIndex p
        (ReferenceGeneratedActivePrefixFactor.splitSource j r control0 retained0.1) = j := by
    rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p j r control0 retained0.1 retained0.2.1
  have hrem : retained0.1 = retainedActual.1 := by
    rw [ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch_val,
      ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch_val]
  have hstate := ReferenceGeneratedDownPrefixEvent.retainedPrefixFinalState_eq_of_remainder_eq
    rate rewards C_star C_h j r s hsr control0 actualControl retained0 retainedActual hrem
      (r.val - s) (by omega)
  have hrunInput := ReferenceGeneratedDownPrefixEvent.retainedPrefixRunInput_eq_source
    rate rewards C_star C_h j r s hs hsr sourceLaunch hselected retainedActual
    (ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch_val
      (rate := rate) rewards C_star C_h j r (0, i) s hsr actualControl branch)
  have hbranchState := ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch_state
    (rate := rate) rewards C_star C_h j r (0, i) s hsr control0 branch
  have hstateSource :
      (generatedCurrentDownInput (rate := rate) rewards C_star C_h j r i s hsr
        control0 branch).state =
      (ReferenceActiveHorizonMeasurability.runOfInput s (r.val - s) (by omega)
        (generatedSourceRunInput rate rewards C_star C_h s hs sourceLaunch)).finalState := by
    calc
      _ = (ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
          rate rewards C_star C_h j r control0 retained0.1 retained0.2.1 s
          (r.val - s) hsr retained0.2.2 (by omega)).finalState := by
            simpa [generatedCurrentDownInput] using hbranchState
      _ = (ReferenceActiveHorizonMeasurability.runOfInput s (r.val - s) (by omega)
            (retainedPrefixRunInput rate rewards C_star C_h j r s hsr control0 retained0)).finalState := by
              simp only [ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor,
                ReferenceActiveHorizonMeasurability.runOfInput, retainedPrefixRunInput,
                ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed]
              rw [hsplitSelected]
      _ = (ReferenceActiveHorizonMeasurability.runOfInput s (r.val - s) (by omega)
            (retainedPrefixRunInput rate rewards C_star C_h j r s hsr actualControl retainedActual)).finalState := hstate
      _ = (ReferenceActiveHorizonMeasurability.runOfInput s (r.val - s) (by omega)
            (generatedSourceRunInput rate rewards C_star C_h s hs sourceLaunch)).finalState := by
              rw [hrunInput]
  have hfields := ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch_original_fields
    (rate := rate) rewards C_star C_h j r (0, i) s hsr control0 branch
  have hsourceSelected :
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p branch.1 = j := by
    rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact hselected
  have hinput : generatedCurrentDownInput (rate := rate) rewards C_star C_h j r i s hsr
      control0 branch =
      ReferenceDownCompletedAmbiguityMeasurability.prefixInput s (r.val - s) (by omega)
        (generatedSourceRunInput rate rewards C_star C_h s hs sourceLaunch) := by
    apply roundInput_ext
    · exact hstateSource
    · simpa [generatedCurrentDownInput,
        ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
        ReferenceActivePhysicalHorizon.roundInputAt, generatedSourceRunInput,
        sourceLaunch] using hfields.1
    · calc
        (generatedCurrentDownInput (rate := rate) rewards C_star C_h j r i s hsr
          control0 branch).selected =
            ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p branch.1 := by
              simpa [generatedCurrentDownInput] using hfields.2.1
        _ = j := hsourceSelected
        _ = (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s (r.val - s)
            (by omega) (generatedSourceRunInput rate rewards C_star C_h s hs sourceLaunch)).selected := by
              simpa [ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
                ReferenceActivePhysicalHorizon.roundInputAt, generatedSourceRunInput,
                sourceLaunch] using hselected.symm
    · calc
        (generatedCurrentDownInput (rate := rate) rewards C_star C_h j r i s hsr
          control0 branch).time = r := by
            simpa [generatedCurrentDownInput] using hfields.2.2.1
        _ = (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s (r.val - s)
            (by omega) (generatedSourceRunInput rate rewards C_star C_h s hs sourceLaunch)).time := by
              apply Fin.ext
              simp only [ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
                ReferenceActivePhysicalHorizon.roundInputAt]
              omega
    · simpa [generatedCurrentDownInput,
        ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
        ReferenceActivePhysicalHorizon.roundInputAt, generatedSourceRunInput, sourceLaunch]
        using hfields.2.2.2
  exact hinput

private theorem generatedCurrentDownTest_eq_sourceTest
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (j : Fin (M p)) (r : Fin p.T) (hsr : s ≤ r.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (branch : GeneratedDownBranch (rate := rate) rewards C_star C_h j r i s) :
    ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
        (generatedCurrentDownRecord (rate := rate) rewards C_star C_h j r i s hsr control0
          branch).input i) =
    ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      ((generatedSourceObservation rate rewards C_star C_h s hs i
        ⟨branch.1, branch.2.2.1, branch.2.2.2⟩).2 ⟨r.val - s, by omega⟩) := by
  rw [generatedCurrentDownRecord_input_eq_sourcePrefixInput (rate := rate) rewards C_star C_h
    s hs i alpha halpha j r hsr control0 branch]
  rfl

private theorem sourcePrefixMarker_to_pairCylinder
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (_halphaT : alpha < p.T) (candidate : Candidate p) (q : ℕ)
    (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (j : Fin (M p)) (r : Fin p.T) (hsr : s ≤ r.val) (har : alpha ≤ r.val)
    (source : SourceInput p)
    (hselected : ActualInitializationPhysicalStep.selectedRowIndex p source = j)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s)
    (hmarker : sourcePrefixMarker rate rewards C_star C_h r s hs hsr i alpha halpha har
      candidate q hq hqQ ⟨source, hcross, helapsed⟩)
    (control0 : ContinuousLearningRows.TimeControl p) :
    (ReferenceSelectedAffinePairLaw.fixedPairSplit p j r (0, i) source).2 ∈
      prefixPairCylinder rate rewards C_star C_h j r s hs hsr control0 i alpha halpha har
        candidate q hq hqQ := by
  have hprefix : source ∈ sourcePrefixEvent rate rewards C_star C_h j r s hs hsr
      i alpha halpha har candidate q hq hqQ := by
    change ∃ h : source ∈ sourcePrefixStratum rate rewards C_star C_h j s,
      sourcePrefixMarker rate rewards C_star C_h r s hs hsr i alpha halpha har candidate q hq
        hqQ ⟨source, h.2.1, h.2.2⟩
    refine ⟨⟨hselected, hcross, helapsed⟩, ?_⟩
    exact hmarker
  have hEq := congrArg (fun S : Set (SourceInput p) => source ∈ S)
    (sourcePrefixEvent_eq_pairCylinder rate rewards C_star C_h j r s hs hsr control0
      i alpha halpha har candidate q hq hqQ)
  rw [hEq] at hprefix
  simpa only [Set.mem_preimage] using hprefix

/-- A full-run strong qth detector reconstructs P's physical DOWN selector
from the executed decoder call, then becomes the same-source hash-one event. -/
private theorem generatedDownQthAt_to_hashOneCell
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaT : alpha < p.T) (candidate : Candidate p) (q : ℕ)
    (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (x : ReferenceGeneratedDownQthCalendar.LaunchSource rate rewards C_star C_h s hs)
    (j : Fin (M p)) (hselected : ActualInitializationPhysicalStep.selectedRowIndex p x.1 = j)
    (r : Fin p.T) (hsr : s ≤ r.val) (har : alpha ≤ r.val)
    (hlocal : generatedDownQthAt rewards C_star C_h s hs i alpha halpha halphaT
      candidate q hq hqQ x r hsr har) :
    x.1 ∈ freshHashOneCell (rate := rate) rewards C_star C_h s hs i alpha halpha
      candidate q hq hqQ control0 (j, ⟨r, har⟩) := by
  rcases hlocal with ⟨hmarker, test, htest, hgood⟩
  let input := ReferenceDownCompletedAmbiguityMeasurability.prefixInput s (r.val - s)
    (by omega) (generatedSourceRunInput rate rewards C_star C_h s hs x)
  let record : ReferenceFollowerDownDecoderReplay.Record p rate :=
    ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩
  have htestRecord : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) =
        some test := by
    change ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
        (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s (r.val - s)
          (by omega) (generatedSourceRunInput rate rewards C_star C_h s hs x)) i) = some test
    exact htest
  obtain ⟨call, hcall, heligible, _htimeCall, _hsampleCall, htimeRecord,
    hsampleRecord, hsentRecord⟩ :=
    ReferenceGeneratedDownPrefixList.executedTestOfRound_some_actual record i test htestRecord
  have hdown : ActiveFollowerDownAcceptance.downSelected p i
      (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
      (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i) := by
    classical
    cases hc : ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i with
    | dagger =>
        simp [ReferenceFollowerDownDecoderReplay.actualDownCall, hc] at hcall
    | ordinary state memory =>
        have hcallOrd := ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary
          record i state memory hc
        have hcallEq : call =
            (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i,
              ActiveFollowerDownAcceptance.currentRoundInput p i
                (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
                (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
                (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
                rate state) := Option.some.inj (hcall.symm.trans hcallOrd)
        have hcallInput : call.2 = ActiveFollowerDownAcceptance.currentRoundInput p i
            (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
            (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate state :=
          congrArg Prod.snd hcallEq
        have heligibleInput : AffineBatchDecoder.eligible
            (ActiveFollowerDownAcceptance.currentRoundInput p i
              (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
              (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
              (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate state) := by
          rw [← hcallInput]
          exact heligible
        exact (ReferenceFollowerDownDecoderReplay.actualDownCall_eligible_iff
          record i state).mp heligibleInput |>.1
  have hprepRow : ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i =
      record.input.row := (record.output.preparation.follower_alignment i).1
  have hprepTime : ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i =
      record.input.time := ReferenceFollowerDownDecoderReplay.preparedChoiceTime_eq_recordTime record i
  have hrecordRow : record.input.row = x.1.1.2 j := by
    change x.1.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x.1) =
      x.1.1.2 j
    rw [hselected]
  have hrecordTime : record.input.time = r := by
    apply Fin.ext
    simp [record, input, ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
      ReferenceActivePhysicalHorizon.roundInputAt]
    omega
  have hdownSource : ActiveFollowerDownAcceptance.downSelected p i
      (x.1.1.2 j) r := by
    simpa only [hprepRow, hprepTime, hrecordRow, hrecordTime] using hdown
  have hchannel : ReferenceSelectedAffinePairLaw.selectedChannel p
      ((x.1.1.2 j).2 r).1 = some ((0, i) : ContinuousLearningRows.Channel p) := by
    rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_down p _ hdownSource.1,
      hdownSource.2]
    rfl
  have hselector : ReferenceSelectedAffinePairLaw.selector p r x.1 = (j, some (0, i)) := by
    apply (ReferenceSelectedAffinePairLaw.selector_eq_iff p j r (0, i) x.1).2
    constructor
    · change ActualInitializationPhysicalStep.selectedRowIndex p x.1 = j
      exact hselected
    · exact hchannel
  let branch : GeneratedDownBranch (rate := rate) rewards C_star C_h j r i s :=
    ⟨x.1, ⟨hselector, x.2.1, x.2.2⟩⟩
  have hinputEq := generatedCurrentDownRecord_input_eq_sourcePrefixInput
    (rate := rate) rewards C_star C_h s hs i alpha halpha j r hsr control0 branch
  have htestP : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
        (generatedCurrentDownRecord (rate := rate) rewards C_star C_h j r i s hsr
          control0 branch).input i) = some test := by
    rw [generatedCurrentDownTest_eq_sourceTest (rate := rate) rewards C_star C_h s hs i alpha
      halpha j r hsr control0 branch]
    exact htest
  have htimeP : test.time = r := htimeRecord.trans hrecordTime
  have hsampleP : test.sample = ((x.1.1.2 j).2 r).2 (0, i) := by
    simpa only [hrecordRow, hrecordTime] using hsampleRecord
  have hsentP : test.sent = ReferenceActiveAffinePositiveTest.downSent
      (generatedCurrentDownRecord (rate := rate) rewards C_star C_h j r i s hsr
        control0 branch).input := by
    calc
      test.sent = ReferenceActiveAffinePositiveTest.downSent record.input := hsentRecord
      _ = ReferenceActiveAffinePositiveTest.downSent
          (generatedCurrentDownRecord (rate := rate) rewards C_star C_h j r i s hsr
            control0 branch).input := by
        exact congrArg ReferenceActiveAffinePositiveTest.downSent hinputEq.symm
  have hcylinder := sourcePrefixMarker_to_pairCylinder (rate := rate) rewards C_star C_h s hs
    i alpha halpha halphaT candidate q hq hqQ j r hsr har x.1 hselected x.2.1 x.2.2
    hmarker control0
  have hrecordRowP : (generatedCurrentDownRecord (rate := rate) rewards C_star C_h j r i s
      hsr control0 branch).input.row = x.1.1.2 j := by
    rw [hinputEq]
    exact hrecordRow
  have hpositive : x.1 ∈ downPrefixPositiveSourceEvent (rate := rate) rewards C_star C_h j r s
      hs hsr i alpha halpha har candidate q hq hqQ control0 := by
    simp only [downPrefixPositiveSourceEvent, Set.mem_ofPred_eq]
    refine ⟨branch, rfl, hselector, hmarker, hcylinder, test, htestP, htimeP, ?_, hsentP,
      hgood.1⟩
    simpa only [← hrecordRowP] using hsampleP
  have hhashSource : AffineChannelLaw.affineHash
      (((x.1.1.2 j).2 r).2 (0, i)) candidate = 1 := by
    rw [← hsampleP]
    exact hgood.2
  exact ⟨hpositive, hhashSource⟩

private theorem freshPositiveCell_to_qthSent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaT : alpha < p.T) (candidate : Candidate p) (q : ℕ)
    (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (j : Fin (M p)) (r : Fin p.T) (har : alpha ≤ r.val)
    (source : SourceInput p)
    (hsource : source ∈ freshPositiveCell (rate := rate) rewards C_star C_h s hs i
      alpha halpha candidate q hq hqQ control0 (j, ⟨r, har⟩)) :
    ∃ x : ReferenceGeneratedDownQthCalendar.LaunchSource rate rewards C_star C_h s hs,
      x.1 = source ∧
      generatedDownQthAtSent rewards C_star C_h s hs i alpha halpha halphaT candidate q
        hq hqQ x r (by omega) har := by
  change source ∈ downPrefixPositiveSourceEvent (rate := rate) rewards C_star C_h j r s hs
    (by omega) i alpha halpha har candidate q hq hqQ control0 at hsource
  rcases hsource with ⟨branch, hbranch, hselector, hmarker, _hcylinder, test, htest,
      _htime, _hsample, _hsent, hnotSent⟩
  subst source
  let x : ReferenceGeneratedDownQthCalendar.LaunchSource rate rewards C_star C_h s hs :=
    ⟨branch.1, branch.2.2.1, branch.2.2.2⟩
  refine ⟨x, rfl, ?_⟩
  refine ⟨?_, test, ?_, hnotSent⟩
  · simpa [x] using hmarker
  · change ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        ((generatedSourceObservation rate rewards C_star C_h s hs i x).2
          ⟨r.val - s, by omega⟩) = some test
    rw [← generatedCurrentDownTest_eq_sourceTest (rate := rate) rewards C_star C_h s hs i
      alpha halpha j r (by omega) control0 branch]
    exact htest

private theorem freshHashOneCell_to_qthAt
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaT : alpha < p.T) (candidate : Candidate p) (q : ℕ)
    (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (j : Fin (M p)) (r : Fin p.T) (har : alpha ≤ r.val)
    (source : SourceInput p)
    (hsource : source ∈ freshHashOneCell (rate := rate) rewards C_star C_h s hs i
      alpha halpha candidate q hq hqQ control0 (j, ⟨r, har⟩)) :
    ∃ x : ReferenceGeneratedDownQthCalendar.LaunchSource rate rewards C_star C_h s hs,
      x.1 = source ∧
      generatedDownQthAt rewards C_star C_h s hs i alpha halpha halphaT candidate q hq hqQ
        x r (by omega) har := by
  change source ∈ downPrefixPositiveHashOneSourceEvent (rate := rate) rewards C_star C_h j r s
    hs (by omega) i alpha halpha har candidate q hq hqQ control0 at hsource
  have hgood := downPrefixPositiveHashOneSourceEvent_current_good
    (rate := rate) rewards C_star C_h j r s hs (by omega) i alpha halpha har candidate q hq hqQ
    control0 source hsource
  rcases hgood with ⟨branch, hbranch, test, htest, htestGood⟩
  subst source
  let x : ReferenceGeneratedDownQthCalendar.LaunchSource rate rewards C_star C_h s hs :=
    ⟨branch.1, branch.2.2.1, branch.2.2.2⟩
  have hmarker : sourcePrefixMarker rate rewards C_star C_h r s hs (by omega) i alpha halpha
      har candidate q hq hqQ x := by
    rcases hsource.1 with ⟨branch', hbranch', _hselector, hmarker, _hcylinder,
      _test', _htest, _htime, _hsample, _hsent, _hnotSent⟩
    have hbranchEq : branch' = branch := Subtype.ext hbranch'
    subst branch'
    simpa [x] using hmarker
  refine ⟨x, rfl, hmarker, test, ?_, htestGood⟩
  change ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      ((generatedSourceObservation rate rewards C_star C_h s hs i x).2
        ⟨r.val - s, by omega⟩) = some test
  rw [← generatedCurrentDownTest_eq_sourceTest (rate := rate) rewards C_star C_h s hs i
    alpha halpha j r (by omega) control0 branch]
  exact htest

private theorem generatedDownD_has_qth_by_indicator_sum
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaT : alpha < p.T) (candidate : Candidate p) (q : ℕ)
    (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (x : ReferenceGeneratedDownQthCalendar.LaunchSource rate rewards C_star C_h s hs)
    (hD : generatedDownD rate rewards C_star C_h s q hs i alpha halpha halphaT candidate x) :
    ∃ r : {r : Fin p.T // alpha ≤ r.val},
      generatedDownQthAt rewards C_star C_h s hs i alpha halpha halphaT candidate q hq hqQ
        x r.1 (by omega) r.2 := by
  classical
  let Valid := {r : Fin p.T // alpha ≤ r.val}
  let detects (r : Valid) := generatedDownQthAt rewards C_star C_h s hs i alpha halpha halphaT
    candidate q hq hqQ x r.1 (by omega) r.2
  have hsum := generatedDownQthAt_indicator_sum rewards C_star C_h s hs i alpha halpha halphaT
    candidate q hq hqQ x
  dsimp only at hsum
  rw [ite_eq_left hD] at hsum
  by_contra hnone
  push Not at hnone
  have hzero : (∑ r : Valid, if detects r then (1 : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r _hr
    exact ite_eq_right (hnone r)
  rw [hzero] at hsum
  norm_num at hsum

private theorem freshHashOneUnion_eq_event
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaT : alpha < p.T) (candidate : Candidate p) (q : ℕ)
    (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    freshHashOneUnion (rate := rate) rewards C_star C_h s hs i alpha halpha candidate q hq hqQ
        control0 =
      generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s hs i alpha halpha
        halphaT candidate q := by
  classical
  ext source
  simp only [freshHashOneUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨cell, hcell⟩
    obtain ⟨x, hx, hlocal⟩ := freshHashOneCell_to_qthAt (rate := rate) rewards C_star C_h s hs
      i alpha halpha halphaT candidate q hq hqQ control0 cell.1 cell.2.1 cell.2.2 source hcell
    have hsr : s ≤ cell.2.1.val := Nat.le_trans (Nat.le_of_lt halpha) cell.2.2
    exact ⟨x, hx, (generatedDownD_iff_exists_qth rewards C_star C_h s hs i alpha halpha
      halphaT candidate q hq hqQ x).mpr ⟨cell.2.1, hsr, cell.2.2, hlocal⟩⟩
  · rintro ⟨x, hx, hD⟩
    obtain ⟨r, hlocal⟩ := generatedDownD_has_qth_by_indicator_sum (rate := rate) rewards
      C_star C_h s hs i alpha halpha halphaT candidate q hq hqQ x hD
    have hsr : s ≤ r.1.val := Nat.le_trans (Nat.le_of_lt halpha) r.2
    let j := ActualInitializationPhysicalStep.selectedRowIndex p x.1
    let cell : FreshCellIndex p alpha := (j, r)
    refine ⟨cell, ?_⟩
    have hselected : ActualInitializationPhysicalStep.selectedRowIndex p x.1 = j := rfl
    have hcell := generatedDownQthAt_to_hashOneCell (rate := rate) rewards C_star C_h s hs i
      alpha halpha halphaT candidate q hq hqQ control0 x j hselected r.1 hsr r.2 hlocal
    change source ∈ freshHashOneCell (rate := rate) rewards C_star C_h s hs i alpha halpha
      candidate q hq hqQ control0 cell
    rw [← hx]
    exact hcell

private theorem generatedSourcePreAlphaTests_nil
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (x : ReferenceGeneratedDownQthCalendar.LaunchSource rate rewards C_star C_h s hs) :
    (((List.ofFn (generatedSourceObservation rate rewards C_star C_h s hs i x).2).take
        (alpha - s)).filterMap (fun round =>
          if alpha ≤ round.1.val then executedTestOfRound rate round else none)) = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro round hround
  obtain ⟨k, hk, hget⟩ := List.mem_take_iff_getElem.mp hround
  have hkAlpha : k < alpha - s := by omega
  have hlen : (List.ofFn (generatedSourceObservation rate rewards C_star C_h s hs i x).2).length =
      p.T - s := List.length_ofFn
  have hkFull : k < p.T - s := by rw [← hlen]; omega
  let physicalTime : Fin p.T := ⟨s + k, by omega⟩
  have hkSub : physicalTime.val - s = k := by simp [physicalTime]
  have htime := ReferenceGeneratedDownQthCalendar.generatedSourceObservation_round_time
    rewards C_star C_h s hs i x physicalTime (by dsimp [physicalTime]; omega)
  have htime' : ((generatedSourceObservation rate rewards C_star C_h s hs i x).2
      ⟨k, hkFull⟩).1 = physicalTime := by
    apply Fin.ext
    have htimeVal := congrArg Fin.val htime
    simpa [physicalTime, hkSub] using htimeVal
  have hroundEq : round =
      (generatedSourceObservation rate rewards C_star C_h s hs i x).2 ⟨k, hkFull⟩ := by
    simpa only [List.getElem_ofFn] using hget.symm
  have hnot : ¬ alpha ≤ round.1.val := by
    rw [hroundEq, htime']
    dsimp [physicalTime]
    omega
  simp [hnot]

private theorem sourcePrefixMarker_at_reset_iff_boundary
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaT : alpha < p.T) (candidate : Candidate p)
    (x : ReferenceGeneratedDownQthCalendar.LaunchSource rate rewards C_star C_h s hs) :
    sourcePrefixMarker rate rewards C_star C_h ⟨alpha, halphaT⟩ s hs (Nat.le_of_lt halpha) i alpha halpha
        le_rfl candidate 1 (by omega) (Nat.succ_le_of_lt (AffineBatchDecoder.quota_pos p)) x ↔
      generatedSourceBatchBoundary rate rewards C_star C_h s hs i alpha halpha halphaT x := by
  rw [sourcePrefixMarker_iff rewards C_star C_h s hs i alpha halpha halphaT candidate 1
    (by omega) (Nat.succ_le_of_lt (AffineBatchDecoder.quota_pos p)) x ⟨alpha, halphaT⟩
    (Nat.le_of_lt halpha) le_rfl]
  constructor
  · rintro ⟨hboundary, _hincoming, _hcount, _hgood⟩
    exact hboundary
  · intro hboundary
    have hincoming : ∃ state memory,
        (ReferenceActiveHorizonMeasurability.runOfInput s (alpha - s) (by omega)
          (generatedSourceRunInput rate rewards C_star C_h s hs x)).finalState.followers i =
          .ordinary state memory := by
      exact hboundary.2
    have hprior :
        (((List.ofFn (generatedSourceObservation rate rewards C_star C_h s hs i x).2).take
            (alpha - s)).filterMap (fun round =>
              if alpha ≤ round.1.val then executedTestOfRound rate round else none)) = [] :=
      generatedSourcePreAlphaTests_nil (rate := rate) rewards C_star C_h s hs i alpha halpha x
    refine ⟨hboundary, ?_, ?_, ?_⟩
    · simpa using hincoming
    · change (((List.ofFn (generatedSourceObservation rate rewards C_star C_h s hs i x).2).take
        (alpha - s)).filterMap (fun round =>
          if alpha ≤ round.1.val then executedTestOfRound rate round else none)).length = 1 - 1
      rw [hprior]
      rfl
    · rw [hprior]
      simp

private theorem generatedDownFreshSourceEvent_zero_eq_reset_union
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaT : alpha < p.T) (candidate : Candidate p) :
    generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s hs i alpha halpha
        halphaT candidate 0 =
      ⋃ j : Fin (M p), sourcePrefixEvent rate rewards C_star C_h j ⟨alpha, halphaT⟩ s hs
        (Nat.le_of_lt halpha) i alpha halpha le_rfl candidate 1 (by omega)
        (Nat.succ_le_of_lt (AffineBatchDecoder.quota_pos p)) := by
  classical
  ext source
  simp only [generatedDownFreshSourceEvent, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨x, rfl, hzero⟩
    have hboundary := (generatedDownD_zero rate rewards C_star C_h s hs i alpha halpha halphaT
      candidate x).mp hzero
    let j := ActualInitializationPhysicalStep.selectedRowIndex p x.1
    have hcross : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput x.1 rewards C_star C_h rate)).crossing.isSome =
        true := x.2.1
    have helapsed : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput x.1 rewards C_star C_h rate)).completed = s :=
      x.2.2
    have hstratum : x.1 ∈ sourcePrefixStratum rate rewards C_star C_h j s :=
      ⟨rfl, hcross, helapsed⟩
    have hmarker := (sourcePrefixMarker_at_reset_iff_boundary (rate := rate) rewards C_star C_h
      s hs i alpha halpha halphaT candidate x).2 hboundary
    refine ⟨j, ?_⟩
    change ∃ h : x.1 ∈ sourcePrefixStratum rate rewards C_star C_h j s,
      sourcePrefixMarker rate rewards C_star C_h ⟨alpha, halphaT⟩ s hs (Nat.le_of_lt halpha) i alpha halpha
        le_rfl candidate 1 (by omega) (Nat.succ_le_of_lt (AffineBatchDecoder.quota_pos p))
        ⟨x.1, h.2⟩
    exact ⟨hstratum, by simpa using hmarker⟩
  · rintro ⟨j, hsource⟩
    change ∃ h : source ∈ sourcePrefixStratum rate rewards C_star C_h j s,
      sourcePrefixMarker rate rewards C_star C_h ⟨alpha, halphaT⟩ s hs (Nat.le_of_lt halpha) i alpha halpha
        le_rfl candidate 1 (by omega) (Nat.succ_le_of_lt (AffineBatchDecoder.quota_pos p))
        ⟨source, h.2⟩ at hsource
    rcases hsource with ⟨hstratum, hmarker⟩
    rcases hstratum with ⟨_hselected, hcross, helapsed⟩
    let x : ReferenceGeneratedDownQthCalendar.LaunchSource rate rewards C_star C_h s hs :=
      ⟨source, hcross, helapsed⟩
    have hboundary := (sourcePrefixMarker_at_reset_iff_boundary (rate := rate) rewards C_star C_h
      s hs i alpha halpha halphaT candidate x).mp (by simpa [x] using hmarker)
    exact ⟨x, rfl, (generatedDownD_zero rate rewards C_star C_h s hs i alpha halpha halphaT
      candidate x).mpr hboundary⟩

theorem measurableSet_generatedDownFreshSourceEvent_zero
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaT : alpha < p.T) (candidate : Candidate p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSet (generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s hs i
      alpha halpha halphaT candidate 0) := by
  rw [generatedDownFreshSourceEvent_zero_eq_reset_union (rate := rate) rewards C_star C_h s hs i
    alpha halpha halphaT candidate]
  apply MeasurableSet.iUnion
  intro j
  exact ReferenceGeneratedDownPrefixEvent.measurableSet_sourcePrefixEvent rate rewards C_star C_h j
    ⟨alpha, halphaT⟩ s hs (Nat.le_of_lt halpha) control0 i alpha halpha le_rfl candidate 1
    (by omega) (Nat.succ_le_of_lt (AffineBatchDecoder.quota_pos p))

theorem measurableSet_generatedDownFreshSourceEvent_of_pos
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaT : alpha < p.T) (candidate : Candidate p) (q : ℕ)
    (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSet (generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s hs i
      alpha halpha halphaT candidate q) := by
  rw [← freshHashOneUnion_eq_event (rate := rate) rewards C_star C_h s hs i alpha halpha
    halphaT candidate q hq hqQ control0]
  apply MeasurableSet.iUnion
  intro cell
  exact measurableSet_downPrefixPositiveHashOneSourceEvent (rate := rate) rewards C_star C_h
    cell.1 cell.2.1 s hs (Nat.le_trans (Nat.le_of_lt halpha) cell.2.2) i alpha halpha
    cell.2.2 candidate q hq hqQ control0

theorem measurableSet_generatedDownFreshSourceEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaT : alpha < p.T) (candidate : Candidate p) (q : ℕ)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSet (generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s hs i
      alpha halpha halphaT candidate q) := by
  by_cases hq : q = 0
  · subst q
    exact measurableSet_generatedDownFreshSourceEvent_zero (rate := rate) rewards C_star C_h s hs
      i alpha halpha halphaT candidate control0
  · have hqPos : 1 ≤ q := by omega
    exact measurableSet_generatedDownFreshSourceEvent_of_pos (rate := rate) rewards C_star C_h s hs
      i alpha halpha halphaT candidate q hqPos hqQ control0

private theorem generatedDownQthAtSent_forces_previous_by_indicator_sum
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaT : alpha < p.T) (candidate : Candidate p) (q : ℕ)
    (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (x : ReferenceGeneratedDownQthCalendar.LaunchSource rate rewards C_star C_h s hs)
    (r : Fin p.T) (hsr : s ≤ r.val) (har : alpha ≤ r.val)
    (hlocal : generatedDownQthAtSent rewards C_star C_h s hs i alpha halpha halphaT
      candidate q hq hqQ x r hsr har) :
    generatedDownD rate rewards C_star C_h s (q - 1) hs i alpha halpha halphaT candidate x := by
  classical
  let Valid := {r : Fin p.T // alpha ≤ r.val}
  let detects (t : Valid) := generatedDownQthAtSent rewards C_star C_h s hs i alpha halpha
    halphaT candidate q hq hqQ x t.1 (by omega) t.2
  have hsumLe := generatedDownQthAtSent_indicator_sum_le_previous rewards C_star C_h s hs i alpha
    halpha halphaT candidate q hq hqQ x
  dsimp only at hsumLe
  let t : Valid := ⟨r, har⟩
  have ht : detects t := hlocal
  have hterm : (if detects t then (1 : ℝ) else 0) = 1 := ite_eq_left ht
  have hlower : 1 ≤ ∑ u : Valid, if detects u then (1 : ℝ) else 0 := by
    calc
      1 = (if detects t then (1 : ℝ) else 0) := hterm.symm
      _ ≤ ∑ u : Valid, if detects u then (1 : ℝ) else 0 :=
        Finset.single_le_sum (s := Finset.univ)
          (f := fun u : Valid => if detects u then (1 : ℝ) else 0)
          (fun u _ => by split_ifs <;> positivity) (Finset.mem_univ t)
  by_contra hprevious
  rw [ite_eq_right hprevious] at hsumLe
  have hfalse : (1 : ℝ) ≤ 0 := hlower.trans hsumLe
  norm_num at hfalse

private theorem freshPositiveUnion_subset_previous
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaT : alpha < p.T) (candidate : Candidate p) (q : ℕ)
    (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    freshPositiveUnion (rate := rate) rewards C_star C_h s hs i alpha halpha candidate q
        hq hqQ control0 ⊆
      generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s hs i alpha halpha
        halphaT candidate (q - 1) := by
  intro source hsource
  rcases Set.mem_iUnion.mp hsource with ⟨cell, hcell⟩
  obtain ⟨x, hx, hsent⟩ := freshPositiveCell_to_qthSent (rate := rate) rewards C_star C_h s hs
    i alpha halpha halphaT candidate q hq hqQ control0 cell.1 cell.2.1 cell.2.2 source hcell
  refine ⟨x, hx, ?_⟩
  exact generatedDownQthAtSent_forces_previous_by_indicator_sum rewards C_star C_h s hs i alpha
    halpha halphaT candidate q hq hqQ x cell.2.1
    (Nat.le_trans (Nat.le_of_lt halpha) cell.2.2) cell.2.2 hsent

private theorem freshPositiveUnion_measurable
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (candidate : Candidate p) (q : ℕ) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSet (freshPositiveUnion (rate := rate) rewards C_star C_h s hs i alpha halpha
      candidate q hq hqQ control0) := by
  apply MeasurableSet.iUnion
  intro cell
  exact measurableSet_downPrefixPositiveSourceEvent (rate := rate) rewards C_star C_h cell.1
    cell.2.1 s hs (Nat.le_trans (Nat.le_of_lt halpha) cell.2.2) i alpha halpha cell.2.2
    candidate q hq hqQ control0

private theorem freshPositiveUnion_pairwiseDisjoint
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaT : alpha < p.T) (candidate : Candidate p) (q : ℕ)
    (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Pairwise (Function.onFun Disjoint (fun cell : FreshCellIndex p alpha =>
      freshPositiveCell (rate := rate) rewards C_star C_h s hs i alpha halpha candidate q hq hqQ
        control0 cell)) := by
  classical
  intro a b hab
  change Disjoint (freshPositiveCell (rate := rate) rewards C_star C_h s hs i alpha halpha
      candidate q hq hqQ control0 a)
    (freshPositiveCell (rate := rate) rewards C_star C_h s hs i alpha halpha candidate q hq hqQ
      control0 b)
  rw [Set.disjoint_left]
  intro source ha hb
  obtain ⟨xa, hxa, hsentA⟩ := freshPositiveCell_to_qthSent (rate := rate) rewards C_star C_h
    s hs i alpha halpha halphaT candidate q hq hqQ control0 a.1 a.2.1 a.2.2 source ha
  obtain ⟨xb, hxb, hsentB⟩ := freshPositiveCell_to_qthSent (rate := rate) rewards C_star C_h
    s hs i alpha halpha halphaT candidate q hq hqQ control0 b.1 b.2.1 b.2.2 source hb
  have hlaunch : xa = xb := Subtype.ext (hxa.trans hxb.symm)
  cases hlaunch
  have hr := ReferenceGeneratedDownQthCalendar.generatedDownQthAtSent_unique rewards C_star C_h
    s hs i alpha halpha halphaT candidate q hq hqQ xa a.2.1 b.2.1
    (Nat.le_trans (Nat.le_of_lt halpha) a.2.2) a.2.2
    (Nat.le_trans (Nat.le_of_lt halpha) b.2.2) b.2.2 hsentA hsentB
  have haIndex : ActualInitializationPhysicalStep.selectedRowIndex p source = a.1 := by
    rcases ha with ⟨branch, _hbranch, hselector, _hmarker, _hcylinder, _test, _htest,
      _htime, _hsample, _hsent, _hnotSent⟩
    exact ((ReferenceSelectedAffinePairLaw.selector_eq_iff p a.1 a.2.1 (0, i) source).mp
      hselector).1
  have hbIndex : ActualInitializationPhysicalStep.selectedRowIndex p source = b.1 := by
    rcases hb with ⟨branch, _hbranch, hselector, _hmarker, _hcylinder, _test, _htest,
      _htime, _hsample, _hsent, _hnotSent⟩
    exact ((ReferenceSelectedAffinePairLaw.selector_eq_iff p b.1 b.2.1 (0, i) source).mp
      hselector).1
  have hab' : a = b := by
    apply Prod.ext
    · exact haIndex.symm.trans hbIndex
    · apply Subtype.ext
      exact hr
  exact hab hab'

private theorem freshHashOneUnion_pairwiseDisjoint
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaT : alpha < p.T) (candidate : Candidate p) (q : ℕ)
    (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Pairwise (Function.onFun Disjoint (fun cell : FreshCellIndex p alpha =>
      freshHashOneCell (rate := rate) rewards C_star C_h s hs i alpha halpha candidate q hq hqQ
        control0 cell)) := by
  have hpositive := freshPositiveUnion_pairwiseDisjoint (rate := rate) rewards C_star C_h s hs i
    alpha halpha halphaT candidate q hq hqQ control0
  intro a b hab
  change Disjoint (freshHashOneCell (rate := rate) rewards C_star C_h s hs i alpha halpha
      candidate q hq hqQ control0 a)
    (freshHashOneCell (rate := rate) rewards C_star C_h s hs i alpha halpha candidate q hq hqQ
      control0 b)
  rw [Set.disjoint_left]
  intro source ha hb
  have hdisj : Disjoint
      (freshPositiveCell (rate := rate) rewards C_star C_h s hs i alpha halpha candidate q hq hqQ
        control0 a)
      (freshPositiveCell (rate := rate) rewards C_star C_h s hs i alpha halpha candidate q hq hqQ
        control0 b) := hpositive hab
  exact (Set.disjoint_left.mp hdisj) ha.1 hb.1

theorem generatedDownFreshSourceEvent_recurrence
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaT : alpha < p.T) (candidate : Candidate p) (q : ℕ)
    (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s hs i alpha halpha
          halphaT candidate q) ≤
      ((1 : ℝ≥0∞) / 2) * BootstrapPrivateRoundStreams.sourceInputLaw p
        (generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s hs i alpha halpha
          halphaT candidate (q - 1)) := by
  classical
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  have hHashEq := freshHashOneUnion_eq_event (rate := rate) rewards C_star C_h s hs i alpha
    halpha halphaT candidate q hq hqQ control0
  have hHashDisjoint := freshHashOneUnion_pairwiseDisjoint (rate := rate) rewards C_star C_h s hs
    i alpha halpha halphaT candidate q hq hqQ control0
  have hHashMeas : ∀ cell : FreshCellIndex p alpha,
      MeasurableSet (freshHashOneCell (rate := rate) rewards C_star C_h s hs i alpha halpha
        candidate q hq hqQ control0 cell) := by
    intro cell
    exact measurableSet_downPrefixPositiveHashOneSourceEvent (rate := rate) rewards C_star C_h
      cell.1 cell.2.1 s hs (Nat.le_trans (Nat.le_of_lt halpha) cell.2.2) i alpha halpha
      cell.2.2 candidate q hq hqQ control0
  have hPositiveDisjoint := freshPositiveUnion_pairwiseDisjoint (rate := rate) rewards C_star C_h
    s hs i alpha halpha halphaT candidate q hq hqQ control0
  have hPositiveMeas : ∀ cell : FreshCellIndex p alpha,
      MeasurableSet (freshPositiveCell (rate := rate) rewards C_star C_h s hs i alpha halpha
        candidate q hq hqQ control0 cell) := by
    intro cell
    exact measurableSet_downPrefixPositiveSourceEvent (rate := rate) rewards C_star C_h cell.1
      cell.2.1 s hs (Nat.le_trans (Nat.le_of_lt halpha) cell.2.2) i alpha halpha cell.2.2
      candidate q hq hqQ control0
  have hPrevious : freshPositiveUnion (rate := rate) rewards C_star C_h s hs i alpha halpha
      candidate q hq hqQ control0 ⊆
      generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s hs i alpha halpha
        halphaT candidate (q - 1) :=
    freshPositiveUnion_subset_previous (rate := rate) rewards C_star C_h s hs i alpha halpha
      halphaT candidate q hq hqQ control0
  calc
    μ (generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s hs i alpha halpha
        halphaT candidate q) = μ (freshHashOneUnion (rate := rate) rewards C_star C_h s hs i
          alpha halpha candidate q hq hqQ control0) := by rw [← hHashEq]
    _ = ∑ cell : FreshCellIndex p alpha,
          μ (freshHashOneCell (rate := rate) rewards C_star C_h s hs i alpha halpha candidate q
            hq hqQ control0 cell) := by
      rw [freshHashOneUnion, measure_iUnion hHashDisjoint hHashMeas, tsum_fintype]
    _ = ∑ cell : FreshCellIndex p alpha,
          ((1 : ℝ≥0∞) / 2) * μ (freshPositiveCell (rate := rate) rewards C_star C_h s hs i
            alpha halpha candidate q hq hqQ control0 cell) := by
      apply Finset.sum_congr rfl
      intro cell _hcell
      exact downPrefixPositive_hash_half (rate := rate) rewards C_star C_h cell.1 cell.2.1 s hs
        (Nat.le_trans (Nat.le_of_lt halpha) cell.2.2) i alpha halpha cell.2.2 candidate q hq hqQ
        control0
    _ = ((1 : ℝ≥0∞) / 2) * μ (freshPositiveUnion (rate := rate) rewards C_star C_h s hs i
          alpha halpha candidate q hq hqQ control0) := by
      rw [← Finset.mul_sum, freshPositiveUnion,
        measure_iUnion hPositiveDisjoint hPositiveMeas,
        tsum_fintype]
    _ ≤ ((1 : ℝ≥0∞) / 2) * μ
        (generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s hs i alpha halpha
          halphaT candidate (q - 1)) := by
      gcongr

theorem generatedDownFreshSourceEvent_measure_le_geometric
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaT : alpha < p.T) (candidate : Candidate p) (q : ℕ)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s hs i alpha halpha
          halphaT candidate q) ≤
      ((1 : ℝ≥0∞) / 2) ^ q * BootstrapPrivateRoundStreams.sourceInputLaw p
        (generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s hs i alpha halpha
          halphaT candidate 0) := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hprev : q ≤ AffineBatchDecoder.quota p := by omega
      have hrec := generatedDownFreshSourceEvent_recurrence (rate := rate) rewards C_star C_h s hs
        i alpha halpha halphaT candidate (q + 1) (by omega) hqQ control0
      have hbound := ih hprev
      calc
        _ ≤ ((1 : ℝ≥0∞) / 2) * BootstrapPrivateRoundStreams.sourceInputLaw p
              (generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s hs i alpha
                halpha halphaT candidate q) := by simpa using hrec
        _ ≤ ((1 : ℝ≥0∞) / 2) *
              (((1 : ℝ≥0∞) / 2) ^ q * BootstrapPrivateRoundStreams.sourceInputLaw p
                (generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s hs i alpha
                  halpha halphaT candidate 0)) := by gcongr
        _ = ((1 : ℝ≥0∞) / 2) ^ (q + 1) * BootstrapPrivateRoundStreams.sourceInputLaw p
              (generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s hs i alpha
                halpha halphaT candidate 0) := by
          rw [pow_succ]
          ac_rfl

theorem generatedDownFreshSourceEvent_measure_le_geometric_unconditional
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaT : alpha < p.T) (candidate : Candidate p) (q : ℕ)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s hs i alpha halpha
          halphaT candidate q) ≤ ((1 : ℝ≥0∞) / 2) ^ q := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  have hreset : μ (generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s hs i alpha
      halpha halphaT candidate 0) ≤ 1 := by
    calc
      μ (generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s hs i alpha halpha
          halphaT candidate 0) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  calc
    μ (generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s hs i alpha halpha
        halphaT candidate q) ≤ ((1 : ℝ≥0∞) / 2) ^ q * μ
          (generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s hs i alpha halpha
            halphaT candidate 0) :=
      generatedDownFreshSourceEvent_measure_le_geometric (rate := rate) rewards C_star C_h s hs
        i alpha halpha halphaT candidate q hqQ control0
    _ ≤ ((1 : ℝ≥0∞) / 2) ^ q := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hreset (by positivity : (0 : ℝ≥0∞) ≤ ((1 : ℝ≥0∞) / 2) ^ q)

end Bandits.Support.ReferenceGeneratedDownFreshSourceTail

end
