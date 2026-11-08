/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedMixedDownAtBirthTail
public import Bandits.Support.ReferenceGeneratedDownAmbiguityMeasurability

import Lean.Elab.Tactic.Omega

/-!
# An inherited first-completion obstruction witness

On an actual first inherited completion whose receiver accepts a unique wrong
DOWN word, either the original source is in the mixed detector or an earlier
test in the same first cohort actually sent that word. The latter branch keeps
its physical sample, source-generated record, call, cut, and chronology; it is
not assigned a probability bound here.

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-148`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.AffineChannelLaw
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ReferenceGeneratedDownBatchCalendar
open Bandits.Support.ReferenceGeneratedInheritedDownCompletion
open Bandits.Support.ReferenceGeneratedInheritedDownCohort
open Bandits.Support.ReferenceGeneratedInheritedDownPrefixMarker
open Bandits.Support.ReferenceGeneratedPrelaunchDownCohort

namespace Bandits.Support.ReferenceGeneratedInheritedDownWrongCompletionWitness

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem record_eq_of_input_eq
    (left right : ReferenceFollowerDownDecoderReplay.Record p rate)
    (hinput : left.input = right.input) : left = right := by
  cases left with
  | mk input output houtput =>
      cases right with
      | mk input' output' houtput' =>
          cases hinput
          have hout : output = output' := houtput.trans houtput'.symm
          cases hout
          rfl

private theorem run_records_eq_ofFn_same_time
    (start count : ℕ) (span : start + count ≤ p.T)
    (input : ReferenceActiveHorizonMeasurability.ActiveRunInput
      (p := p) (rate := rate) start)
    (left right : ReferenceFollowerDownDecoderReplay.Record p rate)
    (hleft : left ∈ (ReferenceActiveHorizonMeasurability.runOfInput
      (p := p) (rate := rate) start count span input).records)
    (hright : right ∈ (ReferenceActiveHorizonMeasurability.runOfInput
      (p := p) (rate := rate) start count span input).records)
    (htime : left.input.time = right.input.time) : left = right := by
  have hrecords := ReferenceDownCompletedAmbiguityMeasurability.run_records_eq_ofFn
    start count span input
  rw [hrecords] at hleft hright
  obtain ⟨u, hu⟩ := List.mem_ofFn.mp hleft
  obtain ⟨v, hv⟩ := List.mem_ofFn.mp hright
  have hleftTime : left.input.time.val = start + u.val := by
    rw [← hu]
    simp [ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
      ReferenceActivePhysicalHorizon.roundInputAt]
  have hrightTime : right.input.time.val = start + v.val := by
    rw [← hv]
    simp [ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
      ReferenceActivePhysicalHorizon.roundInputAt]
  have huv : u = v := Fin.ext (by
    have hsum : start + u.val = start + v.val := by
      calc
        start + u.val = left.input.time.val := hleftTime.symm
        _ = right.input.time.val := congrArg Fin.val htime
        _ = start + v.val := hrightTime
    omega)
  subst v
  exact hu.symm.trans hv

private theorem record_down_selected_of_comparison
    (record : ReferenceFollowerDownDecoderReplay.Record p rate)
    (i : Fin (p.m - 1)) (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : (record.output.followers i).down = some cut)
    (hcomparison : cut.rawComparison.isSome = true) :
    ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time := by
  have hdiag : ReferenceActiveAffinePositiveTest.downDiagnosticCall
      (record.output.followers i) = true := by
    simp only [ReferenceActiveAffinePositiveTest.downDiagnosticCall, hcut, hcomparison]
  rw [← ReferenceDownCompletedAmbiguityMeasurability.record_preparationDiagnostics record i] at hdiag
  change ReferenceActiveAffinePositiveTest.downDiagnosticCall
    (ReferenceActivePhysicalStep.finishFollower record.output.preparation.coordinator.downView
      (record.output.preparation.followers.followers i)
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))) = true at hdiag
  rw [ReferenceActiveAffinePositiveTest.finishFollower_down_call,
    ReferenceActiveAffinePositiveTest.downCallGate_eq_prefix] at hdiag
  cases hc : (record.output.preparation.followers.followers i).configuration with
  | dagger => simp only [ReferenceActiveAffinePositiveTest.downPrefixGate, hc,
      Bool.false_eq_true] at hdiag
  | ordinary state memory =>
      simp only [ReferenceActiveAffinePositiveTest.downPrefixGate, hc,
        decide_eq_true_eq] at hdiag
      have hselected := hdiag.2.1
      rw [(record.output.preparation.follower_alignment i).1,
        (record.output.preparation.follower_alignment i).2.1,
        (record.output.preparation.follower_alignment i).2.2.1] at hselected
      exact hselected

private theorem reference_cut_expected_ne_raw
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hfalse : (ReferenceDownReception.referenceDownCut p view i row time observation
      rate state).rawComparison = some false)
    (hraw : (ReferenceDownReception.referenceDownCut p view i row time observation
      rate state).raw = some word) :
    (ReferenceDownReception.referenceDownCut p view i row time observation
      rate state).expectedWord ≠ some word := by
  have hcompared : (ReferenceDownReception.referenceDownCut p view i row time observation
      rate state).rawComparison ≠ none := by rw [hfalse]; decide
  have hrawStep := ReferenceDownReception.referenceDownCut_raw_eq_currentDecodeStep_of_compared
    view i row time observation rate state hcompared
  have hdecoded : (ActiveFollowerDownAcceptance.currentDecodeStep
      p i row time observation rate state).2 = some word := hrawStep.symm.trans hraw
  intro hexpected
  have hcall := ReferenceActiveAffinePositiveTest.referenceDownCut_has_call
    view i row time observation state
  rw [hfalse] at hcall
  have hgate : ReferenceActiveAffinePositiveTest.downReceiverGate i row time state :=
    of_decide_eq_true (by simpa using hcall)
  rcases hgate with ⟨hselected, hstatus, hregisters, hbatch, hbuffer⟩
  by_cases hmatches : (ActiveFollowerDownAcceptance.currentDecodeStep
      p i row time observation rate state).2 =
        ReferenceDownReception.expectedDownFlatWord view i row time
  · have htrue : (ReferenceDownReception.referenceDownCut p view i row time observation
        rate state).rawComparison = some true := by
      simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
        hregisters, hbatch, hbuffer, hmatches]
    rw [hfalse] at htrue
    cases htrue
  · have hexpected' : ReferenceDownReception.expectedDownFlatWord view i row time =
        some word := by
      simpa [ReferenceDownReception.referenceDownCut, hselected, hstatus,
        hregisters, hbatch, hbuffer, hmatches] using hexpected
    exact hmatches (hdecoded.trans hexpected'.symm)

/-- A first inherited completion with a physical wrong-acceptance cut has a
same-source obstruction witness. The second branch records an actual earlier
sent word in this first cohort, with its original call and source record. -/
def generatedSourceRecordAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (n : Fin (p.T - s)) : ReferenceFollowerDownDecoderReplay.Record p rate :=
  let input := ReferenceDownCompletedAmbiguityMeasurability.prefixInput s n.val (by omega)
    (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
      rate rewards C_star C_h s hs x)
  ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩

/-- `generatedSourceRecordAt` is the literal nth record of the existing full
source-generated run, as retained by its chronological record list. -/
theorem generatedSourceRecordAt_getElem?
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (n : Fin (p.T - s)) :
    (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
      rate rewards C_star C_h s hs x).records[n.val]? =
      some (generatedSourceRecordAt rate rewards C_star C_h s hs x n) := by
  have hrecords := ReferenceDownCompletedAmbiguityMeasurability.run_records_eq_ofFn
    s (p.T - s) (by omega)
    (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
      rate rewards C_star C_h s hs x)
  dsimp [ReferenceGeneratedDownBatchCalendar.generatedSourceRun]
  rw [hrecords]
  simp [generatedSourceRecordAt]

private theorem generatedSourceRun_eq_completeSuffixRecords_take
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs) :
    (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
      rate rewards C_star C_h s hs x).records =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate x.val rewards C_star C_h).take (p.T - s) := by
  have hfiberMem : x.val ∈
      ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
        (rate := rate) rewards C_star C_h s := by
    change _ ∧ _
    exact x.property
  let fiber : ReferenceGeneratedDownAmbiguityMeasurability.GeneratedLaunchFiber
      (rate := rate) rewards C_star C_h s := ⟨x.val, hfiberMem⟩
  have hseed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
    rate rewards C_star C_h s hs x
  have hpayload := ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
    rate x.val rewards C_star C_h
      (ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunch_ne_none
        (rate := rate) rewards C_star C_h s fiber)
  have hpayloadEq :
      ReferenceCompletePhysicalHistory.correctedLaunchPayload rate x.val rewards
        C_star C_h
        (ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunch_ne_none
          (rate := rate) rewards C_star C_h s fiber) =
      ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
        rate rewards C_star C_h s hs x :=
    Option.some.inj (hpayload.symm.trans hseed.1)
  have hinput :
      ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput
          (rate := rate) rewards C_star C_h s fiber =
        ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
          rate rewards C_star C_h s hs x := by
    apply Subtype.ext
    rw [ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput_val,
      ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput]
    simp [fiber, hpayloadEq]
  have hsuffix := ReferenceGeneratedDownAmbiguityMeasurability.generatedRun_records_eq_completeSuffixRecords_take
    (rate := rate) rewards C_star C_h s (p.T - s) (by omega) fiber
  rw [hinput] at hsuffix
  simpa [ReferenceGeneratedDownBatchCalendar.generatedSourceRun, fiber] using hsuffix

theorem generated_inherited_down_first_wrong_completion_witness
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s))
    (control0 : ContinuousLearningRows.TimeControl p)
    (hfirst :
      ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s hs i x).2 n) ∧
        ∀ l (hl : l < n.val),
          ¬ ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
            ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
              rate rewards C_star C_h s hs i x).2 ⟨l, lt_trans hl n.isLt⟩))
    (hwrong : ∃ cut,
      ((generatedSourceRecordAt rate rewards C_star C_h s hs x n).output.followers i).down = some cut ∧
        ReferenceDownReception.wrongUniqueAccepted cut) :
    let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
      rate rewards C_star C_h s hs x i).downBatch
    ∃ cut word alpha, ∃ hAlpha : alpha ≤ p.T,
      ((generatedSourceRecordAt rate rewards C_star C_h s hs x n).output.followers i).down = some cut ∧
      ReferenceDownReception.wrongUniqueAccepted cut ∧
      cut.raw = some word ∧ alpha ≤ s ∧
      ReferenceGeneratedPrelaunchDownPrefix.birthAt rate rewards C_star C_h
        x.val i alpha hAlpha B0.completed.length ∧
      ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownCohortBoundary
        rate rewards C_star C_h x.val i B0.completed.length = some alpha ∧
      (∀ test ∈ ReferenceGeneratedInheritedDownCohort.generatedInheritedDownFirstCohortTests
          rate rewards C_star C_h s hs i x,
        AffineChannelLaw.affineHash test.sample word = 1) ∧
      generatedSourceRecordAt rate rewards C_star C_h s hs x n ∈
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate x.val rewards C_star C_h).take (p.T - s) ∧
      (x.val ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha B0.completed.length hAlpha word control0
          (AffineBatchDecoder.quota p) ∨
        ∃ earlier : ReferenceGeneratedDownBatchCalendar.ExecutedTest p,
          earlier ∈ ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownPrefix
            (rate := rate) rewards C_star C_h s hs i x n.val ∧
          earlier.sent = some word ∧
          ∃ offset : Fin (p.T - s),
            ∃ record : ReferenceFollowerDownDecoderReplay.Record p rate,
              record ∈ (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
                rate rewards C_star C_h s hs x).records ∧
              record ∈ (ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate x.val rewards C_star C_h).take (p.T - s) ∧
              record.input.time.val = s + offset.val ∧
              s + offset.val < s + n.val ∧
              earlier.time = record.input.time ∧
              ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
                (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
                  record.input i) = some earlier ∧
              ∃ call cutEarlier,
                ReferenceFollowerDownDecoderReplay.actualDownCall i record = some call ∧
                (record.output.followers i).down = some cutEarlier ∧
                earlier.sample = ((x.val.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p x.val)).2
                  earlier.time).2 (0, i) ∧
                cutEarlier.expectedWord = some word) := by
  classical
  let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
    rate rewards C_star C_h s hs x i).downBatch
  let cohort := ReferenceGeneratedInheritedDownCohort.generatedInheritedDownFirstCohortTests
    rate rewards C_star C_h s hs i x
  let testPrefix := ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownPrefix
    (rate := rate) rewards C_star C_h s hs i x n.val
  let run := ReferenceGeneratedDownBatchCalendar.generatedSourceRun
    rate rewards C_star C_h s hs x
  have hrunSuffix := generatedSourceRun_eq_completeSuffixRecords_take
    rate rewards C_star C_h s hs x
  have hrecords := ReferenceDownCompletedAmbiguityMeasurability.run_records_eq_ofFn
    s (p.T - s) (by omega)
    (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
      rate rewards C_star C_h s hs x)
  let Rn : ReferenceFollowerDownDecoderReplay.Record p rate :=
    generatedSourceRecordAt rate rewards C_star C_h s hs x n
  have hRnInput : Rn.input =
      ReferenceDownCompletedAmbiguityMeasurability.prefixInput s n.val (by omega)
        (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
          rate rewards C_star C_h s hs x) := by
    rfl
  have hwrong' : ∃ cut, (Rn.output.followers i).down = some cut ∧
      ReferenceDownReception.wrongUniqueAccepted cut := by
    exact hwrong
  obtain ⟨wrongCut, hwrongCut, hwrongFlag⟩ := hwrong'
  obtain ⟨bankRecord, callCode, loggedCode, cutCode, logged, bankCut,
      hbankInput, hcallObservation, hactualCall, hlogged, hbankCut,
      hloggedCode, hcutCode, hcallTime, hquota, hcomparison, hpositive,
      hrawBatch, hdecoded, hpending, hcompleted, hbankLength, hjoin⟩ :=
    ReferenceGeneratedInheritedDownCohort.generated_inherited_down_cohort_first_completion_bank
      rewards C_star C_h s hs x i n.val n.isLt hfirst
  have hrecordInput : bankRecord.input = Rn.input := by
    rw [hbankInput, hRnInput]
  have hrecordEq : bankRecord = Rn := record_eq_of_input_eq bankRecord Rn hrecordInput
  have hwrongCutEq : bankCut = wrongCut := by
    have hleft := hbankCut
    have hright := hwrongCut
    rw [hrecordEq] at hleft
    exact Option.some.inj (hleft.symm.trans hright)
  subst wrongCut
  have hwrongBank : ReferenceDownReception.wrongUniqueAccepted bankCut := hwrongFlag
  have hword : ∃ word, bankCut.raw = some word := by
    cases hraw : bankCut.raw with
    | none => exact False.elim (hwrongBank.2.1 hraw)
    | some word => exact ⟨word, rfl⟩
  obtain ⟨word, hrawWord⟩ := hword

  have hfirstIff := (ReferenceGeneratedInheritedDownFirstCompletion.generated_inherited_down_first_completion_iff
    rewards C_star C_h s hs x i n.val n.isLt).mp hfirst
  have hOld := ReferenceGeneratedInheritedDownCohort.generated_inherited_down_old_pending
    rewards C_star C_h s hs x i
  have hprefixLength : testPrefix.length = AffineBatchDecoder.quota p - 1 := by
    have hOldCount :
        (ReferenceGeneratedInheritedDownCohort.generatedInheritedDownOldFirstTests
          rate rewards C_star C_h s hs x i).length = B0.pending.length := hOld.2
    have hPendingCount : logged.downBatch.pending.length = B0.pending.length +
        (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
          rate rewards C_star C_h s hs i x n.val).length := by
      rw [hpending]
      simp only [List.length_append, List.length_map]
      dsimp [B0]
    dsimp [testPrefix, ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownPrefix]
    simp only [List.length_append]
    rw [hOldCount]
    omega

  have hhistory := ReferenceGeneratedPrelaunchDownLaunchCohortHistory.source_launch_down_historical_cohort
    rate rewards C_star C_h x.val i
  have hcross := x.property.1
  have hhistoryForStop := hhistory.2 hcross
  have hstopActual : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
          rate rewards C_star C_h x.val)).completed < p.T := by
    change ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate)).completed < p.T
    rw [x.property.2]
    exact hs
  have hhistoryLaunch := hhistoryForStop.1 hstopActual
  obtain ⟨launchSource, hsourceEq, _hcorrected, _hseedFollower, _hdownSeed,
    _hfailure, _hactivationAtStart, _hpendingLt, _hpending, hlaunchTail⟩ := hhistoryLaunch
  obtain ⟨activation, _hactivation, _hcase, _hactualCohort, _hsourceTests,
    hbirthTail⟩ := hlaunchTail
  obtain ⟨alpha, hAlpha, hAlphaS, _hbankBirth, hbirth, _hunique,
      hhistoryBoundary, _hinterval⟩ :=
    hbirthTail
  have hAlphaSOriginal : alpha ≤ s := by
    rw [← x.property.2]
    exact hAlphaS
  have hsourceEqX : launchSource.val = x.val := by simpa using hsourceEq
  have hhistoryBoundary' :
      ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownCohortBoundary
        rate rewards C_star C_h x.val i B0.completed.length = some alpha := by
    simpa [B0, ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower,
      ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput,
      hsourceEqX] using hhistoryBoundary
  have hbirth' : ReferenceGeneratedPrelaunchDownPrefix.birthAt rate rewards C_star C_h
      x.val i alpha hAlpha B0.completed.length := by
    simpa [B0, ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower,
      ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput,
      hsourceEqX] using hbirth
  obtain ⟨alpha', hAlpha', hboundaryOrigin, htestOrigin⟩ :=
    ReferenceGeneratedInheritedDownCohort.generated_inherited_down_cohort_test_origin
      rewards C_star C_h s hs x i
  have hAlphaEq : alpha' = alpha := by
    exact Option.some.inj (hboundaryOrigin.symm.trans hhistoryBoundary')
  subst alpha'

  have hcohortLength : cohort.length = AffineBatchDecoder.quota p := by
    have hlen := hbankLength
    rw [hjoin] at hlen
    simpa only [List.length_map] using hlen
  have hcurrentIsSome := hfirstIff.2
  have hcurrent : ∃ test,
      ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h s hs i x).2 n) = some test := by
    cases htest : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h s hs i x).2 n) with
    | none => simp [htest] at hcurrentIsSome
    | some test => exact ⟨test, rfl⟩
  obtain ⟨currentTest, hcurrentTest⟩ := hcurrent
  have hprefixCohort : testPrefix ++ [currentTest] = cohort := by
    have htake := ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownPrefix_current_take
      rewards C_star C_h s hs i x n.val (AffineBatchDecoder.quota p)
      (by omega) (by omega) (le_rfl) hprefixLength currentTest hcurrentTest
    have htakeCohort : cohort.take (AffineBatchDecoder.quota p) = cohort :=
      List.take_of_length_le (by omega)
    rw [htakeCohort] at htake
    exact htake
  have hcurrentMem : currentTest ∈ cohort := by
    rw [← hprefixCohort]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hhashAll : ∀ test ∈ cohort,
      AffineChannelLaw.affineHash test.sample word = 1 := by
    intro test htest
    have hentryMem : ReferenceGeneratedPrelaunchDownCohort.testEntry test ∈
        logged.downBatch.pending ++ [⟨bankRecord.input.time,
          (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample⟩] := by
      rw [hjoin]
      exact List.mem_map.mpr ⟨test, htest, rfl⟩
    have hequation := ((AffineBatchDecoder.batchOutput_eq_some_iff _ word).mp
      (hrawBatch.symm.trans hrawWord)).1 _ hentryMem
    exact (AffineBatchDecoder.equation_iff_affineHash test.sample word).mp hequation

  have hprefixCurrentTime : currentTest.time.val = s + n.val := by
    exact ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownCurrentTest_time
      rewards C_star C_h s hs i x n currentTest hcurrentTest
  have hcurrentOrigin := htestOrigin currentTest hcurrentMem
  have hcurrentSample : currentTest.sample = ((x.val.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p x.val)).2
        currentTest.time).2 (0, i) := hcurrentOrigin.2.1
  have hcurrentTimeFin : currentTest.time =
      (⟨s + n.val, by omega⟩ : Fin p.T) := Fin.ext hprefixCurrentTime
  have hcurrentNew := hcurrentOrigin.2.2
  have hcurrentOldImpossible : ¬ (∃ hOld : currentTest ∈
      ReferenceGeneratedInheritedDownCohort.generatedInheritedDownOldFirstTests
        rate rewards C_star C_h s hs x i, currentTest.time.val < s ∧
        currentTest.sent = none) := by
    rintro ⟨_, hbefore, _⟩
    rw [hprefixCurrentTime] at hbefore
    omega
  have hnewCurrentMember : currentTest ∈
      ReferenceGeneratedInheritedDownCohort.generatedInheritedDownNewFirstTests
        rate rewards C_star C_h s hs i x := by
    rcases hcurrentNew with holdCurrent | hnewCurrent
    · exact False.elim (hcurrentOldImpossible holdCurrent)
    · exact hnewCurrent.1
  obtain ⟨kCurrent, currentRecord, hcurrentRecord, hcurrentRecordTime,
      hcurrentRecordTimeEq, _hcurrentSamplePhysical, _hcurrentExecuted,
      currentCall, currentCut, hcurrentCall, hcurrentCut, _hcurrentCallTime,
      _hcurrentCallSample, hcurrentSentExpected, _hcurrentExpectedDownSent,
      hcurrentPositive, hcurrentComparison⟩ :=
    ReferenceGeneratedInheritedDownCohort.generated_inherited_down_new_test_physical
      rewards C_star C_h s hs x i currentTest hnewCurrentMember
  have hbankEqRn : bankRecord = Rn := by
    apply record_eq_of_input_eq
    exact hbankInput.trans hRnInput.symm
  have hbankRecord : bankRecord ∈ run.records := by
    change bankRecord ∈ (ReferenceActiveHorizonMeasurability.runOfInput
      (p := p) (rate := rate) s (p.T - s) (by omega)
      (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
        rate rewards C_star C_h s hs x)).records
    rw [hrecords, hbankEqRn]
    exact List.mem_ofFn.mpr ⟨n, by simp [Rn, generatedSourceRecordAt]⟩
  have hbankSuffix : bankRecord ∈
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate x.val rewards C_star C_h).take (p.T - s) := by
    rw [← hrunSuffix]
    exact hbankRecord
  have hsourceRecordSuffix : generatedSourceRecordAt
      rate rewards C_star C_h s hs x n ∈
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate x.val rewards C_star C_h).take (p.T - s) := by
    have hRnSuffix : Rn ∈
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate x.val rewards C_star C_h).take (p.T - s) := by
      rw [← hbankEqRn]
      exact hbankSuffix
    simpa [Rn] using hRnSuffix
  have htimeCurrentBank : currentRecord.input.time = bankRecord.input.time := by
    apply Fin.ext
    calc
      currentRecord.input.time.val = currentTest.time.val :=
        congrArg Fin.val hcurrentRecordTimeEq.symm
      _ = s + n.val := hprefixCurrentTime
      _ = bankRecord.input.time.val := by
        rw [hbankInput]
        simp [ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
          ReferenceActivePhysicalHorizon.roundInputAt,
          ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput]
  have hcurrentRecordEq : currentRecord = bankRecord :=
    run_records_eq_ofFn_same_time s (p.T - s) (by omega)
      (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
        rate rewards C_star C_h s hs x)
      currentRecord bankRecord
      (by simpa [run, ReferenceGeneratedDownBatchCalendar.generatedSourceRun] using hcurrentRecord)
      (by simpa [run, ReferenceGeneratedDownBatchCalendar.generatedSourceRun] using hbankRecord)
      htimeCurrentBank
  have hcurrentCutBank : currentCut = bankCut := by
    have hcurrentCut' := hcurrentCut
    rw [hcurrentRecordEq] at hcurrentCut'
    exact Option.some.inj (hcurrentCut'.symm.trans hbankCut)
  have hcurrentExpectedMismatch : currentTest.sent ≠ some word := by
    intro hsent
    have hexpected : currentCut.expectedWord = some word :=
      hcurrentSentExpected.symm.trans hsent
    have hexpectedBank : bankCut.expectedWord = some word := by
      rw [← hcurrentCutBank]
      exact hexpected
    have hcutActual := ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
      bankRecord i logged bankCut hlogged hbankCut
    have hfalse := hwrongBank.1
    have hraw := hrawWord
    have hnotExpected := reference_cut_expected_ne_raw (p := p) (rate := rate)
      bankRecord.output.preparation.coordinator.downView i bankRecord.input.row
      bankRecord.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation
        bankRecord i) logged word
      (by rw [← hcutActual]; exact hfalse)
      (by rw [← hcutActual]; exact hraw)
    exact hnotExpected (by rw [← hcutActual]; exact hexpectedBank)

  by_cases hNoSent : ∀ test ∈ testPrefix, test.sent ≠ some word
  · have hhashPrefix : ∀ test ∈ testPrefix,
        AffineChannelLaw.affineHash test.sample word = 1 := by
      intro test htest
      exact hhashAll test (by rw [← hprefixCohort]; exact List.mem_append_left _ htest)
    have hselectorCall := record_down_selected_of_comparison
      bankRecord i bankCut hbankCut hcomparison
    have hselector : ReferenceSelectedAffinePairLaw.selector p currentTest.time x.val =
        (ActualInitializationPhysicalStep.selectedRowIndex p x.val,
          some ((0, i) : ContinuousLearningRows.Channel p)) := by
      have hrow : bankRecord.input.row =
          x.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x.val) := by
        rw [hbankInput]
        rfl
      have htime : currentTest.time = bankRecord.input.time := by
        apply Fin.ext
        rw [hprefixCurrentTime, hbankInput]
        simp [ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
          ReferenceActivePhysicalHorizon.roundInputAt,
          ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput]
      apply (ReferenceSelectedAffinePairLaw.selector_eq_iff p
        (ActualInitializationPhysicalStep.selectedRowIndex p x.val)
        currentTest.time (0, i) x.val).mpr
      refine ⟨rfl, ?_⟩
      rw [htime, ← hrow]
      simp only [ReferenceSelectedAffinePairLaw.selectedChannel,
        ReferenceSelectedAffinePairLaw.channelFromDraws,
        hselectorCall.1, ite_true, hselectorCall.2]
    have hstopAtTest : s + n.val < p.T := by
      calc
        s + n.val < s + (p.T - s) := Nat.add_lt_add_left n.isLt s
        _ = p.T := by
          rw [Nat.add_comm]
          exact Nat.sub_add_cancel (Nat.le_of_lt hs)
    let delta : ReferenceGeneratedInheritedDownPostlaunchOccurrence.Lambda p alpha :=
      ⟨(ActualInitializationPhysicalStep.selectedRowIndex p x.val,
        (⟨s, hs⟩ : Fin p.T),
        (⟨s + n.val, hstopAtTest⟩ : Fin p.T)),
        ⟨hAlphaSOriginal, Nat.le_add_right s n.val⟩⟩
    have hoccurrence : x.val ∈
        ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence
          (rate := rate) rewards C_star C_h i alpha B0.completed.length
          (AffineBatchDecoder.quota p) hAlpha word
          (by omega) (le_rfl) control0 delta := by
      refine ⟨?_, x, rfl, hAlphaSOriginal, rfl, hhistoryBoundary',
        ?_, ?_, ⟨currentTest, ?_, hcurrentExpectedMismatch⟩⟩
      · simpa [delta, hcurrentTimeFin] using hselector
      · simpa [delta, testPrefix,
          ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownPrefix,
          Nat.add_sub_cancel_left]
          using hprefixLength
      · intro test hmem
        have hmemPrefix : test ∈ testPrefix := by
          simpa [delta, testPrefix,
            ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownPrefix,
            Nat.add_sub_cancel_left] using hmem
        exact ⟨hNoSent test hmemPrefix, hhashPrefix test hmemPrefix⟩
      · simpa [delta, Nat.add_sub_cancel_left] using hcurrentTest
    have hhashed : x.val ∈
        ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchHashedOccurrence
          (rate := rate) rewards C_star C_h i alpha B0.completed.length
          (AffineBatchDecoder.quota p) hAlpha word
          (by omega) (le_rfl) control0 delta := by
      refine ⟨hoccurrence, ?_⟩
      change AffineChannelLaw.affineHash
        (((x.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x.val)).2
          (⟨s + n.val, by omega⟩ : Fin p.T)).2 (0, i)) word = 1
      rw [← hcurrentTimeFin, ← hcurrentSample]
      exact hhashAll currentTest hcurrentMem
    have hdet : x.val ∈
        ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha B0.completed.length hAlpha word control0
          (AffineBatchDecoder.quota p) := by
      rw [ReferenceGeneratedMixedDownPredecessor.mixedDownDetector_positive
        rate rewards C_star C_h i alpha B0.completed.length (AffineBatchDecoder.quota p)
        hAlpha word (by omega) (le_rfl) control0]
      apply Or.inr
      exact Set.mem_iUnion.mpr ⟨delta, hhashed⟩
    exact ⟨bankCut, word, alpha, hAlpha, hwrongCut, hwrongBank, hrawWord, hAlphaSOriginal,
      hbirth', hhistoryBoundary', hhashAll, hsourceRecordSuffix, Or.inl hdet⟩
  · push Not at hNoSent
    obtain ⟨earlier, hearlierPrefix, hearlierSent⟩ := hNoSent
    have hearlierCohort : earlier ∈ cohort := by
      rw [← hprefixCohort]
      exact List.mem_append_left _ hearlierPrefix
    have hearlierOrigin := htestOrigin earlier hearlierCohort
    rcases hearlierOrigin.2.2 with hOld | hNew
    · rcases hOld with ⟨_, _, hsentNone⟩
      rw [hsentNone] at hearlierSent
      cases hearlierSent
    · rcases hNew with ⟨hnew, _⟩
      obtain ⟨offset, earlierRecord, hrecord, htime, htestTime,
        _hearlierSamplePhysical, htestRound, call, cutEarlier,
        hcall, hcut, _hcallTime, _hcallSample, htestSent,
        _hcutExpectedDownSent, hpositive, _hcomparison⟩ :=
        ReferenceGeneratedInheritedDownCohort.generated_inherited_down_new_test_physical
          rewards C_star C_h s hs x i earlier hnew
      have hpair := (ReferenceGeneratedInheritedDownCohort.generated_inherited_down_cohort_pairwise
        rewards C_star C_h s hs x i).1
      have hpairAppend : (testPrefix ++ [currentTest]).Pairwise
          (fun a b => a.time.val < b.time.val) := by
        simpa [hprefixCohort, cohort] using hpair
      have hltTime : earlier.time.val < currentTest.time.val := by
        have hcross := (List.pairwise_append.mp hpairAppend).2.2 earlier hearlierPrefix
          currentTest (List.mem_singleton_self _)
        exact hcross
      have hEarlierSuffix : earlierRecord ∈
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate x.val rewards C_star C_h).take (p.T - s) := by
        rw [← hrunSuffix]
        exact hrecord
      refine ⟨bankCut, word, alpha, hAlpha, ?_, hwrongBank, hrawWord, hAlphaSOriginal,
        hbirth', hhistoryBoundary', hhashAll, hsourceRecordSuffix, Or.inr ?_⟩
      · exact hwrongCut
      · refine ⟨earlier, hearlierPrefix, hearlierSent, offset, earlierRecord,
          hrecord, hEarlierSuffix, htime, ?_, htestTime, htestRound, ?_⟩
        · rw [hprefixCurrentTime] at hltTime
          rw [htestTime, htime] at hltTime
          omega
        · refine ⟨call, cutEarlier, hcall, hcut, ?_, ?_⟩
          · exact hearlierOrigin.2.1
          · exact htestSent.symm.trans hearlierSent


end Bandits.Support.ReferenceGeneratedInheritedDownWrongCompletionWitness

end
