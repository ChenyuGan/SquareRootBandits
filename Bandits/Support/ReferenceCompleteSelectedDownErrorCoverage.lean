/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteMatchingDownSenderChronology
public import Bandits.Support.ReferenceStrictPastFailureCalendarAlignment

import Lean.Elab.Tactic.Omega

/-!
# Selected DOWN wrong-diagnostic cohort coverage

On the actual selected branch of a wrong accepted DOWN diagnostic in the
original complete suffix, the exact inherited or fresh DOWN cohort contains
the source input. No stopped-calendar equality or probability estimate is
claimed here.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceGeneratedDownBatchCalendar
open Bandits.Support.ReferenceGeneratedDownCohortFiniteUnion
open Bandits.Support.ReferenceDownCompletedAmbiguityMeasurability

namespace Bandits.Support.ReferenceCompleteSelectedDownErrorCoverage

variable {p : ConstructorDimensions.Parameters}

private theorem wrongDownCut_completedBatchAtRound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceFollowerDownDecoderReplay.Record p rate)
    (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : (record.output.followers i).down = some cut)
    (hwrong : ReferenceDownReception.wrongUniqueAccepted cut) :
    completedBatchAtRound rate (roundDownObservation record.input i) := by
  classical
  obtain ⟨_choice, _memory, logged, _hchoice, _hstatus, _hlocal, hlogged, _hsource⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice record i cut hcut
  have hcutActual := record_downCut_eq_actual record i logged cut hlogged hcut
  obtain ⟨word, hraw⟩ : ∃ word, cut.raw = some word := by
    cases hword : cut.raw with
    | none => exact False.elim (hwrong.2.1 hword)
    | some word => exact ⟨word, rfl⟩
  have hfalse :
      (ReferenceDownReception.referenceDownCut p
        record.output.preparation.coordinator.downView i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged).rawComparison =
        some false := by
    simpa only [hcutActual] using hwrong.1
  have hcompared :
      (ReferenceDownReception.referenceDownCut p
        record.output.preparation.coordinator.downView i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged).rawComparison ≠
        none := by
    rw [hfalse]
    decide
  have hrawActual := ReferenceDownReception.referenceDownCut_raw_eq_currentDecodeStep_of_compared
    record.output.preparation.coordinator.downView i record.input.row record.input.time
    (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged hcompared
  have hrawActual' :
      (ReferenceDownReception.referenceDownCut p
        record.output.preparation.coordinator.downView i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged).raw =
        some word := by
    simpa only [hcutActual] using hraw
  have hstep :
      (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged).2 =
        some word := hrawActual.symm.trans hrawActual'
  have hquota : AffineBatchDecoder.quota p ≤
      (logged.downBatch.pending ++ AffineBatchDecoder.positiveAt p
        (ActiveFollowerDownAcceptance.currentInputExtension p
          (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged))
        record.input.time).length := by
    have houtput : AffineBatchDecoder.stepOutput p
        (ActiveFollowerDownAcceptance.currentInputExtension p
          (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged))
        logged.downBatch record.input.time = some word := by
      simpa only [ActiveFollowerDownAcceptance.currentDecodeStep,
        AffineBatchDecoder.decodeStep] using hstep
    exact (AffineBatchDecoder.stepOutput_eq_some_iff p
      (ActiveFollowerDownAcceptance.currentInputExtension p
        (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged))
      logged.downBatch record.input.time word).mp houtput |>.1
  apply (ReferenceGeneratedDownResetCompletionCensus.completedBatchAtRound_iff_executed_quota
    record i).2
  exact ⟨logged, cut, hlogged, hcut, by rw [hwrong.1]; rfl, hquota⟩

private theorem completeSuffixRecord_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[j.val].input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + j.val := by
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate source rewards C_star C_h
  have hlt : j.val < p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h := by
    rw [← ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    exact j.isLt
  have hget := congrArg (fun values : List ℕ => values[j.val]?) htimes
  rw [List.getElem?_map, List.getElem?_eq_getElem j.isLt, Option.map_some,
    ReferenceActivePhysicalHorizon.calendar, List.getElem?_range' hlt, Nat.one_mul] at hget
  exact Option.some.inj hget

private theorem completeSuffixRecord_eq_generatedSourceRecordAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (j : Fin (p.T - s)) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate x.val rewards C_star C_h)[j.val]'(by
        have hstart : ReferenceCompletePhysicalHistory.physicalStart
            rate x.val rewards C_star C_h = s := x.property.2
        rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length, hstart]
        exact j.isLt) =
      ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x j := by
  let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate x.val rewards C_star C_h
  let generated := ReferenceGeneratedDownBatchCalendar.generatedSourceRun
    rate rewards C_star C_h s hs x
  have hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate x.val rewards C_star C_h = s := x.property.2
  have hrecords : records = generated.records := by
    have hseed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
      rate rewards C_star C_h s hs x
    have hfull := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate x.val rewards C_star C_h
      (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed rate rewards C_star C_h s hs x)
      hseed.1
    have hphysical :
        ReferenceCompletePhysicalHistory.completeSuffixRecords rate x.val rewards C_star C_h =
          (ReferenceActivePhysicalHorizon.run
            (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed rate rewards C_star C_h s hs x)
            x.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s
            (p.T - s) (by omega) hseed.2.1).records := by
      change _ = (ReferenceActivePhysicalHorizon.run
        (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed rate rewards C_star C_h s hs x)
        x.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s
        (p.T - s) (by omega) hseed.2.1).records
      simpa only [hstart] using hfull
    simpa only [records, generated,
      ReferenceGeneratedDownBatchCalendar.generatedSourceRun,
      ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput,
      ReferenceActiveHorizonMeasurability.runOfInput] using hphysical
  have hlen : generated.records.length = p.T - s := by
    rw [← hrecords]
    calc
      records.length = p.T - ReferenceCompletePhysicalHistory.physicalStart
          rate x.val rewards C_star C_h :=
        ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate x.val rewards C_star C_h
      _ = p.T - s := by rw [hstart]
  have hindex : j.val < generated.records.length := by
    rw [hlen]
    exact j.isLt
  have hrecord? :=
    ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt_getElem?
      rate rewards C_star C_h s hs x j
  have hrecord : generated.records[j.val] =
      ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x j := by
    rw [List.getElem?_eq_getElem hindex] at hrecord?
    exact Option.some.inj hrecord?
  have hfullIndex : j.val < records.length := by
    simpa only [records, ReferenceCompletePhysicalHistory.completeSuffixRecords_length, hstart]
      using j.isLt
  exact (List.getElem_of_eq hrecords hfullIndex).trans hrecord

/-- Every actual selected wrong DOWN diagnostic on a record of the original
complete physical suffix belongs to the existing finite mixed-or-fresh DOWN
cohort union. The sole record-level premises are the actual cut, its wrong
accepted diagnostic, and the same record's actual coordinator selection. -/
theorem selected_wrong_down_diagnostic_mem_downCohortUnion
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h
    ∀ k : Fin R.length,
      let r := R[k.val]
      ∀ (i : Fin (p.m - 1)) (cut : ReferenceDownReception.ReferenceDownCutOutput p rate),
        (r.output.followers i).down = some cut →
        ReferenceDownReception.wrongUniqueAccepted cut →
        ∀ v : ReferenceActivePhysicalStep.Selection r.input,
          r.output.preparation.coordinator.selection = some v →
          z ∈ ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
            rate rewards C_star C_h control0 (AffineBatchDecoder.quota p) := by
  classical
  dsimp only
  intro k
  let L := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hlen : L.length = p.T - s :=
    ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  have hkval : k.val < p.T - s := by
    have hk : k.val < L.length := by simpa only [L] using k.isLt
    simpa only [hlen] using hk
  have hs : s < p.T := by
    omega
  have hlaunchNe : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h ≠ none := by
    intro hnone
    have hstart := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
      rate z rewards C_star C_h hnone
    dsimp [s] at hs
    omega
  have hlaunchSome :
      (ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h).isSome =
        true := by
    cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h with
    | none => exact False.elim (hlaunchNe hlaunch)
    | some active => rfl
  have hcross := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate z rewards C_star C_h).mp hlaunchSome
  let x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs :=
    ⟨z, hcross, rfl⟩
  let n : Fin (p.T - s) := ⟨k.val, hkval⟩
  let current := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
    rate rewards C_star C_h s hs x n
  have hcurrent : L[k.val] = current := by
    have hEq := completeSuffixRecord_eq_generatedSourceRecordAt
      rate rewards C_star C_h s hs x n
    simpa only [L, n, current] using hEq
  intro i cut hcut hwrong v hv
  have hcutCurrent : (current.output.followers i).down = some cut := by
    rw [← hcurrent]
    exact hcut
  have hnoSent :=
    ReferenceCompleteMatchingDownSenderChronology.complete_selected_wrong_down_not_sent_before
      rate rewards C_star C_h z k i cut hcut hwrong v hv
  have hrawSome : ∃ word, cut.raw = some word := by
    cases hraw : cut.raw with
    | none => exact False.elim (hwrong.2.1 hraw)
    | some word => exact ⟨word, rfl⟩
  obtain ⟨word, hraw⟩ := hrawSome
  have hcompleteCurrent := wrongDownCut_completedBatchAtRound rate current i cut
    hcutCurrent hwrong
  have hcomplete : ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s hs i x).2 n) := by
    simpa only [ReferenceGeneratedDownBatchCalendar.generatedSourceObservation,
      ReferenceDownCompletedAmbiguityMeasurability.runDownObservation,
      ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt,
      current] using hcompleteCurrent
  have hinterval :=
    ReferenceGeneratedDownLaterCompletionDetector.generated_down_later_raw_detector_of_not_sent
      rate rewards C_star C_h s hs x i n cut word control0 hcomplete hcutCurrent hraw
  dsimp only at hinterval
  rcases hinterval with hfirst | ⟨m, hmn, hcompm, hgreatest, hnoMiddle, hunique, hlater⟩
  · have hfirst' :
        ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
            ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
              rate rewards C_star C_h s hs i x).2 n) ∧
          ∀ l (hl : l < n.val),
            ¬ ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
              ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
                rate rewards C_star C_h s hs i x).2
                ⟨l, Nat.lt_trans hl n.isLt⟩) := by
      refine ⟨hcomplete, ?_⟩
      intro l hl
      exact hfirst ⟨l, Nat.lt_trans hl n.isLt⟩ (Fin.lt_def.mpr hl)
    have hwitness := ReferenceGeneratedInheritedDownWrongCompletionWitness.generated_inherited_down_first_wrong_completion_witness
          rate rewards C_star C_h s hs x i n control0 hfirst' ⟨cut, hcutCurrent, hwrong⟩
    dsimp only at hwitness
    rcases hwitness with
      ⟨witnessCut, witnessWord, alpha, hAlpha, hcutWitness, _hwrongWitness,
        hrawWitness, hAlphaS, hbirth, _hboundary, _hhash, _hsuffixRecord, hbranch⟩
    have hcutEq : witnessCut = cut :=
      Option.some.inj (hcutWitness.symm.trans hcutCurrent)
    have hwordEq : witnessWord = word := by
      rw [hcutEq] at hrawWitness
      exact Option.some.inj (hrawWitness.symm.trans hraw)
    subst witnessWord
    rcases hbranch with hmixed | hearlier
    · have hbound := ReferenceGeneratedDownCohortFiniteUnion.birthAt_ordinal_le
        rate rewards C_star C_h i alpha
        (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
          rate rewards C_star C_h s hs x i).downBatch.completed.length
        hAlpha z hbirth
      let kBirth : Fin (alpha + 1) := ⟨
        (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
          rate rewards C_star C_h s hs x i).downBatch.completed.length,
        Nat.lt_succ_of_le hbound⟩
      change z ∈ ⋃ i' : Fin (p.m - 1), ⋃ alpha' : Fin p.T, ⋃ w,
        (⋃ j : Fin (alpha'.val + 1),
          {source | source ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
            rate rewards C_star C_h i' alpha'.val j.val alpha'.isLt.le w control0
              (AffineBatchDecoder.quota p)}) ∪
        ReferenceGeneratedDownFreshAllLaunchTail.generatedDownFreshAllLaunchSourceEvent
          (rate := rate) rewards C_star C_h i' alpha'.val alpha'.isLt w
            (AffineBatchDecoder.quota p)
      simp only [Set.mem_iUnion]
      have hAlphaT : alpha < p.T := lt_of_le_of_lt hAlphaS hs
      refine ⟨i, ⟨⟨alpha, hAlphaT⟩, ⟨word, ?_⟩⟩⟩
      apply Or.inl
      apply Set.mem_iUnion.mpr
      refine ⟨kBirth, ?_⟩
      exact hmixed
    · rcases hearlier with
        ⟨earlier, hearlier, hearlierSent, offset, earlierRecord, hrunMem,
          hsuffixMem, htime, hbeforeCurrent, htimeEq, hexecuted, hcallCut⟩
      obtain ⟨j, hjTake, hrecordEq⟩ :=
        List.mem_take_iff_getElem.mp hsuffixMem
      have hjLength : j < L.length :=
        lt_of_lt_of_le (Nat.lt_of_succ_le hjTake) (Nat.min_le_right _ _)
      let jFin : Fin L.length := ⟨j, hjLength⟩
      have htimeIndex := completeSuffixRecord_time rate rewards C_star C_h z jFin
      have hjEq : j = offset := by
        have htime' : s + j = s + offset := by
          calc
            s + j = (L[j]).input.time.val := by simpa [s] using htimeIndex.symm
            _ = earlierRecord.input.time.val :=
              congrArg (fun record : ReferenceCompletePhysicalHistory.RoundRecord p rate =>
                record.input.time.val) hrecordEq
            _ = s + offset := by simpa [s] using htime
        omega
      have hjBefore : j ≤ k.val := by
        have : offset < n.val := by omega
        rw [hjEq]
        simpa [n] using Nat.le_of_lt this
      rcases hcallCut with
        ⟨_call, cutEarlier, _hactual, hcutEarlier, _hsample, hsentExpected⟩
      have hOldCut : ((L[j]).output.followers i).down = some cutEarlier := by
        rw [hrecordEq]
        exact hcutEarlier
      have hnotSent := hnoSent ⟨j, hjLength⟩ hjBefore cutEarlier hOldCut
      have hearlierExpected : cutEarlier.expectedWord = some word := hsentExpected
      have hsent : cutEarlier.expectedWord = cut.raw :=
        hearlierExpected.trans hraw.symm
      exact (hnotSent hsent).elim
  · rcases hlater with ⟨halpha, halphaN, hspanT, halphaT, hboundary, hthroughN⟩
    let a := m.val + 1
    let alpha := s + a
    rcases hthroughN with
      ⟨_callCodeN, _loggedN, _cutN, _testN, _hcallN, _hactualN, _hloggedN,
        _hcutN, _hcomparisonN, _hpositiveN, _hquotaN, _htestN, hlistFacts⟩
    rcases hlistFacts with
      ⟨_hlistA, _hlistB, _hlength, _hcountBefore, _hbank, _hrawBatch,
        _hchronological, hprovenance, _hhash, hfinish⟩
    let tests := ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
      rate rewards C_star C_h s hs i alpha x
    have hnotSentTests : ∀ test ∈ tests, test.sent ≠ some word := by
      intro test htest
      obtain ⟨j, hjAfterReset, hjCurrent, _htestEq, _htestTime, _htestSample,
        _htestSent, hcallData⟩ := hprovenance test htest
      rcases hcallData with
        ⟨_call, _logged, cutTest, _hcall, _hactual, _hlogged, hcutTest,
          _hcomparison, _hpositive, hsentExpected⟩
      have hjLength : j.val < L.length := by
        simpa only [L, hlen] using j.isLt
      have hsourceRecord := completeSuffixRecord_eq_generatedSourceRecordAt
        rate rewards C_star C_h s hs x j
      have htestCutSource :
          ((ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
            rate rewards C_star C_h s hs x j).output.followers i).down = some cutTest := by
        simpa only [ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt]
          using hcutTest
      have htestCutActual : ((L[j.val]).output.followers i).down = some cutTest := by
        rw [hsourceRecord]
        exact htestCutSource
      have hnoWord := hnoSent ⟨j.val, hjLength⟩ (by omega) cutTest htestCutActual
      intro hsent
      apply hnoWord
      calc
        cutTest.expectedWord = test.sent := hsentExpected.symm
        _ = some word := hsent
        _ = cut.raw := hraw.symm
    have hfinal := hfinish (by simpa only [tests, alpha, a] using hnotSentTests)
    have hsourceFresh :
        x.val ∈ ReferenceGeneratedDownFreshSourceTail.generatedDownFreshSourceEvent
          (rate := rate) rewards C_star C_h s hs i alpha halpha halphaT word
          (AffineBatchDecoder.quota p) := by
      exact ⟨x, rfl, hfinal.1⟩
    have hallLaunch :
        x.val ∈ ReferenceGeneratedDownFreshAllLaunchTail.generatedDownFreshAllLaunchSourceEvent
          (rate := rate) rewards C_star C_h i alpha halphaT word
          (AffineBatchDecoder.quota p) :=
      ⟨s, hs, halpha, hsourceFresh⟩
    change z ∈ ⋃ i' : Fin (p.m - 1), ⋃ alpha' : Fin p.T, ⋃ w,
      (⋃ j : Fin (alpha'.val + 1),
        {source | source ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i' alpha'.val j.val alpha'.isLt.le w control0
            (AffineBatchDecoder.quota p)}) ∪
      ReferenceGeneratedDownFreshAllLaunchTail.generatedDownFreshAllLaunchSourceEvent
        (rate := rate) rewards C_star C_h i' alpha'.val alpha'.isLt w
          (AffineBatchDecoder.quota p)
    simp only [Set.mem_iUnion]
    exact ⟨i, ⟨⟨alpha, halphaT⟩, ⟨word, Or.inr hallLaunch⟩⟩⟩

end Bandits.Support.ReferenceCompleteSelectedDownErrorCoverage

end
