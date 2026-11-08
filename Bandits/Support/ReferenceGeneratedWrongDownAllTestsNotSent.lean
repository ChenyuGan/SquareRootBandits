/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCurrentDownPayloadExclusion
public import Bandits.Support.ReferenceGeneratedDownLaterCompletionDetector

/-!
# Original generated wrong DOWN batches were not sent

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109`,
`05_binary_transport.tex:60-124`, `06_interruptions.tex:9-14,40-61,164-177,246-295,327-348`,
and `08_main_theorem.tex:29-42`, under `sources/zip4/manuscript/`.

These internal deterministic results retain the original full physical suffix,
the inherited old/new bank and the later greatest-completion interval. They
consume the accepted all-phase expected-word exclusion, including its current
round case. They assert no probability estimate or manuscript closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ReferenceGeneratedInheritedDownWrongCompletionWitness

namespace Bandits.Support.ReferenceGeneratedWrongDownAllTestsNotSent

variable {p : ConstructorDimensions.Parameters}

private theorem record_eq_of_input_eq
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r t : ReferenceFollowerDownDecoderReplay.Record p rate)
    (h : r.input = t.input) : r = t := by
  cases r with
  | mk ri ro hr =>
    cases t with
    | mk ti tout ht =>
      dsimp only at h
      subst ti
      subst ro
      subst tout
      rfl

/-- Time identifies a member of the original deterministic physical suffix. -/
private theorem source_record_eq_at
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (k : Fin (p.T - s)) (r : ReferenceFollowerDownDecoderReplay.Record p rate)
    (hmem : r ∈ (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
      rate rewards C_star C_h s hs x).records)
    (htime : r.input.time.val = s + k.val) :
    r = generatedSourceRecordAt rate rewards C_star C_h s hs x k := by
  have hrecords := ReferenceDownCompletedAmbiguityMeasurability.run_records_eq_ofFn
    s (p.T - s) (by omega)
    (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
      rate rewards C_star C_h s hs x)
  change r ∈ (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s)
    (by omega) (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
      rate rewards C_star C_h s hs x)).records at hmem
  rw [hrecords] at hmem
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmem
  have hjtime := congrArg
    (fun record : ReferenceFollowerDownDecoderReplay.Record p rate => record.input.time.val) hj
  change s + j.val = r.input.time.val at hjtime
  have hjk : j = k := Fin.ext (by omega)
  subst j
  exact hj.symm

/-- Every test in the actual first inherited completed batch differs from the
wrong accepted raw word. The accompanying witnesses retain the original bank,
its initialized pending and completed parts, and the current quota test. -/
theorem generated_wrong_down_first_cohort_not_sent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : ((generatedSourceRecordAt rate rewards C_star C_h s hs x n).output.followers i).down =
      some cut)
    (hwrong : ReferenceDownReception.wrongUniqueAccepted cut)
    (hfirst :
      ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s hs i x).2 n) ∧
        ∀ l (hl : l < n.val),
          ¬ ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
            ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
              rate rewards C_star C_h s hs i x).2 ⟨l, lt_trans hl n.isLt⟩)) :
    let Rn := generatedSourceRecordAt rate rewards C_star C_h s hs x n
    let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
      rate rewards C_star C_h s hs x i).downBatch
    let cohort := ReferenceGeneratedInheritedDownCohort.generatedInheritedDownFirstCohortTests
      rate rewards C_star C_h s hs i x
    let testPrefix := ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownPrefix
      (rate := rate) rewards C_star C_h s hs i x n.val
    (∀ test ∈ cohort, test.sent ≠ cut.raw) ∧
      ∃ callCode loggedCode cutCode logged testN,
        ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i Rn = some callCode ∧
        ReferenceFollowerDownDecoderReplay.actualDownCall i Rn =
          some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode) ∧
        (Rn.output.followers i).downInput = some logged ∧
        FollowerDownMeasurability.followerStateCode rate logged = loggedCode ∧
        ReferenceDownCompletedAmbiguityMeasurability.cutFields cut = cutCode ∧
        callCode.1 = Rn.input.time ∧
        logged.downBatch.pending.length + 1 = AffineBatchDecoder.quota p ∧
        cut.rawComparison.isSome = true ∧
        0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation Rn i).val.val ∧
        cut.raw = AffineBatchDecoder.batchOutput
          (logged.downBatch.pending ++
            [⟨Rn.input.time,
              (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample⟩]) ∧
        ReferenceDownCompletedAmbiguityMeasurability.decodedLoggedBank callCode loggedCode =
          ⟨[], logged.downBatch.completed ++
            [logged.downBatch.pending ++
              [⟨Rn.input.time,
                (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample⟩]]⟩ ∧
        logged.downBatch.pending = B0.pending ++
          (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
            rate rewards C_star C_h s hs i x n.val).map
              ReferenceGeneratedInheritedDownCompletion.inheritedTestEntry ∧
        logged.downBatch.completed = B0.completed ∧
        (logged.downBatch.pending ++
          [({ time := Rn.input.time,
              sample := (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample } :
            AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))]).length =
          AffineBatchDecoder.quota p ∧
        logged.downBatch.pending ++
          [⟨Rn.input.time,
            (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample⟩] =
          cohort.map ReferenceGeneratedPrelaunchDownCohort.testEntry ∧
        cohort.length = AffineBatchDecoder.quota p ∧
        ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s hs i x).2 n) = some testN ∧
        testPrefix ++ [testN] = cohort ∧ testN ∈ cohort := by
  classical
  let Rn := generatedSourceRecordAt rate rewards C_star C_h s hs x n
  let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
    rate rewards C_star C_h s hs x i).downBatch
  let cohort := ReferenceGeneratedInheritedDownCohort.generatedInheritedDownFirstCohortTests
    rate rewards C_star C_h s hs i x
  let testPrefix := ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownPrefix
    (rate := rate) rewards C_star C_h s hs i x n.val
  obtain ⟨record, callCode, loggedCode, cutCode, logged, bankCut,
      hinput, hcall, hactual, hlogged, hbankCut, hloggedCode, hcutCode,
      hcallTime, hquota, hcomparison, hpositive, hraw, hdecoded,
      hpending, hcompleted, hbankLength, hjoin⟩ :=
    ReferenceGeneratedInheritedDownCohort.generated_inherited_down_cohort_first_completion_bank
      rewards C_star C_h s hs x i n.val n.isLt hfirst
  have hrecord : record = Rn := record_eq_of_input_eq record Rn hinput
  subst record
  have hsame : bankCut = cut := Option.some.inj (hbankCut.symm.trans hcut)
  subst bankCut
  have hcohortLength : cohort.length = AffineBatchDecoder.quota p := by
    rw [hjoin] at hbankLength
    simpa only [List.length_map] using hbankLength
  have hold := ReferenceGeneratedInheritedDownCohort.generated_inherited_down_old_pending
    (rate := rate) rewards C_star C_h s hs x i
  have hprefixLength : testPrefix.length = AffineBatchDecoder.quota p - 1 := by
    have hpendingLength : logged.downBatch.pending.length = B0.pending.length +
        (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
          rate rewards C_star C_h s hs i x n.val).length := by
      rw [hpending]
      simp only [List.length_append, List.length_map]
      rfl
    change (ReferenceGeneratedInheritedDownCohort.generatedInheritedDownOldFirstTests
      rate rewards C_star C_h s hs x i ++
      ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
        rate rewards C_star C_h s hs i x n.val).length = _
    rw [List.length_append, hold.2]
    change B0.pending.length + _ = _
    omega
  have hfirstIff :=
    (ReferenceGeneratedInheritedDownFirstCompletion.generated_inherited_down_first_completion_iff
      (rate := rate) rewards C_star C_h s hs x i n.val n.isLt).mp hfirst
  obtain ⟨testN, htestN⟩ := Option.isSome_iff_exists.mp hfirstIff.2
  have hprefixCohort : testPrefix ++ [testN] = cohort := by
    have htake := ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownPrefix_current_take
      (rate := rate) rewards C_star C_h s hs i x n.val (AffineBatchDecoder.quota p)
      (by omega) (by have := hcohortLength; have := hprefixLength; omega)
      (le_rfl) hprefixLength testN htestN
    change testPrefix ++ [testN] = cohort.take (AffineBatchDecoder.quota p) at htake
    exact htake.trans (List.take_of_length_le hcohortLength.le)
  have hcurrentMem : testN ∈ cohort := by
    rw [← hprefixCohort]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hcurrentTime := ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownCurrentTest_time
    (rate := rate) rewards C_star C_h s hs i x n testN htestN
  have hbefore :=
    (ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownPrefix_chronological
      (rate := rate) rewards C_star C_h s hs i x n.val (by omega)).2
  have htimeBound : ∀ test ∈ cohort, test.time.val ≤ s + n.val := by
    intro test hmem
    rw [← hprefixCohort] at hmem
    rcases List.mem_append.mp hmem with hprefix | hcurrent
    · exact (hbefore test hprefix).le
    · have heq := List.mem_singleton.mp hcurrent
      subst test
      exact hcurrentTime.le
  obtain ⟨_alpha, _halpha, _hbirth, horigin⟩ :=
    ReferenceGeneratedInheritedDownCohort.generated_inherited_down_cohort_test_origin
      (rate := rate) rewards C_star C_h s hs x i
  have hnotSent : ∀ test ∈ cohort, test.sent ≠ cut.raw := by
    intro test hmem
    rcases (horigin test hmem).2.2 with holdTest | hnewTest
    · obtain ⟨_hOld, _htime, hsent⟩ := holdTest
      rw [hsent]
      exact Ne.symm hwrong.2.1
    · obtain ⟨hNew, _⟩ := hnewTest
      obtain ⟨k, oldRecord, hmemRecord, htime, htestTime, _hsample, _htest,
          oldCall, oldCut, _hcall, holdCut, _hcallTime, _hcallSample, hsent,
          _hexpected, _hpositive, _hcomparison⟩ :=
        ReferenceGeneratedInheritedDownCohort.generated_inherited_down_new_test_physical
          (rate := rate) rewards C_star C_h s hs x i test hNew
      have hbound := htimeBound test hmem
      have hkn : k.val ≤ n.val := by
        rw [htestTime, htime] at hbound
        omega
      have heq := source_record_eq_at rate rewards C_star C_h s hs x k oldRecord
        hmemRecord htime
      rw [heq] at holdCut
      rw [hsent]
      exact ReferenceGeneratedCurrentDownPayloadExclusion.generated_wrong_down_earlier_expected_ne_raw
        rate rewards C_star C_h s hs x i n cut hcut hwrong k hkn oldCut holdCut
  exact ⟨hnotSent, callCode, loggedCode, cutCode, logged, testN,
    hcall, hactual, hlogged, hloggedCode, hcutCode, hcallTime, hquota,
    hcomparison, hpositive, hraw, hdecoded, hpending, hcompleted,
    hbankLength,
    hjoin, hcohortLength, htestN, hprefixCohort, hcurrentMem⟩

/-- A wrong accepted completed DOWN batch either is the first postlaunch
completion or has the same greatest earlier completion and literal interval
as the accepted later-batch theorem. All not-sent facts and the detector
consequence are produced for that exact interval, without an extra law. -/
theorem generated_wrong_down_later_completion_detector
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : ((generatedSourceRecordAt rate rewards C_star C_h s hs x n).output.followers i).down =
      some cut)
    (hwrong : ReferenceDownReception.wrongUniqueAccepted cut)
    (control0 : ContinuousLearningRows.TimeControl p)
    (hcomplete : ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s hs i x).2 n)) :
    ∃ word : AffineChannelLaw.Word (AffineBatchDecoder.width p), cut.raw = some word ∧
    let Y := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
      rate rewards C_star C_h s hs x
    let R := ReferenceGeneratedDownBatchCalendar.generatedSourceRun
      rate rewards C_star C_h s hs x
    let O := ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
      rate rewards C_star C_h s hs i x
    let Q := AffineBatchDecoder.quota p
    let Comp := fun k : Fin (p.T - s) =>
      ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate (O.2 k)
    let Rk := fun k : Fin (p.T - s) =>
      (⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega) Y,
        ReferenceActivePhysicalStep.step
          (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega) Y), rfl⟩ :
        ReferenceFollowerDownDecoderReplay.Record p rate)
    let Tests := fun (a b : ℕ) =>
      ((R.records.take b).drop a).filterMap (fun record =>
        ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
          (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i))
    (∀ k : Fin (p.T - s), k < n → ¬ Comp k) ∨
    ∃ m : Fin (p.T - s),
      ∃ hmn : m < n,
      Comp m ∧
      (∀ k : Fin (p.T - s), k < n → Comp k → k ≤ m) ∧
      (∀ k : Fin (p.T - s), m < k → k < n → ¬ Comp k) ∧
      (∀ m' : Fin (p.T - s), m' < n → Comp m' →
        (∀ k : Fin (p.T - s), k < n → Comp k → k ≤ m') → m' = m) ∧
      (let a := m.val + 1
       let alpha := s + a
       s < alpha ∧ alpha ≤ s + n.val ∧ s + n.val < p.T ∧ alpha < p.T ∧
       ReferenceGeneratedDownBatchCalendar.generatedSourceBatchBoundary
         rate rewards C_star C_h s hs i alpha (by omega) (by omega) x ∧
       ∃ callCodeN loggedN cutN testN,
         ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i (Rk n) =
           some callCodeN ∧
         ReferenceFollowerDownDecoderReplay.actualDownCall i (Rk n) =
           some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCodeN) ∧
         ((Rk n).output.followers i).downInput = some loggedN ∧
         ((Rk n).output.followers i).down = some cutN ∧
         cutN.rawComparison.isSome = true ∧
         0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (Rk n) i).val.val ∧
         loggedN.downBatch.pending.length + 1 = Q ∧
         ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate (O.2 n) = some testN ∧
         (let tests := ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
             rate rewards C_star C_h s hs i alpha x
          let Bn := loggedN.downBatch.pending ++
            [⟨(Rk n).input.time,
              (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCodeN).2.sample⟩]
          tests = Tests a n.val ++ [testN] ∧
          Tests a n.val ++ [testN] = Tests a (n.val + 1) ∧
          tests.length = Q ∧
          (Tests a n.val).length = Q - 1 ∧
          Bn = tests.map ReferenceGeneratedDownPrefixList.stampedTest ∧
          cutN.raw = AffineBatchDecoder.batchOutput Bn ∧
          tests.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
          (∀ test ∈ tests,
            ∃ k : Fin (p.T - s),
              a ≤ k.val ∧ k.val ≤ n.val ∧
              ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate (O.2 k) = some test ∧
              test.time = (Rk k).input.time ∧
              test.sample = ((Rk k).input.row.2 (Rk k).input.time).2 (0, i) ∧
              test.sent = ReferenceActiveAffinePositiveTest.downSent (Rk k).input ∧
              ∃ callCode logged cut',
                ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i (Rk k) =
                  some callCode ∧
                ReferenceFollowerDownDecoderReplay.actualDownCall i (Rk k) =
                  some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode) ∧
                ((Rk k).output.followers i).downInput = some logged ∧
                ((Rk k).output.followers i).down = some cut' ∧
                cut'.rawComparison.isSome = true ∧
                0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (Rk k) i).val.val ∧
                test.sent = cut'.expectedWord) ∧
          (∀ test ∈ tests, AffineChannelLaw.affineHash test.sample word = 1) ∧
          (∀ test ∈ tests, test.sent ≠ some word) ∧
            ReferenceGeneratedDownBatchCalendar.generatedDownD rate rewards C_star C_h s Q
              hs i alpha (by omega) (by omega) word x ∧
            x.val ∈ ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
              rate rewards C_star C_h control0 Q)) := by
  classical
  obtain ⟨word, hraw⟩ := Option.ne_none_iff_exists'.mp hwrong.2.1
  refine ⟨word, hraw, ?_⟩
  have hdetector :=
    ReferenceGeneratedDownLaterCompletionDetector.generated_down_later_raw_detector_of_not_sent
      rate rewards C_star C_h s hs x i n cut word control0 hcomplete hcut hraw
  dsimp only at hdetector ⊢
  rcases hdetector with hfirst | ⟨m, hmn, hcompm, hgreatest, hnoMiddle, hunique, hlater⟩
  · exact Or.inl hfirst
  · rcases hlater with ⟨halpha, halphaN, hspanT, halphaT, hboundary,
      callCodeN, loggedN, cutN, testN, hcallN, hactualN, hloggedN, hcutN,
      hcomparisonN, hpositiveN, hquotaN, htestN, hlistFacts⟩
    rcases hlistFacts with
      ⟨hlistA, hlistB, hlength, hcountBeforeN, hbank, hrawN, hchron,
        hprovenance, hhash, hnotSentDetector⟩
    have hcutEq : cutN = cut := Option.some.inj (hcutN.symm.trans hcut)
    have hcurrentRaw : cutN.raw = some word := hcutEq ▸ hraw
    let a := m.val + 1
    let alpha := s + a
    let tests := ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
      rate rewards C_star C_h s hs i alpha x
    have hnotSent : ∀ test ∈ tests, test.sent ≠ some word := by
      intro test hmem
      obtain ⟨k, _hak, hkn, _htest, _htime, _hsample, _hsentInput,
          callCode, logged, oldCut, _hcall, _hactual, _hlogged, holdCut,
          _hcomparison, _hpositive, hsent⟩ := hprovenance test hmem
      have hne :=
        ReferenceGeneratedCurrentDownPayloadExclusion.generated_wrong_down_earlier_expected_ne_raw
          rate rewards C_star C_h s hs x i n cut hcut hwrong k hkn oldCut holdCut
      rw [hsent]
      intro heq
      exact hne (heq.trans (hcutEq ▸ hcurrentRaw).symm)
    obtain ⟨hgenerated, hunion⟩ := hnotSentDetector hnotSent
    refine Or.inr ⟨m, hmn, hcompm, hgreatest, hnoMiddle, hunique,
      halpha, halphaN, hspanT, halphaT, hboundary,
      callCodeN, loggedN, cutN, testN, hcallN, hactualN, hloggedN, hcutN,
      hcomparisonN, hpositiveN, hquotaN, htestN,
      hlistA, hlistB, hlength, hcountBeforeN, hbank, hrawN, hchron,
      hprovenance, hhash, hnotSent, hgenerated, hunion⟩

end Bandits.Support.ReferenceGeneratedWrongDownAllTestsNotSent

end
