/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedDownCompletionTestInterval
public import Bandits.Support.ReferenceGeneratedDownCohortFiniteUnion

/-!
# Later generated DOWN completion detector

This module consumes the accepted same-run completion interval. It derives the
literal generated detector conclusion from all-test goodness and specializes
the hash-one half to an actual raw solution. The remaining `not sent` premise
stays explicit.

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-42`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`,
`sources/zip4/manuscript/08_main_theorem.tex:29-42`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:111-157`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceDownCompletedAmbiguityMeasurability
open Bandits.Support.ReferenceFollowerDownDecoderReplay
open Bandits.Support.ReferenceGeneratedDownBatchCalendar
open Bandits.Support.ReferenceGeneratedDownCompletionTestInterval
open Bandits.Support.ReferenceGeneratedDownPrefixList

namespace Bandits.Support.ReferenceGeneratedDownLaterCompletionDetector

variable {p : ConstructorDimensions.Parameters}

private theorem survives_of_length_eq_and_good
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    ∀ (q : ℕ) (tests : List (ReferenceGeneratedDownBatchCalendar.ExecutedTest p)),
      tests.length = q →
      (∀ test ∈ tests, ReferenceGeneratedDownBatchCalendar.ExecutedTest.good candidate test) →
      ReferenceGeneratedDownBatchCalendar.survives candidate q tests := by
  intro q
  induction q with
  | zero =>
      intro tests _ _
      simp [ReferenceGeneratedDownBatchCalendar.survives]
  | succ q ih =>
      intro tests hlength hgood
      cases tests with
      | nil => simp at hlength
      | cons test rest =>
          have hlength' : rest.length = q := by simp at hlength ⊢; omega
          have hhead := hgood test (by simp)
          have htail : ∀ test' ∈ rest,
              ReferenceGeneratedDownBatchCalendar.ExecutedTest.good candidate test' := by
            intro test' hmem
            exact hgood test' (by simp [hmem])
          simpa [ReferenceGeneratedDownBatchCalendar.survives] using And.intro hhead (ih rest hlength' htail)

private theorem generatedDown_later_fresh_union_of_detector
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (control0 : ContinuousLearningRows.TimeControl p)
    (q alpha : ℕ) (halpha : s < alpha) (halphaT : alpha < p.T)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hdetector : ReferenceGeneratedDownBatchCalendar.generatedDownD rate rewards
      C_star C_h s q hs i alpha halpha halphaT candidate x) :
    x.val ∈ ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
      rate rewards C_star C_h control0 q := by
  classical
  change x.val ∈ ⋃ i : Fin (p.m - 1), ⋃ alpha : Fin p.T, ⋃ w,
    (⋃ k : Fin (alpha.val + 1),
      {z | z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
        rate rewards C_star C_h i alpha.val k.val alpha.isLt.le w control0 q}) ∪
      ReferenceGeneratedDownFreshAllLaunchTail.generatedDownFreshAllLaunchSourceEvent
        (rate := rate) rewards C_star C_h i alpha.val alpha.isLt w q
  simp only [Set.mem_iUnion]
  refine ⟨i, ?_⟩
  refine ⟨⟨alpha, halphaT⟩, ?_⟩
  refine ⟨candidate, ?_⟩
  right
  change x.val ∈ ReferenceGeneratedDownFreshAllLaunchTail.generatedDownFreshAllLaunchSourceEvent
    (rate := rate) rewards C_star C_h i alpha halphaT candidate q
  change ∃ s' : ℕ, ∃ hs' : s' < p.T, ∃ hsa' : s' < alpha,
    x.val ∈ ReferenceGeneratedDownFreshSourceTail.generatedDownFreshSourceEvent
      (rate := rate) rewards C_star C_h s' hs' i alpha hsa' halphaT candidate q
  refine ⟨s, hs, halpha, ?_⟩
  change ∃ y : ReferenceGeneratedDownQthCalendar.LaunchSource rate rewards C_star C_h s hs,
    y.val = x.val ∧ ReferenceGeneratedDownBatchCalendar.generatedDownD rate rewards
      C_star C_h s q hs i alpha halpha halphaT candidate y
  exact ⟨x, rfl, hdetector⟩

private theorem affineHash_eq_one_of_raw_batch
    (tests : List (ReferenceGeneratedDownBatchCalendar.ExecutedTest p))
    (batch : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hbank : batch = tests.map ReferenceGeneratedDownPrefixList.stampedTest)
    (hraw : AffineBatchDecoder.batchOutput batch = some word) :
    ∀ test ∈ tests, AffineChannelLaw.affineHash test.sample word = 1 := by
  intro test htest
  have hsolution := (AffineBatchDecoder.batchOutput_eq_some_iff batch word).mp hraw
  have hentry : ReferenceGeneratedDownPrefixList.stampedTest test ∈ batch := by
    rw [hbank]
    exact List.mem_map.mpr ⟨test, htest, rfl⟩
  have hequation := hsolution.1 _ hentry
  exact (AffineBatchDecoder.equation_iff_affineHash test.sample word).mp
    (by simpa [ReferenceGeneratedDownPrefixList.stampedTest] using hequation)

/-- A completed actual DOWN batch has the accepted greatest-reset interval.
If every original test is good for `candidate`, that same source execution
belongs to the literal fresh DOWN detector and the joint cohort union. -/
theorem generated_down_later_completion_detector_of_good
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s))
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (control0 : ContinuousLearningRows.TimeControl p)
    (hcomplete : ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s hs i x).2 n)) :
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
              ∃ callCode logged cut,
                ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i (Rk k) =
                  some callCode ∧
                ReferenceFollowerDownDecoderReplay.actualDownCall i (Rk k) =
                  some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode) ∧
                ((Rk k).output.followers i).downInput = some logged ∧
                ((Rk k).output.followers i).down = some cut ∧
                cut.rawComparison.isSome = true ∧
                0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (Rk k) i).val.val ∧
                test.sent = cut.expectedWord) ∧
          ((∀ test ∈ tests,
              ReferenceGeneratedDownBatchCalendar.ExecutedTest.good candidate test) →
            ReferenceGeneratedDownBatchCalendar.generatedDownD rate rewards C_star C_h s Q
              hs i alpha (by omega) (by omega) candidate x ∧
            x.val ∈ ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
              rate rewards C_star C_h control0 Q))) := by
  classical
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
  dsimp only
  have hinterval :=
    ReferenceGeneratedDownCompletionTestInterval.generated_down_completion_test_interval
      rate rewards C_star C_h s hs x i n hcomplete
  dsimp only at hinterval
  rcases hinterval with hfirst | ⟨m, hmn, hcompm, hgreatest, hnoMiddle, hunique, hlater⟩
  · exact Or.inl hfirst
  · rcases hlater with ⟨halpha, halphaN, halphaT, hboundary, hafterReset⟩
    rcases hafterReset with
      ⟨stateA, memoryA, callCodeM, loggedM, cutM, _hordinaryA, _hresetA,
        _hcallM, _hactualM, _hloggedM, _hcutM, _hcomparisonM, _hpositiveM,
        _hquotaM, _hbatchM, hthroughN⟩
    rcases hthroughN with
      ⟨stateN, memoryN, callCodeN, loggedN, cutN, testN, _hordinaryN,
        _hcompletedN, _hpendingN, _hloggedBankN, hcountBeforeN, hcallN,
        hactualN, hloggedN, hcutN, hcomparisonN, hpositiveN, hquotaN, htestN,
        hlistFacts⟩
    rcases hlistFacts with
      ⟨hlistA, hlistB, hlengthInterval, hbank, hraw, hchron, hprovenance⟩
    refine Or.inr ⟨m, hmn, hcompm, hgreatest, hnoMiddle, hunique, ?_⟩
    let a := m.val + 1
    let alpha := s + a
    have hspanT : s + n.val < p.T := by omega
    refine ⟨halpha, halphaN, hspanT, halphaT, hboundary,
      callCodeN, loggedN, cutN, testN, hcallN, hactualN, hloggedN, hcutN,
      hcomparisonN, hpositiveN, hquotaN, htestN, ?_⟩
    let tests := ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
      rate rewards C_star C_h s hs i alpha x
    let Bn := loggedN.downBatch.pending ++
      [⟨(Rk n).input.time,
        (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCodeN).2.sample⟩]
    have hlength : tests.length = Q := by
      calc
        tests.length =
            (ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
              rate rewards C_star C_h s hs i alpha x).length := rfl
        _ = (Tests a (n.val + 1)).length := by
          exact congrArg List.length (hlistA.trans hlistB)
        _ = Q := hlengthInterval
    refine ⟨hlistA, hlistB, hlength, hcountBeforeN, ?_, ?_, hchron, hprovenance, ?_⟩
    · simpa [Bn, tests] using hbank
    · simpa [Bn] using hraw
    · intro hgood
      have hsurvives := survives_of_length_eq_and_good candidate Q tests hlength hgood
      have hdetector : ReferenceGeneratedDownBatchCalendar.generatedDownD rate rewards
          C_star C_h s Q hs i alpha (by omega) (by omega) candidate x :=
        ⟨hboundary, hsurvives⟩
      have hmembership := generatedDown_later_fresh_union_of_detector rate rewards C_star C_h
        s hs x i control0 Q alpha (by omega) (by omega) candidate hdetector
      exact ⟨hdetector, hmembership⟩

/-- For an actual raw DOWN solution, every stamped sample hashes to one.
The detector conclusion still assumes that the candidate was not sent in any
test of this exact generated batch. -/
theorem generated_down_later_raw_detector_of_not_sent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (control0 : ContinuousLearningRows.TimeControl p)
    (hcomplete : ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s hs i x).2 n))
    (hcut :
      ((⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s n.val (by omega)
          (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
            rate rewards C_star C_h s hs x),
        ReferenceActivePhysicalStep.step
          (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s n.val (by omega)
            (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
              rate rewards C_star C_h s hs x)), rfl⟩ :
        ReferenceFollowerDownDecoderReplay.Record p rate).output.followers i).down = some cut)
    (hraw : cut.raw = some word) :
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
          ((∀ test ∈ tests, test.sent ≠ some word) →
            ReferenceGeneratedDownBatchCalendar.generatedDownD rate rewards C_star C_h s Q
              hs i alpha (by omega) (by omega) word x ∧
            x.val ∈ ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
              rate rewards C_star C_h control0 Q))) := by
  classical
  let Y := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
    rate rewards C_star C_h s hs x
  let Rk := fun k : Fin (p.T - s) =>
    (⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega) Y,
      ReferenceActivePhysicalStep.step
        (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega) Y), rfl⟩ :
      ReferenceFollowerDownDecoderReplay.Record p rate)
  have hcut' : ((Rk n).output.followers i).down = some cut := by
    simpa only [Rk, Y] using hcut
  let hdetector := generated_down_later_completion_detector_of_good
    rate rewards C_star C_h s hs x i n word control0 hcomplete
  dsimp only at hdetector
  rcases hdetector with hfirst | ⟨m, hmn, hcompm, hgreatest, hnoMiddle, hunique, hlater⟩
  · exact Or.inl hfirst
  · rcases hlater with ⟨halpha, halphaN, hspanT, halphaT, hboundary, hthroughN⟩
    rcases hthroughN with
      ⟨callCodeN, loggedN, cutN, testN, hcallN, hactualN, hloggedN, hcutN,
        hcomparisonN, hpositiveN, hquotaN, htestN, hlistFacts⟩
    rcases hlistFacts with
      ⟨hlistA, hlistB, hlength, hcountBeforeN, hbank, hrawN, hchron, hprovenance,
        hgoodDetector⟩
    have hsame : some cutN = some cut := hcutN.symm.trans
      (by simpa only [Rk, Y] using hcut')
    have hcutEq : cutN = cut := Option.some.inj hsame
    have hrawBank : AffineBatchDecoder.batchOutput
        (loggedN.downBatch.pending ++
          [⟨(Rk n).input.time,
            (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCodeN).2.sample⟩]) =
        some word := by
      have hrawN' : cut.raw = AffineBatchDecoder.batchOutput
          (loggedN.downBatch.pending ++
            [⟨(Rk n).input.time,
              (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCodeN).2.sample⟩]) := by
        simpa only [hcutEq] using hrawN
      exact hrawN'.symm.trans hraw
    let a := m.val + 1
    let alpha := s + a
    let tests := ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
      rate rewards C_star C_h s hs i alpha x
    let Bn := loggedN.downBatch.pending ++
      [⟨(Rk n).input.time,
        (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCodeN).2.sample⟩]
    have hhash := affineHash_eq_one_of_raw_batch tests Bn word (by simpa [Bn, tests] using hbank)
      (by simpa [Bn] using hrawBank)
    refine Or.inr ⟨m, hmn, hcompm, hgreatest, hnoMiddle, hunique, ?_⟩
    refine ⟨halpha, halphaN, hspanT, halphaT, hboundary,
      callCodeN, loggedN, cutN, testN, hcallN, hactualN, hloggedN, hcutN,
      hcomparisonN, hpositiveN, hquotaN, htestN, ?_⟩
    refine ⟨hlistA, hlistB, hlength, hcountBeforeN, ?_, ?_, hchron, hprovenance,
      hhash, ?_⟩
    · simpa [Bn, tests] using hbank
    · simpa [Bn] using hrawN
    · intro hnotSent
      have hgood : ∀ test ∈ tests,
          ReferenceGeneratedDownBatchCalendar.ExecutedTest.good word test := by
        intro test hmem
        exact ⟨hnotSent test hmem, hhash test hmem⟩
      exact hgoodDetector hgood

end Bandits.Support.ReferenceGeneratedDownLaterCompletionDetector

end
