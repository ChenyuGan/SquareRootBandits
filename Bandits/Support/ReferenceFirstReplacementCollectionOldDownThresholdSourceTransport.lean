/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity

import Lean.Elab.Tactic.Omega

/-!
# Original-source transport at the first replacement OLD DOWN threshold

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-55,180-239`,
`sources/zip4/manuscript/06_interruptions.tex:246-349,477-481`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`.

The transport is local to the detecting physical prefix. The physical failure
alternative remains separate from the retained ambiguous-batch readout.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions
open ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity
open ReferenceFirstReplacementCollectionOldDownCallDates
open scoped Classical

namespace Bandits.Support.ReferenceFirstReplacementCollectionOldDownThresholdSourceTransport

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- A real completed batch also satisfies the generated calendar's completion
test. This uses the actual retained decoder input, including its positive test. -/
theorem completedBatchAtRound_of_completedDownBatch
    (r : ReferenceFollowerDownDecoderReplay.Record p rate) (i : Fin (p.m - 1))
    (batch : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hbatch : ReferenceFirstLiveDownCompletionReadout.completedDownBatch r i = some batch) :
    ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation r.input i) := by
  obtain ⟨logged, cut, hl, hc, hcalled, hquota, _⟩ :=
    (ReferenceFirstLiveDownCompletionReadout.completedDownBatch_eq_some_iff r i batch).mp hbatch
  exact (ReferenceGeneratedDownResetCompletionCensus.completedBatchAtRound_iff_executed_quota
    r i).mpr ⟨logged, cut, hl, hc, hcalled, hquota⟩

/-- The strict-past flag at the next calendar boundary contains this actual
record. It places no requirement on any subsequent physical round. -/
theorem strictPastDecoderFlag_of_completed_ambiguity
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceFollowerDownDecoderReplay.Record p rate)
    (i : Fin (p.m - 1))
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      r.input.time source = some r)
    (hamb : ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s r i) :
    ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag s r = true ∧
      ∃ hn : r.input.time.val + 1 ≤ p.T,
        ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag rate rewards
          C_star C_h s (r.input.time.val + 1) hn source = true := by
  have hflag :=
    (ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag_eq_true_iff s r).mpr
      (Or.inr ⟨i, hamb⟩)
  refine ⟨hflag, Nat.succ_le_of_lt r.input.time.isLt, ?_⟩
  apply (ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag_eq_true_iff
    rate rewards C_star C_h s _ _ source).mpr
  exact ⟨⟨r.input.time.val, Nat.lt_succ_self _⟩, r, hrecord, hflag⟩

private theorem survives_of_good
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (tests : List (ReferenceGeneratedDownBatchCalendar.ExecutedTest p))
    (hgood : ∀ test ∈ tests,
      ReferenceGeneratedDownBatchCalendar.ExecutedTest.good candidate test) :
    ReferenceGeneratedDownBatchCalendar.survives candidate tests.length tests := by
  induction tests with
  | nil => trivial
  | cons test tests ih =>
      exact ⟨hgood test (by simp), ih (fun t ht => hgood t (by simp [ht]))⟩

/-- A candidate solving the actual completed bank hashes to one on every
original generated test, once that bank has been identified entry by entry. -/
theorem hashes_of_generated_batch_solution
    (tests : List (ReferenceGeneratedDownBatchCalendar.ExecutedTest p))
    (batch : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hbank : tests.map ReferenceGeneratedDownPrefixList.stampedTest = batch)
    (hsolution : AffineBatchDecoder.satisfies (AffineBatchDecoder.samples batch) candidate) :
    ∀ test ∈ tests, AffineChannelLaw.affineHash test.sample candidate = 1 := by
  intro test ht
  have he : ReferenceGeneratedDownPrefixList.stampedTest test ∈ batch := by
    rw [← hbank]
    exact List.mem_map.mpr ⟨test, ht, rfl⟩
  exact (AffineBatchDecoder.equation_iff_affineHash test.sample candidate).mp
    ((AffineBatchDecoder.satisfies_samples_iff batch candidate).mp hsolution _ he)

/-- Embed an actual generated fresh-batch event in the literal original-source
cohort union. The free control coordinate belongs only to the mixed arm. -/
theorem generatedDownD_mem_cohortUnion
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (alpha q : ℕ) (hsa : s < alpha) (haT : alpha < p.T)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hD : ReferenceGeneratedDownBatchCalendar.generatedDownD rate rewards C_star C_h
      s q hs i alpha hsa haT candidate x) :
    ∀ control0 : ContinuousLearningRows.TimeControl p,
      x.val ∈ ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
        rate rewards C_star C_h control0 q := by
  intro control0
  simp only [ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent, Set.mem_iUnion]
  refine ⟨i, ⟨alpha, haT⟩, candidate, Or.inr ?_⟩
  exact ⟨s, hs, hsa, x, rfl, hD⟩

/-- Conditional calendar join. The earlier actual completion excludes the
no-predecessor arm. The calendar supplies the greatest reset and uniqueness;
its original diagnostic identifies the completed bank, rather than its length.
Only tests through the detecting record need the fixed sender fact. -/
theorem generated_second_completion_transport
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (d n : Fin (p.T - s))
    (sent other : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (batch : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hdn : d < n) :
    let Y := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
      rate rewards C_star C_h s hs x
    let O := ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
      rate rewards C_star C_h s hs i x
    let Rk := fun k : Fin (p.T - s) =>
      (⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega) Y,
        ReferenceActivePhysicalStep.step
          (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega) Y), rfl⟩ :
        ReferenceFollowerDownDecoderReplay.Record p rate)
    ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate (O.2 d) →
    ReferenceFirstLiveDownCompletionReadout.completedDownBatch (Rk n) i = some batch →
    sent ≠ other →
    AffineBatchDecoder.satisfies (AffineBatchDecoder.samples batch) other →
    (∀ k : Fin (p.T - s), d < k → k ≤ n →
      ActiveFollowerDownAcceptance.downSelected p i (Rk k).input.row (Rk k).input.time →
      ReferenceActiveAffinePositiveTest.downSent (Rk k).input = some sent) →
    ∃ m : Fin (p.T - s), m < n ∧ d ≤ m ∧
      ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate (O.2 m) ∧
      (∀ k : Fin (p.T - s), k < n →
        ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate (O.2 k) → k ≤ m) ∧
      (∀ m' : Fin (p.T - s), m' < n →
        ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate (O.2 m') →
        (∀ k : Fin (p.T - s), k < n →
          ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate (O.2 k) → k ≤ m') →
        m' = m) ∧
      ∃ (hsa : s < s + (m.val + 1)) (haT : s + (m.val + 1) < p.T),
        s + (m.val + 1) ≤ s + n.val ∧
        ReferenceGeneratedDownBatchCalendar.generatedSourceBatchBoundary
          rate rewards C_star C_h s hs i (s + (m.val + 1)) hsa haT x ∧
        (∃ state memory,
          (ReferenceActiveHorizonMeasurability.runOfInput s (m.val + 1) (by omega) Y
            ).finalState.followers i = .ordinary state memory ∧
          state.downBatch.pending = []) ∧
        let tests := ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
          rate rewards C_star C_h s hs i (s + (m.val + 1)) x
        tests.map ReferenceGeneratedDownPrefixList.stampedTest = batch ∧
        tests.length = AffineBatchDecoder.quota p ∧
        (∀ test ∈ tests, ∃ k : Fin (p.T - s), m < k ∧ k ≤ n ∧
          ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate (O.2 k) = some test ∧
          test.time = (Rk k).input.time ∧
          test.sample = ((Rk k).input.row.2 (Rk k).input.time).2 (0, i) ∧
          test.sent = some sent ∧
          ReferenceGeneratedDownBatchCalendar.ExecutedTest.good other test) ∧
        ReferenceGeneratedDownBatchCalendar.generatedDownD rate rewards C_star C_h
          s (AffineBatchDecoder.quota p) hs i (s + (m.val + 1)) hsa haT other x ∧
        (∀ control0 : ContinuousLearningRows.TimeControl p,
          x.val ∈ ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
            rate rewards C_star C_h control0 (AffineBatchDecoder.quota p)) := by
  classical
  dsimp only
  intro hd hbatch hne hsolution hsender
  let Y := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
    rate rewards C_star C_h s hs x
  let O := ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
    rate rewards C_star C_h s hs i x
  let Rk := fun k : Fin (p.T - s) =>
    (⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega) Y,
      ReferenceActivePhysicalStep.step
        (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega) Y), rfl⟩ :
      ReferenceFollowerDownDecoderReplay.Record p rate)
  have hn : ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate (O.2 n) := by
    exact completedBatchAtRound_of_completedDownBatch (Rk n) i batch hbatch
  have hinterval :=
    ReferenceGeneratedDownCompletionTestInterval.generated_down_completion_test_interval
      rate rewards C_star C_h s hs x i n hn
  dsimp only at hinterval
  rcases hinterval with hfirst | ⟨m, hmn, hm, hgreatest, _hnoMiddle, hunique, hlater⟩
  · exact (hfirst d hdn hd).elim
  · have hdm : d ≤ m := hgreatest d hdn hd
    rcases hlater with ⟨hsa, halphaN, haT, hboundary, hreset⟩
    rcases hreset with
      ⟨stateA, memoryA, callM, loggedM, cutM, hordA, hempA,
        _hcallM, _hactualM, _hloggedM, _hcutM, _hcompM, _hposM,
        _hquotaM, _hbankM, hthroughN⟩
    rcases hthroughN with
      ⟨stateN, memoryN, callN, loggedN, cutN, tn, _hordN,
        _hcompletedN, _hpendingN, _hloggedBankN, _hcountN,
        _hcallN, hactualN, hloggedN, hcutN, hcomparisonN, hpositiveN,
        _hquotaN, _htestN, hlist⟩
    rcases hlist with ⟨hlistA, hlistB, hlength, hbank, _hraw, _hchron, hprovenance⟩
    let tests := ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
      rate rewards C_star C_h s hs i (s + (m.val + 1)) x
    have heligible : AffineBatchDecoder.eligible
        (ActiveFollowerDownAcceptance.currentRoundInput p i (Rk n).input.row
          (Rk n).input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (Rk n) i)
          rate loggedN) := by
      have hf := ReferenceFirstLiveDownCompletionReadout.retained_call_fields
        (Rk n) i loggedN cutN hloggedN hcutN hcomparisonN
      exact (ActiveFollowerDownAcceptance.currentRoundInput_eligible_iff p i
        (Rk n).input.row (Rk n).input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (Rk n) i) rate loggedN).mpr
          ⟨hf.1, hf.2.1, hpositiveN⟩
    have hfields := ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields
      (Rk n) i _ hactualN
    have happended : ReferenceFirstLiveDownCompletionReadout.appendedDownBatch
        (Rk n) i loggedN = tests.map ReferenceGeneratedDownPrefixList.stampedTest := by
      rw [← hbank]
      simp [ReferenceFirstLiveDownCompletionReadout.appendedDownBatch,
        AffineBatchDecoder.positiveAt, ActiveFollowerDownAcceptance.currentInputExtension,
        heligible, AffineBatchDecoder.entry, hfields.2.1]
      rfl
    have hbatchEq : tests.map ReferenceGeneratedDownPrefixList.stampedTest = batch := by
      obtain ⟨logged, cut, hl, _hc, _hcalled, _hquota, heq⟩ :=
        (ReferenceFirstLiveDownCompletionReadout.completedDownBatch_eq_some_iff
          (Rk n) i batch).mp hbatch
      have hlogEq : logged = loggedN := Option.some.inj (hl.symm.trans hloggedN)
      subst logged
      exact happended.symm.trans heq
    have htestsLength : tests.length = AffineBatchDecoder.quota p := by
      have heq := congrArg List.length (hlistA.trans hlistB)
      exact heq.trans hlength
    have hhash := hashes_of_generated_batch_solution tests batch other hbatchEq hsolution
    have htestFacts : ∀ test ∈ tests, ∃ k : Fin (p.T - s), m < k ∧ k ≤ n ∧
        ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate (O.2 k) = some test ∧
        test.time = (Rk k).input.time ∧
        test.sample = ((Rk k).input.row.2 (Rk k).input.time).2 (0, i) ∧
        test.sent = some sent ∧
        ReferenceGeneratedDownBatchCalendar.ExecutedTest.good other test := by
      intro test ht
      obtain ⟨k, hmk, hkn, hexec, htime, hsample, hsent, call, logged, cut,
        _hcall, _hactual, hl, hc, hcomp, _hpositive, _hexpected⟩ := hprovenance test ht
      have hselected := (ReferenceFirstLiveDownCompletionReadout.retained_call_fields
        (Rk k) i logged cut hl hc hcomp).1
      have hmk' : m < k := by exact hmk
      have hdk : d < k := lt_of_le_of_lt hdm hmk'
      have hsentWord : test.sent = some sent :=
        hsent.trans (hsender k hdk hkn hselected)
      refine ⟨k, hmk', hkn, hexec, htime, hsample, hsentWord, ?_, hhash test ht⟩
      rw [hsentWord]
      exact fun heq => hne (Option.some.inj heq)
    have hgood : ∀ test ∈ tests,
        ReferenceGeneratedDownBatchCalendar.ExecutedTest.good other test := by
      intro test ht
      obtain ⟨_, _, _, _, _, _, _, hg⟩ := htestFacts test ht
      exact hg
    have hD : ReferenceGeneratedDownBatchCalendar.generatedDownD rate rewards C_star C_h
        s (AffineBatchDecoder.quota p) hs i (s + (m.val + 1)) hsa haT other x := by
      refine ⟨hboundary, ?_⟩
      rw [← htestsLength]
      exact survives_of_good other tests hgood
    refine ⟨m, hmn, hdm, hm, hgreatest, hunique, hsa, haT, halphaN, hboundary,
      ⟨stateA, memoryA, hordA, hempA⟩, hbatchEq, htestsLength, htestFacts, hD, ?_⟩
    exact generatedDownD_mem_cohortUnion rate rewards C_star C_h s hs x i
      (s + (m.val + 1)) (AffineBatchDecoder.quota p) hsa haT other hD

/-- Read a coordinate from the actual physical prefix whose post-cut drop
is the collection list. This preserves the record, not merely its date. -/
theorem record_eq_of_run_drop
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s c count : ℕ) (span : s + (c + count) ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial s)
    (K : List (ReferenceFollowerDownDecoderReplay.Record p rate))
    (hdrop : (ReferenceActivePhysicalHorizon.run initial rows selected rewards s
      (c + count) span active).records.drop c = K.take count)
    (b : Fin K.length) (hb : b.val < count) :
    K.get b = ReferenceAssignmentPayloadChronology.actualRunRecordAt
      initial rows selected rewards s (c + b.val) (by omega) active := by
  have heq := congrArg (fun records => records[b.val]?) hdrop
  rw [List.getElem?_drop, List.getElem?_take_of_lt hb,
    List.getElem?_eq_getElem b.isLt] at heq
  have hindex : c + b.val <
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards s
        (c + count) span active).records.length := by
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    omega
  rw [List.getElem?_eq_getElem hindex] at heq
  exact (Option.some.inj heq).symm.trans
    (ReferenceLocalReleaseGateChronology.run_record_at initial rows selected rewards
      s active (c + count) span ⟨c + b.val, by omega⟩)

/-- The first replacement's literal OLD threshold, with only its actual second
pure ambiguity arm transported to the original-source flags and fresh cohort.
The call, mixed and pure banks, recovery from the original queue, and all
exceptional branches are exactly those produced by the admitted threshold root. -/
theorem complete_first_replacement_collection_old_down_threshold_source_transport
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    ∀ control0 : ContinuousLearningRows.TimeControl p,
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.input.state (K.take j)
            let M := fun i => payload.downRecord i
            ∃ initial : ReferenceActivePhysicalStep.State p rate,
              ∃ active : ReferenceActivePhysicalHorizon.allActiveAtStart initial s,
              ReferenceCorrectedInitializationLaunch.correctedLaunch
                rate source rewards C_star C_h = some initial ∧
              ReferenceFollowerDecoderChronology.downBatchSeed initial s ∧
              ∀ i : Fin (p.m - 1),
                ∃ (base : ReferencePrelaunchFollower.State p rate.eta)
                  (baseMemory : ActiveFollowerLifecycle.LocalMemory p)
                  (span0 : s + c ≤ p.T),
                (Z 0).followers i = .ordinary base baseMemory ∧
                (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s c span0 active
                  ).finalState.followers i = .ordinary base baseMemory ∧
                ReferenceFollowerDecoderChronology.downBatchEndpoint base (s + c) ∧
                (base.lastDown = some (M i) → ∀ j : ℕ, j ≤ K.length →
                  oldDownCount K j i (M i) = 0) ∧
                ∀ j : ℕ, j ≤ K.length →
                  let Q := AffineBatchDecoder.quota p
                  let need := (Q - base.downBatch.pending.length) + Q
                  let M := M i
                  need ≤ 2 * Q ∧
                  (oldDownCount K j i M < need ∨
                    ∃ a : Fin K.length, a.val < j ∧
                      oldDownCount K (a.val + 1) i M = need ∧
                      (∀ b : ℕ, b ≤ a.val → oldDownCount K b i M < need) ∧
                      oldDownServiceAt K i M a ∧
                      (ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt
                        (K.get a) ∨
                        ((∀ r ∈ K.take (a.val + 1),
                          ¬ ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt r) ∧
                        (∀ b : Fin K.length, b.val ≤ a.val → actualOldAt (K.get b) i M) ∧
                        (ReferenceFollowerDownDecoderReplay.actualDownPositives i
                          (K.take (a.val + 1))).length = need ∧
                        (∀ b : Fin K.length, b.val ≤ a.val →
                          ActiveFollowerDownAcceptance.downSelected p i
                            (K.get b).input.row (K.get b).input.time →
                          ∃ (state : ReferencePrelaunchFollower.State p rate.eta)
                            (memory : ActiveFollowerLifecycle.LocalMemory p)
                            (diag : ReferenceDownReception.ReferenceDownCutOutput p rate),
                            (ReferenceFollowerFixedReply.actualChoice (K.get b) i).configuration =
                              .ordinary state memory ∧
                            ((K.get b).output.followers i).downInput = some state ∧
                            ((K.get b).output.followers i).down = some diag ∧
                            diag.rawComparison.isSome = true ∧
                            let input := ActiveFollowerDownAcceptance.currentRoundInput p i
                              (K.get b).input.row (K.get b).input.time
                              (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (K.get b) i)
                              rate state
                            ReferenceFollowerDownDecoderReplay.actualDownCall i (K.get b) =
                              some ((K.get b).input.time, input) ∧
                            input.selected = true ∧ input.receiverEnabled = true ∧
                            input.sample = ReferenceDownPhysicalHashRule.originalDownSample (K.get b).input ∧
                            ReferenceActiveAffinePositiveTest.downSent (K.get b).input =
                              some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
                            ReferenceDownReception.ordinaryLocalAcceptanceTest p rate
                              (K.get b).input.time state
                              (ReferenceDownReception.ordinaryParse p rate
                                (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)))) ∧
                        (∃ d : Fin K.length, d.val < a.val ∧
                          (K.get d).input.time.val < (K.get a).input.time.val ∧
                          oldDownCount K (d.val + 1) i M = Q - base.downBatch.pending.length ∧
                          (∀ k : ℕ, k ≤ d.val →
                            oldDownCount K k i M < Q - base.downBatch.pending.length) ∧
                          ∃ (firstState : ReferencePrelaunchFollower.State p rate.eta)
                            (firstDiag : ReferenceDownReception.ReferenceDownCutOutput p rate)
                            (reset : ReferencePrelaunchFollower.State p rate.eta)
                            (resetMemory : ActiveFollowerLifecycle.LocalMemory p),
                            let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i
                              (K.take (a.val + 1))
                            let first := base.downBatch.pending ++
                              P.take (Q - base.downBatch.pending.length)
                            ReferenceFollowerDownDecoderReplay.actualDownPositives i
                              (K.take (d.val + 1)) = P.take (Q - base.downBatch.pending.length) ∧
                            firstState.downBatch =
                              ⟨base.downBatch.pending ++ ReferenceFollowerDownDecoderReplay.actualDownPositives i
                                (K.take d.val), base.downBatch.completed⟩ ∧
                            ((K.get d).output.followers i).downInput = some firstState ∧
                            ((K.get d).output.followers i).down = some firstDiag ∧
                            firstDiag.rawComparison.isSome = true ∧
                            ReferenceFirstLiveDownCompletionReadout.completedDownBatch
                              (K.get d) i = some first ∧
                            firstDiag.raw = AffineBatchDecoder.batchOutput first ∧
                            (ActiveFollowerDownAcceptance.currentDecodeStep p i
                              (K.get d).input.row (K.get d).input.time
                              (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (K.get d) i)
                              rate firstState).1 = ⟨[], base.downBatch.completed ++ [first]⟩ ∧
                            (Z (d.val + 1)).followers i = .ordinary reset resetMemory ∧
                            reset.downBatch = ⟨[], base.downBatch.completed ++ [first]⟩) ∧
                        ∃ (endpoint : ReferencePrelaunchFollower.State p rate.eta)
                          (memory : ActiveFollowerLifecycle.LocalMemory p)
                          (span : s + (c + (a.val + 1)) ≤ p.T),
                          (Z (a.val + 1)).followers i = .ordinary endpoint memory ∧
                          (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                            (c + (a.val + 1)) span active).records.drop c = K.take (a.val + 1) ∧
                          (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                            (c + (a.val + 1)) span active).finalState = Z (a.val + 1) ∧
                          let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i
                            (K.take (a.val + 1))
                          let first := base.downBatch.pending ++
                            P.take (Q - base.downBatch.pending.length)
                          let pure := P.drop (Q - base.downBatch.pending.length)
                          endpoint.downBatch = ⟨[], base.downBatch.completed ++ [first, pure]⟩ ∧
                          first.length = Q ∧ pure.length = Q ∧
                          pure.Pairwise (fun x y => x.time.val < y.time.val) ∧
                          (∀ e ∈ base.downBatch.pending, e ∉ pure) ∧
                          (∀ e ∈ P, s + c ≤ e.time.val ∧
                            e.time.val < s + c + (a.val + 1)) ∧
                          ∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
                            (diag : ReferenceDownReception.ReferenceDownCutOutput p rate),
                            ((K.get a).output.followers i).downInput = some logged ∧
                            ((K.get a).output.followers i).down = some diag ∧
                            diag.rawComparison.isSome = true ∧
                            ReferenceFirstLiveDownCompletionReadout.completedDownBatch
                              (K.get a) i = some pure ∧
                            diag.raw = AffineBatchDecoder.batchOutput pure ∧
                            (ActiveFollowerDownAcceptance.currentDecodeStep p i
                              (K.get a).input.row (K.get a).input.time
                              (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (K.get a) i)
                              rate logged).1 = ⟨[], base.downBatch.completed ++ [first, pure]⟩ ∧
                            AffineBatchDecoder.satisfies (AffineBatchDecoder.samples pure)
                              (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
                            (AffineBatchDecoder.batchOutput pure =
                                some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∨
                              (AffineBatchDecoder.batchOutput pure = none ∧
                                ReferenceFirstLiveDownCompletionReadout.multipleSolutions pure ∧
                                ∃ other,
                                  CoordinatorLocalArmChoice.storedDownFlatWord payload i ≠ other ∧
                                  AffineBatchDecoder.satisfies (AffineBatchDecoder.samples pure) other ∧
                                  ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
                                    (K.get a).input.time source = some (K.get a) ∧
                                  ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag
                                    s (K.get a) = true ∧
                                  (∃ hn : (K.get a).input.time.val + 1 ≤ p.T,
                                    ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag
                                      rate rewards C_star C_h s ((K.get a).input.time.val + 1)
                                      hn source = true) ∧
                                  source ∈ ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
                                    rate rewards C_star C_h control0 Q ∧
                                  ∃ (hs : s < p.T)
                                    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource
                                      rate rewards C_star C_h s hs), x.val = source ∧
                                    let Y := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
                                      rate rewards C_star C_h s hs x
                                    let O := ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
                                      rate rewards C_star C_h s hs i x
                                    let Rk := fun k : Fin (p.T - s) =>
                                      (⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput
                                          s k.val (by omega) Y,
                                        ReferenceActivePhysicalStep.step
                                          (ReferenceDownCompletedAmbiguityMeasurability.prefixInput
                                            s k.val (by omega) Y), rfl⟩ :
                                        ReferenceFollowerDownDecoderReplay.Record p rate)
                                    ∃ n m : Fin (p.T - s), n.val = c + a.val ∧ m < n ∧
                                      ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate (O.2 m) ∧
                                      (∀ k : Fin (p.T - s), k < n →
                                        ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
                                          (O.2 k) → k ≤ m) ∧
                                      (∀ m' : Fin (p.T - s), m' < n →
                                        ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
                                          (O.2 m') →
                                        (∀ k : Fin (p.T - s), k < n →
                                          ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
                                            (O.2 k) → k ≤ m') → m' = m) ∧
                                      ∃ (hsa : s < s + (m.val + 1))
                                        (haT : s + (m.val + 1) < p.T),
                                        s + (m.val + 1) ≤ (K.get a).input.time.val ∧
                                        ReferenceGeneratedDownBatchCalendar.generatedSourceBatchBoundary
                                          rate rewards C_star C_h s hs i (s + (m.val + 1)) hsa haT x ∧
                                        (∃ reset resetMemory,
                                          (ReferenceActiveHorizonMeasurability.runOfInput
                                            s (m.val + 1) (by omega) Y).finalState.followers i =
                                              .ordinary reset resetMemory ∧ reset.downBatch.pending = []) ∧
                                        let tests := ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
                                          rate rewards C_star C_h s hs i (s + (m.val + 1)) x
                                        tests.map ReferenceGeneratedDownPrefixList.stampedTest = pure ∧
                                        tests.length = Q ∧
                                        (∀ test ∈ tests, ∃ k : Fin (p.T - s), m < k ∧ k ≤ n ∧
                                          ReferenceGeneratedDownBatchCalendar.executedTestOfRound
                                            rate (O.2 k) = some test ∧
                                          test.time = (Rk k).input.time ∧
                                          test.sample = ((Rk k).input.row.2 (Rk k).input.time).2 (0, i) ∧
                                          test.sent = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
                                          ReferenceGeneratedDownBatchCalendar.ExecutedTest.good other test) ∧
                                        ReferenceGeneratedDownBatchCalendar.generatedDownD rate rewards C_star C_h
                                          s Q hs i (s + (m.val + 1)) hsa haT other x)) ∧
                            (AffineBatchDecoder.batchOutput pure =
                                some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) →
                              ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get a) i M ∧
                              ∃ (accepted : OrdinaryMessageCodec.acceptDown
                                  (ReferencePrelaunchFollower.codecParams p rate.eta)
                                  (ReferencePrelaunchFollower.acceptedStart logged)
                                  ((K.get a).input.time.val + 1) M)
                                (recovered : ActiveFollowerDownAcceptance.ReplayRegisters)
                                (post : ReferencePrelaunchFollower.State p rate.eta)
                                (memory : ActiveFollowerLifecycle.LocalMemory p),
                                let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M
                                  (K.get a).input.time (ActiveFollowerDownAcceptance.acceptedDownStartLE
                                    p rate M (K.get a).input.time logged accepted) (K.get a).input.row
                                scan.endpoint = cut.input.time.val + 1 ∧
                                ActiveFollowerDownAcceptance.checkedRecovery p rate M logged
                                  (cut.input.time.val + 1) = .ok recovered ∧
                                recovered.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
                                  (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
                                    (cut.input.time.val + 1)) ∧
                                (∀ k : ℕ, ∃ middle,
                                  ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p)
                                    (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩
                                    ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
                                      (cut.input.time.val + 1)).take k) = .ok middle ∧
                                  middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
                                    ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
                                      (cut.input.time.val + 1)).take k)) ∧
                                post.lastDown = some M ∧ post.status = .unoccupied ∧ post.buffer = [] ∧
                                post.downBatch = ⟨[], base.downBatch.completed ++ [first, pure]⟩ ∧
                                diag.raw = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
                                diag.outcome = .accepted logged post
                                  (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)) M scan
                                  recovered.registers recovered.lastService ∧
                                (K.get a).output.followers i =
                                  ⟨.ordinary post memory, none, some logged, some diag⟩ ∧
                                (K.get a).output.next.followers i = .ordinary post memory ∧
                                (Z (a.val + 1)).followers i = .ordinary post memory))))
          | _ => True
      | _ => True := by
  classical
  intro control0
  have hSource := complete_first_replacement_collection_old_down_threshold_banks
    rate source rewards C_star C_h
  dsimp only at hSource ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set J := ActualInitializationPhysicalStep.selectedRowIndex p source
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    rw [hb] at hSource
    dsimp only at hSource ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      rw [hbirth] at hSource
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hSource ⊢
      let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        rw [hc] at hSource
        dsimp only at hSource ⊢
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          rw [hcut] at hSource
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only [ReferenceActivePhysicalStep.collectionInput] at hSource ⊢
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          obtain ⟨initial, active, hlaunch, hseed, hfollowers⟩ := hSource
          refine ⟨initial, active, hlaunch, hseed, ?_⟩
          intro i
          obtain ⟨base0, baseMemory0, span0, hbase0, hrun0, hend0, hretained, hqueries⟩ :=
            hfollowers i
          refine ⟨base0, baseMemory0, span0, hbase0, hrun0, hend0, hretained, ?_⟩
          intro j hj
          obtain ⟨hneed, hcase⟩ := hqueries j hj
          refine ⟨hneed, ?_⟩
          rcases hcase with hsmall | ⟨a, haj, hat, hbefore, hservice, hcases⟩
          · exact Or.inl hsmall
          · refine Or.inr ⟨a, haj, hat, hbefore, hservice, ?_⟩
            rcases hcases with hfailure | hnonfailure
            · exact Or.inl hfailure
            · rcases hnonfailure with ⟨hnof, hOld, hcount, hsender, hfirst, hsecond⟩
              refine Or.inr ⟨hnof, hOld, hcount, hsender, hfirst, ?_⟩
              rcases hsecond with
                ⟨endpoint, memory, span, hendpoint, hdrop, hfinal, hbank,
                  hfirstLength, hpureLength, hpureChron, hdisjoint, hdates,
                  logged, diag, hlogged, hdiag, hcalled, hcompleted, hraw,
                  hdecoded, hsatisfies, hsolver, haccept⟩
              refine ⟨endpoint, memory, span, hendpoint, hdrop, hfinal, hbank,
                hfirstLength, hpureLength, hpureChron, hdisjoint, hdates,
                logged, diag, hlogged, hdiag, hcalled, hcompleted, hraw,
                hdecoded, hsatisfies, ?_, haccept⟩
              rcases hsolver with hsuccess | ⟨hnone, hmultiple, other, hne, hsolution⟩
              · exact Or.inl hsuccess
              · refine Or.inr ⟨hnone, hmultiple, other, hne, hsolution, ?_⟩
                let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i
                  (K.take (a.val + 1))
                let pure := P.drop (AffineBatchDecoder.quota p - base0.downBatch.pending.length)
                have hsT : s < p.T := by
                  have ha := a.isLt
                  omega
                have hcross :=
                  (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
                    rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
                let x : ReferenceGeneratedDownBatchCalendar.LaunchSource
                    rate rewards C_star C_h s hsT := ⟨source, hcross, rfl⟩
                have hseedEq : ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
                    rate rewards C_star C_h s hsT x = initial :=
                  Option.some.inj
                    ((ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
                      rate rewards C_star C_h s hsT x).1.symm.trans hlaunch)
                let Y := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
                  rate rewards C_star C_h s hsT x
                let O := ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
                  rate rewards C_star C_h s hsT i x
                let Rk := fun k : Fin (p.T - s) =>
                  (⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput
                      s k.val (by omega) Y,
                    ReferenceActivePhysicalStep.step
                      (ReferenceDownCompletedAmbiguityMeasurability.prefixInput
                        s k.val (by omega) Y), rfl⟩ :
                    ReferenceFollowerDownDecoderReplay.Record p rate)
                let n : Fin (p.T - s) := ⟨c + a.val, by omega⟩
                have hrecordEq (b : Fin K.length) (hb : b.val ≤ a.val) :
                    K.get b = Rk ⟨c + b.val, by omega⟩ := by
                  have hbEq := record_eq_of_run_drop initial source.1.2 J rewards
                    s c (a.val + 1) span active K hdrop b (by omega)
                  change K.get b = ReferenceAssignmentPayloadChronology.actualRunRecordAt
                    (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
                      rate rewards C_star C_h s hsT x) source.1.2 J rewards
                    s (c + b.val) (by omega)
                    (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
                      rate rewards C_star C_h s hsT x).2.1
                  simpa only [hseedEq] using hbEq
                have hdetectEq : K.get a = Rk n := hrecordEq a le_rfl
                have htime : (K.get a).input.time.val = s + (c + a.val) := by
                  rw [hdetectEq]
                  rfl
                have hactual : ReferenceSourcePrefixHistoryFiltration.actualRecord
                    rate rewards C_star C_h (K.get a).input.time source = some (K.get a) := by
                  have hlookup := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
                    rate rewards C_star C_h (K.get a).input.time source initial hlaunch
                    (by change s ≤ _; omega)
                  have hoffset : (K.get a).input.time.val -
                      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h =
                      c + a.val := by change _ - s = _; omega
                  have hbEq := record_eq_of_run_drop initial source.1.2 J rewards
                    s c (a.val + 1) span active K hdrop a (by omega)
                  have hlookup' : ReferenceSourcePrefixHistoryFiltration.actualRecord
                      rate rewards C_star C_h (K.get a).input.time source =
                      some (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial
                        source.1.2 J rewards s (c + a.val) (by omega) active) := by
                    simpa only [hoffset] using hlookup
                  exact hlookup'.trans (congrArg some hbEq.symm)
                have hamb : ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart
                    s (K.get a) i := by
                  refine ⟨pure, hcompleted, ?_, hmultiple⟩
                  intro e he
                  have heP : e ∈ P := List.mem_of_mem_drop he
                  exact le_trans (Nat.le_add_right s c) (hdates e heP).1
                obtain ⟨hflag, hstrict⟩ := strictPastDecoderFlag_of_completed_ambiguity
                  rate rewards C_star C_h s source (K.get a) i hactual hamb
                obtain ⟨d, hda, _hdateD, _hatD, _hbeforeD, firstState, firstDiag,
                  reset, resetMemory, _hprefixD, _hfirstBank, _hfirstLogged,
                  _hfirstDiag, _hfirstCalled, hfirstCompleted, _hfirstRaw,
                  _hfirstDecoded, _hreset, _hresetBank⟩ := hfirst
                let d' : Fin (p.T - s) := ⟨c + d.val, by omega⟩
                have hdEq : K.get d = Rk d' := hrecordEq d (by omega)
                have hdComp : ReferenceGeneratedDownBatchCalendar.completedBatchAtRound
                    rate (O.2 d') := by
                  have hc := completedBatchAtRound_of_completedDownBatch
                    (K.get d) i _ hfirstCompleted
                  rw [hdEq] at hc
                  exact hc
                have hnBatch : ReferenceFirstLiveDownCompletionReadout.completedDownBatch
                    (Rk n) i = some pure := by rw [← hdetectEq]; exact hcompleted
                have hsend (k : Fin (p.T - s)) (hdk : d' < k) (hkn : k ≤ n)
                    (hselected : ActiveFollowerDownAcceptance.downSelected p i
                      (Rk k).input.row (Rk k).input.time) :
                    ReferenceActiveAffinePositiveTest.downSent (Rk k).input =
                      some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) := by
                  have hkb : c ≤ k.val := by change c + d.val < k.val at hdk; omega
                  have hka : k.val - c ≤ a.val := by
                    change k.val ≤ c + a.val at hkn
                    omega
                  have haK : a.val < K.length := a.isLt
                  let b : Fin K.length := ⟨k.val - c, by omega⟩
                  have heq : K.get b = Rk k := by
                    have hb := hrecordEq b hka
                    have hidx : (⟨c + b.val, by dsimp only [b]; omega⟩ :
                        Fin (p.T - s)) = k := by
                      apply Fin.ext
                      dsimp only [b]
                      omega
                    simpa only [hidx] using hb
                  have hs : ActiveFollowerDownAcceptance.downSelected p i
                      (K.get b).input.row (K.get b).input.time := by rw [heq]; exact hselected
                  obtain ⟨state, stateMemory, cutDiag, _hchoice, _hlog, _hdiag,
                    _hcalled, _hcall, _hsel, _henabled, _hsample, hsent, _haccept⟩ :=
                    hsender b hka hs
                  change ReferenceActiveAffinePositiveTest.downSent (K.get b).input =
                    some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) at hsent
                  rw [heq] at hsent
                  exact hsent
                obtain ⟨m, hmn, _hdm, hm, hgreatest, hunique, hsa, haT,
                  halphaN, hboundary, hresetA, hmap, hlength, htests, hD, hunion⟩ :=
                  generated_second_completion_transport rate rewards C_star C_h
                    s hsT x i d' n (CoordinatorLocalArmChoice.storedDownFlatWord payload i)
                    other pure (by change c + d.val < c + a.val; omega)
                    hdComp hnBatch hne hsolution hsend
                refine ⟨hactual, hflag, hstrict, hunion control0, hsT, x, rfl,
                  n, m, rfl, hmn, hm, hgreatest, hunique, hsa, haT, ?_,
                  hboundary, hresetA, hmap, hlength, htests, hD⟩
                change s + (m.val + 1) ≤ (K.get a).input.time.val
                rw [htime]
                exact halphaN

end Bandits.Support.ReferenceFirstReplacementCollectionOldDownThresholdSourceTransport
