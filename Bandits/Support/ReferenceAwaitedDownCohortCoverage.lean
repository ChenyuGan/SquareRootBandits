/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionAwaitedDownFailureReadout

/-!
# Actual fixed-awaited DOWN ambiguity and the joint cohort event

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-55`,
`appendix_a_local_protocol.tex:111-153`, `07_public_setup.tex:127-164`, and
`08_main_theorem.tex:29-42` in the same manuscript directory.

This is deterministic internal reference-execution mathematics. It retains the
original source, actual launch, stamped equations and inherited decoder bank.
It does not identify the manuscript ambiguity event or its overflow prefix.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceGeneratedDownBatchCalendar
open ReferenceFirstLiveDownCompletionReadout
open ReferenceFirstCollectionAwaitedDownFailureReadout
open ReferenceGeneratedInheritedDownCompletion
open ReferenceGeneratedInheritedDownCohort
open ReferenceGeneratedInheritedDownPrefixMarker
open scoped Classical

namespace Bandits.Support.ReferenceAwaitedDownCohortCoverage

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)

private abbrev canonicalRecord (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs) (n : Fin (p.T - s)) :
    ReferenceFollowerDownDecoderReplay.Record p rate :=
  let input := ReferenceDownCompletedAmbiguityMeasurability.prefixInput s n.val (by omega)
    (generatedSourceRunInput rate rewards C_star C_h s hs x)
  ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩

private theorem canonicalRecord_time (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs) (n : Fin (p.T - s)) :
    (canonicalRecord rate rewards C_star C_h s hs x n).input.time.val = s + n.val := rfl

private theorem actualRunRecordAt_eq_canonical (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs) (n : Fin (p.T - s))
    (start index : ℕ) (hstart : start = s) (hindex : index = n.val)
    (hspan : start + (index + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart
      (generatedSourceSeed rate rewards C_star C_h s hs x) start) :
    ReferenceAssignmentPayloadChronology.actualRunRecordAt
      (generatedSourceSeed rate rewards C_star C_h s hs x) x.val.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards
      start index hspan hmode = canonicalRecord rate rewards C_star C_h s hs x n := by
  subst start
  subst index
  rfl

private theorem actualRecord_eq_canonical (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs) (n : Fin (p.T - s)) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      ⟨s + n.val, by omega⟩ x.val =
        some (canonicalRecord rate rewards C_star C_h s hs x n) := by
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate x.val
      rewards C_star C_h = s := x.property.2
  have hlaunch := (generatedSourceSeed_spec rate rewards C_star C_h s hs x).1
  have hrec := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h ⟨s + n.val, by omega⟩ x.val _ hlaunch (by
      change ReferenceCompletePhysicalHistory.physicalStart rate x.val
        rewards C_star C_h ≤ s + n.val
      rw [hstart]
      omega)
  have hindex : (s + n.val) - ReferenceCompletePhysicalHistory.physicalStart
      rate x.val rewards C_star C_h = n.val := by
    rw [hstart]
    omega
  refine hrec.trans (congrArg some ?_)
  exact actualRunRecordAt_eq_canonical rate rewards C_star C_h s hs x n _ _
    hstart hindex _ _

private theorem alternative_solution
    (W : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (M : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hmultiple : multipleSolutions W) :
    ∃ w : AffineChannelLaw.Word (AffineBatchDecoder.width p),
      w ≠ M ∧ ∀ e ∈ W, AffineBatchDecoder.equation e.sample w := by
  obtain ⟨u, v, hu, hv, huv⟩ := (multipleSolutions_iff W).mp hmultiple
  by_cases huM : u = M
  · refine ⟨v, ?_, (AffineBatchDecoder.satisfies_samples_iff W v).mp hv⟩
    intro hvM
    exact huv (huM.trans hvM.symm)
  · exact ⟨u, huM, (AffineBatchDecoder.satisfies_samples_iff W u).mp hu⟩

private theorem executed_sent_of_awaited
    (r : ReferenceFollowerDownDecoderReplay.Record p rate) (i : Fin (p.m - 1))
    (M : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (test : ExecutedTest p)
    (hawait : awaitedDownAt rate r i M)
    (htest : executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation r.input i) =
        some test) : test.sent = some M := by
  obtain ⟨logged, cut, hlogged, hcut, _, hexpected, _⟩ := hawait
  have hdiagnostic :=
    ReferenceGeneratedDownBatchBankBridge.roundDownObservation_diagnostics_eq_actual r i
  unfold executedTestOfRound at htest
  dsimp only at htest
  rw [hdiagnostic, hcut, Option.map_some] at htest
  cases hcall : (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
      r.input i).2.2.1 with
  | none => simp only [hcall] at htest; cases htest
  | some call =>
      simp only [hcall] at htest
      split at htest
      next hpositive =>
        have heq := Option.some.inj htest
        exact (congrArg ExecutedTest.sent heq).symm.trans hexpected
      next hnegative => cases htest

private theorem generated_test_good
    (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs) (i : Fin (p.m - 1))
    (W : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (M w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hne : w ≠ M)
    (hsolution : ∀ e ∈ W, AffineBatchDecoder.equation e.sample w)
    (hentries : ∀ e ∈ W, ∃ re : ReferenceFollowerDownDecoderReplay.Record p rate,
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        e.time x.val = some re ∧ awaitedDownAt rate re i M)
    (n : Fin (p.T - s)) (test : ExecutedTest p)
    (htest : executedTestOfRound rate
      ((generatedSourceObservation rate rewards C_star C_h s hs i x).2 n) = some test)
    (hmem : ReferenceGeneratedPrelaunchDownCohort.testEntry test ∈ W) :
    ExecutedTest.good w test := by
  have htime := inheritedDownCurrentTest_time rewards C_star C_h s hs i x n test htest
  obtain ⟨re, hre, hawait⟩ := hentries _ hmem
  have hfin : test.time = (⟨s + n.val, by omega⟩ : Fin p.T) := Fin.ext htime
  change ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
    test.time x.val = some re at hre
  rw [hfin, actualRecord_eq_canonical rate rewards C_star C_h s hs x n] at hre
  have heq : canonicalRecord rate rewards C_star C_h s hs x n = re :=
    Option.some.inj hre
  have hawait' : awaitedDownAt rate
      (canonicalRecord rate rewards C_star C_h s hs x n) i M := heq.symm ▸ hawait
  have htest' : executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
        (canonicalRecord rate rewards C_star C_h s hs x n).input i) = some test := htest
  have hsent : test.sent = some M :=
    executed_sent_of_awaited rate
      (canonicalRecord rate rewards C_star C_h s hs x n) i M test hawait' htest'
  refine ⟨?_, ?_⟩
  · intro he
    exact hne (Option.some.inj (he.symm.trans hsent))
  · exact (AffineBatchDecoder.equation_iff_affineHash test.sample w).mp
      (hsolution _ hmem)

private theorem completed_bank_eq
    (r : ReferenceFollowerDownDecoderReplay.Record p rate) (i : Fin (p.m - 1))
    (W : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (call : ReferenceFollowerDownDecoderReplay.Call p)
    (hW : completedDownBatch r i = some W)
    (hlogged : (r.output.followers i).downInput = some logged)
    (hcut : (r.output.followers i).down = some cut)
    (hcomparison : cut.rawComparison.isSome = true)
    (hpositive : 0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i).val.val)
    (hcall : ReferenceFollowerDownDecoderReplay.actualDownCall i r = some call) :
    W = logged.downBatch.pending ++ [⟨r.input.time, call.2.sample⟩] := by
  obtain ⟨_, actualLogged, actualCut, hactualLogged, _, _, hbank, _, _⟩ :=
    completedDownBatch_spec r i W hW
  have hsame : actualLogged = logged :=
    Option.some.inj (hactualLogged.symm.trans hlogged)
  have hbank' : W = appendedDownBatch r i logged := hsame ▸ hbank
  have hfields := retained_call_fields r i logged cut hlogged hcut hcomparison
  let tr := ActiveFollowerDownAcceptance.currentInputExtension p
    (ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate logged)
  have heligible : AffineBatchDecoder.eligible (tr r.input.time) :=
    (ActiveFollowerDownAcceptance.currentRoundInput_eligible_iff p i r.input.row
      r.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i)
      rate logged).2 ⟨hfields.1, hfields.2.1, hpositive⟩
  have hsample :=
    (ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields r i call hcall).2.1
  calc
    W = appendedDownBatch r i logged := hbank'
    _ = logged.downBatch.pending ++
        [⟨r.input.time, (r.input.row.2 r.input.time).2 (0, i)⟩] := by
      change logged.downBatch.pending ++ AffineBatchDecoder.positiveAt p tr r.input.time = _
      rw [AffineBatchDecoder.positiveAt, ite_eq_left heligible]
      rfl
    _ = logged.downBatch.pending ++ [⟨r.input.time, call.2.sample⟩] := by rw [hsample]

private theorem later_completion_coverage
    (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs) (i : Fin (p.m - 1))
    (n : Fin (p.T - s))
    (W : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (M w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (control0 : ContinuousLearningRows.TimeControl p)
    (hne : w ≠ M)
    (hsolution : ∀ e ∈ W, AffineBatchDecoder.equation e.sample w)
    (hentries : ∀ e ∈ W, ∃ re : ReferenceFollowerDownDecoderReplay.Record p rate,
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        e.time x.val = some re ∧ awaitedDownAt rate re i M)
    (hW : completedDownBatch (canonicalRecord rate rewards C_star C_h s hs x n) i = some W)
    (hcomplete : completedBatchAtRound rate
      ((generatedSourceObservation rate rewards C_star C_h s hs i x).2 n)) :
    (∀ k : Fin (p.T - s), k < n → ¬ completedBatchAtRound rate
      ((generatedSourceObservation rate rewards C_star C_h s hs i x).2 k)) ∨
    x.val ∈ ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
      rate rewards C_star C_h control0 (AffineBatchDecoder.quota p) := by
  have hdetector :=
    ReferenceGeneratedDownLaterCompletionDetector.generated_down_later_completion_detector_of_good
      rate rewards C_star C_h s hs x i n w control0 hcomplete
  dsimp only at hdetector
  rcases hdetector with hfirst | ⟨m, _, _, _, _, _, hlater⟩
  · exact Or.inl hfirst
  · rcases hlater with ⟨_, _, _, _, _, callCode, logged, cut, testN,
      _, hactual, hlogged, hcut, hcomparison, hpositive, _, _, hlistFacts⟩
    rcases hlistFacts with ⟨_, _, _, _, hbank, _, _, hprovenance, hgoodDetector⟩
    right
    apply (hgoodDetector ?_).2
    intro test hmem
    have hbankW := (completed_bank_eq rate _ i W logged cut _ hW hlogged hcut
      hcomparison hpositive hactual).trans hbank
    have hentry : ReferenceGeneratedPrelaunchDownCohort.testEntry test ∈ W := by
      rw [hbankW]
      exact List.mem_map.mpr ⟨test, hmem, rfl⟩
    obtain ⟨k, _, _, htest, _⟩ := hprovenance test hmem
    exact generated_test_good rate rewards C_star C_h s hs x i W M w hne hsolution
      hentries k test htest hentry

private theorem record_eq_of_input
    (r r' : ReferenceFollowerDownDecoderReplay.Record p rate)
    (hinput : r.input = r'.input) : r = r' := by
  rcases r with ⟨input, output, houtput⟩
  rcases r' with ⟨input', output', houtput'⟩
  dsimp only at hinput
  subst input'
  subst output
  subst output'
  rfl

private theorem generated_prefix_test_offset
    (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs) (i : Fin (p.m - 1))
    (n : ℕ) (test : ExecutedTest p)
    (hmem : test ∈ generatedInheritedDownTests rate rewards C_star C_h s hs i x n) :
    ∃ k : Fin (p.T - s), executedTestOfRound rate
      ((generatedSourceObservation rate rewards C_star C_h s hs i x).2 k) = some test := by
  obtain ⟨round, hround, htest⟩ := List.mem_filterMap.mp hmem
  obtain ⟨k, hk⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hround)
  exact ⟨k, hk ▸ htest⟩

private theorem canonical_selector_of_selected
    (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs) (i : Fin (p.m - 1))
    (n : Fin (p.T - s))
    (hselected : ActiveFollowerDownAcceptance.downSelected p i
      (canonicalRecord rate rewards C_star C_h s hs x n).input.row
      (canonicalRecord rate rewards C_star C_h s hs x n).input.time) :
    ReferenceSelectedAffinePairLaw.selector p ⟨s + n.val, by omega⟩ x.val =
      (ActualInitializationPhysicalStep.selectedRowIndex p x.val, some (0, i)) := by
  change PublicDiscreteDraws.slotDraw
      (((x.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x.val)).2
        ⟨s + n.val, by omega⟩).1) = PublicDiscreteDraws.downSlot ∧
    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (((x.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x.val)).2
        ⟨s + n.val, by omega⟩).1) = i at hselected
  change (_, ReferenceSelectedAffinePairLaw.selectedChannel p _) = _
  rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_down p _ hselected.1, hselected.2]
  rfl

private theorem first_completion_coverage
    (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs) (i : Fin (p.m - 1))
    (n : Fin (p.T - s))
    (W : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (M w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (control0 : ContinuousLearningRows.TimeControl p)
    (hne : w ≠ M)
    (hsolution : ∀ e ∈ W, AffineBatchDecoder.equation e.sample w)
    (hentries : ∀ e ∈ W, ∃ re : ReferenceFollowerDownDecoderReplay.Record p rate,
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        e.time x.val = some re ∧ awaitedDownAt rate re i M)
    (hW : completedDownBatch (canonicalRecord rate rewards C_star C_h s hs x n) i = some W)
    (hcomplete : completedBatchAtRound rate
      ((generatedSourceObservation rate rewards C_star C_h s hs i x).2 n))
    (hfirst : ∀ k : Fin (p.T - s), k < n → ¬ completedBatchAtRound rate
      ((generatedSourceObservation rate rewards C_star C_h s hs i x).2 k)) :
    x.val ∈ ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
      rate rewards C_star C_h control0 (AffineBatchDecoder.quota p) := by
  have hfirst' : completedBatchAtRound rate
      ((generatedSourceObservation rate rewards C_star C_h s hs i x).2 n) ∧
      ∀ l (hl : l < n.val), ¬ completedBatchAtRound rate
        ((generatedSourceObservation rate rewards C_star C_h s hs i x).2
          ⟨l, lt_trans hl n.isLt⟩) :=
    ⟨hcomplete, fun l hl => hfirst ⟨l, lt_trans hl n.isLt⟩ hl⟩
  obtain ⟨record, callCode, loggedCode, cutCode, logged, cut,
      hinput, hcall, hactual, hlogged, hcut, _, _, _, _, hcomparison,
      hpositive, _, _, hpending, _, _, _⟩ :=
    generated_inherited_down_cohort_first_completion_bank
      rewards C_star C_h s hs x i n.val n.isLt hfirst'
  have hrecord : record = canonicalRecord rate rewards C_star C_h s hs x n :=
    record_eq_of_input rate record _ hinput
  have hWrecord : completedDownBatch record i = some W := hrecord.symm ▸ hW
  have hbank := completed_bank_eq rate record i W logged cut _ hWrecord
    hlogged hcut hcomparison hpositive hactual
  let testN : ExecutedTest p :=
    ⟨record.input.time, (record.input.row.2 record.input.time).2 (0, i), cut.expectedWord⟩
  have hcurrent : executedTestOfRound rate
      ((generatedSourceObservation rate rewards C_star C_h s hs i x).2 n) = some testN := by
    change executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
        (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s n.val (by omega)
          (generatedSourceRunInput rate rewards C_star C_h s hs x)) i) = some testN
    rw [← hinput]
    exact (ReferenceGeneratedDownBatchBankBridge.executedTestOfRound_eq_actual
      record i callCode logged cut hcall hlogged hcut hcomparison hpositive).1
  have hsample := (ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields
    record i _ hactual).2.1
  have htestEntry : ReferenceGeneratedPrelaunchDownCohort.testEntry testN =
      (⟨record.input.time,
        (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample⟩ :
          AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) := by
    change (⟨record.input.time, (record.input.row.2 record.input.time).2 (0, i)⟩ :
      AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) = _
    rw [hsample]
  have hold := generated_inherited_down_old_pending rewards C_star C_h s hs x i
  have hprefixMap :
      (inheritedDownPrefix rewards C_star C_h s hs i x n.val).map
        ReferenceGeneratedPrelaunchDownCohort.testEntry = logged.downBatch.pending := by
    rw [inheritedDownPrefix, List.map_append, hold.1]
    exact hpending.symm
  have hbankPrefix : W =
      (inheritedDownPrefix rewards C_star C_h s hs i x n.val ++ [testN]).map
        ReferenceGeneratedPrelaunchDownCohort.testEntry := by
    rw [List.map_append, List.map_cons, List.map_nil, hprefixMap, htestEntry]
    exact hbank
  have hentry : ∀ test ∈ inheritedDownPrefix rewards C_star C_h s hs i x n.val ++ [testN],
      ReferenceGeneratedPrelaunchDownCohort.testEntry test ∈ W := by
    intro test htest
    rw [hbankPrefix]
    exact List.mem_map.mpr ⟨test, htest, rfl⟩
  have hlength : (inheritedDownPrefix rewards C_star C_h s hs i x n.val).length =
      AffineBatchDecoder.quota p - 1 := by
    have h := (completedDownBatch_spec record i W hWrecord).1
    rw [hbankPrefix, List.length_map, List.length_append, List.length_singleton] at h
    omega
  obtain ⟨alpha, halpha, hbirth, holdBirth⟩ :=
    generated_inherited_down_old_test_birth rewards C_star C_h s hs x i
  have hgoodPrefix : ∀ test ∈ inheritedDownPrefix rewards C_star C_h s hs i x n.val,
      ExecutedTest.good w test := by
    intro test hmem
    have he : ReferenceGeneratedPrelaunchDownCohort.testEntry test ∈ W :=
      hentry test (List.mem_append_left _ hmem)
    rcases List.mem_append.mp hmem with holdMem | hnewMem
    · -- An old stamp precedes launch, whereas D requires an actual active
      -- record at every stamp. Keep the inherited bank and exclude this case.
      obtain ⟨re, hre, _⟩ := hentries _ he
      have hstart : ReferenceCompletePhysicalHistory.physicalStart rate x.val
          rewards C_star C_h = s := x.property.2
      have habsent := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
        rate rewards C_star C_h test.time x.val (by
          rw [hstart]
          exact (holdBirth test holdMem).2.1)
      change ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        test.time x.val = some re at hre
      rw [habsent] at hre
      cases hre
    · obtain ⟨k, htest⟩ := generated_prefix_test_offset rate rewards C_star C_h
        s hs x i n.val test hnewMem
      exact generated_test_good rate rewards C_star C_h s hs x i W M w hne
        hsolution hentries k test htest he
  have hgoodCurrent : ExecutedTest.good w testN :=
    generated_test_good rate rewards C_star C_h s hs x i W M w hne hsolution
      hentries n testN hcurrent (hentry testN (List.mem_append_right _ (by simp)))
  have hselected := (retained_call_fields record i logged cut hlogged hcut hcomparison).1
  have hselected' : ActiveFollowerDownAcceptance.downSelected p i
      (canonicalRecord rate rewards C_star C_h s hs x n).input.row
      (canonicalRecord rate rewards C_star C_h s hs x n).input.time := by
    rw [← hrecord]
    exact hselected
  have hselector := canonical_selector_of_selected rate rewards C_star C_h s hs x i n hselected'
  have hsampleSource : testN.sample =
      (((x.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x.val)).2
        ⟨s + n.val, by omega⟩).2 (0, i)) := by
    change (record.input.row.2 record.input.time).2 (0, i) = _
    rw [hinput]
    rfl
  let delta : ReferenceGeneratedInheritedDownPostlaunchOccurrence.Lambda p alpha :=
    ⟨(ActualInitializationPhysicalStep.selectedRowIndex p x.val,
      ⟨s, hs⟩, ⟨s + n.val, by omega⟩), halpha, by
        change s ≤ s + n.val
        omega⟩
  let k := (generatedInheritedInitialFollower rate rewards C_star C_h s hs x i).downBatch.completed.length
  have hQ : 1 ≤ AffineBatchDecoder.quota p := AffineBatchDecoder.quota_pos p
  have hpost : x.val ∈
      ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchHashedOccurrence
        rate rewards C_star C_h i alpha k (AffineBatchDecoder.quota p) (by omega)
          w hQ le_rfl control0 delta := by
    constructor
    · refine ⟨hselector, x, rfl, halpha, rfl, hbirth, ?_, ?_, testN, ?_, hgoodCurrent.1⟩
      · simpa only [delta, Nat.add_sub_cancel_left] using hlength
      · simpa only [delta, Nat.add_sub_cancel_left, ExecutedTest.good] using hgoodPrefix
      · simpa only [delta, Nat.add_sub_cancel_left] using hcurrent
    · exact hsampleSource ▸ hgoodCurrent.2
  have hmixed : x.val ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
      rate rewards C_star C_h i alpha k (by omega) w control0 (AffineBatchDecoder.quota p) := by
    rw [ReferenceGeneratedMixedDownPredecessor.mixedDownDetector_positive
      rate rewards C_star C_h i alpha k (AffineBatchDecoder.quota p) (by omega)
        w hQ le_rfl control0]
    exact Or.inr (Set.mem_iUnion.mpr ⟨delta, hpost⟩)
  have hbirthAt := ReferenceGeneratedDownCohortFiniteUnion.mixedDownDetector_subset_birthAt
    rate rewards C_star C_h i alpha k (by omega) w control0 (AffineBatchDecoder.quota p) hmixed
  have hk := ReferenceGeneratedDownCohortFiniteUnion.birthAt_ordinal_le
    rate rewards C_star C_h i alpha k (by omega) x.val hbirthAt
  change x.val ∈ ⋃ i : Fin (p.m - 1), ⋃ a : Fin p.T, ⋃ candidate,
    (⋃ j : Fin (a.val + 1), {z | z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
      rate rewards C_star C_h i a.val j.val a.isLt.le candidate control0
        (AffineBatchDecoder.quota p)}) ∪ _
  apply Set.mem_iUnion.mpr
  refine ⟨i, Set.mem_iUnion.mpr ⟨⟨alpha, by omega⟩, Set.mem_iUnion.mpr ⟨w, ?_⟩⟩⟩
  exact Or.inl (Set.mem_iUnion.mpr ⟨⟨k, by
    change k < alpha + 1
    omega⟩, hmixed⟩)

/-- Every literal actual fixed-awaited DOWN ambiguity is covered by the
already constructed joint mixed/fresh DOWN cohort event, on the same source.
The existential awaited word is chosen only pointwise in this deterministic
containment; no history measurability of that choice is asserted. -/
theorem fixedAwaitedDownFailureAt_mem_downCohortUnionEvent
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T)
    (hD : fixedAwaitedDownFailureAt rate rewards C_star C_h z t) :
    z ∈ ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
      rate rewards C_star C_h control0 (AffineBatchDecoder.quota p) := by
  obtain ⟨r, i, M, W, a, hr, hW, _, hmultiple, hentries, _⟩ := hD
  have hlaunchBy : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z := by
    by_contra hnone
    have habsent := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hnone
    change ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r at hr
    rw [habsent] at hr
    cases hr
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hst : s ≤ t.val := hlaunchBy.2
  have hs : s < p.T := hst.trans_lt t.isLt
  let x : LaunchSource rate rewards C_star C_h s hs := ⟨z, hlaunchBy.1, rfl⟩
  let n : Fin (p.T - s) := ⟨t.val - s, by omega⟩
  have htime : (⟨s + n.val, by omega⟩ : Fin p.T) = t := by
    apply Fin.ext
    change s + (t.val - s) = t.val
    omega
  have hrec := actualRecord_eq_canonical rate rewards C_star C_h s hs x n
  rw [htime] at hrec
  have heq : r = canonicalRecord rate rewards C_star C_h s hs x n :=
    Option.some.inj (hr.symm.trans hrec)
  have hWcanonical : completedDownBatch
      (canonicalRecord rate rewards C_star C_h s hs x n) i = some W := heq ▸ hW
  have hcomplete : completedBatchAtRound rate
      ((generatedSourceObservation rate rewards C_star C_h s hs i x).2 n) := by
    apply (ReferenceGeneratedDownResetCompletionCensus.completedBatchAtRound_iff_executed_quota
      (canonicalRecord rate rewards C_star C_h s hs x n) i).mpr
    obtain ⟨logged, cut, hlogged, hcut, hcomparison, hquota, _⟩ :=
      (completedDownBatch_eq_some_iff _ i W).mp hWcanonical
    exact ⟨logged, cut, hlogged, hcut, hcomparison, hquota⟩
  obtain ⟨w, hne, hsolution⟩ := alternative_solution W M hmultiple
  have hawaitedEntries : ∀ e ∈ W,
      ∃ re : ReferenceFollowerDownDecoderReplay.Record p rate,
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
          e.time x.val = some re ∧ awaitedDownAt rate re i M := by
    intro e he
    obtain ⟨_, _, _, re, hre, _, hawait⟩ := hentries e he
    exact ⟨re, hre, hawait⟩
  have hcoverage := later_completion_coverage rate rewards C_star C_h s hs x i n
    W M w control0 hne hsolution hawaitedEntries hWcanonical hcomplete
  rcases hcoverage with hfirst | hcovered
  · exact first_completion_coverage rate rewards C_star C_h s hs x i n
      W M w control0 hne hsolution hawaitedEntries hWcanonical hcomplete hfirst
  · exact hcovered

end Bandits.Support.ReferenceAwaitedDownCohortCoverage

end
