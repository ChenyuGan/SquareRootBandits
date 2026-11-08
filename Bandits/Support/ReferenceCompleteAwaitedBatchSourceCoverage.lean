/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteCompletedBankOriginalProvenance

import Lean.Elab.Tactic.Omega

/-!
# Original-source fixed-awaited completed-batch coverage

The public results below inspect actual initialization banks and exclude
fixed-sent prelaunch and inherited prelaunch entries. Original bank entries
are traced to their actual prelaunch test or postlaunch receiver call by the
accepted completed-bank provenance result.

The total physical window predicates below evaluate both initialization and
suffix dispatch. Their existential window endpoint is independent of an
earliest sender-fixation or batch-reset date. Every positive stamp and every
selected date in that window refers to the same original source.

These are deterministic internal characterizations.  They make no probability,
cutoff, queue, or regret claim and do not seal a manuscript source node.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open Bandits.Support.ReferenceLiteralSourceDecoderCoverage
open Bandits.Support.ReferenceCompleteCompletedBankOriginalProvenance
open Bandits.Support.ReferenceFollowerDownDecoderReplay
open Bandits.Support.ReferenceCoordinatorUpDecoderReplay
open Bandits.Support.ReferenceSelectedAffinePairLaw
open scoped Classical

namespace Bandits.Support.ReferenceCompleteAwaitedBatchSourceCoverage

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)

abbrev Source := BootstrapPrivateRoundStreams.SourceInput p
abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev Word := AffineChannelLaw.Word (AffineBatchDecoder.width p)
abbrev Batch := List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
abbrev Down := OrdinaryMessageCodec.DownRecord
  (ReferencePrelaunchFollower.codecParams p rate.eta)
abbrev Up := OrdinaryMessageCodec.UpRecord
  (ReferencePrelaunchFollower.codecParams p rate.eta)
abbrev Follower := Fin (p.m - 1)

private theorem downEntry_actualCall
    (r : Record (rate := rate)) (i : Follower (p := p))
    (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (he : e ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i [r]) :
    ∃ call : ReferenceFollowerDownDecoderReplay.Call p,
      ReferenceFollowerDownDecoderReplay.actualDownCall i r = some call ∧
      AffineBatchDecoder.eligible call.2 ∧
      e ∈ AffineBatchDecoder.positiveAt p
        (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1 := by
  classical
  obtain ⟨call, hcall, hentry⟩ := List.mem_flatMap.mp he
  obtain ⟨record, hrecord, hcall⟩ := List.mem_filterMap.mp hcall
  have hrecord' : record = r := List.mem_singleton.mp hrecord
  subst record
  have heligible : AffineBatchDecoder.eligible call.2 := by
    by_contra hbad
    simp only [AffineBatchDecoder.positiveAt,
      ActiveFollowerDownAcceptance.currentInputExtension, hbad,
      ite_false, List.not_mem_nil] at hentry
  exact ⟨call, hcall, heligible, hentry⟩

private theorem downEntry_equation_of_awaited
    (r : Record (rate := rate)) (i : Follower (p := p))
    (w : Word (p := p)) (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (he : e ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i [r])
    (hsent : ReferenceActiveAffinePositiveTest.downSent r.input = some w)
    (haw : ReferenceFirstCollectionAwaitedDownFailureReadout.awaitedDownAt
      rate r i w) :
    AffineBatchDecoder.equation e.sample w := by
  have hawFull := haw
  obtain ⟨logged, cut, hlogged, hcut, hcomparison, _, _⟩ := hawFull
  obtain ⟨call, hcall, heligible, hentry⟩ := downEntry_actualCall rate r i e he
  cases hconfiguration : ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration r i with
  | dagger =>
      simp [ReferenceFollowerDownDecoderReplay.actualDownCall,
        hconfiguration] at hcall
  | ordinary state memory =>
      have hactual := ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary
        r i state memory hconfiguration
      have hcallInput : call =
          (ReferenceFollowerDownDecoderReplay.preparedChoiceTime r i,
            ActiveFollowerDownAcceptance.currentRoundInput p i
              (ReferenceFollowerDownDecoderReplay.preparedChoiceRow r i)
              (ReferenceFollowerDownDecoderReplay.preparedChoiceTime r i)
              (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i)
              rate state) :=
        Option.some.inj (hcall.symm.trans hactual)
      have heligible' : AffineBatchDecoder.eligible
          (ActiveFollowerDownAcceptance.currentRoundInput p i
            (ReferenceFollowerDownDecoderReplay.preparedChoiceRow r i)
            (ReferenceFollowerDownDecoderReplay.preparedChoiceTime r i)
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i)
            rate state) := by
        simpa only [hcallInput] using heligible
      have hpositive :=
        (ReferenceFollowerDownDecoderReplay.actualDownCall_eligible_iff r i state).mp
          heligible'
      have hsample :=
        ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_sample_original_of_eligible
          r i call hcall heligible
      have heqEntry : e = AffineBatchDecoder.entry p
          (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1 := by
        simpa only [AffineBatchDecoder.positiveAt,
          ActiveFollowerDownAcceptance.currentInputExtension, heligible,
          ite_true, List.mem_singleton] using hentry
      have heqSample : e.sample =
          ReferenceDownPhysicalHashRule.originalDownSample r.input := by
        calc
          e.sample =
              (ActiveFollowerDownAcceptance.currentInputExtension p call.2 call.1).sample := by
            rw [heqEntry]
            rfl
          _ = call.2.sample := rfl
          _ = ReferenceDownPhysicalHashRule.originalDownSample r.input := hsample
      have hpositiveObservation :
          0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i).val.val :=
        hpositive.2.2
      have hEquation := ReferenceFirstLiveDownCompletionReadout.retained_positive_equation
        r i logged cut hlogged hcut hcomparison w hsent hpositiveObservation
      rw [heqSample]
      exact hEquation

private theorem upEntry_equation_of_awaited
    (r : Record (rate := rate)) (i : Follower (p := p))
    (M : Up (rate := rate))
    (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (he : e ∈ ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i)
    (haw : ReferenceLiteralSourceDecoderCoverage.physicalAwaitedUpAt r i M) :
    AffineBatchDecoder.equation e.sample
      (ReferenceCollectionUpFailureReadoutV2.enc rate M) := by
  have hsample :=
    ReferenceLiteralSourceDecoderCoverage.upPositiveEntry_original_coordinates
      r i e he |>.2
  have hpositive : ReferenceActiveAffinePositiveTest.upPositive r.input = true := by
    rw [ReferenceActiveAffinePositiveTest.record_upPositive]
    cases hdiag : r.output.coordinator.up with
    | none => simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hdiag] at he
    | some d =>
        have hselected :
            ReferenceCoordinatorUpDecoderReplay.retainedUpFollower d = i := by
          by_contra hne
          simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
            hdiag, hne] at he
        have hmem : e ∈ AffineBatchDecoder.positiveAt p
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
            (ReferenceCoordinatorUpDecoderReplay.retainedUpTime d) := by
          simpa [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
            hdiag, hselected] using he
        have heligible : AffineBatchDecoder.eligible
            (CoordinatorUpReception.roundInput d.input) := by
          unfold AffineBatchDecoder.positiveAt at hmem
          split at hmem
          · simpa [ReferenceCoordinatorUpDecoderReplay.constantInputTrace,
              ReferenceCoordinatorUpDecoderReplay.retainedUpTime] using ‹_›
          · simp at hmem
        simp [ReferenceActiveAffinePositiveTest.upDiagnosticPositive, heligible]
  obtain ⟨d, hd, hi, _, _, _, _, hsent, _, _, _⟩ := haw
  have hfields := ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields
    r d hd
  obtain ⟨_, _, _, _, _, _, hsender, _, _, _, _, _, _, _⟩ := hfields
  have hindex : ReferenceActivePhysicalStep.upSenderIndex r.input = i :=
    hsender.symm.trans hi
  have hhash := ReferenceUpPhysicalHashRule.upPositive_hash_one r.input
    (ReferenceCollectionUpFailureReadoutV2.enc rate M) hsent hpositive
  rw [hindex] at hhash
  apply (AffineBatchDecoder.equation_iff_affineHash _ _).mpr
  rw [hsample]
  exact hhash

private theorem actualRecord_start_le
    (z : Source (p := p)) (t : Fin p.T) (r : Record (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r) :
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val := by
  by_contra hnot
  have hlt : t.val <
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h :=
    Nat.lt_of_not_ge hnot
  simp [ReferenceSourcePrefixHistoryFiltration.actualRecord] at hr
  omega

private theorem sourcePrelaunchTest_beforeStart
    (z : Source (p := p)) (i : Follower (p := p))
    (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p)
    (htest : test ∈ ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
      rate rewards C_star C_h z i) :
    test.time.val <
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
  obtain ⟨a, _, _, hbefore, _⟩ :=
    ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_test_provenance
      rate rewards C_star C_h z i test htest
  simpa [ReferenceCompletePhysicalHistory.physicalStart,
    ReferenceCompletePhysicalHistory.generatedBoundary,
    ReferenceCompletePhysicalHistory.generatedInput,
    ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput] using hbefore

/-- The source prelaunch observer's prefix and actual current test cannot
form a completed fixed-sent-word batch. This retains the physical prelaunch
branch even though a different postlaunch Q-bank may be ambiguous. -/
private theorem originalSourcePrelaunchDown_no_fixed_word_completed_batch
    (z : Source (p := p)) (i : Follower (p := p)) (r : Fin p.T) :
    let tests := ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests
      rate rewards C_star C_h z i r ++
      (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_test
        rate rewards C_star C_h z i r).toList
    match ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
        rate rewards C_star C_h z i r with
    | .inl (.inl active) =>
        let x := ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
          rate rewards C_star C_h z
        let own := ReferenceInitializationRun.ownEntry
          (ReferenceInitializationRun.physical x active.val.1.val active.val.1.property.1)
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i)) r
        let bank := active.val.2.2.2.downBatch
        let B := bank.pending ++ AffineBatchDecoder.positiveAt p
          (ReferencePrelaunchFollower.traceAt i x.row active.val.2.1 r own) r
        ¬ ∃ batch, (batch ∈ bank.completed ∨ batch = B ∧
          B.length = AffineBatchDecoder.quota p) ∧
          ∃ w : AffineChannelLaw.Word (AffineBatchDecoder.width p), ∀ e ∈ batch,
            ∃ test ∈ tests,
              ReferenceGeneratedPrelaunchDownCohort.testEntry test = e ∧
                test.sent = some w
    | .inl (.inr _) => True
    | .inr stopped =>
        ¬ ∃ batch ∈ stopped.val.2.downBatch.completed,
          ∃ w : AffineChannelLaw.Word (AffineBatchDecoder.width p), ∀ e ∈ batch,
            ∃ test ∈ tests,
              ReferenceGeneratedPrelaunchDownCohort.testEntry test = e ∧
                test.sent = some w := by
  exact ReferencePrelaunchDownDecisionReadout.source_prelaunch_down_no_fixed_word_completed_batch
    rate rewards C_star C_h z i r

private theorem completedDownEntry_suffix_origin
    (z : Source (p := p)) (t : Fin p.T) (r : Record (rate := rate))
    (i : Follower (p := p)) (W : Batch (p := p))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (hcomplete : ReferenceLiteralSourceDecoderCoverage.physicalDownCompletedAt r i W)
    (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (he : e ∈ W)
    (hentryRecord : ∃ re : Record (rate := rate),
      ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h e.time z = some re) :
    ∃ re : Record (rate := rate),
      ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h e.time z = some re ∧
      e ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i [re] ∧
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤
        e.time.val := by
  have hcompleted :=
    (ReferenceLiteralAwaitedAmbiguityRowObservation.physicalDownCompletedAt_iff_completedDownBatch
      rate r i W).mp hcomplete
  have horigins :=
    ReferenceCompleteCompletedBankOriginalProvenance.completedDownBatch_original_entry_provenance
      rate rewards C_star C_h z t r i W hr hcompleted
  rcases horigins e he with hpre | hpost
  · obtain ⟨test, _, htestEntry, hbefore, hsentNone, _⟩ := hpre
    obtain ⟨re, hre⟩ := hentryRecord
    have htime : test.time = e.time := by
      have h := congrArg AffineBatchDecoder.Entry.time htestEntry
      simpa only [ReferenceGeneratedPrelaunchDownCohort.testEntry] using h
    have hfuture : e.time.val <
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
      rw [← htime]
      exact hbefore
    have hnone := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
      rate rewards C_star C_h e.time z hfuture
    rw [hre] at hnone
    cases hnone
  · obtain ⟨re, hrecord, hpositive, hstart, _, _, _, _, _, _, _⟩ := hpost
    exact ⟨re, hrecord, hpositive, hstart⟩

/-- The real prelaunch receiver bank, including stored completions and the
current quota completion. Inactive followers have no bank completion; stopped
initialization retains its ordinary completed banks. No launch reset is used. -/
def prelaunchDownCompletedBankAt (z : Source (p := p)) (i : Follower (p := p))
    (t : Fin p.T) (W : Batch (p := p)) : Prop :=
  match ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
      rate rewards C_star C_h z i t with
  | .inl (.inl active) =>
      let x := ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
        rate rewards C_star C_h z
      let own := ReferenceInitializationRun.ownEntry
        (ReferenceInitializationRun.physical x active.val.1.val active.val.1.property.1)
        (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ActualReferenceInitializationBlock.refFollower i)) t
      let bank := active.val.2.2.2.downBatch
      let B := bank.pending ++ AffineBatchDecoder.positiveAt p
        (ReferencePrelaunchFollower.traceAt i x.row active.val.2.1 t own) t
      W ∈ bank.completed ∨ W = B ∧ B.length = AffineBatchDecoder.quota p
  | .inl (.inr _) => False
  | .inr stopped => W ∈ stopped.val.2.downBatch.completed

private theorem prelaunchTest_entries
    (i : Follower (p := p)) (row : CompletePublicTable.CompleteRow p)
    (a : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (own : Fin p.K × ReferencePrelaunchFollower.Observation p) :
    ((ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i row a t own).toList.map
      ReferenceGeneratedPrelaunchDownCohort.testEntry) =
      AffineBatchDecoder.positiveAt p (ReferencePrelaunchFollower.traceAt i row a t own) t := by
  by_cases h : (ReferencePrelaunchFollower.downInput i row a t own).selected = true ∧
      0 < own.2.val.val
  · have he : AffineBatchDecoder.eligible
        (ReferencePrelaunchFollower.traceAt i row a t own t) := ⟨h.1, rfl, h.2⟩
    rw [ReferenceGeneratedPrelaunchDownCohort.prelaunchTest, ite_eq_left h,
      AffineBatchDecoder.positiveAt, ite_eq_left he]
    rfl
  · have he : ¬ AffineBatchDecoder.eligible
        (ReferencePrelaunchFollower.traceAt i row a t own t) := fun he => h ⟨he.1, he.2.2⟩
    simp only [ReferenceGeneratedPrelaunchDownCohort.prelaunchTest, h, ite_false,
      Option.toList_none, List.map_nil, AffineBatchDecoder.positiveAt, he]

/-- Every entry of an actual prelaunch completion comes from the actual
prefix/current-test list, with the original stamped entry unchanged. This
includes a current completion at the final physical date. -/
theorem prelaunchDownCompletedBankAt_entry_test
    (z : Source (p := p)) (i : Follower (p := p)) (t : Fin p.T)
    (W : Batch (p := p)) (hW : prelaunchDownCompletedBankAt rate rewards C_star C_h z i t W)
    (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) (he : e ∈ W) :
    ∃ test ∈ ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests
        rate rewards C_star C_h z i t ++
        (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_test
          rate rewards C_star C_h z i t).toList,
      ReferenceGeneratedPrelaunchDownCohort.testEntry test = e := by
  have hc := ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_census
    rate rewards C_star C_h z i t
  have fromBank (bank : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
      (tests : List (ReferenceGeneratedDownBatchCalendar.ExecutedTest p))
      (hmap : tests.map ReferenceGeneratedPrelaunchDownCohort.testEntry =
        AffineBatchDecoder.collected bank)
      (hentry : e ∈ AffineBatchDecoder.collected bank) :
      ∃ test ∈ tests, ReferenceGeneratedPrelaunchDownCohort.testEntry test = e := by
    rw [← hmap] at hentry
    exact List.mem_map.mp hentry
  cases hpref : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
      rate rewards C_star C_h z i t with
  | inl branch =>
    cases branch with
    | inl active =>
      simp only [prelaunchDownCompletedBankAt, hpref] at hW
      rw [hpref] at hc
      have prefixEntry (hentry : e ∈ AffineBatchDecoder.collected
          active.val.2.2.2.downBatch) :
          ∃ test ∈ ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests
              rate rewards C_star C_h z i t ++
              (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_test
                rate rewards C_star C_h z i t).toList,
            ReferenceGeneratedPrelaunchDownCohort.testEntry test = e := by
        obtain ⟨test, ht, heq⟩ := fromBank _ _ hc.1 hentry
        exact ⟨test, List.mem_append_left _ ht, heq⟩
      rcases hW with hstored | ⟨rfl, _⟩
      · apply prefixEntry
        exact List.mem_append_left _ (List.mem_flatten.mpr ⟨W, hstored, he⟩)
      · rcases List.mem_append.mp he with hpending | hcurrent
        · exact prefixEntry (List.mem_append_right _ hpending)
        · have hmap := prelaunchTest_entries i
            (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
              rate rewards C_star C_h z).row active.val.2.1 t
            (ReferenceInitializationRun.ownEntry
              (ReferenceInitializationRun.physical
                (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
                  rate rewards C_star C_h z) active.val.1.val active.val.1.property.1)
              (PublicDiscreteDraws.followerPlayer p.two_le_m
                (ActualReferenceInitializationBlock.refFollower i)) t)
          rw [← hmap] at hcurrent
          obtain ⟨test, ht, heq⟩ := List.mem_map.mp hcurrent
          refine ⟨test, List.mem_append_right _ ?_, heq⟩
          simpa only [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_test,
            hpref] using ht
    | inr inactive => simp only [prelaunchDownCompletedBankAt, hpref] at hW
  | inr stopped =>
    simp only [prelaunchDownCompletedBankAt, hpref] at hW
    rw [hpref] at hc
    obtain ⟨test, ht, heq⟩ := fromBank _ _ hc.1
      (List.mem_append_left _ (List.mem_flatten.mpr ⟨W, hW, he⟩))
    exact ⟨test, List.mem_append_left _ ht, heq⟩

/-- A fixed word cannot have been sent by all actual calls contributing to a
prelaunch completed bank. The accepted prelaunch exclusion is consumed on
the real bank branches, after the actual test census supplies the entries. -/
theorem prelaunchDownCompletedBankAt_not_fixed_sent_calls
    (z : Source (p := p)) (i : Follower (p := p)) (t : Fin p.T)
    (W : Batch (p := p)) (hW : prelaunchDownCompletedBankAt rate rewards C_star C_h z i t W)
    (w : Word (p := p)) :
    ¬ (∀ test ∈ ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests
        rate rewards C_star C_h z i t ++
        (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_test
          rate rewards C_star C_h z i t).toList,
      ReferenceGeneratedPrelaunchDownCohort.testEntry test ∈ W → test.sent = some w) := by
  intro hsent
  have hentries : ∀ e ∈ W,
      ∃ test ∈ ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests
          rate rewards C_star C_h z i t ++
          (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_test
            rate rewards C_star C_h z i t).toList,
        ReferenceGeneratedPrelaunchDownCohort.testEntry test = e ∧ test.sent = some w := by
    intro e he
    obtain ⟨test, ht, heq⟩ := prelaunchDownCompletedBankAt_entry_test
      rate rewards C_star C_h z i t W hW e he
    exact ⟨test, ht, heq, hsent test ht (heq ▸ he)⟩
  have hno := originalSourcePrelaunchDown_no_fixed_word_completed_batch
    rate rewards C_star C_h z i t
  cases hpref : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
      rate rewards C_star C_h z i t with
  | inl branch =>
    cases branch with
    | inl active =>
      simp only [prelaunchDownCompletedBankAt, hpref] at hW
      rw [hpref] at hno
      exact hno ⟨W, hW, w, hentries⟩
    | inr inactive => simp only [prelaunchDownCompletedBankAt, hpref] at hW
  | inr stopped =>
    simp only [prelaunchDownCompletedBankAt, hpref] at hW
    rw [hpref] at hno
    exact hno ⟨W, hW, w, hentries⟩

/-- Applying completed-bank provenance excludes every inherited prelaunch
entry using the sent annotation of that very original call. No suffix lookup
at entry dates is assumed. Every remaining entry retains its actual positive
call, time, channel, selected row, index and reward table. -/
theorem completedDownBatch_suffix_origins_of_fixed_sent_calls
    (z : Source (p := p)) (t : Fin p.T) (r : Record (rate := rate))
    (i : Follower (p := p)) (W : Batch (p := p)) (w : Word (p := p))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (hW : ReferenceFirstLiveDownCompletionReadout.completedDownBatch r i = some W)
    (hsent : ∀ test ∈ ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
        rate rewards C_star C_h z i,
      ReferenceGeneratedPrelaunchDownCohort.testEntry test ∈ W → test.sent = some w) :
    ∀ e ∈ W, ∃ re : Record (rate := rate),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        e.time z = some re ∧
      e ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i [re] ∧
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ e.time.val ∧
      e.time.val ≤ t.val ∧
      e.sample = ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2
        e.time).2 (0, i) ∧
      ReferenceSelectedAffinePairLaw.selectedChannel p
        ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 e.time).1 =
          some (0, i) ∧
      re.input.rows = z.1.2 ∧
      re.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      re.input.time = e.time ∧ re.input.rewards = rewards ∧
      (e.time.val < t.val ∨ e.time.val = t.val) := by
  intro e he
  rcases ReferenceCompleteCompletedBankOriginalProvenance.completedDownBatch_original_entry_provenance
      rate rewards C_star C_h z t r i W hr hW e he with hpre | hsuffix
  · obtain ⟨test, ht, heq, _, hnone, _⟩ := hpre
    have hword := hsent test ht (heq ▸ he)
    rw [hnone] at hword
    cases hword
  · exact hsuffix

/-- Actual active prelaunch DOWN calls use tuple arms and execute the ordinary
decoder on their inherited bank. Selection, rather than positivity, is the
premise: the same statement therefore covers selected zero observations. -/
theorem sourcePrelaunchSelectedDownCall
    (z : Source (p := p)) (i : Follower (p := p)) (t : Fin p.T) :
    match ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
        rate rewards C_star C_h z i t with
    | .inl (.inl active) =>
        let x := ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
          rate rewards C_star C_h z
        let b := active.val.1.val
        let phy := ReferenceInitializationRun.physical x b active.val.1.property.1
        let f := ActualReferenceInitializationBlock.refFollower i
        let own := ReferenceInitializationRun.ownEntry phy
          (PublicDiscreteDraws.followerPlayer p.two_le_m f) t
        (ReferencePrelaunchFollower.downInput i x.row active.val.2.1 t own).selected = true →
          ReferenceInitializationRun.coordinatorLearner b = none ∧
          BootstrapPhysicalBlock.actions phy (BootstrapPhysicalBlock.run phy t.val) t
              (ActiveRoundActions.coordinator p.two_le_m) =
            (BootstrapPhysicalBlock.tuple phy t).val (ActiveRoundActions.coordinator p.two_le_m) ∧
          BootstrapPhysicalBlock.actions phy (BootstrapPhysicalBlock.run phy t.val) t
              (PublicDiscreteDraws.followerPlayer p.two_le_m f) =
            (BootstrapPhysicalBlock.tuple phy t).val
              (PublicDiscreteDraws.followerPlayer p.two_le_m f) ∧
          ReferencePrelaunchFollower.decodeAt i x.row active.val.2.1 t own
              active.val.2.2.2.downBatch =
            AffineBatchDecoder.decodeStep p
              (ReferencePrelaunchFollower.traceAt i x.row active.val.2.1 t own)
              active.val.2.2.2.downBatch t
    | .inl (.inr _) => True
    | .inr _ => True := by
  cases hpref : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
      rate rewards C_star C_h z i t with
  | inl branch =>
    cases branch with
    | inl active =>
      dsimp only
      intro hselected
      have hsel := of_decide_eq_true hselected
      obtain ⟨_, hslot, _⟩ := hsel
      have hnone := active.val.1.property.2.1
      have hactivation := active.property.choose_spec.1
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [ReferenceInitializationRun.coordinatorLearner, hnone,
          Option.isSome_none, Bool.false_eq_true, ite_false]
      · rw [BootstrapPhysicalBlock.actions_coordinator]
        exact BootstrapPhysicalBlock.coordinatorAction_down _ _ t hslot
      · rw [BootstrapPhysicalBlock.actions_follower]
        have hnot : ActualReferenceInitializationBlock.refFollower i ∉
            (ReferenceInitializationRun.physical
              (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
                rate rewards C_star C_h z) active.val.1.val
              active.val.1.property.1).uninformed := by
          change ActualReferenceInitializationBlock.refFollower i ∉
            ReferenceInitializationRun.uninformed active.val.1.val
          rw [ReferenceInitializationRun.mem_uninformed, hactivation]
          intro h
          cases h
        rw [BootstrapPhysicalBlock.followerAction, dite_eq_right hnot]
        exact BootstrapPhysicalBlock.unoccupiedAction_down _ _ _ hslot
      · exact ite_eq_left hselected
    | inr inactive => trivial
  | inr stopped => trivial

/-- The coordinator receiver is disabled on every actual initialization
selector branch, including an inactive follower and a stopped boundary. -/
theorem sourcePrelaunchUpReceiverDisabled
    (z : Source (p := p)) (i : Follower (p := p)) (t : Fin p.T) :
    match ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
        rate rewards C_star C_h z i t with
    | .inl (.inl active) =>
        ReferenceInitializationRun.coordinatorUpEnabled active.val.1.val = false
    | .inl (.inr inactive) =>
        ReferenceInitializationRun.coordinatorUpEnabled inactive.val.1.val = false
    | .inr stopped =>
        ReferenceInitializationRun.coordinatorUpEnabled stopped.val.1 = false := by
  cases hpref : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
      rate rewards C_star C_h z i t with
  | inl branch =>
    cases branch with
    | inl active =>
      exact ReferencePrelaunchDownDecisionReadout.prelaunchCoordinatorUpDisabled active.val.1.val
    | inr inactive =>
      exact ReferencePrelaunchDownDecisionReadout.prelaunchCoordinatorUpDisabled inactive.val.1.val
  | inr stopped =>
    exact ReferencePrelaunchDownDecisionReadout.prelaunchCoordinatorUpDisabled stopped.val.1

/-- The original launch option has empty UP pending and completed banks in
every present branch, including a crossing at the terminal sentinel. No launch
state, crossing witness or seed-bank equality is a logical input. -/
theorem sourceLaunchUpBanksEmpty (z : Source (p := p)) :
    match ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h with
    | none => True
    | some active => ∀ i : Follower (p := p),
        (active.upDecoderBank i).pending = [] ∧
          (active.upDecoderBank i).completed = [] := by
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none => trivial
  | some active =>
    have hcross := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate z rewards C_star C_h).mp (by rw [hlaunch]; rfl)
    obtain ⟨actual, ⟨hactual, _, hbank, _, _⟩, _⟩ :=
      ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
        rate z rewards C_star C_h hcross
    have heq : active = actual := Option.some.inj (hlaunch.symm.trans hactual)
    subst actual
    intro i
    rw [hbank]
    exact ⟨rfl, rfl⟩

/-- The ordinary DOWN call on one actual source record: the selected
unoccupied receiver runs the call on its retained domains, the actual sender
encodes `w`, and the ordinary DOWN parser and accepted-start/calendar test
pass.  Positivity is deliberately absent. -/
def originalDownAwaitedCallAt (r : Record (rate := rate)) (i : Follower (p := p))
    (w : Word (p := p)) : Prop :=
  ∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
      (M : Down (rate := rate)),
    (r.output.followers i).downInput = some logged ∧
    (r.output.followers i).down = some cut ∧
    ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
    logged.status = .unoccupied ∧
    ActiveFollowerDownAcceptance.registerInputDomain p rate logged ∧
    ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch ∧
    ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer ∧
    ReferenceActiveAffinePositiveTest.downSent r.input = some w ∧
    ReferenceDownReception.ordinaryParse p rate (some w) = some M ∧
    ReferencePrelaunchFollower.acceptedStart logged < M.val.sigma ∧
    M.val.sigma ≤ r.input.time.val + 1

/-- This ordinary call is the existing physical dictionary expanded in its
actual retained fields, rather than a saved expected-word comparison. -/
theorem originalDownAwaitedCallAt_iff_physical
    (r : Record (rate := rate)) (i : Follower (p := p)) (w : Word (p := p)) :
    originalDownAwaitedCallAt rate r i w ↔
      ReferenceLiteralSourceDecoderCoverage.physicalAwaitedDownAt r i w := Iff.rfl

/-- The ordinary UP call on one actual source record.  Its acceptance is the
literal UP codec test against the retained ledger.  The positive-start
consequence is derived from this test in the application theorem. -/
def originalUpAwaitedCallAt (r : Record (rate := rate)) (i : Follower (p := p))
    (M : Up (rate := rate)) : Prop :=
  ∃ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
    r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
    CoordinatorUpReception.receptionInputDomain d.input ∧
    d.input.ledger.cutoff ≤ d.input.time.val + 1 ∧
    d.input.slot = PublicDiscreteDraws.upSlot ∧
    i ∈ d.input.ledger.pending ∧
    ReferenceActiveAffinePositiveTest.upSent r.input =
      some (ReferenceCollectionUpFailureReadoutV2.enc rate M) ∧
    CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
      (some (ReferenceCollectionUpFailureReadoutV2.enc rate M)) = some M ∧
    OrdinaryMessageCodec.acceptUp (ReferencePrelaunchFollower.codecParams p rate.eta)
      d.input.ledger.cutoff (d.input.time.val + 1) i.val
      (CoordinatorCollectionLedger.pendingNaturalLabels d.input.ledger)
      d.input.ledger.sigma M

/-- Ordinary UP acceptance on the retained ledger forces the decoded record's
start to be positive, excluding the initial placeholder. -/
theorem originalUpAwaitedCallAt_to_physical
    (r : Record (rate := rate)) (i : Follower (p := p)) (M : Up (rate := rate))
    (h : originalUpAwaitedCallAt rate r i M) :
    ReferenceLiteralSourceDecoderCoverage.physicalAwaitedUpAt r i M := by
  obtain ⟨d, hd, hi, hdom, hcut, hslot, hpending, hsent, hparse, haccept⟩ := h
  obtain ⟨_, hledgerSigma, _, _, _, _, _, _⟩ :=
    CoordinatorUpReception.receptionInputDomain_parts d.input hdom
  have hlabel : M.val.sigma = d.input.ledger.sigma := haccept.2.2
  have hsigma : 1 ≤ M.val.sigma := by omega
  exact ⟨d, hd, hi, hdom, hcut, hslot, hpending, hsent, hparse, hsigma, haccept⟩

/-- The physical UP dictionary expands back to the same ordinary receiver
call, while keeping its parser and sender tied to the actual diagnostic. -/
theorem originalUpAwaitedCallAt_of_physical
    (r : Record (rate := rate)) (i : Follower (p := p)) (M : Up (rate := rate))
    (h : ReferenceLiteralSourceDecoderCoverage.physicalAwaitedUpAt r i M) :
    originalUpAwaitedCallAt rate r i M := by
  obtain ⟨d, hd, hi, hdom, hcut, hslot, hpending, hsent, hparse, _, haccept⟩ := h
  exact ⟨d, hd, hi, hdom, hcut, hslot, hpending, hsent, hparse, haccept⟩

/-- Private suffix-only candidate. It already requires suffix records at
every entry, and therefore is not the literal whole-source predicate. Its
calendar condition includes zero observations only on the chosen interval. -/
private def suffixDownFixedAwaitedCompletionAt (z : Source (p := p))
    (t : Fin p.T) : Prop :=
  ∃ (r : Record (rate := rate)) (i : Follower (p := p)) (w : Word (p := p))
      (W : Batch (p := p)) (a : Fin p.T),
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
    ReferenceLiteralSourceDecoderCoverage.physicalDownCompletedAt r i W ∧
    a.val ≤ t.val ∧
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ a.val ∧
    (∃ u v, satisfies (samples W) u ∧ satisfies (samples W) v ∧ u ≠ v) ∧
    (∀ e, e ∈ W → ∀ test,
      test ∈ ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
        rate rewards C_star C_h z i →
      ReferenceGeneratedPrelaunchDownCohort.testEntry test = e →
      test.sent = some w) ∧
    (∀ e, e ∈ W → a.val ≤ e.time.val ∧ e.time.val ≤ t.val ∧
      ∃ re : Record (rate := rate),
        ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h e.time z = some re ∧
        re.input.rows = z.1.2 ∧
        re.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
        re.input.time = e.time ∧ re.input.rewards = rewards ∧
        originalDownAwaitedCallAt rate re i w) ∧
    (∀ v : Fin p.T, a.val ≤ v.val → v.val ≤ t.val →
      ReferenceSelectedAffinePairLaw.selectedChannel p
        ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v).1 =
          some (0, i) →
      ∃ rv : Record (rate := rate),
        ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h v z = some rv ∧
        rv.input.rows = z.1.2 ∧
        rv.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
        rv.input.time = v ∧ rv.input.rewards = rewards ∧
        originalDownAwaitedCallAt rate rv i w)

/-- Private UP suffix-only candidate, with the carried bank and ordinary
acceptance on its chosen interval. No actual fixing-boundary claim is made. -/
private def suffixUpFixedAwaitedCompletionAt (z : Source (p := p))
    (t : Fin p.T) : Prop :=
  ∃ (r : Record (rate := rate)) (i : Follower (p := p)) (M : Up (rate := rate))
      (W : Batch (p := p)) (a : Fin p.T),
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
    ReferenceLiteralSourceDecoderCoverage.physicalUpCompletedAt r i W ∧
    a.val ≤ t.val ∧
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ a.val ∧
    (∃ u v, satisfies (samples W) u ∧ satisfies (samples W) v ∧ u ≠ v) ∧
    (∀ e, e ∈ W → a.val ≤ e.time.val ∧ e.time.val ≤ t.val ∧
      ∃ re : Record (rate := rate),
        ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h e.time z = some re ∧
        re.input.rows = z.1.2 ∧
        re.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
        re.input.time = e.time ∧ re.input.rewards = rewards ∧
        originalUpAwaitedCallAt rate re i M) ∧
    (∀ v : Fin p.T, a.val ≤ v.val → v.val ≤ t.val →
      ReferenceSelectedAffinePairLaw.selectedChannel p
        ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v).1 =
          some (1, i) →
      ∃ rv : Record (rate := rate),
        ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h v z = some rv ∧
        rv.input.rows = z.1.2 ∧
        rv.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
        rv.input.time = v ∧ rv.input.rewards = rewards ∧
        originalUpAwaitedCallAt rate rv i M)

/-- Private suffix-only event; no whole-source interpretation is claimed. -/
private def suffixFixedAwaitedCompletionAt (z : Source (p := p))
    (t : Fin p.T) : Prop :=
  suffixDownFixedAwaitedCompletionAt rate rewards C_star C_h z t ∨
    suffixUpFixedAwaitedCompletionAt rate rewards C_star C_h z t

/-- Conditional application of the private suffix candidate to the admitted
literal DOWN event. This does not construct the whole-source condition. -/
private theorem suffixDownFixedAwaitedCompletionAt_to_literal
    (z : Source (p := p)) (t : Fin p.T)
    (h : suffixDownFixedAwaitedCompletionAt rate rewards C_star C_h z t) :
    ReferenceLiteralSourceDecoderCoverage.literalDownAmbiguityAt
      rate rewards C_star C_h z t := by
  obtain ⟨r, i, w, W, a, hr, hcomplete, ha, hstart, hmulti, hprelaunch,
    hentries, hcalendar⟩ := h
  have hcompleted :=
    (ReferenceLiteralAwaitedAmbiguityRowObservation.physicalDownCompletedAt_iff_completedDownBatch
      rate r i W).mp hcomplete
  have horigins :=
    ReferenceCompleteCompletedBankOriginalProvenance.completedDownBatch_original_entry_provenance
      rate rewards C_star C_h z t r i W hr hcompleted
  refine ⟨r, i, w, W, a, hr, hcomplete, ha, hmulti, ?_, ?_⟩
  · intro e he
    obtain ⟨hae, hte, re, hre, hrows, hselected, htime, hrewards, hawaited⟩ :=
      hentries e he
    rcases horigins e he with hpre | hsuffix
    · obtain ⟨test, htest, htestEntry, _, hsentNone, _⟩ := hpre
      have hsentFixed := hprelaunch e he test htest htestEntry
      rw [hsentNone] at hsentFixed
      cases hsentFixed
    · obtain ⟨re', hactual, hpositive, _, _, hsample, _, _, _, _, _⟩ := hsuffix
      have hrecordEq : re' = re := Option.some.inj (hactual.symm.trans hre)
      subst re'
      have hawPhysical :=
        (originalDownAwaitedCallAt_iff_physical rate re i w).mp hawaited
      have hawSaved :=
        (ReferenceLiteralSourceDecoderCoverage.physicalAwaitedDownAt_iff
          re i w).mp hawPhysical
      rcases hawaited with
        ⟨logged, cut, cohort, hlogged, hcut, hdownSelected, hstatus, hregister,
          hdecoder, hbuffer, hsent, hparse, haccepted, htimeBound⟩
      have hequation :=
        downEntry_equation_of_awaited rate re i w e hpositive hsent hawSaved
      exact ⟨hae, hte, hequation, re, hre, hrows, hselected, htime, hrewards,
        hsample, hpositive, hawPhysical⟩
  · intro v hav hvt hchannel
    obtain ⟨rv, hrv, hrows, hselected, htime, hrewards, haw⟩ :=
      hcalendar v hav hvt hchannel
    exact ⟨rv, hrv, hrows, hselected, htime, hrewards,
      (originalDownAwaitedCallAt_iff_physical rate rv i w).mp haw⟩

/-- Conditional application of the private suffix candidate to the admitted
literal UP event, retaining the original bank and accepted encoded record. -/
private theorem suffixUpFixedAwaitedCompletionAt_to_literal
    (z : Source (p := p)) (t : Fin p.T)
    (h : suffixUpFixedAwaitedCompletionAt rate rewards C_star C_h z t) :
    ReferenceLiteralSourceDecoderCoverage.literalUpAmbiguityAt
      rate rewards C_star C_h z t := by
  obtain ⟨r, i, M, W, a, hr, hcomplete, ha, hstart, hmulti,
    hentries, hcalendar⟩ := h
  have hcompleted :=
    (ReferenceLiteralAwaitedAmbiguityRowObservation.physicalUpCompletedAt_iff_completedUpBatch
      rate r i W).mp hcomplete
  have horigins :=
    ReferenceCompleteCompletedBankOriginalProvenance.completedUpBatch_original_entry_provenance
      rate rewards C_star C_h z t r i W hr hcompleted
  refine ⟨r, i, M, W, a, hr, hcomplete, ha, ?_, hmulti, ?_, ?_⟩
  · have hlen :=
      (ReferenceCollectionUpFailureReadoutV2.completedUpBatch_spec rate r i W
        hcompleted).1
    cases hW : W with
    | nil =>
        have hzero : 0 = AffineBatchDecoder.quota p := by
          simpa [hW, ReferenceCollectionUpFailureReadoutV2.Q] using hlen
        have hquota := AffineBatchDecoder.quota_pos p
        omega
    | cons e tail =>
        have he : e ∈ W := by rw [hW]; simp
        obtain ⟨_, _, re, _, _, _, _, _, haw⟩ := hentries e he
        obtain ⟨d, hd, hi, hdomain, hcut, hslot, hpending, hsent, hparse,
          hsigma, haccept⟩ := originalUpAwaitedCallAt_to_physical rate re i M haw
        exact hsigma
  · intro e he
    obtain ⟨hae, hte, re, hre, hrows, hselected, htime, hrewards, haw⟩ :=
      hentries e he
    obtain ⟨re', hactual, hpositive, _, _, hsample, _, _, _, _, _⟩ :=
      horigins e he
    have hrecordEq : re' = re := Option.some.inj (hactual.symm.trans hre)
    subst re'
    have hawPhysical := originalUpAwaitedCallAt_to_physical rate re i M haw
    have hequation := upEntry_equation_of_awaited rate re i M e hpositive hawPhysical
    exact ⟨hae, hte, hequation, re, hre, hrows, hselected, htime, hrewards,
      hsample, hpositive, hawPhysical⟩
  · intro v hav hvt hchannel
    obtain ⟨rv, hrv, hrows, hselected, htime, hrewards, haw⟩ :=
      hcalendar v hav hvt hchannel
    exact ⟨rv, hrv, hrows, hselected, htime, hrewards,
      originalUpAwaitedCallAt_to_physical rate rv i M haw⟩

/-- A literal DOWN event recovers the same original bank and calls.  The
interval is advanced to the launch boundary only after the accepted
entry-origin result proves every stamped entry is a suffix call. -/
private theorem literalDownAmbiguityAt_to_suffix
    (z : Source (p := p)) (t : Fin p.T)
    (h : ReferenceLiteralSourceDecoderCoverage.literalDownAmbiguityAt
      rate rewards C_star C_h z t) :
    suffixDownFixedAwaitedCompletionAt rate rewards C_star C_h z t := by
  obtain ⟨r, i, w, W, a, hr, hcomplete, ha, hmulti, hentries, hcalendar⟩ := h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hsT : s ≤ t.val := actualRecord_start_le rate rewards C_star C_h z t r hr
  let A : Fin p.T := ⟨max a.val s, by
    apply Nat.lt_of_le_of_lt
    · exact Nat.max_le.mpr ⟨ha, hsT⟩
    · exact t.isLt⟩
  have hcompleted :=
    (ReferenceLiteralAwaitedAmbiguityRowObservation.physicalDownCompletedAt_iff_completedDownBatch
      rate r i W).mp hcomplete
  refine ⟨r, i, w, W, A, hr, hcomplete, ?_, ?_, hmulti, ?_, ?_, ?_⟩
  · exact Nat.max_le.mpr ⟨ha, hsT⟩
  · exact Nat.le_max_right _ _
  · intro e he test htest htestEntry
    obtain ⟨hae, _, _, reLit, hreLit, _, _, _, _, _, _, _, _⟩ := hentries e he
    obtain ⟨re, hactual, _, hsEntry⟩ := completedDownEntry_suffix_origin
      rate rewards C_star C_h z t r i W hr hcomplete e he ⟨reLit, hreLit⟩
    have hrecordEq : re = reLit := Option.some.inj (hactual.symm.trans hreLit)
    subst re
    have htestBefore := sourcePrelaunchTest_beforeStart
      rate rewards C_star C_h z i test htest
    have htestTime : test.time = e.time := by
      have h := congrArg AffineBatchDecoder.Entry.time htestEntry
      simpa only [ReferenceGeneratedPrelaunchDownCohort.testEntry] using h
    have htestBefore' : test.time.val < s := by simpa [s] using htestBefore
    have hentryStart : s ≤ test.time.val := by simpa [htestTime] using hsEntry
    omega
  · intro e he
    obtain ⟨hae, hte, hequation, re, hre, hrows, hselected, htime,
      hrewards, hsample, hpositive, haw⟩ := hentries e he
    obtain ⟨re', hactual, hpositiveOrigin, hsEntry⟩ := completedDownEntry_suffix_origin
      rate rewards C_star C_h z t r i W hr hcomplete e he ⟨re, hre⟩
    have hrecordEq : re' = re := Option.some.inj (hactual.symm.trans hre)
    subst re'
    have hinterval : A.val ≤ e.time.val := by
      change max a.val s ≤ e.time.val
      exact Nat.max_le.mpr ⟨hae, by simpa [s] using hsEntry⟩
    exact ⟨hinterval, hte, re, hre, hrows, hselected, htime, hrewards,
      (originalDownAwaitedCallAt_iff_physical rate re i w).mpr haw⟩
  · intro v hvA hvt hchannel
    have hv : a.val ≤ v.val := le_trans (Nat.le_max_left _ _) hvA
    obtain ⟨rv, hrv, hrows, hselected, htime, hrewards, haw⟩ :=
      hcalendar v hv hvt hchannel
    exact ⟨rv, hrv, hrows, hselected, htime, hrewards,
      (originalDownAwaitedCallAt_iff_physical rate rv i w).mpr haw⟩

/-- A literal UP event recovers the original completed bank and every
ordinary accepted call from the same actual UP word. -/
private theorem literalUpAmbiguityAt_to_suffix
    (z : Source (p := p)) (t : Fin p.T)
    (h : ReferenceLiteralSourceDecoderCoverage.literalUpAmbiguityAt
      rate rewards C_star C_h z t) :
    suffixUpFixedAwaitedCompletionAt rate rewards C_star C_h z t := by
  obtain ⟨r, i, M, W, a, hr, hcomplete, ha, hsigma, hmulti,
    hentries, hcalendar⟩ := h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hsT : s ≤ t.val := actualRecord_start_le rate rewards C_star C_h z t r hr
  let A : Fin p.T := ⟨max a.val s, by
    apply Nat.lt_of_le_of_lt
    · exact Nat.max_le.mpr ⟨ha, hsT⟩
    · exact t.isLt⟩
  have hcompleted :=
    (ReferenceLiteralAwaitedAmbiguityRowObservation.physicalUpCompletedAt_iff_completedUpBatch
      rate r i W).mp hcomplete
  have horigins :=
    ReferenceCompleteCompletedBankOriginalProvenance.completedUpBatch_original_entry_provenance
      rate rewards C_star C_h z t r i W hr hcompleted
  refine ⟨r, i, M, W, A, hr, hcomplete, ?_, ?_, hmulti, ?_, ?_⟩
  · exact Nat.max_le.mpr ⟨ha, hsT⟩
  · exact Nat.le_max_right _ _
  · intro e he
    obtain ⟨hae, hte, hequation, re, hre, hrows, hselected, htime,
      hrewards, hsample, hpositive, haw⟩ := hentries e he
    obtain ⟨re', hactual, hpositiveOrigin, hsEntry, _, _, _, _, _, _, _⟩ :=
      horigins e he
    have hrecordEq : re' = re := Option.some.inj (hactual.symm.trans hre)
    subst re'
    have hinterval : A.val ≤ e.time.val := by
      change max a.val s ≤ e.time.val
      exact Nat.max_le.mpr ⟨hae, by simpa [s] using hsEntry⟩
    exact ⟨hinterval, hte, re, hre, hrows, hselected, htime, hrewards,
      (originalUpAwaitedCallAt_of_physical rate re i M haw)⟩
  · intro v hvA hvt hchannel
    have hv : a.val ≤ v.val := le_trans (Nat.le_max_left _ _) hvA
    obtain ⟨rv, hrv, hrows, hselected, htime, hrewards, haw⟩ :=
      hcalendar v hv hvt hchannel
    exact ⟨rv, hrv, hrows, hselected, htime, hrewards,
      originalUpAwaitedCallAt_of_physical rate rv i M haw⟩

/-- Private equivalence for the suffix-only candidate. This does not identify
the original source event or its actual sender fixing boundary. -/
private theorem suffixFixedAwaitedCompletionAt_iff_literal
    (z : Source (p := p)) (t : Fin p.T) :
    suffixFixedAwaitedCompletionAt rate rewards C_star C_h z t ↔
      ReferenceLiteralSourceDecoderCoverage.literalDownAmbiguityAt
          rate rewards C_star C_h z t ∨
        ReferenceLiteralSourceDecoderCoverage.literalUpAmbiguityAt
          rate rewards C_star C_h z t := by
  constructor
  · rintro (hdown | hup)
    · exact Or.inl (suffixDownFixedAwaitedCompletionAt_to_literal
        rate rewards C_star C_h z t hdown)
    · exact Or.inr (suffixUpFixedAwaitedCompletionAt_to_literal
        rate rewards C_star C_h z t hup)
  · rintro (hdown | hup)
    · exact Or.inl (literalDownAmbiguityAt_to_suffix
        rate rewards C_star C_h z t hdown)
    · exact Or.inr (literalUpAmbiguityAt_to_suffix
        rate rewards C_star C_h z t hup)

/-- Total DOWN sender readout. Initialization uses the actual current-test
annotation, which is absent on a zero observation as well as on inactive and
stopped branches. On active selected zero rounds the tuple-arm identity in
`sourcePrelaunchSelectedDownCall` still gives no ordinary encoded word. -/
def sourceDownSentAt (z : Source (p := p)) (i : Follower (p := p))
    (t : Fin p.T) : Option (Word (p := p)) :=
  match actualRecord rate rewards C_star C_h t z with
  | some r => ReferenceActiveAffinePositiveTest.downSent r.input
  | none => (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_test
      rate rewards C_star C_h z i t).bind (fun test => test.sent)

/-- Total UP sender readout, retaining the actual initialization placeholder
when its active selected offer exists. A disabled receiver is not a zero call. -/
def sourceUpSentAt (z : Source (p := p)) (i : Follower (p := p))
    (t : Fin p.T) : Option (Word (p := p)) :=
  match actualRecord rate rewards C_star C_h t z with
  | some r => ReferenceActiveAffinePositiveTest.upSent r.input
  | none =>
      match ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
          rate rewards C_star C_h z i t with
      | .inl (.inl active) =>
          (ReferencePrelaunchFollower.upOffer rate.eta i
            (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
              rate rewards C_star C_h z).row active.val.2.1 t).map
              (ReferenceCollectionUpFailureReadoutV2.enc rate)
      | .inl (.inr _) => none
      | .inr _ => none

/-- Literal total ordinary DOWN awaiting test. The initialization active branch
retains its actual selected decoder call, bank and ordinary Parse/Acc test,
including zero feedback, and its actual absent ordinary sender. Inactive and
stopped initialization have no current ordinary DOWN receiver call. -/
def sourceDownAwaitedAt (z : Source (p := p)) (i : Follower (p := p))
    (w : Word (p := p)) (t : Fin p.T) : Prop :=
  match actualRecord rate rewards C_star C_h t z with
  | some r => originalDownAwaitedCallAt rate r i w
  | none =>
      match ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
          rate rewards C_star C_h z i t with
      | .inl (.inl active) =>
          let x := ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
            rate rewards C_star C_h z
          let own := ReferenceInitializationRun.ownEntry
            (ReferenceInitializationRun.physical x active.val.1.val active.val.1.property.1)
            (PublicDiscreteDraws.followerPlayer p.two_le_m
              (ActualReferenceInitializationBlock.refFollower i)) t
          (ReferencePrelaunchFollower.downInput i x.row active.val.2.1 t own).selected = true ∧
          ReferenceInitializationRun.coordinatorLearner active.val.1.val = none ∧
          ReferencePrelaunchFollower.decodeAt i x.row active.val.2.1 t own
              active.val.2.2.2.downBatch = AffineBatchDecoder.decodeStep p
                (ReferencePrelaunchFollower.traceAt i x.row active.val.2.1 t own)
                active.val.2.2.2.downBatch t ∧
          sourceDownSentAt rate rewards C_star C_h z i t = some w ∧
          ∃ M : Down (rate := rate),
            ReferenceDownReception.ordinaryParse p rate (some w) = some M ∧
            OrdinaryMessageCodec.acceptDown
              (ReferencePrelaunchFollower.codecParams p rate.eta)
              (ReferencePrelaunchFollower.acceptedStart active.val.2.2.2) (t.val + 1) M
      | .inl (.inr _) => False
      | .inr _ => False

/-- Total ordinary UP awaiting test. Before launch the actual receiver enable
bit is false, so no ordinary receiver/parser/acceptance call is reached. The
active branch still retains the actual offered record, rather than replacing
that offer by an arbitrary absent word. -/
def sourceUpAwaitedAt (z : Source (p := p)) (i : Follower (p := p))
    (M : Up (rate := rate)) (t : Fin p.T) : Prop :=
  match actualRecord rate rewards C_star C_h t z with
  | some r => originalUpAwaitedCallAt rate r i M
  | none =>
      match ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
          rate rewards C_star C_h z i t with
      | .inl (.inl active) =>
          ReferenceInitializationRun.coordinatorUpEnabled active.val.1.val = true ∧
          ReferencePrelaunchFollower.upOffer rate.eta i
            (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
              rate rewards C_star C_h z).row active.val.2.1 t = some M
      | .inl (.inr inactive) =>
          ReferenceInitializationRun.coordinatorUpEnabled inactive.val.1.val = true
      | .inr stopped =>
          ReferenceInitializationRun.coordinatorUpEnabled stopped.val.1 = true

/-- Current physical DOWN completion. The initialization census retains stored
banks, but their last positive stamp must be this decision date. An old stored
bank is therefore not relabelled as a new completion. -/
def sourceDownCompletedAt (z : Source (p := p)) (i : Follower (p := p))
    (t : Fin p.T) (W : Batch (p := p)) : Prop :=
  match actualRecord rate rewards C_star C_h t z with
  | some r => physicalDownCompletedAt r i W
  | none => prelaunchDownCompletedBankAt rate rewards C_star C_h z i t W ∧
      AffineBatchDecoder.decisionTime W = some t

/-- Current physical UP completion. Initialization's actual disabled receiver
cannot make a decoder decision. Both original UP banks at launch are empty,
as proved by `sourceLaunchUpBanksEmpty`; no inherited UP completion is reset. -/
def sourceUpCompletedAt (z : Source (p := p)) (i : Follower (p := p))
    (t : Fin p.T) (W : Batch (p := p)) : Prop :=
  match actualRecord rate rewards C_star C_h t z with
  | some r => physicalUpCompletedAt r i W
  | none =>
      match ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
          rate rewards C_star C_h z i t with
      | .inl (.inl active) =>
          ReferenceInitializationRun.coordinatorUpEnabled active.val.1.val = true
      | .inl (.inr inactive) =>
          ReferenceInitializationRun.coordinatorUpEnabled inactive.val.1.val = true
      | .inr stopped =>
          ReferenceInitializationRun.coordinatorUpEnabled stopped.val.1 = true

/-- Whole-source fixed-awaited DOWN window: actual current completion, multiple
solvers, the same actually sent word on every original positive stamp, and the
ordinary awaiting call on every selected date in the window, including zeros.
Neither equations for that word nor provenance/record/field witnesses are inputs. -/
def sourceDownFixedAwaitedCompletionAt (z : Source (p := p)) (t : Fin p.T) : Prop :=
  ∃ (i : Follower (p := p)) (w : Word (p := p)) (W : Batch (p := p)) (a : Fin p.T),
    sourceDownCompletedAt rate rewards C_star C_h z i t W ∧ a.val ≤ t.val ∧
    (∃ u v, satisfies (samples W) u ∧ satisfies (samples W) v ∧ u ≠ v) ∧
    (∀ e ∈ W, a.val ≤ e.time.val ∧ e.time.val ≤ t.val ∧
      sourceDownSentAt rate rewards C_star C_h z i e.time = some w) ∧
    (∀ v : Fin p.T, a.val ≤ v.val → v.val ≤ t.val →
      selectedChannel p ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v).1 =
        some (0, i) → sourceDownAwaitedAt rate rewards C_star C_h z i w v)

/-- The UP window uses an actual ordinary record and the same total sender and
receiver queries. Positive start, ordinary acceptance, and exclusion of the
initial placeholder are consequences of the reached ordinary call. -/
def sourceUpFixedAwaitedCompletionAt (z : Source (p := p)) (t : Fin p.T) : Prop :=
  ∃ (i : Follower (p := p)) (M : Up (rate := rate)) (W : Batch (p := p)) (a : Fin p.T),
    sourceUpCompletedAt rate rewards C_star C_h z i t W ∧ a.val ≤ t.val ∧
    (∃ u v, satisfies (samples W) u ∧ satisfies (samples W) v ∧ u ≠ v) ∧
    (∀ e ∈ W, a.val ≤ e.time.val ∧ e.time.val ≤ t.val ∧
      sourceUpSentAt rate rewards C_star C_h z i e.time =
        some (ReferenceCollectionUpFailureReadoutV2.enc rate M)) ∧
    (∀ v : Fin p.T, a.val ≤ v.val → v.val ≤ t.val →
      selectedChannel p ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v).1 =
        some (1, i) → sourceUpAwaitedAt rate rewards C_star C_h z i M v)

/-- Bidirectional whole-source window event, before any physical cutoff projection. -/
def sourceFixedAwaitedCompletionAt (z : Source (p := p)) (t : Fin p.T) : Prop :=
  sourceDownFixedAwaitedCompletionAt rate rewards C_star C_h z t ∨
    sourceUpFixedAwaitedCompletionAt rate rewards C_star C_h z t

private theorem sourceDownSentAt_none_of_no_record
    (z : Source (p := p)) (i : Follower (p := p)) (t : Fin p.T)
    (hr : actualRecord rate rewards C_star C_h t z = none) :
    sourceDownSentAt rate rewards C_star C_h z i t = none := by
  simp only [sourceDownSentAt, hr]
  cases ht : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_test
      rate rewards C_star C_h z i t with
  | none => rfl
  | some test =>
    have hsent := ReferencePrelaunchDownDecisionReadout.source_prelaunch_down_tests_through_sent_none
      rate rewards C_star C_h z i t test
      (List.mem_append_right _ (by simp only [ht, Option.toList_some, List.mem_cons_self]))
    exact hsent

/-- An original initialization test's sender readout is the sent annotation of
that very test, at that very stamp, without matching equal affine samples. -/
theorem sourceDownSentAt_original_prelaunch_test
    (z : Source (p := p)) (i : Follower (p := p))
    (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p)
    (ht : test ∈ ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
      rate rewards C_star C_h z i) :
    sourceDownSentAt rate rewards C_star C_h z i test.time = test.sent := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hnone⟩ :=
    ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_test_provenance
      rate rewards C_star C_h z i test ht
  rw [hnone]
  apply sourceDownSentAt_none_of_no_record
  apply actualRecord_eq_none_of_future_start
  exact sourcePrelaunchTest_beforeStart rate rewards C_star C_h z i test ht

private theorem actualRecord_none_before_start
    (z : Source (p := p)) (t : Fin p.T)
    (hr : actualRecord rate rewards C_star C_h t z = none) :
    t.val < ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
  by_contra hn
  have hs := Nat.le_of_not_gt hn
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
  | none =>
    have hT := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
      rate z rewards C_star C_h hl
    have ht := t.isLt
    omega
  | some active =>
    have he := actualRecord_on_launch rate rewards C_star C_h t z active hl hs
    rw [hr] at he
    cases he

private theorem sourceDownCompletion_suffix
    (z : Source (p := p)) (i : Follower (p := p)) (t : Fin p.T)
    (W : Batch (p := p)) (w : Word (p := p))
    (hc : sourceDownCompletedAt rate rewards C_star C_h z i t W)
    (hsent : ∀ e ∈ W, e.time.val ≤ t.val ∧
      sourceDownSentAt rate rewards C_star C_h z i e.time = some w) :
    ∃ r : Record (rate := rate), actualRecord rate rewards C_star C_h t z = some r ∧
      physicalDownCompletedAt r i W := by
  cases hr : actualRecord rate rewards C_star C_h t z with
  | some r => exact ⟨r, rfl, by simpa only [sourceDownCompletedAt, hr] using hc⟩
  | none =>
    have hbank := (show prelaunchDownCompletedBankAt rate rewards C_star C_h z i t W ∧
        AffineBatchDecoder.decisionTime W = some t by
      simpa only [sourceDownCompletedAt, hr] using hc).1
    have hbefore := actualRecord_none_before_start rate rewards C_star C_h z t hr
    apply False.elim
    apply prelaunchDownCompletedBankAt_not_fixed_sent_calls
      rate rewards C_star C_h z i t W hbank w
    intro test ht he
    obtain ⟨htime, hw⟩ := hsent _ he
    have hnone := ReferencePrelaunchDownDecisionReadout.source_prelaunch_down_tests_through_sent_none
      rate rewards C_star C_h z i t test ht
    have hzero := sourceDownSentAt_none_of_no_record rate rewards C_star C_h z i test.time
      (actualRecord_eq_none_of_future_start rate rewards C_star C_h test.time z
        (lt_of_le_of_lt htime hbefore))
    change sourceDownSentAt rate rewards C_star C_h z i test.time = some w at hw
    exact hnone.trans (hzero.symm.trans hw)

private theorem sourceUpCompletion_suffix
    (z : Source (p := p)) (i : Follower (p := p)) (t : Fin p.T) (W : Batch (p := p))
    (hc : sourceUpCompletedAt rate rewards C_star C_h z i t W) :
    ∃ r : Record (rate := rate), actualRecord rate rewards C_star C_h t z = some r ∧
      physicalUpCompletedAt r i W := by
  cases hr : actualRecord rate rewards C_star C_h t z with
  | some r => exact ⟨r, rfl, by simpa only [sourceUpCompletedAt, hr] using hc⟩
  | none =>
    simp only [sourceUpCompletedAt, hr] at hc
    cases hp : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
        rate rewards C_star C_h z i t with
    | inl branch => cases branch <;>
        simp only [hp, ReferenceInitializationRun.coordinatorUpEnabled, Bool.false_eq_true] at hc
    | inr stopped =>
        simp only [hp, ReferenceInitializationRun.coordinatorUpEnabled, Bool.false_eq_true] at hc

/-- Whole-source DOWN coverage: B supplies every original occurrence. Only
then is the window intersected with the actual launch suffix. The same-call
prelaunch annotations exclude inherited entries without clearing that bank. -/
theorem sourceDownFixedAwaitedCompletionAt_to_literal
    (z : Source (p := p)) (t : Fin p.T)
    (h : sourceDownFixedAwaitedCompletionAt rate rewards C_star C_h z t) :
    literalDownAmbiguityAt rate rewards C_star C_h z t := by
  obtain ⟨i, w, W, a, hc, hat, hmulti, hentries, hcalendar⟩ := h
  obtain ⟨r, hr, hcomplete⟩ := sourceDownCompletion_suffix rate rewards C_star C_h z i t W w hc
    (fun e he => ⟨(hentries e he).2.1, (hentries e he).2.2⟩)
  have hW := (ReferenceLiteralAwaitedAmbiguityRowObservation.physicalDownCompletedAt_iff_completedDownBatch
    rate r i W).mp hcomplete
  have hsent : ∀ test ∈ ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
      rate rewards C_star C_h z i,
      ReferenceGeneratedPrelaunchDownCohort.testEntry test ∈ W → test.sent = some w := by
    intro test ht he
    have hw := (hentries _ he).2.2
    change sourceDownSentAt rate rewards C_star C_h z i test.time = some w at hw
    rw [sourceDownSentAt_original_prelaunch_test rate rewards C_star C_h z i test ht] at hw
    exact hw
  have horigins := completedDownBatch_suffix_origins_of_fixed_sent_calls
    rate rewards C_star C_h z t r i W w hr hW hsent
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hst : s ≤ t.val := actualRecord_start_le rate rewards C_star C_h z t r hr
  let a' : Fin p.T := ⟨max a.val s, lt_of_le_of_lt (Nat.max_le.mpr ⟨hat, hst⟩) t.isLt⟩
  apply suffixDownFixedAwaitedCompletionAt_to_literal rate rewards C_star C_h z t
  refine ⟨r, i, w, W, a', hr, hcomplete, Nat.max_le.mpr ⟨hat, hst⟩,
    Nat.le_max_right _ _, hmulti, ?_, ?_, ?_⟩
  · intro e he test ht hte
    exact hsent test ht (hte ▸ he)
  · intro e he
    obtain ⟨hae, het, hsender⟩ := hentries e he
    obtain ⟨re, hre, hpositive, hs, _, _, hchannel, hrows, hJ, htime, hrew, _⟩ := horigins e he
    have haw := hcalendar e.time hae het hchannel
    simp only [sourceDownAwaitedAt, hre] at haw
    exact ⟨Nat.max_le.mpr ⟨hae, hs⟩, het, re, hre, hrows, hJ, htime, hrew, haw⟩
  · intro v hav hvt hchannel
    have haw := hcalendar v (le_trans (Nat.le_max_left _ _) hav) hvt hchannel
    cases hv : actualRecord rate rewards C_star C_h v z with
    | some rv =>
      have hf := actualRecord_original_fields rate rewards C_star C_h z v rv hv
      exact ⟨rv, rfl, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2,
        by simpa only [sourceDownAwaitedAt, hv] using haw⟩
    | none =>
      have hbefore := actualRecord_none_before_start rate rewards C_star C_h z v hv
      have hsv : s ≤ v.val := le_trans (Nat.le_max_right _ _) hav
      omega

/-- Whole-source UP coverage on the actual original bank and call. The
ordinary acceptance in the reached calendar calls supplies positive sigma. -/
theorem sourceUpFixedAwaitedCompletionAt_to_literal
    (z : Source (p := p)) (t : Fin p.T)
    (h : sourceUpFixedAwaitedCompletionAt rate rewards C_star C_h z t) :
    literalUpAmbiguityAt rate rewards C_star C_h z t := by
  obtain ⟨i, M, W, a, hc, hat, hmulti, hentries, hcalendar⟩ := h
  obtain ⟨r, hr, hcomplete⟩ := sourceUpCompletion_suffix rate rewards C_star C_h z i t W hc
  have hW := (ReferenceLiteralAwaitedAmbiguityRowObservation.physicalUpCompletedAt_iff_completedUpBatch
    rate r i W).mp hcomplete
  have horigins := completedUpBatch_original_entry_provenance
    rate rewards C_star C_h z t r i W hr hW
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hst : s ≤ t.val := actualRecord_start_le rate rewards C_star C_h z t r hr
  let a' : Fin p.T := ⟨max a.val s, lt_of_le_of_lt (Nat.max_le.mpr ⟨hat, hst⟩) t.isLt⟩
  apply suffixUpFixedAwaitedCompletionAt_to_literal rate rewards C_star C_h z t
  refine ⟨r, i, M, W, a', hr, hcomplete, Nat.max_le.mpr ⟨hat, hst⟩,
    Nat.le_max_right _ _, hmulti, ?_, ?_⟩
  · intro e he
    obtain ⟨hae, het, hsender⟩ := hentries e he
    obtain ⟨re, hre, hpositive, hs, _, _, hchannel, hrows, hJ, htime, hrew, _⟩ := horigins e he
    have haw := hcalendar e.time hae het hchannel
    simp only [sourceUpAwaitedAt, hre] at haw
    exact ⟨Nat.max_le.mpr ⟨hae, hs⟩, het, re, hre, hrows, hJ, htime, hrew, haw⟩
  · intro v hav hvt hchannel
    have haw := hcalendar v (le_trans (Nat.le_max_left _ _) hav) hvt hchannel
    cases hv : actualRecord rate rewards C_star C_h v z with
    | some rv =>
      have hf := actualRecord_original_fields rate rewards C_star C_h z v rv hv
      exact ⟨rv, rfl, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2,
        by simpa only [sourceUpAwaitedAt, hv] using haw⟩
    | none =>
      have hbefore := actualRecord_none_before_start rate rewards C_star C_h z v hv
      have hsv : s ≤ v.val := le_trans (Nat.le_max_right _ _) hav
      omega

/-- Converse on the same physical DOWN bank, sent word and all-selected
window. No earliest-fixation or physical reset endpoint is asserted. -/
theorem literalDownAmbiguityAt_to_source
    (z : Source (p := p)) (t : Fin p.T)
    (h : literalDownAmbiguityAt rate rewards C_star C_h z t) :
    sourceDownFixedAwaitedCompletionAt rate rewards C_star C_h z t := by
  obtain ⟨r, i, w, W, a, hr, hc, hat, hmulti, hentries, hcalendar⟩ := h
  refine ⟨i, w, W, a, ?_, hat, hmulti, ?_, ?_⟩
  · simpa only [sourceDownCompletedAt, hr] using hc
  · intro e he
    obtain ⟨hae, het, _, re, hre, _, _, _, _, _, _, haw⟩ := hentries e he
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hsent, _⟩ := haw
    exact ⟨hae, het, by simpa only [sourceDownSentAt, hre] using hsent⟩
  · intro v hav hvt hchannel
    obtain ⟨rv, hrv, _, _, _, _, haw⟩ := hcalendar v hav hvt hchannel
    have haw' := (originalDownAwaitedCallAt_iff_physical rate rv i w).mpr haw
    simpa only [sourceDownAwaitedAt, hrv] using haw'

/-- Converse on the same actual UP completion and encoded ordinary record,
retaining every original private array, row and calendar witness. -/
theorem literalUpAmbiguityAt_to_source
    (z : Source (p := p)) (t : Fin p.T)
    (h : literalUpAmbiguityAt rate rewards C_star C_h z t) :
    sourceUpFixedAwaitedCompletionAt rate rewards C_star C_h z t := by
  obtain ⟨r, i, M, W, a, hr, hc, hat, _, hmulti, hentries, hcalendar⟩ := h
  refine ⟨i, M, W, a, ?_, hat, hmulti, ?_, ?_⟩
  · simpa only [sourceUpCompletedAt, hr] using hc
  · intro e he
    obtain ⟨hae, het, _, re, hre, _, _, _, _, _, _, haw⟩ := hentries e he
    obtain ⟨_, _, _, _, _, _, _, hsent, _⟩ := haw
    exact ⟨hae, het, by simpa only [sourceUpSentAt, hre] using hsent⟩
  · intro v hav hvt hchannel
    obtain ⟨rv, hrv, _, _, _, _, haw⟩ := hcalendar v hav hvt hchannel
    have haw' := originalUpAwaitedCallAt_of_physical rate rv i M haw
    simpa only [sourceUpAwaitedAt, hrv] using haw'

/-- Deterministic whole-source bidirectional window coverage. This is an
internal event characterization, without a probability or source-node seal. -/
theorem sourceFixedAwaitedCompletionAt_iff_literal
    (z : Source (p := p)) (t : Fin p.T) :
    sourceFixedAwaitedCompletionAt rate rewards C_star C_h z t ↔
      literalDownAmbiguityAt rate rewards C_star C_h z t ∨
        literalUpAmbiguityAt rate rewards C_star C_h z t :=
  or_congr ⟨sourceDownFixedAwaitedCompletionAt_to_literal rate rewards C_star C_h z t,
    literalDownAmbiguityAt_to_source rate rewards C_star C_h z t⟩
    ⟨sourceUpFixedAwaitedCompletionAt_to_literal rate rewards C_star C_h z t,
    literalUpAmbiguityAt_to_source rate rewards C_star C_h z t⟩

/-- Finite physical scan of the total event, before projecting any stopping cutoff. -/
theorem sourceFixedAwaitedCompletionAt_exists_iff_literal (z : Source (p := p)) :
    (∃ t : Fin p.T, sourceFixedAwaitedCompletionAt rate rewards C_star C_h z t) ↔
      ∃ t : Fin p.T, literalDownAmbiguityAt rate rewards C_star C_h z t ∨
        literalUpAmbiguityAt rate rewards C_star C_h z t :=
  exists_congr (fun t => sourceFixedAwaitedCompletionAt_iff_literal rate rewards C_star C_h z t)

/-- The actual prelaunch active DOWN branch has no ordinary encoded sender;
inactive and stopped branches have no current call. This excludes awaiting,
not the existence of raw ambiguous initialization banks. -/
theorem sourceDownAwaitedAt_false_of_no_record
    (z : Source (p := p)) (i : Follower (p := p)) (w : Word (p := p)) (t : Fin p.T)
    (hr : actualRecord rate rewards C_star C_h t z = none) :
    ¬ sourceDownAwaitedAt rate rewards C_star C_h z i w t := by
  intro h
  have hsent := sourceDownSentAt_none_of_no_record rate rewards C_star C_h z i t hr
  simp only [sourceDownAwaitedAt, hr] at h
  cases hp : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
      rate rewards C_star C_h z i t with
  | inl branch =>
    cases branch with
    | inl active =>
      rw [hp] at h
      have hw := h.2.2.2.1
      rw [hsent] at hw
      cases hw
    | inr inactive => simp only [hp] at h
  | inr stopped => simp only [hp] at h

/-- Initialization UP preserves its actual placeholder offer but has a disabled
receiver on each original selector branch. It supplies no ordinary awaited call. -/
theorem sourceUpAwaitedAt_false_of_no_record
    (z : Source (p := p)) (i : Follower (p := p)) (M : Up (rate := rate)) (t : Fin p.T)
    (hr : actualRecord rate rewards C_star C_h t z = none) :
    ¬ sourceUpAwaitedAt rate rewards C_star C_h z i M t := by
  intro h
  simp only [sourceUpAwaitedAt, hr] at h
  cases hp : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
      rate rewards C_star C_h z i t with
  | inl branch => cases branch <;>
      simp only [hp, ReferenceInitializationRun.coordinatorUpEnabled, Bool.false_eq_true,
        false_and] at h
  | inr stopped =>
      simp only [hp, ReferenceInitializationRun.coordinatorUpEnabled, Bool.false_eq_true] at h

/-- Ordinary UP acceptance on the actual total call excludes the placeholder. -/
theorem sourceUpAwaitedAt_sigma_pos
    (z : Source (p := p)) (i : Follower (p := p)) (M : Up (rate := rate)) (t : Fin p.T)
    (h : sourceUpAwaitedAt rate rewards C_star C_h z i M t) : 1 ≤ M.val.sigma := by
  cases hr : actualRecord rate rewards C_star C_h t z with
  | none => exact False.elim (sourceUpAwaitedAt_false_of_no_record
      rate rewards C_star C_h z i M t hr h)
  | some r =>
    have haw : originalUpAwaitedCallAt rate r i M := by
      simpa only [sourceUpAwaitedAt, hr] using h
    obtain ⟨_, _, _, _, _, _, _, _, _, hsigma, _⟩ :=
      originalUpAwaitedCallAt_to_physical rate r i M haw
    exact hsigma

/-- Actual original fixed-sent completed DOWN banks have no prelaunch entry.
This also excludes a launch-straddling bank with even one inherited positive;
the original bank is retained unchanged throughout the argument. -/
theorem sourceDownCompletedAt_fixed_sent_no_prelaunch_entries
    (z : Source (p := p)) (i : Follower (p := p)) (t : Fin p.T)
    (W : Batch (p := p)) (w : Word (p := p))
    (hc : sourceDownCompletedAt rate rewards C_star C_h z i t W)
    (hsent : ∀ e ∈ W, e.time.val ≤ t.val ∧
      sourceDownSentAt rate rewards C_star C_h z i e.time = some w) :
    ∀ e ∈ W, ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h ≤ e.time.val := by
  obtain ⟨r, hr, hcomplete⟩ := sourceDownCompletion_suffix
    rate rewards C_star C_h z i t W w hc hsent
  have hW := (ReferenceLiteralAwaitedAmbiguityRowObservation.physicalDownCompletedAt_iff_completedDownBatch
    rate r i W).mp hcomplete
  have hfixed : ∀ test ∈ ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
      rate rewards C_star C_h z i,
      ReferenceGeneratedPrelaunchDownCohort.testEntry test ∈ W → test.sent = some w := by
    intro test ht he
    have hw := (hsent _ he).2
    change sourceDownSentAt rate rewards C_star C_h z i test.time = some w at hw
    rw [sourceDownSentAt_original_prelaunch_test rate rewards C_star C_h z i test ht] at hw
    exact hw
  intro e he
  obtain ⟨_, _, _, hs, _⟩ := completedDownBatch_suffix_origins_of_fixed_sent_calls
    rate rewards C_star C_h z t r i W w hr hW hfixed e he
  exact hs

/-- Launch is a consequence of the total event after evaluating initialization
banks and actual sender/receiver calls, rather than a conjunct of its body. -/
theorem sourceFixedAwaitedCompletionAt_requires_launch
    (z : Source (p := p)) (t : Fin p.T)
    (h : sourceFixedAwaitedCompletionAt rate rewards C_star C_h z t) :
    actualLaunchBy rate rewards C_star C_h t.val z := by
  have hl := (sourceFixedAwaitedCompletionAt_iff_literal rate rewards C_star C_h z t).mp h
  have hrecord : ∃ r : Record (rate := rate),
      actualRecord rate rewards C_star C_h t z = some r := by
    rcases hl with ⟨r, _, _, _, _, hr, _⟩ | ⟨r, _, _, _, _, hr, _⟩ <;> exact ⟨r, hr⟩
  by_contra hn
  obtain ⟨r, hr⟩ := hrecord
  rw [actualRecord_eq_none_of_not_launchBy rate rewards C_star C_h t z hn] at hr
  cases hr

/-- There is no fixed-awaited completion at a genuinely prelaunch physical date. -/
theorem sourceFixedAwaitedCompletionAt_false_of_prelaunch
    (z : Source (p := p)) (t : Fin p.T)
    (ht : t.val < ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) :
    ¬ sourceFixedAwaitedCompletionAt rate rewards C_star C_h z t := by
  intro h
  have hs := (sourceFixedAwaitedCompletionAt_requires_launch rate rewards C_star C_h z t h).2
  omega

/-- Horizon exhaustion and a launch crossing at the terminal sentinel give no
fixed-awaited completion, although initialization DOWN banks still exist. -/
theorem sourceFixedAwaitedCompletionAt_false_of_terminal_start
    (z : Source (p := p)) (t : Fin p.T)
    (hT : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = p.T) :
    ¬ sourceFixedAwaitedCompletionAt rate rewards C_star C_h z t :=
  sourceFixedAwaitedCompletionAt_false_of_prelaunch rate rewards C_star C_h z t (by
    rw [hT]; exact t.isLt)

/-- No-launch initialization is excluded using its physical branches and banks. -/
theorem sourceFixedAwaitedCompletionAt_false_of_no_launch
    (z : Source (p := p)) (t : Fin p.T)
    (hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = none) :
    ¬ sourceFixedAwaitedCompletionAt rate rewards C_star C_h z t :=
  sourceFixedAwaitedCompletionAt_false_of_terminal_start rate rewards C_star C_h z t
    (ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T rate z rewards C_star C_h hl)

/-- DOWN application to the accepted saved-event interface, after the original
source bank/call/provenance construction above. -/
theorem sourceDownFixedAwaitedCompletionAt_iff_saved
    (z : Source (p := p)) (t : Fin p.T) :
    sourceDownFixedAwaitedCompletionAt rate rewards C_star C_h z t ↔
      ReferenceFirstCollectionAwaitedDownFailureReadout.fixedAwaitedDownFailureAt
        rate rewards C_star C_h z t :=
  (Iff.intro (sourceDownFixedAwaitedCompletionAt_to_literal rate rewards C_star C_h z t)
    (literalDownAmbiguityAt_to_source rate rewards C_star C_h z t)).trans
      (ReferenceLiteralAwaitedAmbiguityRowObservation.literalDownAmbiguityAt_iff_fixedAwaitedDownFailureAt
        rate rewards C_star C_h z t)

/-- UP application to the same accepted interface, without treating a raw
NONE output, an old reply or the initial placeholder as ambiguity. -/
theorem sourceUpFixedAwaitedCompletionAt_iff_saved
    (z : Source (p := p)) (t : Fin p.T) :
    sourceUpFixedAwaitedCompletionAt rate rewards C_star C_h z t ↔
      ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt rate rewards C_star C_h z t :=
  (Iff.intro (sourceUpFixedAwaitedCompletionAt_to_literal rate rewards C_star C_h z t)
    (literalUpAmbiguityAt_to_source rate rewards C_star C_h z t)).trans
      (ReferenceLiteralAwaitedAmbiguityRowObservation.literalUpAmbiguityAt_iff_fixedAwaitedUpFailureAt
        rate rewards C_star C_h z t)

end Bandits.Support.ReferenceCompleteAwaitedBatchSourceCoverage

end
