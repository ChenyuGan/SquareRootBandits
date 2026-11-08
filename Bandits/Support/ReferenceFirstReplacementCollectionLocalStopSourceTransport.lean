/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionStoppedPureUpQuota

/-!
# Original-source dates for the first replacement UP stop

Sources: `sources/zip4/manuscript/06_interruptions.tex:110-177,246-349,477-481`,
`sources/zip4/manuscript/05_binary_transport.tex:20-55,180-239`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`.

The per-date predicate below is the literal detecting-date body of the
original-source awaited-UP ambiguity event. Its source inclusion is kept
separate from the physical-list predicate in
`ReferenceFirstReplacementCollectionStoppedPureUpQuota`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceGeneratedUpBatchPrefixEvent
open Bandits.Support.ReferenceGeneratedUpAwaitedBatchCoverage
open Bandits.Support.ReferenceFirstReplacementCollectionStoppedPureUpQuota

namespace Bandits.Support.ReferenceFirstReplacementCollectionLocalStopSourceTransport

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The literal original-source UP ambiguity event body with its detecting
date fixed. The current record, whole incoming bank, awaited trace, and the two
solutions all come from the same original source run. -/
def originalUpAwaitedAmbiguityAtDate
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (t : Fin p.T) : Prop :=
  ∃ (q : Fin (M p)) (s : ℕ) (hs : s ≤ t.val)
      (hz : source ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
        (rate := rate) rewards C_star C_h q t (1, i) s)
      (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
    let z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
        (rate := rate) rewards C_star C_h q t s i :=
      ⟨source, hz⟩
    let current := ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
      (rate := rate) rewards C_star C_h q t s hs control0 i z
    let bank := current.input.state.upDecoderBank i
    current.output.coordinator.up = some d ∧
      d.input.selectedFollower = i ∧
      ReferenceActiveAffinePositiveTest.upPositive current.input = true ∧
      bank.pending.length + 1 = AffineBatchDecoder.quota p ∧
      (∃ (message : OrdinaryMessageCodec.UpRecord
          (CoordinatorCollectionLedger.codecParams p rate.eta)) (beta : ℕ),
        awaited_up_source_trace rewards C_star C_h q t s hs control0 i z beta message ∧
        (∀ entry ∈ bank.pending ++
          [AffineBatchDecoder.entry p
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time],
          beta ≤ entry.time.val)) ∧
      ∃ v₁ v₂ : AffineChannelLaw.Word (AffineBatchDecoder.width p),
        v₁ ≠ v₂ ∧
        AffineBatchDecoder.satisfies
          ((bank.pending ++
            [AffineBatchDecoder.entry p
              (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
              d.input.time]).map AffineBatchDecoder.Entry.sample) v₁ ∧
        AffineBatchDecoder.satisfies
          ((bank.pending ++
            [AffineBatchDecoder.entry p
              (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
              d.input.time]).map AffineBatchDecoder.Entry.sample) v₂

/-- A fixed original detecting date is a member of the actual original-source
UP awaited ambiguity event. -/
theorem originalUpAwaitedAmbiguityAtDate_mem_event
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (h : originalUpAwaitedAmbiguityAtDate
      (rate := rate) rewards C_star C_h control0 source i t) :
    source ∈ ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEvent
      (rate := rate) rewards C_star C_h control0 := by
  simp only [ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEvent,
    Set.mem_ofPred_eq]
  dsimp only [originalUpAwaitedAmbiguityAtDate] at h
  rcases h with ⟨q, s, hs, hz, d, hbody⟩
  exact ⟨q, t, s, hs, i, hz, d, hbody⟩

/-- The union over the follower and its fixed detecting date is contained in
the literal original-source event. -/
theorem originalUpAwaitedAmbiguityDates_subset_event
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    {source : BootstrapPrivateRoundStreams.SourceInput p |
      ∃ i : Fin (p.m - 1), ∃ t : Fin p.T,
        originalUpAwaitedAmbiguityAtDate
          (rate := rate) rewards C_star C_h control0 source i t} ⊆
      ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEvent
        (rate := rate) rewards C_star C_h control0 := by
  intro source hsource
  rcases hsource with ⟨i, t, hdate⟩
  exact originalUpAwaitedAmbiguityAtDate_mem_event
    (rate := rate) rewards C_star C_h control0 source i t hdate

/-- The first-replacement source-aware common stop at a physical record. -/
def commonSourceStopAt
    (_K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1))
    (_U : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate) : Prop :=
  acceptanceAt r i ∨ physicalFailureAt r ∨
    originalUpAwaitedAmbiguityAtDate (rate := rate) rewards C_star C_h
      control0 source i r.input.time

/-- First source-aware common-stop date, or the physical list length if there
is no common stop. -/
def commonSourceStopIndex
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) : ℕ := by
  classical
  exact K.findIdx (fun r => decide
    (commonSourceStopAt (rate := rate) K i U source rewards C_star C_h control0 r))

/-- Any requested inclusive prefix reaches the source-aware common stop no
later than a supplied detecting coordinate. -/
theorem commonSourceStopIndex_le_of_at
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (f : ℕ) (hf : f < K.length)
    (hstop : commonSourceStopAt (rate := rate) K i U source rewards C_star C_h
      control0 (K.get ⟨f, hf⟩)) :
    commonSourceStopIndex (rate := rate) K i U source rewards C_star C_h control0 ≤ f := by
  classical
  by_contra hnot
  have hlt : f < commonSourceStopIndex (rate := rate) K i U source rewards C_star C_h
      control0 := by omega
  have hno := List.not_of_lt_findIdx (xs := K)
    (p := fun r => decide
      (commonSourceStopAt (rate := rate) K i U source rewards C_star C_h control0 r)) hlt
  have hstop' : commonSourceStopAt (rate := rate) K i U source rewards C_star C_h
      control0 K[f] := by simpa using hstop
  have hyes : decide (commonSourceStopAt (rate := rate) K i U source rewards C_star C_h
      control0 K[f]) = true := by simp [hstop']
  rw [hyes] at hno
  cases hno

/-- Inclusive formed UP count stopped at the source-aware common date. -/
def commonSourceStoppedUpCount
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (b : ℕ) (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (j : ℕ) : ℕ :=
  (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
    ((K.take (min j (commonSourceStopIndex (rate := rate) K i U source rewards
      C_star C_h control0 + 1))).drop b) i).length

/-- The inclusive source-aware prefix is contained in the same UP counter's
local-stop prefix, when the local first stop is the detecting coordinate. -/
theorem commonSourceStoppedUpCount_le_localStoppedFormedCount
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (b : ℕ) (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (f j : ℕ) (_hf : f < K.length)
    (hlocal : stopIndex K i U = f)
    (hcommon : commonSourceStopIndex (rate := rate) K i U source rewards C_star C_h
      control0 ≤ f) :
    commonSourceStoppedUpCount (rate := rate) K b i U source rewards C_star C_h
        control0 j ≤ stoppedFormedCount K b i U (f + 1) := by
  classical
  let nc := min j (commonSourceStopIndex (rate := rate) K i U source rewards
    C_star C_h control0 + 1)
  let left := (K.take nc).drop b
  let right := (K.take (f + 1)).drop b
  let positive : ReferenceCompletePhysicalHistory.RoundRecord p rate →
      List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) :=
    fun r => ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries
      (rate := rate) r i
  have hnc : nc ≤ f + 1 := by dsimp [nc]; omega
  have hprefix : K.take nc <+: K.take (f + 1) := by
    exact (List.take_isPrefix_take).2 (Or.inl hnc)
  have hdrop := hprefix.drop b
  have hflat : left.flatMap positive <+: right.flatMap positive := by
    rcases hdrop with ⟨suffix, hsuffix⟩
    refine ⟨suffix.flatMap positive, ?_⟩
    calc
      left.flatMap positive ++ suffix.flatMap positive =
          (left ++ suffix).flatMap positive := by rw [List.flatMap_append]
      _ = right.flatMap positive := congrArg (fun records => records.flatMap positive) hsuffix
  have hlen : (left.flatMap positive).length ≤ (right.flatMap positive).length := by
    rcases hflat with ⟨suffix, hsuffix⟩
    have hsum := congrArg List.length hsuffix
    simp only [List.length_append] at hsum
    omega
  have hlocalCount : stoppedFormedCount K b i U (f + 1) =
      (right.flatMap positive).length := by
    simp [stoppedFormedCount, hlocal, right, positive,
      ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries]
  simpa [commonSourceStoppedUpCount, nc, left, positive,
    ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries] using
      hlen.trans_eq hlocalCount.symm

/-- The original awaited-source trace follows once the original run's entire
stamped interval is aligned record-for-record with the canonical physical
prefix and every selected call is discharged by the local awaited-call
certificate. -/
private theorem awaitedSourceTrace_of_aligned_records
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (beta : ℕ)
    (message : OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta))
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (hsbeta : s ≤ beta) (hbetat : beta ≤ t.val)
    (halign : ∀ record ∈
        (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega)
          (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
            (rate := rate) rewards C_star C_h q t s hs control0 i z)).records,
      beta ≤ record.input.time.val → record.input.time.val ≤ t.val →
      ReferenceSelectedAffinePairLaw.selectedChannel p
        (record.input.row.2 record.input.time).1 = some (1, i) →
      ∃ x ∈ K, record = x ∧ beta ≤ x.input.time.val ∧
        x.input.time.val ≤ t.val ∧
        ReferenceSelectedAffinePairLaw.selectedChannel p
          (x.input.row.2 x.input.time).1 = some (1, i) ∧
        awaitedCall x i message) :
    awaited_up_source_trace rewards C_star C_h q t s hs control0 i z beta message := by
  dsimp only [awaited_up_source_trace]
  refine ⟨hsbeta, hbetat, ?_⟩
  intro record hrecord hbeta htime hchannel
  obtain ⟨x, _hxK, hEq, _, _, _, hcall⟩ :=
    halign record hrecord hbeta htime hchannel
  rw [hEq]
  rcases hcall with ⟨hsent, d, hd, hdi, _hcheck, hselected, henabled,
    haccept, _hexpected⟩
  exact ⟨hsent, d, hd, hdi, hselected, henabled, haccept⟩

/-- Transfer a fixed local UP ambiguity to the literal original-source event
once its current record and full awaited trace have been reconstructed. -/
private theorem originalDateEvent_of_fixedLocalAmbiguity
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (hsource : source = z.1)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (U : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hlocal : fixedAwaitedAmbiguityAt K i U r)
    (hcurrent : ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
      (rate := rate) rewards C_star C_h q t s hs control0 i z = r)
    (htrace : ∀ (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      r.output.coordinator.up = some d →
      ∃ (beta : ℕ),
        awaited_up_source_trace rewards C_star C_h q t s hs control0 i z beta U ∧
        ∀ entry ∈
          ((ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
              (rate := rate) rewards C_star C_h q t s hs control0 i z).input.state.upDecoderBank
              i).pending ++
            [AffineBatchDecoder.entry p
              (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
              d.input.time],
          beta ≤ entry.time.val) :
    originalUpAwaitedAmbiguityAtDate (rate := rate) rewards C_star C_h
      control0 source i t := by
  classical
  let current := ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
    (rate := rate) rewards C_star C_h q t s hs control0 i z
  subst source
  have hlocal' := hlocal
  rw [← hcurrent] at hlocal'
  rcases hlocal' with ⟨_hUsigma, dLocal, beta0, hdLocal, hdi, _hcheck,
    heligible, _hbank, _hdtime, hlength, _hrawEq, _hrawNone,
    hequations, hother, _htimes, _hcalls⟩
  have hdiagR : r.output.coordinator.up = some dLocal := by
    rw [← hcurrent]
    exact hdLocal
  rcases htrace dLocal hdiagR with ⟨beta, hawaited, hentryTime⟩
  have hdCurrent : current.output.coordinator.up = some dLocal := hdLocal
  have hpositive : ReferenceActiveAffinePositiveTest.upPositive current.input = true := by
    have h := ReferenceActiveAffinePositiveTest.record_upPositive current
    rw [hdCurrent, ReferenceActiveAffinePositiveTest.upDiagnosticPositive] at h
    simpa [heligible] using h
  refine ⟨q, s, hs, z.2, dLocal, ?_⟩
  dsimp only [originalUpAwaitedAmbiguityAtDate, current]
  refine ⟨hdCurrent, hdi, hpositive, ?_, ⟨U, beta, hawaited, ?_⟩, ?_⟩
  · simpa only [current, hcurrent, List.length_append, List.length_singleton] using hlength
  · exact hentryTime
  · rcases hother with ⟨other, hneq, heq⟩
    refine ⟨ActiveFollowerArmChoice.offeredUpWord rate.eta U, other, ?_, ?_, ?_⟩
    · exact Ne.symm hneq
    · apply (AffineBatchDecoder.satisfies_samples_iff
        (B := AffineBatchDecoder.width p) _
        (ActiveFollowerArmChoice.offeredUpWord rate.eta U)).2
      intro entry hentry
      exact hequations entry hentry
    · apply (AffineBatchDecoder.satisfies_samples_iff
        (B := AffineBatchDecoder.width p) _ other).2
      intro entry hentry
      exact heq entry hentry

/-- A record at a list coordinate of a computed run is the literal record
formed at that same physical round. -/
private theorem run_records_getElem?_actualRunRecordAt
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (index : ℕ) (hindex : index < total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
      hspan hmode).records[index]? = some
      (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selected rewards
        start index (by omega) hmode) := by
  induction total generalizing index with
  | zero => omega
  | succ total ih =>
      have hspan' : start + (total + 1) ≤ p.T := by omega
      have hprefixSpan : start + total ≤ p.T := by omega
      have hprefixLength := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
        rewards start total hprefixSpan hmode
      rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
        initial rows selected rewards start total hspan' hmode]
      by_cases hlt : index < total
      · rw [List.getElem?_append_left (by simpa [hprefixLength] using hlt)]
        exact ih hprefixSpan index hlt
      · have hlast : index = total := by omega
        subst index
        simp [hprefixLength]

/-- Calendar bounds and the canonical K-prefix identify every original-run
record in a stamped interval with the same physical K record. -/
private theorem originalIntervalRecord_aligned
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total c f : ℕ) (hspan : start + total ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (R : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (hR : R = (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start total hspan hmode).records)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (hKprefix : K <+: R.drop c)
    (hf : f < K.length) (t : Fin p.T) (ht : t.val = start + c + f)
    (beta : ℕ) (hbeta : start + c ≤ beta)
    (sourceRecords : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (hsourceRecords : sourceRecords = R)
    (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (record : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hrecord : record ∈ sourceRecords)
    (hrecordBeta : beta ≤ record.input.time.val)
    (hrecordTime : record.input.time.val ≤ t.val)
    (hchannel : ReferenceSelectedAffinePairLaw.selectedChannel p
      (record.input.row.2 record.input.time).1 = some (1, i))
    (hcall : ∀ x ∈ K, beta ≤ x.input.time.val → x.input.time.val ≤ t.val →
      ReferenceSelectedAffinePairLaw.selectedChannel p
        (x.input.row.2 x.input.time).1 = some (1, i) → awaitedCall x i U) :
    ∃ x ∈ K, record = x ∧ beta ≤ x.input.time.val ∧ x.input.time.val ≤ t.val ∧
      ReferenceSelectedAffinePairLaw.selectedChannel p
        (x.input.row.2 x.input.time).1 = some (1, i) ∧ awaitedCall x i U := by
  have hrecordRun : record ∈
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
        hspan hmode).records := by
    rw [← hR, ← hsourceRecords]
    exact hrecord
  obtain ⟨n, hget⟩ := List.mem_iff_getElem?.mp hrecordRun
  have hn : n < total := by
    have hlt := (List.getElem?_eq_some_iff.mp hget).1
    rw [ReferenceActivePhysicalHorizon.run_record_count] at hlt
    exact hlt
  have hactual := run_records_getElem?_actualRunRecordAt initial rows selected rewards
    start total hspan hmode n hn
  have hrecordEq : record =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selected
        rewards start n (by omega) hmode :=
    Option.some.inj (hget.symm.trans hactual)
  have htime : record.input.time.val = start + n := by
    rw [hrecordEq]
    simp [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
  have hcn : c ≤ n := by omega
  have hnf : n ≤ c + f := by omega
  let a := n - c
  have ha : a ≤ f := by dsimp [a]; omega
  have haLt : a < K.length := lt_of_le_of_lt ha hf
  have hgetR : R[n]? = some record := by
    simpa only [hR] using hget
  have hdropGet : (R.drop c)[a]? = some record := by
    have hsum : c + a = n := by dsimp [a]; omega
    simpa only [List.getElem?_drop, hsum] using hgetR
  obtain ⟨suffix, hK⟩ := hKprefix
  have hKgetOpt : K[a]? = some record := by
    rw [← hK] at hdropGet
    rw [List.getElem?_append_left haLt] at hdropGet
    exact hdropGet
  have hKget := (List.getElem?_eq_some_iff.mp hKgetOpt).2
  let x := K.get ⟨a, haLt⟩
  have hx : x = record := by dsimp [x]; exact hKget
  have hxmem : x ∈ K := by
    dsimp [x]
    exact List.get_mem _ _
  have hcall' : awaitedCall x i U := by
    apply hcall x hxmem
    · rw [hx]
      exact hrecordBeta
    · rw [hx]
      exact hrecordTime
    · rw [hx]
      exact hchannel
  exact ⟨x, hxmem, hx.symm, by rw [hx]; exact hrecordBeta,
    by rw [hx]; exact hrecordTime, by rw [hx]; exact hchannel, hcall'⟩

/-- A kept prefix cannot contain the first transition into dagger. Its
failure witness is a physical local stop, so the incoming state at the first
detecting coordinate is still ordinary. -/
private theorem localKept_prefix_nondagger
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (Z : ℕ → ReferenceActivePhysicalStep.State p rate)
    (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (f : ℕ)
    (hlinks : ∀ q : Fin K.length,
      (K.get q).input.state = Z q.val ∧ (K.get q).output.next = Z (q.val + 1))
    (hzero : (Z 0).coordinator ≠ .dagger)
    (hf : f < K.length)
    (hkept : ReferenceFirstReplacementCollectionStoppedPureUpQuota.kept K i U f) :
    ∀ j : ℕ, j ≤ f → (Z j).coordinator ≠ .dagger := by
  intro j
  induction j with
  | zero => intro _; exact hzero
  | succ j ih =>
      intro hj
      have hjK : j < K.length := by omega
      have hbefore := ih (by omega)
      intro hdagger
      obtain ⟨reason, hreason⟩ :=
        ReferenceFirstReplacementCollectionPureUpWindowCut.first_dagger_record_failure
          (K.get ⟨j, hjK⟩)
          (by rw [(hlinks ⟨j, hjK⟩).1]; exact hbefore)
          (by rw [(hlinks ⟨j, hjK⟩).2]; exact hdagger)
      have hnotStop := hkept (K.get ⟨j, hjK⟩) (List.mem_iff_getElem.mpr
        ⟨j, by simp; omega, by simp⟩)
      exact hnotStop (Or.inr (Or.inl (Or.inl ⟨reason, hreason⟩)))

/-- The original K calendar places every physical round strictly before the
detecting coordinate at or after the cutoff date. -/
private theorem K_prefix_times_ge_cutoff
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (f : ℕ) (hf : f < K.length) (cutTime : ℕ)
    (hcalendar : ∀ q : Fin K.length,
      (K.get q).input.time.val + 1 = cutTime + 1 + q.val)
    (time : Fin p.T)
    (htime : time ∈ (K.take f).map (fun record => record.input.time)) :
    cutTime ≤ time.val := by
  obtain ⟨record, hrecord, hrecordTime⟩ := List.mem_map.mp htime
  obtain ⟨a, ha, hget⟩ := List.mem_iff_getElem.mp hrecord
  have haf : a < f := by simp only [List.length_take] at ha; omega
  have haK : a < K.length := lt_of_lt_of_le haf (Nat.le_of_lt hf)
  let q : Fin K.length := ⟨a, haK⟩
  have hcal := hcalendar q
  have hcal' : K[a].input.time.val + 1 = cutTime + 1 + a := by
    simpa only [q, List.get_eq_getElem] using hcal
  have hrecordTime' : record.input.time.val + 1 = cutTime + 1 + a := by
    have hgetK : K[a] = record := by
      simpa only [List.getElem_take] using hget
    rw [hgetK] at hcal'
    exact hcal'
  rw [← hrecordTime]
  omega

/-- A pending entry in a decoder run came from the incoming bank or an
eligible positive in one of the listed rounds. -/
private theorem decoderRun_pending_mem_initial_or_positive
    (tr : AffineBatchDecoder.Trace p)
    (rounds : List (Fin p.T))
    (state : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hsmall : state.pending.length < AffineBatchDecoder.quota p)
    (hcomplete : ∀ batch ∈ state.completed,
      batch.length = AffineBatchDecoder.quota p)
    (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (hentry : entry ∈ (AffineBatchDecoder.run p tr rounds state).pending) :
    entry ∈ state.pending ∨ entry ∈ AffineBatchDecoder.positives p tr rounds := by
  induction rounds generalizing state with
  | nil => simpa only [AffineBatchDecoder.run] using Or.inl hentry
  | cons t ts ih =>
      have hspec := AffineBatchDecoder.step_spec p tr state t hsmall hcomplete
      rcases ih (AffineBatchDecoder.step p tr state t) hspec.1 hspec.2.1 hentry with
        hpending | hrest
      · by_cases hlt :
            (state.pending ++ AffineBatchDecoder.positiveAt p tr t).length <
              AffineBatchDecoder.quota p
        · have hmem : entry ∈
              state.pending ++ AffineBatchDecoder.positiveAt p tr t := by
            simpa only [AffineBatchDecoder.step, ite_eq_left hlt] using hpending
          rcases List.mem_append.mp hmem with hprior | hnow
          · exact Or.inl hprior
          · right
            rw [AffineBatchDecoder.positives_cons]
            exact List.mem_append.mpr (Or.inl hnow)
        · simp only [AffineBatchDecoder.step, ite_eq_right hlt, List.mem_nil_iff] at hpending
      · right
        rw [AffineBatchDecoder.positives_cons]
        exact List.mem_append.mpr (Or.inr hrest)

/-- With an empty incoming pending bank, final pending entries came from a
positive on a physical round in the listed prefix. -/
private theorem decoderRun_pending_time_mem_rounds_of_emptyPending
    (tr : AffineBatchDecoder.Trace p)
    (rounds : List (Fin p.T))
    (state : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hsmall : state.pending.length < AffineBatchDecoder.quota p)
    (hcomplete : ∀ batch ∈ state.completed,
      batch.length = AffineBatchDecoder.quota p)
    (hempty : state.pending = [])
    (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (hentry : entry ∈
      (AffineBatchDecoder.run p tr rounds state).pending) :
    entry.time ∈ rounds := by
  have hmem := decoderRun_pending_mem_initial_or_positive
    (p := p) tr rounds state hsmall hcomplete entry hentry
  rcases hmem with hinitial | hpositive
  · rw [hempty] at hinitial
    simp at hinitial
  · exact (AffineBatchDecoder.mem_positives_iff p tr rounds entry).mp hpositive |>.1

/-- Canonical-prefix transport for one actual first local ambiguity. The
source run is identified with the same cutoff replay; the decoder replay ends
at the detecting record's incoming state. -/
private theorem canonicalLocalAmbiguity_originalDateEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (hsource : source = z.1)
    (R : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (c total f : ℕ) (hf : f < K.length)
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (hspan : s + total ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hR : R = (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      s total hspan hmode).records)
    (hKprefix : K <+: R.drop c)
    (hsourceRun : (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s)
      (by omega) (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
        (rate := rate) rewards C_star C_h q t s hs control0 i z)).records = R)
    (cut : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hcutMem : cut ∈ R)
    (hcutChosen : ReferenceUpDecoderBankInvariant.isActualCutoffChosen
      cut.output.preparation.coordinator)
    (hcutTime : cut.input.time.val = s + c)
    (hcalendar : ∀ j : Fin K.length,
      (K.get j).input.time.val + 1 = cut.input.time.val + 1 + j.val)
    (Z : ℕ → ReferenceActivePhysicalStep.State p rate)
    (hlinks : ∀ j : Fin K.length,
      (K.get j).input.state = Z j.val ∧ (K.get j).output.next = Z (j.val + 1))
    (hzero : (Z 0).coordinator ≠ .dagger)
    (hcurrent : ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
      (rate := rate) rewards C_star C_h q t s hs control0 i z = K.get ⟨f, hf⟩)
    (hcurrentTime : (K.get ⟨f, hf⟩).input.time = t)
    (htimeDate : t.val = cut.input.time.val + f)
    (U : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hkept : ReferenceFirstReplacementCollectionStoppedPureUpQuota.kept K i U f)
    (hprefixState :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards s c
        (by omega) hmode).finalState = cut.input.state)
    (hprefixRecords :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards s (c + f)
        (by omega) hmode).records.drop c = K.take f)
    (hendState :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards s (c + f)
        (by omega) hmode).finalState = Z f)
    (hlocal : fixedAwaitedAmbiguityAt K i U (K.get ⟨f, hf⟩)) :
    source=z.1 ∧
    originalUpAwaitedAmbiguityAtDate (rate := rate) rewards C_star C_h
      control0 z.1 i t ∧
    ∀ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
      (K.get ⟨f, hf⟩).output.coordinator.up = some d →
      ∃ beta : ℕ, cut.input.time.val ≤ beta ∧
        awaited_up_source_trace rewards C_star C_h q t s hs control0 i z beta U ∧
        ∀ entry ∈ ((K.get ⟨f, hf⟩).input.state.upDecoderBank i).pending ++
          [AffineBatchDecoder.entry p
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time],
          beta ≤ entry.time.val := by
  classical
  let r := K.get ⟨f, hf⟩
  have hordinaryPrefix := localKept_prefix_nondagger K Z i U f hlinks hzero hf hkept
  have hordinary :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards s (c + f)
        (by omega) hmode).finalState.coordinator ≠ .dagger := by
    rw [hendState]
    exact hordinaryPrefix f (by omega)
  have hcutMemRun : cut ∈
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards s total
        hspan hmode).records := by rw [← hR]; exact hcutMem
  have hcutPending := ReferenceUpDecoderBankInvariant.run_cutoff_up_pending_empty
    initial rows selected rewards s total hspan hmode hinitial cut hcutMemRun hcutChosen
  have hcutInvariant :=
    ReferenceUpDecoderBankInvariant.run_record_input_upBankInvariant
      initial rows selected rewards s total hspan hmode hinitial cut hcutMemRun
  have hcutInvariant' := hcutInvariant
  change ReferenceUpDecoderBankInvariant.upBankInvariant cut.input.state at hcutInvariant'
  change ReferenceUpDecoderBankInvariant.coordinatorBankInvariant
      cut.input.state.coordinator cut.input.state.upDecoderBank at hcutInvariant'
  have hcutWellFormed := hcutInvariant'.1
  have hcutSmall := (hcutWellFormed i).1
  have hcutComplete := (hcutWellFormed i).2
  have hintervalSpan : s + (c + f) ≤ p.T := by
    have ht := t.isLt
    rw [htimeDate, hcutTime] at ht
    omega
  have hfold0 := ReferenceCoordinatorUpIntervalWindow.run_interval_focal_decoder_fold
    initial rows selected rewards s c (c + f) (by omega) hintervalSpan hmode
    hinitial hordinary i
  have hfold :
      AffineBatchDecoder.run p
        (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace (K.take f) i)
        ((K.take f).map (fun record => record.input.time))
        (cut.input.state.upDecoderBank i) = (Z f).upDecoderBank i := by
    change AffineBatchDecoder.run p
        (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
          ((ReferenceActivePhysicalHorizon.run initial rows selected rewards s (c + f)
            (by omega) hmode).records.drop c) i)
        (((ReferenceActivePhysicalHorizon.run initial rows selected rewards s (c + f)
            (by omega) hmode).records.drop c).map
          (fun record => record.input.time))
        (((ReferenceActivePhysicalHorizon.run initial rows selected rewards s c
            (by omega) hmode).finalState).upDecoderBank i) =
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards s (c + f)
        (by omega) hmode).finalState).upDecoderBank i at hfold0
    rw [hprefixRecords, hprefixState, hendState] at hfold0
    exact hfold0
  have hlocal' := hlocal
  rcases hlocal' with ⟨_hUsigma, d, beta0, hd, hdi, _hcheck, _heligible,
    _hbank, hdtime, _hlength, _hrawEq, _hrawNone, _hequations, _hother,
    htimes, hcalls⟩
  have hcurrentClock : d.input.time.val = t.val := by
    calc
      d.input.time.val = (K.get ⟨f, hf⟩).input.time.val := congrArg Fin.val hdtime
      _ = t.val := congrArg Fin.val hcurrentTime
  have hentryFloor (entry : AffineBatchDecoder.Entry p.T
      (AffineBatchDecoder.width p))
      (hentry : entry ∈ (r.input.state.upDecoderBank i).pending) :
      cut.input.time.val ≤ entry.time.val := by
    have hstate : r.input.state.upDecoderBank i = (Z f).upDecoderBank i := by
      dsimp only [r]
      exact congrArg (fun state => state.upDecoderBank i) (hlinks ⟨f, hf⟩).1
    have hentryEnd : entry ∈ ((Z f).upDecoderBank i).pending := by
      rw [← hstate]
      exact hentry
    have hentryRun : entry ∈
        (AffineBatchDecoder.run p
          (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace (K.take f) i)
          ((K.take f).map (fun record => record.input.time))
          (cut.input.state.upDecoderBank i)).pending := by
      rw [hfold]
      exact hentryEnd
    have htimeInPrefix :=
      decoderRun_pending_time_mem_rounds_of_emptyPending (p := p)
      (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace (K.take f) i)
      ((K.take f).map (fun record => record.input.time)) (cut.input.state.upDecoderBank i)
      hcutSmall hcutComplete (hcutPending i) entry hentryRun
    exact K_prefix_times_ge_cutoff K f hf cut.input.time.val hcalendar
      entry.time htimeInPrefix
  have htrace : ∀ (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      r.output.coordinator.up = some diagnostic →
      ∃ beta : ℕ, cut.input.time.val ≤ beta ∧
        awaited_up_source_trace rewards C_star C_h q t s hs control0 i z beta U ∧
        ∀ entry ∈
          ((ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
            (rate := rate) rewards C_star C_h q t s hs control0 i z).input.state.upDecoderBank
            i).pending ++
          [AffineBatchDecoder.entry p
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
            diagnostic.input.time], beta ≤ entry.time.val := by
    intro diagnostic hdiagnostic
    have hsame : d = diagnostic := Option.some.inj (hd.symm.trans hdiagnostic)
    subst diagnostic
    let beta := max beta0 cut.input.time.val
    have hbetaStart : s ≤ beta := by dsimp [beta]; omega
    have hbetaDetect : beta ≤ t.val := by
      have htimeStamp := htimes
        (AffineBatchDecoder.entry p
          (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time)
        (List.mem_append_right _ (by simp))
      change beta0 ≤ d.input.time.val ∧ d.input.time.val ≤
        (K.get ⟨f, hf⟩).input.time.val at htimeStamp
      have hbeta0 : beta0 ≤ t.val := by simpa [hcurrentClock] using htimeStamp.1
      dsimp [beta]
      omega
    have halign : ∀ record ∈
        (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega)
          (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
            (rate := rate) rewards C_star C_h q t s hs control0 i z)).records,
      beta ≤ record.input.time.val → record.input.time.val ≤ t.val →
      ReferenceSelectedAffinePairLaw.selectedChannel p
        (record.input.row.2 record.input.time).1 = some (1, i) →
      ∃ x ∈ K, record = x ∧ beta ≤ x.input.time.val ∧ x.input.time.val ≤ t.val ∧
        ReferenceSelectedAffinePairLaw.selectedChannel p
          (x.input.row.2 x.input.time).1 = some (1, i) ∧ awaitedCall x i U := by
      intro record hrecord hbetaRecord htimeRecord hchannelRecord
      obtain ⟨x, hx, hEq, hxBeta, hxTime, hxChannel, hawaitedCall⟩ :=
        originalIntervalRecord_aligned initial rows selected rewards s total c f hspan hmode
          R hR K hKprefix hf t (by omega) beta (by dsimp [beta]; omega)
          (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega)
            (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
              (rate := rate) rewards C_star C_h q t s hs control0 i z)).records
          hsourceRun i U record hrecord hbetaRecord htimeRecord hchannelRecord
          (by
            intro x hx hxβ hxT hxChannel
            apply hcalls x hx
            · exact le_trans (Nat.le_max_left beta0 _) hxβ
            · have htimeEq : t.val = (K.get ⟨f, hf⟩).input.time.val :=
                congrArg Fin.val hcurrentTime.symm
              exact hxT.trans (le_of_eq htimeEq)
            · exact hxChannel)
      exact ⟨x, hx, hEq, hxBeta, hxTime, hxChannel, hawaitedCall⟩
    have hawaited := awaitedSourceTrace_of_aligned_records rewards C_star C_h q t s hs
      control0 i z beta U K hbetaStart hbetaDetect halign
    have hentryBound : ∀ entry ∈
        ((ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
          (rate := rate) rewards C_star C_h q t s hs control0 i z).input.state.upDecoderBank
          i).pending ++
        [AffineBatchDecoder.entry p
          (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time],
        beta ≤ entry.time.val := by
      intro entry hentry
      have hentryLocal : entry ∈ ((r.input.state.upDecoderBank i).pending ++
          [AffineBatchDecoder.entry p
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]) := by
        simpa only [hcurrent, r] using hentry
      rcases List.mem_append.mp hentryLocal with hpending | hdetect
      · have hlow := (htimes entry hentryLocal).1
        have hfloor := hentryFloor entry hpending
        dsimp [beta]
        omega
      · simp only [List.mem_singleton] at hdetect
        subst entry
        change beta ≤ d.input.time.val
        calc
          beta ≤ t.val := hbetaDetect
          _ = d.input.time.val := hcurrentClock.symm
    exact ⟨beta, Nat.le_max_right _ _, hawaited, hentryBound⟩
  have hEvent := originalDateEvent_of_fixedLocalAmbiguity
    rewards C_star C_h control0 source q t s hs i z hsource K U r hlocal hcurrent (by
      intro diagnostic hdiagnostic
      obtain ⟨beta, _, hawaited, hbound⟩ := htrace diagnostic hdiagnostic
      exact ⟨beta, hawaited, hbound⟩)
  refine ⟨hsource, by simpa only [hsource] using hEvent, ?_⟩
  intro diagnostic hdiagnostic
  obtain ⟨beta, hfloor, hawaited, hbound⟩ := htrace diagnostic hdiagnostic
  refine ⟨beta, hfloor, hawaited, ?_⟩
  simpa only [hcurrent] using hbound

/-- Reconstruct the original source constructor at a canonical first ambiguity.
All replay premises of the interval adapter are obtained from the actual cut. -/
private theorem canonicalSource_first_ambiguity
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (c : ℕ)
    (cut : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hc : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[c]? = some cut)
    (hchosen : ReferenceUpDecoderBankInvariant.isActualCutoffChosen
      cut.output.preparation.coordinator)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (hKprefix : K <+: (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).drop c)
    (hcalendar : ∀ a : Fin K.length,
      (K.get a).input.time.val + 1 = cut.input.time.val + 1 + a.val)
    (hlinks : ∀ a : Fin K.length,
      (K.get a).input.state = ReferenceCollectionSegmentExtraction.endpointState
        cut.input.state (K.take a.val) ∧
      (K.get a).output.next = ReferenceCollectionSegmentExtraction.endpointState
        cut.input.state (K.take (a.val + 1)))
    (hzero : cut.input.state.coordinator ≠ .dagger)
    (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (f : Fin K.length) (hkept : kept K i U f.val)
    (hamb : fixedAwaitedAmbiguityAt K i U (K.get f))
    (control0 : ContinuousLearningRows.TimeControl p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let t := (K.get f).input.time
    ∃ (hs : s ≤ t.val)
      (hz : source ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
        (rate := rate) rewards C_star C_h J t (1, i) s),
      ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
        (rate := rate) rewards C_star C_h J t s hs control0 i ⟨source, hz⟩ = K.get f ∧
      (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega)
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h J t s hs control0 i ⟨source, hz⟩)).records = R ∧
      originalUpAwaitedAmbiguityAtDate (rate := rate) rewards C_star C_h
        control0 source i t ∧
      ∀ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
        (K.get f).output.coordinator.up = some d →
        ∃ beta : ℕ, cut.input.time.val ≤ beta ∧
          awaited_up_source_trace rewards C_star C_h J t s hs control0 i
            ⟨source, hz⟩ beta U ∧
          ∀ entry ∈ ((K.get f).input.state.upDecoderBank i).pending ++
            [AffineBatchDecoder.entry p
              (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time],
            beta ≤ entry.time.val := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  let r := K.get f
  let t := r.input.time
  let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState cut.input.state (K.take j)
  obtain ⟨initial, active, hlaunch, _, _, hinvariant, _, hfull, hRuns⟩ :=
    ReferenceFirstReplacementCollectionPureUpWindowCut.source_interval_runs
      rate source rewards C_star C_h c cut hc K hKprefix
  have hsT : s ≤ p.T :=
    ReferenceCompletePhysicalHistory.physicalStart_le_T rate source rewards C_star C_h
  have hcutIndex : c < p.T - s := by
    have h := (List.getElem?_eq_some_iff.mp hc).1
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] at h
    exact h
  have hcutActual : cut = ReferenceAssignmentPayloadChronology.actualRunRecordAt
      initial source.1.2 J rewards s c (by omega) active := by
    have hget : (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
        (p.T - s) (by omega) active).records[c]? = some cut := by
      rw [← hfull]; exact hc
    exact Option.some.inj (hget.symm.trans (run_records_getElem?_actualRunRecordAt
      initial source.1.2 J rewards s (p.T - s) (by omega) active c hcutIndex))
  have hcutTime : cut.input.time.val = s + c := by
    rw [hcutActual]; rfl
  have htime : t.val = s + c + f.val := by
    have h := hcalendar f
    change r.input.time.val + 1 = cut.input.time.val + 1 + f.val at h
    dsimp only [t]; omega
  have hsf : s ≤ t.val := by omega
  have hindex : c + f.val < p.T - s := by have := t.isLt; omega
  have hlookup : R[c + f.val]? = some r := by
    obtain ⟨suffix, heq⟩ := hKprefix
    have hget : (R.drop c)[f.val]? = some r := by
      rw [← heq, List.getElem?_append_left f.isLt]
      exact List.getElem?_eq_getElem f.isLt
    simpa only [List.getElem?_drop] using hget
  have hrActual : r = ReferenceAssignmentPayloadChronology.actualRunRecordAt
      initial source.1.2 J rewards s (c + f.val) (by omega) active := by
    have hget : (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
        (p.T - s) (by omega) active).records[c + f.val]? = some r := by
      rw [← hfull]; exact hlookup
    exact Option.some.inj (hget.symm.trans (run_records_getElem?_actualRunRecordAt
      initial source.1.2 J rewards s (p.T - s) (by omega) active (c + f.val) hindex))
  have hrows : r.input.rows = source.1.2 := by rw [hrActual]; rfl
  have hselected : r.input.selected = J := by rw [hrActual]; rfl
  have hambCopy := hamb
  obtain ⟨_, d, beta, hd, hdi, _, heligible, _⟩ := hambCopy
  obtain ⟨ledger, _, _, _, _, _, hdraw, _, hslot, _⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r d hd
  have hgate := (CoordinatorUpReception.roundInput_selected_iff_gate d.input).mp heligible.1
  have hphysicalSlot : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
      PublicDiscreteDraws.upSlot := hslot.symm.trans hgate.2.1
  have hphysicalDraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (r.input.row.2 r.input.time).1 = i := by
    exact (CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw
      (r.input.row.2 r.input.time)).symm.trans (hdraw.symm.trans hdi)
  have hchannel : ReferenceSelectedAffinePairLaw.selectedChannel p
      ((source.1.2 J).2 t).1 = some (1, i) := by
    have h : ReferenceSelectedAffinePairLaw.selectedChannel p
        (r.input.row.2 r.input.time).1 = some (1, i) := by
      rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_up p _ hphysicalSlot,
        hphysicalDraw]
      rfl
    simpa only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hselected, t] using h
  have hcross := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate source rewards C_star C_h).mp (show
      (ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h).isSome =
        true by rw [hlaunch]; rfl)
  have hz : source ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
      (rate := rate) rewards C_star C_h J t (1, i) s := by
    exact ⟨(ReferenceSelectedAffinePairLaw.selector_eq_iff p J t (1, i) source).2
      ⟨rfl, hchannel⟩, hcross, rfl⟩
  let z : UpLaunchSource (rate := rate) rewards C_star C_h J t s i := ⟨source, hz⟩
  have hinput : originalSourceRunInput (rate := rate) rewards C_star C_h J t s hsf control0 i z =
      (⟨(initial, source.1.2, J, rewards), active⟩ :
        ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s) := by
    apply Subtype.ext
    apply Prod.ext
    · exact Option.some.inj ((originalSourceRunInput_launch (rate := rate)
        rewards C_star C_h J t s hsf control0 i z).symm.trans hlaunch)
    · rfl
  have hsourceRun : (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega)
      (originalSourceRunInput (rate := rate) rewards C_star C_h J t s hsf control0 i z)).records =
      R := by
    rw [hinput]
    exact hfull.symm
  have hcurrent : ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
      (rate := rate) rewards C_star C_h J t s hsf control0 i z = r := by
    have hcurrentInput : ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentInput
        (rate := rate) rewards C_star C_h J t s hsf control0 i z =
        (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2 J rewards
          s (c + f.val) (by omega) active).input := by
      let nextInput := fun input :
          ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s =>
        ReferenceActivePhysicalHorizon.roundInputAt input.val.1 input.val.2.1
          input.val.2.2.1 input.val.2.2.2 s input.property
          (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) (by omega) input)
          ⟨t.val, by omega, t.isLt⟩
      change nextInput (originalSourceRunInput
        (rate := rate) rewards C_star C_h J t s hsf control0 i z) = _
      rw [hinput]
      have hsub : t.val - s = c + f.val := by omega
      dsimp only [nextInput, ReferenceActiveHorizonMeasurability.runOfInput,
        ReferenceAssignmentPayloadChronology.actualRunRecordAt]
      simp only [hsub]
      congr 1
      apply Subtype.ext
      change t.val = s + (c + f.val)
      omega
    change ReferenceAssignmentPayloadChronology.actualStepRecord _ = r
    calc
      _ = ReferenceAssignmentPayloadChronology.actualStepRecord
          (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2 J rewards
            s (c + f.val) (by omega) active).input :=
        congrArg ReferenceAssignmentPayloadChronology.actualStepRecord hcurrentInput
      _ = r := by rw [hrActual]; rfl
  obtain ⟨span0, _, hstate0⟩ := hRuns 0 (by omega)
  obtain ⟨spanf, hrecordsf, hstatef⟩ := hRuns f.val (Nat.le_of_lt f.isLt)
  have hcutMem : cut ∈ R := List.mem_of_getElem? hc
  have hevent := canonicalLocalAmbiguity_originalDateEvent rewards C_star C_h control0 source
    J t s hsf i z rfl R K c (p.T - s) f.val f.isLt initial source.1.2 J (by omega)
    active hinvariant hfull hKprefix hsourceRun cut hcutMem hchosen hcutTime hcalendar Z
    hlinks hzero hcurrent rfl (by omega) U hkept
    (by simpa only [Nat.add_zero, Z, List.take_zero,
      ReferenceCollectionSegmentExtraction.endpointState, List.foldl_nil] using hstate0)
    hrecordsf hstatef hamb
  exact ⟨hsf, hz, hcurrent, hsourceRun, hevent.2.1, hevent.2.2⟩

/-- Prefix inclusion also covers the sentinel case with no local stop. -/
private theorem common_count_le_local
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (b : ℕ) (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (horder : commonSourceStopIndex K i U source rewards C_star C_h control0 ≤ stopIndex K i U)
    (j : ℕ) :
    commonSourceStoppedUpCount K b i U source rewards C_star C_h control0 j ≤
      stoppedFormedCount K b i U j := by
  let nc := min j (commonSourceStopIndex K i U source rewards C_star C_h control0 + 1)
  let nl := min j (stopIndex K i U + 1)
  have hlength : nc ≤ nl := by dsimp only [nc, nl]; omega
  have hprefix : (K.take nc).drop b <+: (K.take nl).drop b :=
    ((List.take_isPrefix_take).2 (Or.inl hlength)).drop b
  obtain ⟨suffix, heq⟩ := hprefix
  have hflat := congrArg (fun records =>
    (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries records i).length) heq
  simp only [ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries,
    List.flatMap_append, List.length_append] at hflat
  change (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
      ((K.take nc).drop b) i).length ≤
    (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries ((K.take nl).drop b) i).length
  dsimp only [ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries]
  omega

/-- Original-source first-ambiguity transport and inclusive common-stop quota,
using exactly the formation, origin, inherited bank and reply from the local quota.
Only the actual source inputs occur outside the original birth/cutoff matches. -/
theorem complete_first_replacement_collection_local_stop_source_transport
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
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
        let X := (R.drop v).take (1 + tail.length)
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
            let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.output.next (W.take j)
            let M := fun i => payload.downRecord i
            (∀ i : Fin (p.m - 1),
              (∃ (b : ℕ) (anchor : ReferencePrelaunchFollower.State p rate.eta)
                (memory : ActiveFollowerLifecycle.LocalMemory p)
                (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)),
                ((b = 0 ∧
                  (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
                    .ordinary anchor memory ∧
                  ∃! x : Fin X.length,
                    ReferenceAcceptedUpFollowerHistory.RetainedDown (X.get x) i (M i)) ∨
                 (∃ q : Fin K.length, b = q.val + 1 ∧
                  ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i (M i) ∧
                  (∀ a : Fin K.length, a.val < q.val →
                    ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get a) i (M i)) ∧
                  (K.get q).output.next.followers i = .ordinary anchor memory)) ∧
                b ≤ K.length ∧ anchor.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid anchor ∧
                anchor.lastDown = some (M i) ∧
                U.val = ActiveFollowerQueueOperation.upOfferFields anchor ∧
                U.val.sigma = (M i).val.sigma ∧ 0 < U.val.sigma ∧
                let channel := (Z b).upDecoderBank i
                let Q := AffineBatchDecoder.quota p
                let need := Q - channel.pending.length + Q
                channel.pending.length < Q ∧ need ≤ 2 * Q ∧
                (∀ j : ℕ, j ≤ K.length → stoppedFormedCount K b i U j ≤ need) ∧
                (∀ control0 : ContinuousLearningRows.TimeControl p,
                  (∀ f : Fin K.length, stopIndex K i U = f.val →
                    fixedAwaitedAmbiguityAt K i U (K.get f) →
                    let t := (K.get f).input.time
                    ∃ (hs : s ≤ t.val)
                      (hz : source ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
                        (rate := rate) rewards C_star C_h J t (1, i) s),
                      ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
                        (rate := rate) rewards C_star C_h J t s hs control0 i
                          ⟨source, hz⟩ = K.get f ∧
                      (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega)
                        (originalSourceRunInput (rate := rate) rewards C_star C_h
                          J t s hs control0 i ⟨source, hz⟩)).records = R ∧
                      originalUpAwaitedAmbiguityAtDate (rate := rate) rewards C_star C_h
                        control0 source i t ∧
                      ∀ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
                        (K.get f).output.coordinator.up = some d →
                        ∃ beta : ℕ, cut.input.time.val ≤ beta ∧
                          awaited_up_source_trace rewards C_star C_h J t s hs control0 i
                            ⟨source, hz⟩ beta U ∧
                          ∀ entry ∈ ((K.get f).input.state.upDecoderBank i).pending ++
                            [AffineBatchDecoder.entry p
                              (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
                              d.input.time], beta ≤ entry.time.val) ∧
                  (∀ f : Fin K.length, stopIndex K i U = f.val →
                    localStop K i U (K.get f) →
                    commonSourceStopAt K i U source rewards C_star C_h control0 (K.get f)) ∧
                  commonSourceStopIndex K i U source rewards C_star C_h control0 ≤
                    stopIndex K i U ∧
                  ∀ j : ℕ, j ≤ K.length →
                    commonSourceStoppedUpCount K b i U source rewards C_star C_h control0 j ≤
                      stoppedFormedCount K b i U j ∧
                    commonSourceStoppedUpCount K b i U source rewards C_star C_h control0 j ≤
                      need) ∧
                ((∃ a : Fin K.length, stopIndex K i U = a.val ∧
                  localStop K i U (K.get a) ∧ kept K i U a.val) ∨
                 (stopIndex K i U = K.length ∧ ∀ r ∈ K, ¬ localStop K i U r))) ∨
              ((∀ a : Fin K.length, ∃ state memory,
                  (ReferenceFollowerFixedReply.actualChoice (K.get a) i).configuration =
                    .ordinary state memory ∧ state.status = .unoccupied ∧
                  state.lastDown ≠ some (M i) ∧
                  ReferencePrelaunchFollower.acceptedStart state < (M i).val.sigma ∧
                  ((state.lastDown = none ∧ state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∨
                   ∃ old, state.lastDown = some old ∧ 0 < old.val.sigma ∧
                     old.val.sigma < (M i).val.sigma)) ∧
               (∀ a : Fin K.length,
                 ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get a) i (M i)) ∧
               R[c + 1 + W.length]? = none ∧
               ∀ j : ℕ, j ≤ K.length → formedPositiveEntries (K.take j) i (M i) = [])) ∧
            (∀ (a : Fin K.length) (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
              let r := K.get a
              r.output.coordinator.up = some d →
              d.input.upDecoderBank = (Z a.val).upDecoderBank ∧
              d.expected = ReferenceActivePhysicalStep.upExpected
                (ReferenceActivePhysicalStep.prepare r.input) ∧
              d.raw = (CoordinatorUpReception.decoderTransition d.input).2 ∧
              ∃ ledger,
                ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some ledger ∧
                CoordinatorUpReception.receptionInputCheck
                  (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input ledger) = true ∧
                d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input ledger ∧
                d.decoderAfter = (CoordinatorUpReception.decoderTransition
                  (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input ledger)).1 ∧
                (((ReferenceActivePhysicalStep.receiveUp
                    (ReferenceActivePhysicalStep.prepare r.input) ledger).result = .invalid ∧
                    r.output.next.upDecoderBank = r.input.state.upDecoderBank) ∨
                  ∃ out,
                    ((ReferenceActivePhysicalStep.receiveUp
                      (ReferenceActivePhysicalStep.prepare r.input) ledger).result = .success out ∨
                     (ReferenceActivePhysicalStep.receiveUp
                      (ReferenceActivePhysicalStep.prepare r.input) ledger).result = .rejected out) ∧
                    out.2 = CoordinatorUpReception.decoderBankAfter d.input ∧
                    r.output.next.upDecoderBank = out.2)) ∧
            match R[c + 1 + W.length]? with
            | none => c + 1 + W.length = R.length ∧
                ReferenceCompletePhysicalHistory.completeTerminalState rate source rewards C_star C_h =
                  some (E W.length)
            | some next => next.input.state = E W.length ∧
                ReferenceCollectionPhaseHistory.laterChosen next.input = true ∧
                ∃ ledger saved, (E W.length).coordinator = .collection payload ledger saved ∧
                  ledger.pending = ∅ ∧
                  ∀ i : Fin (p.m - 1), ∃ r ∈ K, ∃ U,
                    ReferenceCollectionPhaseHistory.AcceptedUp r.input i U
          | _ => True
      | _ => True := by
  classical
  have hQuota := complete_first_replacement_collection_stopped_pure_up_quota
    rate source rewards C_star C_h
  have hRoot :=
    ReferenceFirstReplacementCollectionPureUpAcceptanceRoot.complete_first_replacement_collection_pure_up_acceptance
      rate source rewards C_star C_h
  simp (config := { zeta := true }) only [] at hQuota hRoot ⊢
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
    simp only [hb] at hQuota hRoot ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hQuota hRoot ⊢
      cases outcome <;> try trivial
      rename_i core consistent birthStarted hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hQuota hRoot ⊢
      let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      rcases hRoot with ⟨_, _, hRoot⟩
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        simp only [hc] at hQuota hRoot ⊢
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hQuota hRoot ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only at hQuota hRoot ⊢
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          rcases hRoot with ⟨hcalendar, hZ, _, _⟩
          rcases hQuota with ⟨hfollowers, hdiagnostics, hboundary⟩
          have hKprefix : K <+: R.drop c := by
            obtain ⟨hci, hce⟩ := List.getElem?_eq_some_iff.mp hc
            rw [List.drop_eq_getElem_cons hci, hce]
            refine ⟨(R.drop (c + 1)).dropWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input), ?_⟩
            simp only [K, W, List.cons_append, List.takeWhile_append_dropWhile]
          have hchosen : ReferenceUpDecoderBankInvariant.isActualCutoffChosen
              cut.output.preparation.coordinator := by
            have horigin : match cut.output.preparation.coordinator with
                | .live r q base _ => cut.input.state.coordinator = .live r q base
                | _ => True := by
              rw [cut.output_eq]
              change match ReferenceActivePhysicalStep.dispatch cut.input with
                | .live r q base _ => cut.input.state.coordinator = .live r q base
                | _ => True
              unfold ReferenceActivePhysicalStep.dispatch
              cases hphase : cut.input.state.coordinator with
              | first => trivial
              | live r q base =>
                simp only [CoordinatorRoundDispatch.dispatch]
                rfl
              | collection payload ledger saved =>
                simp only [CoordinatorRoundDispatch.dispatch]
                split_ifs <;> trivial
              | dagger => trivial
            rw [hcut] at horigin
            exact ⟨registers, owned, base, _, horigin, hcut, trivial⟩
          have hzero : cut.input.state.coordinator ≠ .dagger := by
            intro hd
            have hp := ReferenceActivePhysicalStep.dispatch_dagger cut.input hd
            change (ReferenceActivePhysicalStep.prepare cut.input).coordinator = .dagger at hp
            have hactual := hcut
            rw [cut.output_eq] at hactual
            change (ReferenceActivePhysicalStep.prepare cut.input).coordinator = _ at hactual
            rw [hp] at hactual
            cases hactual
          refine ⟨?_, hdiagnostics, hboundary⟩
          intro i
          rcases hfollowers i with hformed | habsent
          · rcases hformed with ⟨b, anchor, memory, U, horigin, hbK, hstatus, hdomain,
                hlastDown, hfields, hsigma, hpositive, hsmall, hneed, hcount, hcertificate⟩
            refine Or.inl ⟨b, anchor, memory, U, horigin, hbK, hstatus, hdomain,
              hlastDown, hfields, hsigma, hpositive, hsmall, hneed, hcount, ?_, hcertificate⟩
            intro control0
            have htransport := fun (f : Fin K.length) (hfirst : stopIndex K i U = f.val)
                (hamb : fixedAwaitedAmbiguityAt K i U (K.get f)) =>
              canonicalSource_first_ambiguity rate source rewards C_star C_h c cut hc hchosen
                K hKprefix hcalendar hZ.2.2 hzero i U f
                ((kept_iff_le_stopIndex K i U f.val (Nat.le_of_lt f.isLt)).mpr
                  (Nat.le_of_eq hfirst.symm)) hamb control0
            have hat : ∀ f : Fin K.length, stopIndex K i U = f.val →
                localStop K i U (K.get f) →
                commonSourceStopAt K i U source rewards C_star C_h control0 (K.get f) := by
              intro f hfirst hstop
              rcases hstop with haccept | hfailure | hamb
              · exact Or.inl haccept
              · exact Or.inr (Or.inl hfailure)
              · obtain ⟨_, _, _, _, hevent, _⟩ := htransport f hfirst hamb
                exact Or.inr (Or.inr hevent)
            have horder : commonSourceStopIndex K i U source rewards C_star C_h control0 ≤
                stopIndex K i U := by
              rcases hcertificate with ⟨f, hfirst, hstop, _⟩ | ⟨hnone, _⟩
              · rw [hfirst]
                exact commonSourceStopIndex_le_of_at K i U source rewards C_star C_h control0
                  f.val f.isLt (hat f hfirst hstop)
              · rw [hnone]
                exact List.findIdx_le_length
            refine ⟨htransport, hat, horder, ?_⟩
            intro j hj
            have hle := common_count_le_local K b i U source rewards C_star C_h control0 horder j
            exact ⟨hle, hle.trans (hcount j hj)⟩
          · exact Or.inr habsent

end Bandits.Support.ReferenceFirstReplacementCollectionLocalStopSourceTransport

end
