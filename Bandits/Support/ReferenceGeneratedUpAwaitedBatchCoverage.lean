/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedUpSourceCalendar

/-!
# Actual completed UP batches and literal awaited ambiguity

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`,
`sources/zip4/manuscript/05_binary_transport.tex:20-53,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:164-177,277-284,327-348`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The completed batch is the actual incoming bank followed by the current
positive equation. One physical birth is chosen before quantifying over
candidate words. Every test retains its actual record and optional sender.
The awaited branch below is a literal condition on the same original-source
run; its physical production for an arbitrary reply remains a separate task.
These are internal deterministic inclusions, with no probability estimate,
stale-admissibility assertion, stopping-time identification or source closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceGeneratedUpBatchPrefixEvent
open Bandits.Support.ReferenceGeneratedUpPrefixPositiveHalf
open Bandits.Support.ReferenceGeneratedUpSourceCalendar
open Bandits.Support.AdaptiveAffineBatchTail
open scoped Classical

namespace Bandits.Support.ReferenceGeneratedUpAwaitedBatchCoverage

variable {p : ConstructorDimensions.Parameters}
  {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem fold_records_take
    (s : ℕ) (input : ReferenceActiveHorizonMeasurability.ActiveRunInput
      (p := p) (rate := rate) s)
    (entries : List (ReferenceActivePhysicalHorizon.CalendarEntry p s))
    (acc : ReferenceActivePhysicalHorizon.Run input.val.1) :
    ((entries.foldl (ReferenceActivePhysicalHorizon.foldRound input.val.1 input.val.2.1
      input.val.2.2.1 input.val.2.2.2 s input.property) acc).records).take
        acc.records.length = acc.records := by
  induction entries generalizing acc with
  | nil => simp only [List.foldl_nil, List.take_length]
  | cons entry rest ih =>
      let next := ReferenceActivePhysicalHorizon.foldRound input.val.1 input.val.2.1
        input.val.2.2.1 input.val.2.2.2 s input.property acc entry
      have hlen : acc.records.length ≤ next.records.length := by
        simp only [next, ReferenceActivePhysicalHorizon.foldRound,
          List.length_append, List.length_singleton]
        omega
      change ((rest.foldl _ next).records).take acc.records.length = acc.records
      rw [← Nat.min_eq_left hlen, ← List.take_take, ih]
      simp only [next, ReferenceActivePhysicalHorizon.foldRound,
        List.take_append, List.take_length, Nat.sub_self, List.take_zero, List.append_nil]

private theorem run_records_take (s count n : ℕ) (hspan : s + count ≤ p.T)
    (input : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s)
    (hn : n ≤ count) :
    (ReferenceActiveHorizonMeasurability.runOfInput s n (by omega) input).records =
      (ReferenceActiveHorizonMeasurability.runOfInput s count hspan input).records.take n := by
  have hsplit := ReferenceActivePhysicalHorizon.run_append input.val.1 input.val.2.1
    input.val.2.2.1 input.val.2.2.2 s n (count - n) (by omega) input.property
  have htake := fold_records_take s input
    (ReferenceActivePhysicalHorizon.calendarEntries s (s + n) (count - n) (by omega)
      (by omega))
    (ReferenceActiveHorizonMeasurability.runOfInput s n (by omega) input)
  have hlen := ReferenceActivePhysicalHorizon.run_record_count input.val.1 input.val.2.1
    input.val.2.2.1 input.val.2.2.2 s n (by omega) input.property
  have hsplit' := hsplit
  simp only [Nat.add_sub_of_le hn] at hsplit'
  change _ = (ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1 input.val.2.2.1
    input.val.2.2.2 s count hspan input.property).records.take n
  rw [hsplit']
  simpa only [ReferenceActivePhysicalHorizon.foldCalendar,
    ReferenceActiveHorizonMeasurability.runOfInput, hlen] using htake.symm

private theorem birth_take (i : Fin (p.m - 1)) (s alpha n : ℕ)
    (initial : ReferenceActivePhysicalStep.State p rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate)))
    (ha : s ≤ alpha) (han : alpha - s ≤ n) :
    upBatchBirth i s alpha initial (records.take n) ↔
      upBatchBirth i s alpha initial records := by
  by_cases heq : alpha = s
  · simp only [upBatchBirth, incomingState?, heq, ↓reduceIte, true_or, and_true]
  · have hindex : alpha - s - 1 < n := by omega
    simp only [upBatchBirth, incomingState?, heq, ↓reduceIte,
      List.getElem?_take_of_lt hindex]

private theorem record_test_fields (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (test : Test (AffineBatchDecoder.width p))
    (htest : upTestOfDiagnostic i record.output.coordinator.up = some test) :
    test.time = record.input.time.val ∧
      test.sample = ((record.input.rows record.input.selected).2 record.input.time).2 (1, i) ∧
      test.sent = ReferenceActiveAffinePositiveTest.upSent record.input ∧
      ReferenceActiveAffinePositiveTest.upPositive record.input = true ∧
      ReferenceSelectedAffinePairLaw.selectedChannel p (record.input.row.2 record.input.time).1 =
        some (1, i) := by
  obtain ⟨d, hd, htime, hsample, hsent⟩ :=
    ReferenceGeneratedUpResetPrefixBridge.evidenceUpTest_sender_fields i record test htest
  have hcondition : d.input.selectedFollower = i ∧
      AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) := by
    rw [hd] at htest
    by_contra hn
    simp only [upTestOfDiagnostic, hn, ↓reduceIte, reduceCtorEq] at htest
  obtain ⟨other, ho, ht, hs, _⟩ := actualRecordUpTest_fields i record d hd
    hcondition.1 hcondition.2
  have htestD : upTestOfDiagnostic i (some d) = some test := by
    simpa only [hd] using htest
  have heq : test = other := Option.some.inj (htestD.symm.trans ho)
  obtain ⟨ledger, _, _, _, htime', _, hdraw, _, hslot, _, hgate, _⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields record d hd
  have hselected := hcondition.2.1
  rw [hgate] at hselected
  have hup : d.input.slot = PublicDiscreteDraws.upSlot := (of_decide_eq_true hselected).2.1
  have hfollower : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (record.input.row.2 record.input.time).1 = i := hdraw.symm.trans hcondition.1
  refine ⟨htime.trans (congrArg Fin.val htime'), ?_, ?_, ?_, ?_⟩
  · exact (congrArg Test.sample heq).trans hs
  · exact hsent.trans (actualRecordUpDiagnostic_expected record d hd)
  · rw [ReferenceActiveAffinePositiveTest.record_upPositive, hd]
    simp only [ReferenceActiveAffinePositiveTest.upDiagnosticPositive, hcondition.2, decide_true]
  · change ReferenceSelectedAffinePairLaw.selectedChannel p
      ((record.input.rows record.input.selected).2 record.input.time).1 = some (1, i)
    have hfollower' : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        ((record.input.rows record.input.selected).2 record.input.time).1 = i := hfollower
    rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_up p _ (hslot.symm.trans hup),
      hfollower']
    rfl

private theorem test_hash_of_batch_projection
    (tests : List (Test (AffineBatchDecoder.width p)))
    (batch : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hcoordinates : tests.map (fun test => (test.time, test.sample)) =
      batch.map (fun entry => (entry.time.val, entry.sample)))
    (v : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hv : AffineBatchDecoder.satisfies (batch.map AffineBatchDecoder.Entry.sample) v)
    (test : Test (AffineBatchDecoder.width p)) (htest : test ∈ tests) :
    AffineChannelLaw.affineHash test.sample v = 1 := by
  have hmem : (test.time, test.sample) ∈
      batch.map (fun entry => (entry.time.val, entry.sample)) := by
    rw [← hcoordinates]
    exact List.mem_map.mpr ⟨test, htest, rfl⟩
  obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmem
  have hsample : entry.sample = test.sample := congrArg Prod.snd heq
  apply (AffineBatchDecoder.satisfies_iff_hashes _ v).mp hv
  exact List.mem_map.mpr ⟨entry, hentry, hsample⟩

/-- A single actual completed UP batch supplies one birth for all candidate
words. The explicit sent inequality is retained; no stale-word exclusion is
asserted. Only the retained diagnostic bank is identified on failure paths. -/
theorem actual_completed_up_candidates
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : (originalSourceCurrentRecord (rate := rate)
      rewards C_star C_h q t s hs control0 i z).output.coordinator.up = some d)
    (hi : d.input.selectedFollower = i)
    (hp : ReferenceActiveAffinePositiveTest.upPositive
      (originalSourceCurrentRecord (rate := rate)
        rewards C_star C_h q t s hs control0 i z).input = true)
    (hQ : (((originalSourceCurrentRecord (rate := rate)
      rewards C_star C_h q t s hs control0 i z).input.state.upDecoderBank i).pending).length + 1 =
        AffineBatchDecoder.quota p) :
    let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
    let full := ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input
    let current := originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z
    let bank := current.input.state.upDecoderBank i
    let batch := bank.pending ++ [AffineBatchDecoder.entry p
      (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]
    ∃ alpha, s ≤ alpha ∧ alpha ≤ t.val ∧
      upBatchBirth i s alpha input.val.1
        (full.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) ∧
      let tests := originalSourceTests (rate := rate) rewards C_star C_h q t s hs control0 alpha i z
      let kept := tests.take (AffineBatchDecoder.quota p)
      kept.length = AffineBatchDecoder.quota p ∧
      kept.Pairwise (fun a b => a.time < b.time) ∧
      kept.map (fun test => (test.time, test.sample)) =
        batch.map (fun entry => (entry.time.val, entry.sample)) ∧
      (∀ test ∈ kept, ∃ record, record ∈ full.records ∧
        upTestOfDiagnostic i record.output.coordinator.up = some test ∧
        test.time = record.input.time.val ∧
        test.sample = ((record.input.rows record.input.selected).2 record.input.time).2 (1, i) ∧
        test.sent = ReferenceActiveAffinePositiveTest.upSent record.input ∧
        ReferenceActiveAffinePositiveTest.upPositive record.input = true ∧
        ReferenceSelectedAffinePairLaw.selectedChannel p (record.input.row.2 record.input.time).1 =
          some (1, i) ∧ record.input.time.val ≤ t.val) ∧
      d.decoderAfter.pending = [] ∧ d.decoderAfter.completed = bank.completed ++ [batch] ∧
      d.raw = AffineBatchDecoder.batchOutput batch ∧
      ∀ v : AffineChannelLaw.Word (AffineBatchDecoder.width p),
        AffineBatchDecoder.satisfies (batch.map AffineBatchDecoder.Entry.sample) v →
        (z.1 ∈ upSourceSurvivalEvent (rate := rate)
          rewards C_star C_h q control0 alpha v i (AffineBatchDecoder.quota p) ↔
          ∀ test ∈ kept, test.sent ≠ some v) := by
  dsimp only
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  let full := ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input
  let prior := ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) (by omega) input
  let current := originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z
  let bank := current.input.state.upDecoderBank i
  let batch := bank.pending ++ [AffineBatchDecoder.entry p
    (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]
  obtain ⟨alpha, ha, hat, hbirth, hlength, hcoordinates, _, _, _⟩ :=
    actual_current_positive_birth rewards C_star C_h q t s hs control0 (fun _ => 0) i z hp
  let before := upBatchTestsSince i s alpha
    (prior.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)
  change before.length = bank.pending.length at hlength
  change before.map (fun test => (test.time, test.sample)) =
    bank.pending.map (fun entry => (entry.time.val, entry.sample)) at hcoordinates
  obtain ⟨test, htest, htime, _, _⟩ := originalSourceCurrentRecord_upPositive_fields
    rewards C_star C_h q t s hs control0 i z hp
  obtain ⟨rest, hsplit⟩ := originalSourceTests_split_current
    rewards C_star C_h q t s hs control0 alpha i z ha hat test htest
  let tests := originalSourceTests (rate := rate) rewards C_star C_h q t s hs control0 alpha i z
  let kept := tests.take (AffineBatchDecoder.quota p)
  change tests = before ++ test :: rest at hsplit
  have hprefixLength : (before ++ [test]).length = AffineBatchDecoder.quota p := by
    simp only [List.length_append, List.length_singleton, hlength]
    exact hQ
  have hkept : kept = before ++ [test] := by
    change tests.take _ = _
    rw [hsplit, ← hprefixLength]
    simpa only [List.append_assoc, List.singleton_append] using
      (List.take_left (l₁ := before ++ [test]) (l₂ := rest))
  have hkeptLength : kept.length = AffineBatchDecoder.quota p := by
    rw [hkept]
    exact hprefixLength
  have horder := originalSourceTests_ordered rewards C_star C_h q t s hs control0 alpha i z
  change tests.Pairwise (fun a b => a.time < b.time) at horder
  have hupper : ∀ previous ∈ kept, previous.time ≤ t.val := by
    rw [hsplit, List.pairwise_append] at horder
    intro previous hprevious
    rw [hkept, List.mem_append, List.mem_singleton] at hprevious
    rcases hprevious with hprevious | rfl
    · have hlt := horder.2.2 previous hprevious test List.mem_cons_self
      omega
    · omega
  have hfullBirth : upBatchBirth i s alpha input.val.1
      (full.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) := by
    rw [run_records_take s (p.T - s) (t.val - s) (by omega) input (by omega),
      List.map_take] at hbirth
    exact (birth_take i s alpha (t.val - s) input.val.1 _ ha (by omega)).mp hbirth
  have hcompletion := ReferenceGeneratedUpBatchCalendar.record_up_quota_completion
    current d hd i hi hp hQ
  have hlast : (test.time, test.sample) =
      ((AffineBatchDecoder.entry p
        (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time).time.val,
       (AffineBatchDecoder.entry p
        (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time).sample) := by
    obtain ⟨other, hd', ht, hsample, _⟩ :=
      ReferenceGeneratedUpResetPrefixBridge.evidenceUpTest_sender_fields i current test htest
    have heq : other = d := Option.some.inj (hd'.symm.trans hd)
    subst other
    exact Prod.ext ht hsample
  have hprojection : kept.map (fun test => (test.time, test.sample)) =
      batch.map (fun entry => (entry.time.val, entry.sample)) := by
    rw [hkept, List.map_append, hcoordinates]
    simp only [batch, List.map_append, List.map_singleton, hlast]
  refine ⟨alpha, ha, hat, hfullBirth, hkeptLength, ?_, hprojection, ?_,
    hcompletion.1, hcompletion.2.1, hcompletion.2.2.2, ?_⟩
  · exact (originalSourceTests_ordered rewards C_star C_h q t s hs control0 alpha i z).take
  · intro previous hprevious
    have hmem : previous ∈ tests := List.mem_of_mem_take hprevious
    change previous ∈ recordsUpTests i (full.records.drop (alpha - s)) at hmem
    rw [recordsUpTests] at hmem
    obtain ⟨evidence, hevidence, hproject⟩ := List.mem_filterMap.mp hmem
    obtain ⟨record, hrecord, rfl⟩ := List.mem_map.mp hevidence
    have hf := record_test_fields i record previous hproject
    exact ⟨record, List.mem_of_mem_drop hrecord, hproject, hf.1, hf.2.1, hf.2.2.1,
      hf.2.2.2.1, hf.2.2.2.2, by rw [← hf.1]; exact hupper previous hprevious⟩
  · intro v hv
    rw [mem_upSourceSurvivalEvent_iff rewards C_star C_h q t s hs control0 alpha
      (AffineBatchDecoder.quota p) v i z (AffineBatchDecoder.quota_pos p)]
    constructor
    · rintro ⟨_, _, _, hsurvives⟩ test htest
      exact ((survives_iff v _ tests).mp hsurvives).2 test htest |>.1
    · intro hsent
      refine ⟨AffineBatchDecoder.quota_pos p, le_refl _, hfullBirth, ?_⟩
      apply (survives_iff v _ tests).mpr
      refine ⟨?_, fun test htest => ⟨hsent test htest, ?_⟩⟩
      · have htake := List.length_take_le' (AffineBatchDecoder.quota p) tests
        change kept.length ≤ tests.length at htake
        omega
      · exact test_hash_of_batch_projection kept batch hprojection v hv test htest

/-- Literal source awaitedness on the original full physical run. On every
selected focal UP round in the interval the same offered word is sent, the
actual retained receiver is enabled and selected, and its own ledger accepts
the parsed record. The pending/unaccepted test is the local `acceptUpCheck`.
No assertion about hash equations, completion, or reference acceptance is
part of this predicate. -/
def awaited_up_source_trace
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (beta : ℕ)
    (message : OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta)) : Prop :=
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  let full := ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input
  s ≤ beta ∧ beta ≤ t.val ∧
    ∀ record ∈ full.records,
      beta ≤ record.input.time.val → record.input.time.val ≤ t.val →
      ReferenceSelectedAffinePairLaw.selectedChannel p (record.input.row.2 record.input.time).1 =
        some (1, i) →
      ReferenceActiveAffinePositiveTest.upSent record.input =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta message) ∧
      ∃ diagnostic, record.output.coordinator.up = some diagnostic ∧
        diagnostic.input.selectedFollower = i ∧
        (CoordinatorUpReception.roundInput diagnostic.input).selected = true ∧
        (CoordinatorUpReception.roundInput diagnostic.input).receiverEnabled = true ∧
        CoordinatorCollectionLedger.acceptUpCheck diagnostic.input.ledger i message = true

private theorem current_record_mem
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i) :
    originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z ∈
      (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega)
        (originalSourceRunInput (rate := rate)
          rewards C_star C_h q t s hs control0 i z)).records := by
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  have hsucc := run_records_take s (p.T - s) (t.val - s + 1) (by omega) input (by omega)
  have happend : (ReferenceActiveHorizonMeasurability.runOfInput s
      (t.val - s + 1) (by omega) input).records =
      (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) (by omega) input).records ++
        [originalSourceCurrentRecord (rate := rate)
          rewards C_star C_h q t s hs control0 i z] := by
    dsimp only [ReferenceActiveHorizonMeasurability.runOfInput]
    rw [ReferenceActivePhysicalHorizon.run_successor_step]
    have hentry : (⟨s + (t.val - s), by omega, by omega⟩ :
        ReferenceActivePhysicalHorizon.CalendarEntry p s) = ⟨t.val, hs, t.isLt⟩ :=
      Subtype.ext (Nat.add_sub_of_le hs)
    rw [hentry]
    rfl
  apply List.mem_of_mem_take (i := t.val - s + 1)
  rw [← hsucc, happend]
  exact List.mem_append_right _ List.mem_cons_self

private theorem current_awaited_local_fields
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : (originalSourceCurrentRecord (rate := rate)
      rewards C_star C_h q t s hs control0 i z).output.coordinator.up = some d)
    (beta : ℕ) (message : OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta))
    (hawaited : awaited_up_source_trace rewards C_star C_h q t s hs control0 i z beta message) :
    CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta)
        (some (ActiveFollowerArmChoice.offeredUpWord rate.eta message)) = some message ∧
      CoordinatorCollectionLedger.acceptUpCheck d.input.ledger i message = true ∧
      i ∈ d.input.ledger.pending ∧ message.val.sigma = d.input.ledger.sigma ∧
      0 < message.val.sigma ∧
      message ≠ CoordinatorUpReception.placeholderUpRecord p rate.eta := by
  let current := originalSourceCurrentRecord (rate := rate)
    rewards C_star C_h q t s hs control0 i z
  obtain ⟨hrows, hselected, htime, _⟩ := originalSourceCurrentInput_original_fields
    rewards C_star C_h q t s hs control0 i z
  have htime' : current.input.time = t := htime
  have hchannel : ReferenceSelectedAffinePairLaw.selectedChannel p
      (current.input.row.2 current.input.time).1 = some (1, i) := by
    change ReferenceSelectedAffinePairLaw.selectedChannel p
      ((current.input.rows current.input.selected).2 current.input.time).1 = some (1, i)
    rw [show current.input.rows = z.1.1.2 from hrows,
      show current.input.selected = q from hselected, htime']
    exact (ReferenceSelectedAffinePairLaw.selector_eq_iff p q t (1, i) z.1).mp z.2.1 |>.2
  obtain ⟨_, other, hother, _, _, _, haccept⟩ := hawaited.2.2 current
    (current_record_mem rewards C_star C_h q t s hs control0 i z)
    (by rw [htime']; exact hawaited.2.1) (by rw [htime']) hchannel
  have heq : other = d := Option.some.inj (hother.symm.trans hd)
  subst other
  obtain ⟨_, _, hcheck, hinput, _⟩ :=
    ReferenceGeneratedUpBatchCalendar.record_up_executed_fields current d hd
  have hcheck' : CoordinatorUpReception.receptionInputCheck d.input = true := by
    rw [hinput]
    exact hcheck
  have hpositive := ((CoordinatorUpReception.receptionInputCheck_eq_true_iff d.input).mp hcheck').2.1
  have hlocal : i ∈ d.input.ledger.pending ∧ message.val.sigma = d.input.ledger.sigma := by
    have hchecks : d.input.ledger.cutoff ≤ d.input.ledger.cursor ∧
        (i ∈ d.input.ledger.pending ∧ message.val.sigma = d.input.ledger.sigma) := by
      simpa only [CoordinatorCollectionLedger.acceptUpCheck, Bool.and_eq_true,
        decide_eq_true_eq] using haccept
    exact hchecks.2
  refine ⟨?_, haccept, hlocal.1, hlocal.2, by omega, ?_⟩
  · change OrdinaryMessageCodec.parseUp (CoordinatorCollectionLedger.codecParams p rate.eta)
      (some ((OrdinaryMessageCodec.wordEquivFlat
        (CoordinatorCollectionLedger.codecParams p rate.eta)).symm
          ((OrdinaryMessageCodec.wordEquivFlat (CoordinatorCollectionLedger.codecParams p rate.eta))
            (OrdinaryMessageCodec.encodeUp (CoordinatorCollectionLedger.codecParams p rate.eta)
              message)))) = some message
    rw [Equiv.symm_apply_apply]
    exact OrdinaryMessageCodec.parseUp_encode _ message
  · intro heq
    have hzero : message.val.sigma = 0 := by
      rw [heq]
      rfl
    omega

/-- Inclusion of the explicitly awaited actual-source ambiguity branch.
The interval may start on either side of the batch birth, provided every
retained equation lies in it. Mixed older equations are never discarded.
The two distinct solutions are an explicit event input, not inferred from
`raw = none`. Awaitedness itself is not produced for arbitrary replies. -/
theorem awaited_up_ambiguous_source_coverage
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : (originalSourceCurrentRecord (rate := rate)
      rewards C_star C_h q t s hs control0 i z).output.coordinator.up = some d)
    (hi : d.input.selectedFollower = i)
    (hp : ReferenceActiveAffinePositiveTest.upPositive
      (originalSourceCurrentRecord (rate := rate)
        rewards C_star C_h q t s hs control0 i z).input = true)
    (hQ : (((originalSourceCurrentRecord (rate := rate)
      rewards C_star C_h q t s hs control0 i z).input.state.upDecoderBank i).pending).length + 1 =
        AffineBatchDecoder.quota p)
    (hawaited : ∃ (message : OrdinaryMessageCodec.UpRecord
        (CoordinatorCollectionLedger.codecParams p rate.eta)) (beta : ℕ),
      awaited_up_source_trace rewards C_star C_h q t s hs control0 i z beta message ∧
      ∀ entry ∈ ((originalSourceCurrentRecord (rate := rate)
          rewards C_star C_h q t s hs control0 i z).input.state.upDecoderBank i).pending ++
        [AffineBatchDecoder.entry p
          (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time],
        beta ≤ entry.time.val)
    (hamb : ∃ v₁ v₂ : AffineChannelLaw.Word (AffineBatchDecoder.width p), v₁ ≠ v₂ ∧
      AffineBatchDecoder.satisfies
        ((((originalSourceCurrentRecord (rate := rate)
            rewards C_star C_h q t s hs control0 i z).input.state.upDecoderBank i).pending ++
          [AffineBatchDecoder.entry p
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]).map
              AffineBatchDecoder.Entry.sample) v₁ ∧
      AffineBatchDecoder.satisfies
        ((((originalSourceCurrentRecord (rate := rate)
            rewards C_star C_h q t s hs control0 i z).input.state.upDecoderBank i).pending ++
          [AffineBatchDecoder.entry p
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]).map
              AffineBatchDecoder.Entry.sample) v₂) :
    let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
    let full := ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input
    let current := originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z
    let bank := current.input.state.upDecoderBank i
    let batch := bank.pending ++ [AffineBatchDecoder.entry p
      (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]
    ∃ alpha, s ≤ alpha ∧ alpha ≤ t.val ∧
      upBatchBirth i s alpha input.val.1
        (full.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) ∧
      let kept := (originalSourceTests (rate := rate)
        rewards C_star C_h q t s hs control0 alpha i z).take (AffineBatchDecoder.quota p)
      kept.length = AffineBatchDecoder.quota p ∧
      kept.Pairwise (fun a b => a.time < b.time) ∧
      kept.map (fun test => (test.time, test.sample)) =
        batch.map (fun entry => (entry.time.val, entry.sample)) ∧
      d.decoderAfter.pending = [] ∧ d.decoderAfter.completed = bank.completed ++ [batch] ∧
      ∃ (message : OrdinaryMessageCodec.UpRecord
          (CoordinatorCollectionLedger.codecParams p rate.eta)) (beta : ℕ),
        awaited_up_source_trace rewards C_star C_h q t s hs control0 i z beta message ∧
        (∀ entry ∈ batch, beta ≤ entry.time.val) ∧
        CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta)
          (some (ActiveFollowerArmChoice.offeredUpWord rate.eta message)) = some message ∧
        CoordinatorCollectionLedger.acceptUpCheck d.input.ledger i message = true ∧
        i ∈ d.input.ledger.pending ∧ message.val.sigma = d.input.ledger.sigma ∧
        0 < message.val.sigma ∧
        message ≠ CoordinatorUpReception.placeholderUpRecord p rate.eta ∧
        (∀ test ∈ kept, test.sent = some (ActiveFollowerArmChoice.offeredUpWord rate.eta message)) ∧
        AffineBatchDecoder.satisfies (batch.map AffineBatchDecoder.Entry.sample)
          (ActiveFollowerArmChoice.offeredUpWord rate.eta message) ∧
        d.raw = none ∧
        (∀ v : AffineChannelLaw.Word (AffineBatchDecoder.width p),
          AffineBatchDecoder.satisfies (batch.map AffineBatchDecoder.Entry.sample) v →
          v ≠ ActiveFollowerArmChoice.offeredUpWord rate.eta message →
          z.1 ∈ upSourceSurvivalEvent (rate := rate)
            rewards C_star C_h q control0 alpha v i (AffineBatchDecoder.quota p)) ∧
        ∃ v : AffineChannelLaw.Word (AffineBatchDecoder.width p),
          AffineBatchDecoder.satisfies (batch.map AffineBatchDecoder.Entry.sample) v ∧
          v ≠ ActiveFollowerArmChoice.offeredUpWord rate.eta message ∧
          z.1 ∈ upSourceSurvivalEvent (rate := rate)
            rewards C_star C_h q control0 alpha v i (AffineBatchDecoder.quota p) := by
  dsimp only
  let current := originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z
  let batch := (current.input.state.upDecoderBank i).pending ++ [AffineBatchDecoder.entry p
    (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]
  obtain ⟨alpha, ha, hat, hbirth, hlength, horder, hcoordinates, hrecords,
      hpending, hcompleted, hraw, hcandidates⟩ :=
    actual_completed_up_candidates rewards C_star C_h q t s hs control0 i z d hd hi hp hQ
  let kept := (originalSourceTests (rate := rate)
    rewards C_star C_h q t s hs control0 alpha i z).take (AffineBatchDecoder.quota p)
  obtain ⟨message, beta, htrace, hbeta⟩ := hawaited
  let word := ActiveFollowerArmChoice.offeredUpWord rate.eta message
  have htests : ∀ test ∈ kept,
      test.sent = some word ∧ AffineChannelLaw.affineHash test.sample word = 1 := by
    intro test htest
    obtain ⟨record, hrecord, hproject, htime, hsample, hsent, hpositive, hchannel, hupper⟩ :=
      hrecords test htest
    have hmem : (test.time, test.sample) ∈
        batch.map (fun entry => (entry.time.val, entry.sample)) := by
      rw [← hcoordinates]
      exact List.mem_map.mpr ⟨test, htest, rfl⟩
    obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmem
    have htimeEntry : entry.time.val = test.time := congrArg Prod.fst heq
    have hstart : beta ≤ record.input.time.val := by
      rw [← htime, ← htimeEntry]
      exact hbeta entry hentry
    have hsend := (htrace.2.2 record hrecord hstart hupper hchannel).1
    have hhash := ReferenceUpPhysicalHashRule.upPositive_hash_one record.input word hsend hpositive
    obtain ⟨diagnostic, hdiagnostic, _, _, _⟩ :=
      ReferenceGeneratedUpResetPrefixBridge.evidenceUpTest_sender_fields i record test hproject
    obtain ⟨_, _, _, _, _, _, hselected, _⟩ :=
      ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields record diagnostic hdiagnostic
    have hi' : diagnostic.input.selectedFollower = i := by
      rw [hdiagnostic] at hproject
      by_contra hn
      simp only [upTestOfDiagnostic, hn, false_and, ↓reduceIte, reduceCtorEq] at hproject
    have hsender : ReferenceActivePhysicalStep.upSenderIndex record.input = i :=
      hselected.symm.trans hi'
    rw [hsender] at hhash
    exact ⟨hsent.trans hsend, by rw [hsample]; exact hhash⟩
  have hword : AffineBatchDecoder.satisfies (batch.map AffineBatchDecoder.Entry.sample) word := by
    apply (AffineBatchDecoder.satisfies_iff_hashes _ word).mpr
    intro sample hsample
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hsample
    have hmem : (entry.time.val, entry.sample) ∈
        kept.map (fun test => (test.time, test.sample)) := by
      rw [hcoordinates]
      exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
    obtain ⟨test, htest, heq⟩ := List.mem_map.mp hmem
    have hsample : test.sample = entry.sample := congrArg Prod.snd heq
    rw [← hsample]
    exact (htests test htest).2
  have hnone : d.raw = none := by
    rw [hraw]
    apply (AffineBatchDecoder.solve_eq_none_iff_empty_or_ambiguous _).mpr
    right
    obtain ⟨v₁, v₂, hne, h₁, h₂⟩ := hamb
    exact ⟨v₁, v₂, h₁, h₂, hne⟩
  have hother : ∀ v : AffineChannelLaw.Word (AffineBatchDecoder.width p),
      AffineBatchDecoder.satisfies (batch.map AffineBatchDecoder.Entry.sample) v →
      v ≠ word → z.1 ∈ upSourceSurvivalEvent (rate := rate)
        rewards C_star C_h q control0 alpha v i (AffineBatchDecoder.quota p) := by
    intro v hv hne
    apply (hcandidates v hv).mpr
    intro test htest heq
    apply hne
    exact Option.some.inj (heq.symm.trans (htests test htest).1)
  have hexists : ∃ v : AffineChannelLaw.Word (AffineBatchDecoder.width p),
      AffineBatchDecoder.satisfies (batch.map AffineBatchDecoder.Entry.sample) v ∧ v ≠ word ∧
      z.1 ∈ upSourceSurvivalEvent (rate := rate)
        rewards C_star C_h q control0 alpha v i (AffineBatchDecoder.quota p) := by
    obtain ⟨v₁, v₂, hne, h₁, h₂⟩ := hamb
    by_cases heq : v₁ = word
    · have hne' : v₂ ≠ word := fun h => hne (heq.trans h.symm)
      exact ⟨v₂, h₂, hne', hother v₂ h₂ hne'⟩
    · exact ⟨v₁, h₁, heq, hother v₁ h₁ heq⟩
  obtain ⟨hparse, haccept, hpendingLocal, hsigma, hpositiveSigma, hplaceholder⟩ :=
    current_awaited_local_fields rewards C_star C_h q t s hs control0 i z d hd beta message htrace
  exact ⟨alpha, ha, hat, hbirth, hlength, horder, hcoordinates, hpending, hcompleted,
    message, beta, htrace, hbeta, hparse, haccept, hpendingLocal, hsigma, hpositiveSigma,
    hplaceholder, fun test htest => (htests test htest).1, hword, hnone, hother, hexists⟩

end Bandits.Support.ReferenceGeneratedUpAwaitedBatchCoverage

end
