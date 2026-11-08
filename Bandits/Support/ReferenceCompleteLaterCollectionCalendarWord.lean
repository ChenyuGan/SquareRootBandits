/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteLaterCollectionCalendarReadout

import Mathlib.Tactic

/-!
# Literal word on an actual later-LIVE collection segment

Sources: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-174`.

This module is the source-operation component for the collection segment
reached from an actual later `.live` prefix. Its readout and physical queue
claims remain conditional on that actual branch and its strict later-start
invariant. It does not assemble the larger successor prefix or close a regret
claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceCollectionSegmentExtraction

namespace Bandits.Support.ReferenceCompleteLaterCollectionCalendarWord

variable {p : ConstructorDimensions.Parameters}

private theorem complete_suffix_member_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).input.time.val =
        ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + k.val := by
  exact ReferenceLaterCollectionArrivalReadout.sourceIndexedReadout_time
    rate rewards C_star C_h source k

/-- Enumerate one actual readout at each finite physical slot. The supplied
existence proof is used by `Option.get`; a missing cell is never converted to
a default value. -/
def readoutWord
    {α β : Type*} (readout : α → Option β) (records : List α)
    (hslots : ∀ i : Fin records.length, ∃ c, readout records[i.val] = some c) :
    List β :=
  List.ofFn fun i : Fin records.length =>
    (readout records[i.val]).get (by
      rcases hslots i with ⟨c, hc⟩
      rw [hc]
      rfl)

theorem readoutWord_get
    {α β : Type*} (readout : α → Option β) (records : List α)
    (hslots : ∀ i : Fin records.length, ∃ c, readout records[i.val] = some c)
    (i : Fin records.length) :
    readout records[i.val] = some ((readoutWord readout records hslots)[i.val]'(by
      simp [readoutWord])) := by
  rcases hslots i with ⟨c, hc⟩
  have hget : (readout records[i.val]).get (by rw [hc]; rfl) = c := by simp [hc]
  simpa [readoutWord, hget] using hc

theorem readoutWord_length
    {α β : Type*} (readout : α → Option β) (records : List α)
    (hslots : ∀ i : Fin records.length, ∃ c, readout records[i.val] = some c) :
    (readoutWord readout records hslots).length = records.length := by
  simp [readoutWord]

/-- The option readouts and the constructed word have the same literal map,
including every coordinate and with no `filterMap` loss. -/
theorem readoutWord_map_some
    {α β : Type*} (readout : α → Option β) (records : List α)
    (hslots : ∀ i : Fin records.length, ∃ c, readout records[i.val] = some c) :
    records.map readout = (readoutWord readout records hslots).map some := by
  rw [← List.ofFn_getElem_eq_map records readout, readoutWord, List.map_ofFn]
  congr 1
  funext i
  rcases hslots i with ⟨c, hc⟩
  simp [hc]

/-- Any equally long list whose coordinates realize the same `SOME` values is
the constructed word. This is the uniqueness of actual optional readouts, not
a choice of values for absent cells. -/
theorem readoutWord_unique
    {α β : Type*} (readout : α → Option β) (records : List α)
    (hslots : ∀ i : Fin records.length, ∃ c, readout records[i.val] = some c)
    (word : List β) (hlen : word.length = records.length)
    (hword : ∀ i : Fin records.length,
      readout records[i.val] = some (word[i.val]'(by omega))) :
    word = readoutWord readout records hslots := by
  apply List.ext_getElem
  · calc
      word.length = records.length := hlen
      _ = (readoutWord readout records hslots).length :=
        (readoutWord_length readout records hslots).symm
  · intro n hwordIndex hreadoutIndex
    let i : Fin records.length := ⟨n, by omega⟩
    have hgiven := hword i
    have hmade := readoutWord_get readout records hslots i
    have hvalue := Option.some.inj (hgiven.symm.trans hmade)
    simpa [i] using hvalue

private theorem continuing_preparation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hcontinue : ReferenceCollectionSegmentExtraction.continuing record = true) :
    ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
      (ledger : ReferenceActivePhysicalStep.Ledger rate)
      (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
      (core : CoordinatorRoundDispatch.CollectionCoreValid
        (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff))
      (snapshot : CoordinatorCollectionInteractive.PreparedSnapshot
        (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff))
      (boundary : snapshot.clockStarted.clock.g ≤ p.T + 1)
      (scores : CoordinatorRoundDispatch.collectionCurrentScoresCheck
        (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff) = true),
      record.output.preparation.coordinator =
        .collection payload ledger clock cutoff (.continuing core snapshot boundary scores) := by
  have hprepare : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  unfold ReferenceCollectionSegmentExtraction.continuing at hcontinue
  cases hextract : ReferenceCollectionSegmentExtraction.extractRound record with
  | none => simp [hextract] at hcontinue
  | some completed =>
      have hinitializer : completed.context.initializer = none := by
        simpa [hextract] using hcontinue
      have hchoice := (ReferenceCollectionSegmentExtraction.actual_collection_round_checked
        record completed hextract).1
      unfold ReferenceCollectionSegmentExtraction.choice at hchoice
      by_cases hselection : (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = none
      · simp [hselection] at hchoice
      · simp only [ite_eq_right hselection] at hchoice
        cases hcoord : (ReferenceActivePhysicalStep.prepare record.input).coordinator with
        | first outcome =>
            simp only [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hchoice
            cases hchoice
        | live registers owned base outcome =>
            cases outcome with
            | cutoffChosen dispatched _ newLedger _ _ _ _ _ _ =>
                have hchoice' :
                    some (⟨registers.payload,
                      ReferenceActivePhysicalStep.sharedLedger newLedger,
                      dispatched.startResult,
                      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights,
                      some (ReferenceCollectionSegmentExtraction.cutoffInitializer
                        (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time)
                        (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time)
                        base record.input.time)⟩ : ReferenceCollectionSegmentExtraction.Choice rate) =
                      some completed.context := by
                  simpa only [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] using hchoice
                have hctx := Option.some.inj hchoice'
                have hinitEq := congrArg ReferenceCollectionSegmentExtraction.Choice.initializer hctx
                rw [hinitializer] at hinitEq
                simp at hinitEq
            | _ =>
                simp only [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hchoice
                cases hchoice
        | collection payload ledger clock cutoff outcome =>
            cases outcome with
            | continuing core snapshot boundary scores =>
                have hcoord' : record.output.preparation.coordinator =
                    .collection payload ledger clock cutoff (.continuing core snapshot boundary scores) := by
                  rw [hprepare]
                  exact hcoord
                exact ⟨payload, ledger, clock, cutoff, core, snapshot, boundary, scores, hcoord'⟩
            | _ =>
                simp only [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hchoice
                cases hchoice
        | invalidCollectionCutoff =>
            simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hchoice
        | dagger =>
            simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hchoice

private theorem segment_slot_record
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (offset : ℕ) (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hpartition : seg.records ++ seg.remaining = records.drop offset)
    (j : Fin seg.records.length) :
    records[offset + j.val]? = some seg.records[j.val] := by
  have hlength : seg.records.length + seg.remaining.length = records.length - offset := by
    have h := congrArg List.length hpartition
    simpa only [List.length_append, List.length_drop] using h
  have hdropLen : seg.records.length ≤ (records.drop offset).length := by
    simpa only [List.length_drop] using (Nat.le_of_lt_succ (by omega : seg.records.length < records.length - offset + 1))
  have hdropIndex : j.val < (records.drop offset).length := Nat.lt_of_lt_of_le j.isLt hdropLen
  have hindex : offset + j.val < records.length := by omega
  have htake : (records.drop offset).take seg.records.length = seg.records := by
    rw [← hpartition]
    simp
  have htakeIndex : j.val < ((records.drop offset).take seg.records.length).length := by
    simp only [List.length_take]
    omega
  have hrecordTake : seg.records[j.val] =
      ((records.drop offset).take seg.records.length)[j.val]'htakeIndex := by
    have hopt := congrArg (fun xs : List (ReferenceActivePhysicalHorizon.RoundRecord
        (p := p) (rate := rate)) => xs[j.val]?) htake.symm
    have hopt' : some seg.records[j.val] =
        some ((records.drop offset).take seg.records.length)[j.val] := by
      simpa only [List.getElem?_eq_getElem j.isLt,
        List.getElem?_eq_getElem htakeIndex] using hopt
    exact Option.some.inj hopt'
  have hrecordDrop :
      ((records.drop offset).take seg.records.length)[j.val]'htakeIndex =
        (records.drop offset)[j.val]'hdropIndex := by
    simp [List.getElem_take]
  have hrecord : seg.records[j.val] = records[offset + j.val] := by
    calc
      seg.records[j.val] =
          ((records.drop offset).take seg.records.length)[j.val]'htakeIndex := hrecordTake
      _ = (records.drop offset)[j.val]'hdropIndex := hrecordDrop
      _ = records[offset + j.val]'hindex := by simp [List.getElem_drop]
  rw [List.getElem?_eq_getElem hindex, hrecord]

/-- The actual source calendar turns the boundary's first-cutoff equation into
the true-date guard at every retained slot. The eventual caller obtains
`hfirst` from the same boundary witness returned by the live cutoff producer;
this helper does not assume a readout, extraction success, or a new segment. -/
private theorem segment_slot_cutoff_date
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (offset : ℕ)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hpartition : seg.records ++ seg.remaining =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).drop offset)
    (firstCutoff : ℕ)
    (hfirst : firstCutoff =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + offset + 1)
    (j : Fin seg.records.length) :
    firstCutoff ≤
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[offset + j.val]'(by
          have hlen := congrArg List.length hpartition
          simp only [List.length_append, List.length_drop] at hlen
          omega)).input.time.val + 1 := by
  let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  have hlen := congrArg List.length hpartition
  simp only [List.length_append, List.length_drop] at hlen
  have hindex' : offset + j.val <
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length := by omega
  have hindex : offset + j.val < records.length := by
    simpa only [records] using hindex'
  have hslot := segment_slot_record rate records offset seg hpartition j
  have hrecord : records[offset + j.val]'hindex = seg.records[j.val] := by
    apply Option.some.inj
    simpa only [List.getElem?_eq_getElem hindex] using hslot
  have htime := complete_suffix_member_time rate rewards C_star C_h source
    ⟨offset + j.val, hindex⟩
  have htimeR : (records[offset + j.val]'hindex).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h +
        (offset + j.val) := by
    simpa only [records, Fin.val_mk] using htime
  change firstCutoff ≤ (records[offset + j.val]'hindex).input.time.val + 1
  rw [htimeR, hfirst]
  omega

/-- The finite coordinate of an actual `segmentAt` result is the same physical
record at the corresponding source-calendar index. -/
theorem actual_later_segment_slot_record
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (offset : ℕ)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h) offset = some seg)
    (j : Fin seg.records.length) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[offset + j.val]? = some seg.records[j.val] := by
  exact segment_slot_record rate _ offset seg
    (ReferenceCollectionSegmentExtraction.segmentAt_partition _ offset seg hsegment) j

/-- Every physical coordinate retained by an actual segment has its own
successful checked extraction. The excluded suffix is not inspected. -/
theorem actual_later_segment_slot_extracts
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (offset : ℕ)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h) offset = some seg)
    (j : Fin seg.records.length) :
    ∃ completed, ReferenceCollectionSegmentExtraction.extractRound seg.records[j.val] =
      some completed := by
  have hbranch := ReferenceCollectionSegmentExtraction.segmentAt_branch _ offset seg hsegment
  have hexists := ReferenceCollectionSegmentExtraction.segment_all_completed _ seg hbranch.1
    seg.records[j.val] (List.getElem_mem j.isLt)
  cases h : ReferenceCollectionSegmentExtraction.extractRound seg.records[j.val] with
  | none => simp [h] at hexists
  | some completed => exact ⟨completed, rfl⟩

/-- The slot keeps the complete original source row family, selected row (and
its original `J` index), and whole reward table carried by the physical run. -/
theorem actual_later_segment_slot_source_inputs
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (offset : ℕ)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h) offset = some seg)
    (j : Fin seg.records.length) :
    seg.records[j.val].input.rows = source.1.2 ∧
      seg.records[j.val].input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      seg.records[j.val].input.rewards = rewards := by
  let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  have hpart := ReferenceCollectionSegmentExtraction.segmentAt_partition records offset seg hsegment
  have hlen := congrArg List.length hpart
  simp only [List.length_append, List.length_drop] at hlen
  have hlen' : seg.records.length + seg.remaining.length =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length - offset := by
    simpa only [records] using hlen
  have hindex : offset + j.val < records.length := by
    have hindex' : offset + j.val <
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).length := by omega
    simpa only [records] using hindex'
  have hslot := actual_later_segment_slot_record rate rewards C_star C_h source
    offset seg hsegment j
  have hrecord : records[offset + j.val]'hindex = seg.records[j.val] := by
    apply Option.some.inj
    simpa only [List.getElem?_eq_getElem hindex, records] using hslot
  have hsource := ReferenceLaterCollectionArrivalReadout.sourceIndexedReadout_inputs
    rate rewards C_star C_h source ⟨offset + j.val, hindex⟩
  constructor
  · rw [← hrecord]
    exact hsource.1
  · constructor
    · rw [← hrecord]
      exact hsource.2.1
    · rw [← hrecord]
      exact hsource.2.2

/-- The complete physical calendar gives the exact time of each retained
segment slot, including the original offset and within-segment coordinate. -/
theorem actual_later_segment_slot_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (offset : ℕ)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h) offset = some seg)
    (j : Fin seg.records.length) :
    seg.records[j.val].input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h +
        (offset + j.val) := by
  let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  have hpart := ReferenceCollectionSegmentExtraction.segmentAt_partition records offset seg hsegment
  have hlen := congrArg List.length hpart
  simp only [List.length_append, List.length_drop] at hlen
  have hlen' : seg.records.length + seg.remaining.length =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length - offset := by
    simpa only [records] using hlen
  have hindex' : offset + j.val <
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length := by omega
  have hindex : offset + j.val < records.length := by
    simpa only [records] using hindex'
  have hslot := actual_later_segment_slot_record rate rewards C_star C_h source
    offset seg hsegment j
  have hrecord : records[offset + j.val]'hindex = seg.records[j.val] := by
    apply Option.some.inj
    simpa only [List.getElem?_eq_getElem hindex, records] using hslot
  have htime := complete_suffix_member_time rate rewards C_star C_h source
    ⟨offset + j.val, hindex⟩
  have htimeR : (records[offset + j.val]'hindex).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h +
        (offset + j.val) := by
    simpa only [records, Fin.val_mk] using htime
  rw [← hrecord]
  exact htimeR

/-- Internal date discharge for a retained coordinate of an actual segment.
The caller supplies the first-cutoff equation carried by the same live
boundary witness; this lemma derives the cell's own true-date inequality from
the complete source calendar and `segmentAt` partition. It gives no readout or
extraction premise and does not select a separate segment. -/
theorem actual_later_segment_slot_cutoff_date
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (offset : ℕ)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h) offset = some seg)
    (firstCutoff : ℕ)
    (hfirst : firstCutoff =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + offset + 1)
    (j : Fin seg.records.length) :
    firstCutoff ≤
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[offset + j.val]'(by
          have hpart := ReferenceCollectionSegmentExtraction.segmentAt_partition
            _ offset seg hsegment
          have hlen := congrArg List.length hpart
          simp only [List.length_append, List.length_drop] at hlen
          omega)).input.time.val + 1 := by
  exact segment_slot_cutoff_date rate rewards C_star C_h source offset seg
    (ReferenceCollectionSegmentExtraction.segmentAt_partition _ offset seg hsegment)
    firstCutoff hfirst j

private theorem segment_nonhead_continues
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (offset : ℕ) (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt records offset = some seg)
    (hoffset : offset < records.length)
    (hentry : seg.entry = records[offset])
    (hhead : (ReferenceCollectionSegmentExtraction.extractRound seg.entry).isSome = true)
    (j : Fin seg.records.length) (hj : 0 < j.val) :
    ReferenceCollectionSegmentExtraction.continuing seg.records[j.val] = true := by
  have hbranch := (ReferenceCollectionSegmentExtraction.segmentAt_branch
    records offset seg hsegment).1
  rw [List.drop_eq_getElem_cons hoffset] at hbranch
  have hhead' : (ReferenceCollectionSegmentExtraction.extractRound records[offset]).isSome = true := by
    simpa only [hentry] using hhead
  cases hchoice : ReferenceCollectionSegmentExtraction.choice records[offset].input with
  | none =>
      simp [ReferenceCollectionSegmentExtraction.segment, hchoice] at hbranch
  | some context =>
      simp only [ReferenceCollectionSegmentExtraction.segment, hchoice, Option.map_some,
        hhead', ite_true] at hbranch
      have heq := Option.some.inj hbranch
      have hrecords := congrArg ReferenceCollectionSegmentExtraction.Segment.records heq
      let tail := List.drop (offset + 1) records |>.takeWhile
        ReferenceCollectionSegmentExtraction.continuing
      have hrecords' : records[offset] :: tail = seg.records := by
        simpa [tail] using hrecords
      have hconstructedLen : j.val < (records[offset] :: tail).length := by
        rw [hrecords']
        exact j.isLt
      have hlenrecords := congrArg List.length hrecords'
      simp only [List.length_cons] at hlenrecords
      have hjbound : j.val < tail.length + 1 := by omega
      have hjtail : j.val - 1 <
          tail.length := by omega
      have hmem : tail[j.val - 1] ∈ tail := List.getElem_mem hjtail
      have hpred := List.mem_takeWhile_imp hmem
      have hjEq : j.val = j.val - 1 + 1 := by omega
      have hopt := congrArg (fun xs : List (ReferenceActivePhysicalHorizon.RoundRecord
          (p := p) (rate := rate)) => xs[j.val]?) hrecords'.symm
      have hval : seg.records[j.val] = (records[offset] :: tail)[j.val]'hconstructedLen := by
        have hopt' : some seg.records[j.val] = some (records[offset] :: tail)[j.val] := by
          simpa only [List.getElem?_eq_getElem j.isLt,
            List.getElem?_eq_getElem hconstructedLen] using hopt
        exact Option.some.inj hopt'
      have hconsOpt : (records[offset] :: tail)[j.val]? = tail[j.val - 1]? := by
        calc
          (records[offset] :: tail)[j.val]? =
              (records[offset] :: tail)[j.val - 1 + 1]? :=
            congrArg (fun n : ℕ => (records[offset] :: tail)[n]?) hjEq
          _ = tail[j.val - 1]? := by simp only [List.getElem?_cons_succ]
      have hcons : (records[offset] :: tail)[j.val]'hconstructedLen =
          tail[j.val - 1]'hjtail := by
        have hsome : some ((records[offset] :: tail)[j.val]'hconstructedLen) =
            some (tail[j.val - 1]'hjtail) := by
          simpa only [List.getElem?_eq_getElem hconstructedLen,
            List.getElem?_eq_getElem hjtail] using hconsOpt
        exact Option.some.inj hsome
      have hslot : seg.records[j.val] = tail[j.val - 1]'hjtail := by
        calc
          seg.records[j.val] = (records[offset] :: tail)[j.val]'hconstructedLen := hval
          _ = tail[j.val - 1]'hjtail := hcons
      rw [hslot]
      exact hpred

/-- Every non-entry coordinate of an actual complete-source segment is an
actual continuing collection record. Its later readout can therefore be
obtained from the continuing PREPARE constructor after the source date guard. -/
theorem actual_later_segment_nonhead_continues
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (offset : ℕ)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h) offset = some seg)
    (j : Fin seg.records.length) (hj : 0 < j.val) :
    ReferenceCollectionSegmentExtraction.continuing seg.records[j.val] = true := by
  let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  have hpart := ReferenceCollectionSegmentExtraction.segmentAt_partition records offset seg hsegment
  have hlen := congrArg List.length hpart
  simp only [List.length_append, List.length_drop] at hlen
  have hlen' : seg.records.length + seg.remaining.length =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length - offset := by
    simpa only [records] using hlen
  have hoffset : offset < records.length := by omega
  have hbranch := ReferenceCollectionSegmentExtraction.segmentAt_branch records offset seg hsegment
  have hsegbase : ReferenceCollectionSegmentExtraction.segment (records.drop offset) = some seg :=
    hbranch.1
  rw [List.drop_eq_getElem_cons hoffset] at hsegbase
  have hshape : ReferenceCollectionSegmentExtraction.segment
      (records[offset] :: records.drop (offset + 1)) = some seg := hsegbase
  unfold ReferenceCollectionSegmentExtraction.segment at hshape
  cases hchoice : ReferenceCollectionSegmentExtraction.choice records[offset].input with
  | none => simp [hchoice] at hshape
  | some context =>
      simp only [hchoice, Option.map_some] at hshape
      split at hshape
      · have heq := Option.some.inj hshape
        have hentry : seg.entry = records[offset] :=
          (congrArg ReferenceCollectionSegmentExtraction.Segment.entry heq).symm
        have hhead :
            (ReferenceCollectionSegmentExtraction.extractRound seg.entry).isSome = true := by
          simpa only [hentry] using ‹(ReferenceCollectionSegmentExtraction.extractRound
            records[offset]).isSome = true›
        exact segment_nonhead_continues rate records offset seg hsegment hoffset
          hentry hhead j hj
      · have heq := Option.some.inj hshape
        have hrecords : seg.records = [] :=
          (congrArg ReferenceCollectionSegmentExtraction.Segment.records heq).symm
        have hbad : j.val < 0 := by simpa [hrecords] using j.isLt
        omega


open ReferenceLaterCollectionArrivalReadout ReferenceCollectionRawBufferHistory

variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- A completed physical tail keeps the payload of its actual collection call. -/
private theorem completed_payload
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (done : CompletedRound rate)
    (he : extractRound r = some done) :
    ∃ saved, r.output.next.coordinator = .collection done.context.payload done.final saved := by
  obtain ⟨hc, _, _, P, saved, hn⟩ := actual_collection_round_checked r done he
  have ht : r.output.coordinator = collectionPostChoice (prepare r.input)
      done.context.payload done.context.preLedger done.context.started done.context.weights := by
    rw [r.output_eq]
    exact choice_tail r.input done.context hc
  have hf := ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
    (prepare r.input) done.context.payload done.context.preLedger
      done.context.started done.context.weights
  have hs : r.output.coordinator.configuration = .collection P done.final saved := by
    rw [r.output_eq] at hn ⊢
    exact hn
  rw [← ht, hs] at hf
  simp only [ReferenceAssignmentPayloadPersistence.storedPayload_collection,
    reduceCtorEq, false_or] at hf
  exact ⟨saved, Option.some.inj hf ▸ hn⟩

private theorem choice_collection_payload
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (c : Choice rate) (hstate : x.state.coordinator = .collection P l saved)
    (hc : choice x = some c) : c.payload = P := by
  classical
  unfold choice at hc
  split at hc
  · contradiction
  next =>
    change choiceOfCut (ReferenceActivePhysicalStep.dispatch x) = some c at hc
    simp only [ReferenceActivePhysicalStep.dispatch, hstate] at hc
    split at hc
    next hcut =>
      let u : Fin p.T := ⟨l.cutoff - 1, by omega⟩
      let clock := collectionClock P l saved u
      change choiceOfCut (.collection P l clock u
        (CoordinatorRoundDispatch.dispatchCollection (collectionInput x P l clock u))) = some c at hc
      cases ho : CoordinatorRoundDispatch.dispatchCollection (collectionInput x P l clock u) <;>
        simp only [choiceOfCut, ho] at hc
      all_goals first | contradiction | (cases Option.some.inj hc; rfl)
    · simp only [choiceOfCut, reduceCtorEq] at hc

/-- Propagate the whole payload and fixed ledger context through actual
completed continuing rounds, including both checked UP outcomes. -/
private theorem continuing_contexts
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalStep.State p rate)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hchain : Connected initial records final)
    (hcoord : initial.coordinator = .collection P l saved) :
    ∀ r ∈ records.takeWhile continuing, ∀ done : CompletedRound rate,
      extractRound r = some done →
      done.context.payload = P ∧
      CollectionBufferProvenance.collectionContext done.context.preLedger =
        CollectionBufferProvenance.collectionContext l := by
  induction records generalizing initial P l saved with
  | nil => simp only [List.takeWhile_nil, List.not_mem_nil, false_implies, implies_true]
  | cons r rest ih =>
    by_cases hc : continuing r = true
    · rw [List.takeWhile_cons, hc]
      obtain ⟨done, hext⟩ := Option.isSome_iff_exists.mp (continuing_isSome r hc)
      obtain ⟨hchoice, _, hchecked, _, _, _⟩ := actual_collection_round_checked r done hext
      have hstate : r.input.state.coordinator = .collection P l saved := hchain.1 ▸ hcoord
      have hpre := (choice_collection_pre r.input P l saved done.context hstate hchoice).1
      have hpay := choice_collection_payload r.input P l saved done.context hstate hchoice
      obtain ⟨savedNext, hnext⟩ := completed_payload r done hext
      rw [hpay] at hnext
      have hframe := CollectionBufferProvenance.checkedRounds_success_preserves_context
        done.context.preLedger done.final [done.input] [done.accepted] hchecked
      have htail := ih r.output.next P done.final savedNext hchain.2 hnext
      intro r' hr done' hext'
      rcases List.mem_cons.mp hr with hsame | hrest
      · subst r'
        have hd : done' = done := Option.some.inj (hext'.symm.trans hext)
        rw [hd, hpre]
        exact ⟨hpay, rfl⟩
      · obtain ⟨hp, hf⟩ := htail r' hrest done' hext'
        exact ⟨hp, hf.trans (by simpa only [hpre] using hframe)⟩
    · have hc' : continuing r = false := Bool.eq_false_iff.mpr hc
      simp only [List.takeWhile_cons, hc', Bool.false_eq_true, ↓reduceIte,
        List.not_mem_nil, false_implies, implies_true]

private theorem segment_contexts
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalStep.State p rate) (seg : Segment rate)
    (hchain : Connected initial records final) (hseg : segment records = some seg) :
    ∀ r ∈ seg.records, ∀ done : CompletedRound rate, extractRound r = some done →
      done.context.payload = seg.context.payload ∧
      CollectionBufferProvenance.collectionContext done.context.preLedger =
        CollectionBufferProvenance.collectionContext seg.context.preLedger := by
  cases records with
  | nil => simp only [ReferenceCollectionSegmentExtraction.segment, reduceCtorEq] at hseg
  | cons entry rest =>
    unfold ReferenceCollectionSegmentExtraction.segment at hseg
    cases hc : choice entry.input with
    | none => simp only [hc, Option.map_none, reduceCtorEq] at hseg
    | some ctx =>
      simp only [hc, Option.map_some] at hseg
      cases he : extractRound entry with
      | none =>
        simp only [he, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hseg
        cases Option.some.inj hseg
        simp only [List.not_mem_nil, false_implies, implies_true]
      | some done =>
        simp only [he, Option.isSome_some, ↓reduceIte] at hseg
        cases Option.some.inj hseg
        obtain ⟨hchoice, _, hchecked, _, _, _⟩ := actual_collection_round_checked entry done he
        have hctx : done.context = ctx := Option.some.inj (hchoice.symm.trans hc)
        have hframe := CollectionBufferProvenance.checkedRounds_success_preserves_context
          done.context.preLedger done.final [done.input] [done.accepted] hchecked
        obtain ⟨savedNext, hnext⟩ := completed_payload entry done he
        have htail := continuing_contexts rest entry.output.next final done.context.payload
          done.final savedNext hchain.2 hnext
        intro r hr done' hext
        rcases List.mem_cons.mp hr with hsame | hrest
        · subst r
          have hd : done' = done := Option.some.inj (hext.symm.trans he)
          rw [hd, hctx]
          exact ⟨rfl, rfl⟩
        · obtain ⟨hp, hf⟩ := htail r hrest done' hext
          exact ⟨hp.trans (congrArg Choice.payload hctx),
            hf.trans (by simpa only [hctx] using hframe)⟩

/-- Constructor uniqueness aligns the guarded diagnostic with the actual
checked call, including its clock, rather than only its enabled bit. -/
private theorem readout_call_context (s : ℕ) (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : RecordedQueueRun.RoundInput p.K) (done : CompletedRound rate)
    (hread : laterCollectionReadout s r = some c)
    (hextract : extractRound r = some done) :
    laterCollectionCall s r = some ⟨done.context.payload, done.context.preLedger,
      done.context.started, done.context.weights⟩ := by
  classical
  have hchoice := (actual_collection_round_checked r done hextract).1
  have hdomain := (laterCollectionReadout_domain s r).mp (by rw [hread]; rfl)
  unfold choice at hchoice
  split at hchoice
  next => contradiction
  next =>
    have hprep : (prepare r.input).coordinator = r.output.preparation.coordinator := by
      rw [r.output_eq]; rfl
    rw [hprep] at hchoice
    unfold laterCollectionCall
    rw [ite_eq_left hdomain.1]
    cases hc : r.output.preparation.coordinator with
    | first outcome => cases outcome <;> simp [hc, choiceOfCut] at hchoice
    | invalidCollectionCutoff => simp [hc, choiceOfCut] at hchoice
    | dagger => simp [hc, choiceOfCut] at hchoice
    | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simp only [hc, choiceOfCut] at hchoice
      all_goals first | contradiction | (rw [← Option.some.inj hchoice])
    | live registers owned base outcome =>
      cases outcome <;> simp only [hc, choiceOfCut] at hchoice
      all_goals try contradiction
      next dispatched hs ledger hi he hd hclock hp hn selected =>
        rw [← Option.some.inj hchoice]
        have hlater : s < registers.payload.sigma.val := by simpa only [hc] using hdomain.2
        simp only [ite_eq_left hlater]

/-- Apply the accepted per-operation producer at an actual extracted call.
Its date guard is supplied by the segment proof below, not by the public root. -/
private theorem completed_calendar_readout
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (done : CompletedRound rate)
    (hext : extractRound (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val] = some done)
    (hlater : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h <
      done.context.payload.sigma.val)
    (hcut : FollowerCutoffScan.firstCutoff p rate.eta.val done.context.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val].input.row) ≤
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val].input.time.val + 1) :
    ∃ c, laterCollectionReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] = some c ∧
      (c.enabled = false → c.recordedArm = none ∧ ∀ a,
        RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) := by
  classical
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
  have hc := (actual_collection_round_checked r done hext).1
  unfold choice at hc
  split at hc
  · contradiction
  next =>
    have hprep : (prepare r.input).coordinator = r.output.preparation.coordinator := by
      rw [r.output_eq]; rfl
    rw [hprep] at hc
    cases hb : r.output.preparation.coordinator with
    | first outcome => cases outcome <;> simp [hb, choiceOfCut] at hc
    | invalidCollectionCutoff => simp [hb, choiceOfCut] at hc
    | dagger => simp [hb, choiceOfCut] at hc
    | collection P l clock cutoff outcome =>
      cases outcome <;> simp only [hb, choiceOfCut] at hc
      all_goals try contradiction
      next core snapshot boundary scores =>
        have hctx := Option.some.inj hc
        rw [← hctx] at hlater hcut
        obtain ⟨c, hr, _, _, _, _, _, _, _, _, _, _, _, _, hz⟩ :=
          ReferenceCompleteLaterCollectionCalendarReadout.complete_continuing_collection_calendar_readout
            rate rewards C_star C_h z k P l clock cutoff core snapshot boundary scores hb hlater hcut
        exact ⟨c, hr, hz.2⟩
    | live registers owned base outcome =>
      cases outcome <;> simp only [hb, choiceOfCut] at hc
      all_goals try contradiction
      next dispatched hs ledger hi he hd hclock hp hn selected =>
        have hctx := Option.some.inj hc
        rw [← hctx] at hlater hcut
        obtain ⟨c, hr, _, _, _, _, _, _, _, _, _, _, _, _, hz⟩ :=
          ReferenceCompleteLaterCollectionCalendarReadout.complete_later_live_cutoff_collection_calendar_readout
            rate rewards C_star C_h z k registers owned base dispatched hs ledger hi he hd hclock hp hn
              selected hb hlater hcut
        exact ⟨c, hr, hz.2⟩


private theorem collection_readout_zero (s : ℕ)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : RecordedQueueRun.RoundInput p.K) (hr : laterCollectionReadout s r = some c) :
    laterCollectionReadout 0 r = some c ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
  classical
  obtain ⟨hf, hb⟩ := (laterCollectionReadout_domain s r).mp (by rw [hr]; rfl)
  have hz : laterCollectionReadout 0 r = some c := by
    cases hc : r.output.preparation.coordinator with
    | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
        simpa only [laterCollectionReadout, dite_eq_left hf, hc] using hr
      | _ => simp only [hc] at hb
    | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen dispatched hs ledger hi he hd hclock hp hn selected =>
        have hg : s < registers.payload.sigma.val := by simpa only [hc] using hb
        have hg0 : 0 < registers.payload.sigma.val := by omega
        simpa only [laterCollectionReadout, dite_eq_left hf, hc, hg, hg0, ite_true] using hr
      | _ => simp only [hc] at hb
    | first outcome => cases outcome <;> simp only [hc] at hb
    | invalidCollectionCutoff => simp only [hc] at hb
    | dagger => simp only [hc] at hb
  refine ⟨hz, ?_⟩
  have hnone : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = none := by
    cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r with
    | none => rfl
    | some d =>
      exact False.elim (ReferenceCompleteNumericalBranchObservation.readouts_disjoint rate 0 r
        ⟨by rw [hl]; rfl, by rw [hz]; rfl⟩)
  simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hnone, Option.none_or, hz]


/-- The actual clock boundary is identified by its constructor equations.
This equality does not follow merely from equality of enabled bits. -/
private theorem choice_started_freeze
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (ctx : Choice rate)
    (hc : choice x = some ctx) : ctx.started.clock.g = ctx.preLedger.freezeAt := by
  classical
  unfold choice at hc
  split at hc
  · contradiction
  next =>
    cases hb : (prepare x).coordinator with
    | first outcome => cases outcome <;> simp [hb, choiceOfCut] at hc
    | invalidCollectionCutoff => simp [hb, choiceOfCut] at hc
    | dagger => simp [hb, choiceOfCut] at hc
    | collection P l clock cutoff outcome =>
      cases outcome <;> simp only [hb, choiceOfCut] at hc
      all_goals try contradiction
      next core snapshot boundary scores =>
        cases Option.some.inj hc
        change snapshot.clockStarted.clock.g = l.freezeAt
        calc
          snapshot.clockStarted.clock.g = clock.g :=
            congrArg CoordinatorPhaseClock.ClockRegisters.g snapshot.clockStarted_frame.1
          _ = l.freezeAt := core.ledger_freeze_eq.symm
    | live registers owned base outcome =>
      cases outcome <;> simp only [hb, choiceOfCut] at hc
      all_goals try contradiction
      next dispatched hs ledger hi he hd hclock hp hn selected =>
        cases Option.some.inj hc
        change dispatched.startResult.clock.g = (sharedLedger ledger).freezeAt
        have hfields := sharedLedger_fields ledger
        rw [hfields.2.2.2.1, he]
        change dispatched.startResult.clock.g = (liveRegistersAt registers x.time).gridBoundary
        rw [hclock]
        exact hd.2.1.symm

/-- Align all arguments of the call before removing the physical freeze guard.
The disabled zero theorem here is obtained from the accepted operation producer. -/
private theorem readout_physical
    (s : ℕ) (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (done : CompletedRound rate) (c : RecordedQueueRun.RoundInput p.K) (l0 : Ledger rate)
    (hext : extractRound r = some done) (hr : laterCollectionReadout s r = some c)
    (hframe : CollectionBufferProvenance.collectionContext done.context.preLedger =
      CollectionBufferProvenance.collectionContext l0)
    (hpositive : 0 < l0.sigma) (hcut : l0.cutoff ≤ r.input.time.val + 1)
    (hdisabled : c.enabled = false → c.recordedArm = none ∧ ∀ a,
      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) :
    c.enabled = collectionEnabled l0 r.input.time ∧
    c.enabled = decide (r.input.time.val + 1 < l0.freezeAt) ∧
    c.rate = done.context.payload.rate ∧
    c.reward = (fun a => ((r.input.rewards r.input.time a).val : ℝ) / (D p : ℝ)) ∧
    ∃ out : CoordinatorRecordingOperation.Output p,
      laterCollectionCall s r = some ⟨done.context.payload, done.context.preLedger,
        done.context.started, done.context.weights⟩ ∧
      CoordinatorRecorderComplementBridge.run (collectionRecordingInput r.output.preparation
        done.context.payload done.context.started done.context.weights) = some out ∧
      r.output.coordinator.recording = some out ∧ out.gateArm = c.recordedArm ∧
      (∀ a, CoordinatorCollectionLedger.localArrival (rawDiagnostic r) a =
        RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) ∧
      (∀ a, physicalQueueRecord l0 a r = (c.enabled,
        RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)) ∧
      (∀ a, CoordinatorCollectionLedger.localQueueRecord l0 done.input.round
        done.input.enabled done.input.raw a = physicalQueueRecord l0 a r) ∧
      done.context.started.clock.g = l0.freezeAt := by
  classical
  obtain ⟨P, l, started, weights, out, hcall, _hdiag, hrun, henabled, _hclock,
    hrate, hreward, hrecording, hgate, harrival⟩ := laterCollectionReadout_call s r c hr
  have hcanonical := readout_call_context s r c done hr hext
  have heq := Option.some.inj (hcall.symm.trans hcanonical)
  cases heq
  have hs : done.context.preLedger.sigma = l0.sigma := congrArg (fun x => x.2.1) hframe
  have hc : done.context.preLedger.cutoff = l0.cutoff := congrArg (fun x => x.2.2.1) hframe
  have hg : done.context.preLedger.freezeAt = l0.freezeAt := congrArg (fun x => x.2.2.2.1) hframe
  have henabled0 : c.enabled = collectionEnabled l0 r.input.time := by
    rw [henabled]
    simp only [collectionEnabled, hs, hc, hg]
  have henabledFreeze : c.enabled = decide (r.input.time.val + 1 < l0.freezeAt) := by
    rw [henabled0]
    simp only [collectionEnabled, hpositive, hcut, true_and]
  change r.output.coordinator.recording = some out at hrecording
  have hraw : rawDiagnostic r = out.gateArm.map (fun a => (a, out.rawArrival)) := by
    simp only [rawDiagnostic, hrecording, Option.bind_some]
  have harr : ∀ a, CoordinatorCollectionLedger.localArrival (rawDiagnostic r) a =
      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a := by
    intro a
    rw [hraw]
    exact harrival a
  refine ⟨henabled0, henabledFreeze, hrate, hreward, out, hcanonical, hrun,
    hrecording, hgate, harr, ?_, ?_, ?_⟩
  · intro a
    simp only [physicalQueueRecord, ← henabled0, ← henabledFreeze, Bool.and_self, harr a]
    by_cases hf : r.input.time.val + 1 < l0.freezeAt
    · rw [ite_eq_left hf]
    · have he : c.enabled = false := by simp only [henabledFreeze, hf, decide_false]
      rw [ite_eq_right hf, (hdisabled he).2 a]
  · intro a
    obtain ⟨hrawInput, henabledInput⟩ := actual_completed_input_raw_and_enabled r done hext
    have hround := (actual_collection_round_checked r done hext).2.1
    rw [hround, hrawInput, henabledInput]
    simp only [CoordinatorCollectionLedger.localQueueRecord, CoordinatorCollectionLedger.sourceRound,
      physicalQueueRecord, collectionEnabled, hs, hc, hg, hpositive, hcut, true_and]
    by_cases hf : r.input.time.val + 1 < l0.freezeAt <;> simp only [hf, decide_true,
      decide_false, Bool.and_self, ite_true, Bool.false_eq_true, ite_false]
  · exact (choice_started_freeze r.input done.context
      (actual_collection_round_checked r done hext).1).trans hg

private theorem actual_segment_contexts
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (e : ℕ) (seg : Segment rate)
    (hat : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg) :
    ∀ r ∈ seg.records, ∀ done : CompletedRound rate, extractRound r = some done →
      done.context.payload = seg.context.payload ∧
      CollectionBufferProvenance.collectionContext done.context.preLedger =
        CollectionBufferProvenance.collectionContext seg.context.preLedger := by
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
  | none =>
    have hnil := (ReferenceCompletePhysicalHistory.no_launch_complete_history rate z rewards C_star C_h hl).2.1
    have hlt := b.isLt
    have hlen : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length = 0 :=
      congrArg List.length hnil
    omega
  | some initial =>
    have hchain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
      rate z rewards C_star C_h initial hl
    exact segment_contexts _ _ _ seg (connected_drop _ initial _ e hchain)
      (segmentAt_branch _ e seg hat).1


/-- Every retained slot obtains its own date discharge on the original row.
No extraction or numerical readout is an input to this segment lemma. -/
private theorem segment_calendar_slots
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (e : ℕ) (seg : Segment rate) (I : Initializer p)
    (hat : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg)
    (hinit : I.checkedStart rate = .success seg.context.preLedger)
    (hsigma : I.sigma = seg.context.payload.sigma.val + 1)
    (hdate : I.cutoff = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e + 1)
    (hfirst : I.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val seg.context.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))))
    (hlater : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h <
      seg.context.payload.sigma.val) :
    ∀ j : Fin seg.records.length,
    ∃ (done : CompletedRound rate) (c : RecordedQueueRun.RoundInput p.K),
      extractRound seg.records[j.val] = some done ∧
      laterCollectionReadout (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        seg.records[j.val] = some c ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate seg.records[j.val] = some c ∧
      done.context.payload = seg.context.payload ∧
      CollectionBufferProvenance.collectionContext done.context.preLedger =
        CollectionBufferProvenance.collectionContext seg.context.preLedger ∧
      c.enabled = collectionEnabled seg.context.preLedger seg.records[j.val].input.time ∧
      c.enabled = decide (seg.records[j.val].input.time.val + 1 < seg.context.preLedger.freezeAt) ∧
      c.rate = seg.context.payload.rate ∧
      c.reward = (fun a => ((rewards seg.records[j.val].input.time a).val : ℝ) / (D p : ℝ)) ∧
      (c.enabled = false → c.recordedArm = none ∧ ∀ a,
        RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) ∧
      ∃ out : CoordinatorRecordingOperation.Output p,
        laterCollectionCall (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
          seg.records[j.val] = some ⟨done.context.payload, done.context.preLedger,
            done.context.started, done.context.weights⟩ ∧
        CoordinatorRecorderComplementBridge.run (collectionRecordingInput seg.records[j.val].output.preparation
          done.context.payload done.context.started done.context.weights) = some out ∧
        seg.records[j.val].output.coordinator.recording = some out ∧ out.gateArm = c.recordedArm ∧
        (∀ a, CoordinatorCollectionLedger.localArrival (rawDiagnostic seg.records[j.val]) a =
          RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) ∧
        (∀ a, physicalQueueRecord seg.context.preLedger a seg.records[j.val] = (c.enabled,
          RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)) ∧
        (∀ a, CoordinatorCollectionLedger.localQueueRecord seg.context.preLedger done.input.round
          done.input.enabled done.input.raw a = physicalQueueRecord seg.context.preLedger a seg.records[j.val]) ∧
        done.context.started.clock.g = seg.context.preLedger.freezeAt := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hframes := actual_segment_contexts rewards C_star C_h z b e seg hat
  have hinitFields := CollectionBufferProvenance.startCollectionChecked_success_context
    I.assignment I.sigma I.cutoff I.freezeAt I.base I.outside seg.context.preLedger hinit
  have hpositive : 0 < seg.context.preLedger.sigma := by rw [hinitFields.2.1, hsigma]; omega
  intro j
  obtain ⟨done, hext⟩ := actual_later_segment_slot_extracts rate rewards C_star C_h z e seg hat j
  obtain ⟨hpay, hframe⟩ := hframes _ (List.getElem_mem j.isLt) done hext
  have hslot := actual_later_segment_slot_record rate rewards C_star C_h z e seg hat j
  obtain ⟨hk, hrecord⟩ := List.getElem?_eq_some_iff.mp hslot
  have hinputs := actual_later_segment_slot_source_inputs rate rewards C_star C_h z e seg hat j
  have hrow : seg.records[j.val].input.row = z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
    change seg.records[j.val].input.rows seg.records[j.val].input.selected = _
    rw [hinputs.1, hinputs.2.1]
  have htime := actual_later_segment_slot_time rate rewards C_star C_h z e seg hat j
  have hcutLe : seg.context.preLedger.cutoff ≤ seg.records[j.val].input.time.val + 1 := by
    rw [hinitFields.2.2.2.1, hdate, htime]
    omega
  have htrueCut : FollowerCutoffScan.firstCutoff p rate.eta.val done.context.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val seg.records[j.val].input.row) ≤
      seg.records[j.val].input.time.val + 1 := by
    rw [hpay, hrow, ← hfirst, hdate, htime]
    omega
  have hlater' : s < done.context.payload.sigma.val := by rw [hpay]; exact hlater
  obtain ⟨c, hr, hz⟩ := completed_calendar_readout rewards C_star C_h z ⟨e + j.val, hk⟩ done
    (by simpa only [hrecord] using hext) hlater' (by simpa only [hrecord] using htrueCut)
  have hr' : laterCollectionReadout s seg.records[j.val] = some c := by
    simpa only [hrecord] using hr
  obtain ⟨henabled, hfreeze, hrate, hreward, hout⟩ :=
    readout_physical s seg.records[j.val] done c seg.context.preLedger hext hr' hframe hpositive hcutLe hz
  refine ⟨done, c, hext, hr', (collection_readout_zero s _ c hr').2, hpay, hframe,
    henabled, hfreeze, ?_, ?_, hz, hout⟩
  · rw [hrate, hpay]
  · rw [hreward, hinputs.2.2]


/-- Total enumeration happens only after every actual slot has a SOME.
The map through extracted inputs uses the same retained checked round. -/
private theorem segment_calendar_word
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (e : ℕ) (seg : Segment rate) (I : Initializer p)
    (hat : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg)
    (hinit : I.checkedStart rate = .success seg.context.preLedger)
    (hsigma : I.sigma = seg.context.payload.sigma.val + 1)
    (hdate : I.cutoff = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e + 1)
    (hfirst : I.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val seg.context.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))))
    (hlater : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h <
      seg.context.payload.sigma.val) :
    ∃ Dword : List (RecordedQueueRun.RoundInput p.K),
      ∃ hD : Dword.length = seg.records.length,
      (∀ j : Fin seg.records.length,
        let r := seg.records[j.val]
        let c := Dword[j.val]'(by omega)
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[e + j.val]? = some r ∧
        r.input.time.val = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + (e + j.val) ∧
        r.input.rows = z.1.2 ∧
        r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
        r.input.rewards = rewards ∧
        ∃ done : CompletedRound rate,
          extractRound r = some done ∧
          laterCollectionReadout (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) r = some c ∧
          ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧
          done.context.payload = seg.context.payload ∧
          CollectionBufferProvenance.collectionContext done.context.preLedger =
            CollectionBufferProvenance.collectionContext seg.context.preLedger ∧
          c.enabled = collectionEnabled seg.context.preLedger r.input.time ∧
          c.enabled = decide (r.input.time.val + 1 < seg.context.preLedger.freezeAt) ∧
          c.rate = seg.context.payload.rate ∧
          c.reward = (fun a => ((rewards r.input.time a).val : ℝ) / (D p : ℝ)) ∧
          (c.enabled = false → c.recordedArm = none ∧ ∀ a,
            RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) ∧
          ∃ out : CoordinatorRecordingOperation.Output p,
            laterCollectionCall (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) r =
              some ⟨done.context.payload, done.context.preLedger, done.context.started, done.context.weights⟩ ∧
            CoordinatorRecorderComplementBridge.run (collectionRecordingInput r.output.preparation
              done.context.payload done.context.started done.context.weights) = some out ∧
            r.output.coordinator.recording = some out ∧ out.gateArm = c.recordedArm ∧
            (∀ a, CoordinatorCollectionLedger.localArrival (rawDiagnostic r) a =
              RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) ∧
            (∀ a, physicalQueueRecord seg.context.preLedger a r = (c.enabled,
              RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)) ∧
            (∀ a, CoordinatorCollectionLedger.localQueueRecord seg.context.preLedger done.input.round
              done.input.enabled done.input.raw a = physicalQueueRecord seg.context.preLedger a r) ∧
            done.context.started.clock.g = seg.context.preLedger.freezeAt) ∧
      seg.records.map (laterCollectionReadout
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)) = Dword.map some ∧
      (∀ a, CollectionKnownQueueContinuation.inputQueueRecords seg.context.preLedger a seg.inputs =
          seg.records.map (physicalQueueRecord seg.context.preLedger a) ∧
        seg.records.map (physicalQueueRecord seg.context.preLedger a) =
          Dword.map (fun c => (c.enabled,
            RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a))) ∧
      (∀ (Dother : List (RecordedQueueRun.RoundInput p.K))
        (hlen : Dother.length = seg.records.length),
        (∀ j : Fin seg.records.length, laterCollectionReadout
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) seg.records[j.val] =
            some (Dother[j.val]'(by omega))) → Dother = Dword) := by
  classical
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hslots := segment_calendar_slots rewards C_star C_h z b e seg I hat hinit hsigma hdate hfirst hlater
  have hexists : ∀ j : Fin seg.records.length, ∃ c, laterCollectionReadout s seg.records[j.val] = some c := by
    intro j
    obtain ⟨done, c, _, hr, _⟩ := hslots j
    exact ⟨c, hr⟩
  let Dword := readoutWord (laterCollectionReadout s) seg.records hexists
  have hD : Dword.length = seg.records.length := readoutWord_length _ _ _
  have hread (j : Fin seg.records.length) : laterCollectionReadout s seg.records[j.val] =
      some (Dword[j.val]'(by omega)) := readoutWord_get _ _ _ j
  have hvalues (j : Fin seg.records.length) := hslots j
  have hphysical (a : Fin p.K) : seg.records.map (physicalQueueRecord seg.context.preLedger a) =
      Dword.map (fun c => (c.enabled,
        RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)) := by
    apply List.ext_getElem
    · simp only [List.length_map, hD]
    · intro k hk hk'
      have hj : k < seg.records.length := by simpa only [List.length_map] using hk
      obtain ⟨done, c, _, hr, _, _, _, _, _, _, _, _, out, _, _, _, _, _, hp, _⟩ := hvalues ⟨k, hj⟩
      have heq := Option.some.inj (hr.symm.trans (hread ⟨k, hj⟩))
      simpa only [List.getElem_map, ← heq] using hp a
  have hinputs (a : Fin p.K) : CollectionKnownQueueContinuation.inputQueueRecords
      seg.context.preLedger a seg.inputs = seg.records.map (physicalQueueRecord seg.context.preLedger a) := by
    simp only [CollectionKnownQueueContinuation.inputQueueRecords, Segment.inputs, inputs, completed,
      List.map_filterMap]
    apply List.filterMap_eq_map_iff_forall_eq_some.mpr
    intro r hr
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hr
    obtain ⟨done, c, hext, _, _, _, _, _, _, _, _, _, out, _, _, _, _, _, _, hlocal⟩ := hvalues ⟨j, hj⟩
    subst r
    simpa only [hext, Option.map_some, Function.comp_apply] using congrArg some (hlocal.1 a)
  refine ⟨Dword, hD, ?_, readoutWord_map_some _ _ _, fun a => ⟨hinputs a, hphysical a⟩, ?_⟩
  · intro j
    obtain ⟨done, c, hext, hr, hcell, hpay, hctx, hen, hfreeze, hrate, hreward, hz, hout⟩ := hslots j
    have heq := Option.some.inj (hr.symm.trans (hread j))
    have hsource := actual_later_segment_slot_source_inputs rate rewards C_star C_h z e seg hat j
    refine ⟨actual_later_segment_slot_record rate rewards C_star C_h z e seg hat j,
      actual_later_segment_slot_time rate rewards C_star C_h z e seg hat j,
      hsource.1, hsource.2.1, hsource.2.2, done, ?_⟩
    rw [← heq]
    exact ⟨hext, hr, hcell, hpay, hctx, hen, hfreeze, hrate, hreward, hz, hout⟩
  · intro Dother hlen hother
    exact readoutWord_unique _ _ hexists Dother hlen hother


/-- Internal conditional producer for the complete numerical word of the
collection reached from an actual later LIVE prefix. The only local invariant
is the displayed strict later-start condition. The horizon alternative creates
no collection segment. All other incoming coordinator tags assert `True`.
This result supplies neither a global seed nor manuscript or regret closure. -/
theorem complete_later_live_collection_calendar_word
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    match hstate : R[b.val].input.state.coordinator with
    | .live r0 q0 beta =>
      ∀ hlater : s < r0.payload.sigma.val,
      let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix rate rewards C_star C_h z b.val
      let n := W.length
      let e := b.val + n
      let A := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
        rewards C_star C_h z b r0 q0 beta hstate hlater
      let V := fun (j : CanonicalFastSampling.FastArm r0.payload.slowSet) (v : ℕ) =>
        QueueReplay.replay (4 * rate.n) (r0.complementScores j, q0.queue j)
          ((A.take v).map fun c => (c.enabled, RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val))
      let d := fun j => if n = 0 then q0.previousService j else (V j n).1 - (V j (n - 1)).1
      e ≤ R.length ∧ s + e ≤ p.T ∧
      ∃ (rE : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (qE : CoordinatorLiveServiceFinish.OwnedRegisters rE)
        (hp : rE.payload = r0.payload),
        (∀ hpos : 0 < n, (W[n - 1]'(by omega)).output.next.coordinator = .live rE qE beta) ∧
        (∀ he : e < R.length, (R[e]'he).input.state.coordinator = .live rE qE beta) ∧
        (∀ j : CanonicalFastSampling.FastArm r0.payload.slowSet,
          let jE : CanonicalFastSampling.FastArm rE.payload.slowSet := ⟨j.val, by simpa only [hp] using j.property⟩
          (rE.complementScores jE, qE.queue jE) = V j n ∧ qE.previousService jE = d j) ∧
        (e = R.length ∨
          ∃ (he : e < R.length)
            (chosen : CoordinatorRoundDispatch.LiveOutcome (liveInput (R[e]'he).input rE qE beta)),
            chosen = CoordinatorRoundDispatch.dispatchLive (liveInput (R[e]'he).input rE qE beta) ∧
            (R[e]'he).output.preparation.coordinator = .live rE qE beta chosen ∧
            match chosen with
            | .cutoffChosen _dispatched _ ledger _ _ _ _ _ _ _ =>
              let cut := R[e]'he
              let t := cut.input.time
              let l0 := sharedLedger ledger
              t.val + 1 = s + e + 1 ∧
              t.val + 1 = FollowerCutoffScan.firstCutoff p rate.eta.val r0.payload.sigma
                (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                  (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) ∧
              ∃ (seg : Segment rate) (I : Initializer p)
                (Dword : List (RecordedQueueRun.RoundInput p.K)) (hD : Dword.length = seg.records.length),
                segmentAt R e = some seg ∧ seg.entry = cut ∧
                seg.context.payload = r0.payload ∧ seg.context.preLedger = l0 ∧
                seg.context.initializer = some I ∧
                I = cutoffInitializer (liveRegistersAt rE t) (liveOwnedAt rE qE t) beta t ∧
                I.checkedStart rate = .success l0 ∧
                I.assignment.arm = r0.payload.assignment.assigned ∧
                I.sigma = r0.payload.sigma.val + 1 ∧ I.cutoff = s + e + 1 ∧
                I.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val r0.payload.sigma
                  (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                    (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) ∧
                I.freezeAt = rE.gridBoundary ∧ I.base = beta ∧
                ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
                (∃ tail, seg.records = cut :: tail) ∧
                seg.records ++ seg.remaining = R.drop e ∧ seg.exit = exitOf seg.remaining ∧
                CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
                  (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
                  I.assignment I.sigma I.cutoff I.freezeAt I.base I.outside seg.inputs =
                    .success ⟨l0, seg.accepted, seg.final⟩ ∧
                e + seg.records.length ≤ R.length ∧ s + (e + seg.records.length) ≤ p.T ∧
                (∀ j : Fin seg.records.length,
                  let r := seg.records[j.val]
                  let c := Dword[j.val]'(by omega)
                  (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[e + j.val]? = some r ∧
                  r.input.time.val = s + (e + j.val) ∧
                  r.input.rows = z.1.2 ∧
                  r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
                  r.input.rewards = rewards ∧
                  ∃ done : CompletedRound rate,
                    extractRound r = some done ∧
                    laterCollectionReadout s r = some c ∧
                    ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧
                    done.context.payload = r0.payload ∧
                    CollectionBufferProvenance.collectionContext done.context.preLedger =
                      CollectionBufferProvenance.collectionContext l0 ∧
                    c.enabled = collectionEnabled l0 r.input.time ∧
                    c.enabled = decide (r.input.time.val + 1 < l0.freezeAt) ∧
                    c.rate = r0.payload.rate ∧
                    c.reward = (fun a => ((rewards r.input.time a).val : ℝ) / (D p : ℝ)) ∧
                    (c.enabled = false → c.recordedArm = none ∧ ∀ a,
                      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) ∧
                    ∃ out : CoordinatorRecordingOperation.Output p,
                      laterCollectionCall s r =
                        some ⟨done.context.payload, done.context.preLedger, done.context.started, done.context.weights⟩ ∧
                      CoordinatorRecorderComplementBridge.run (collectionRecordingInput r.output.preparation
                        done.context.payload done.context.started done.context.weights) = some out ∧
                      r.output.coordinator.recording = some out ∧ out.gateArm = c.recordedArm ∧
                      (∀ a, CoordinatorCollectionLedger.localArrival (rawDiagnostic r) a =
                        RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) ∧
                      (∀ a, physicalQueueRecord l0 a r = (c.enabled,
                        RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)) ∧
                      (∀ a, CoordinatorCollectionLedger.localQueueRecord l0 done.input.round
                        done.input.enabled done.input.raw a = physicalQueueRecord l0 a r) ∧
                      done.context.started.clock.g = l0.freezeAt) ∧
                seg.records.map (laterCollectionReadout s) = Dword.map some ∧
                (∀ a, CollectionKnownQueueContinuation.inputQueueRecords l0 a seg.inputs =
                    seg.records.map (physicalQueueRecord l0 a) ∧
                  seg.records.map (physicalQueueRecord l0 a) =
                    Dword.map (fun c => (c.enabled,
                      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a))) ∧
                (∀ (Dother : List (RecordedQueueRun.RoundInput p.K))
                  (hlen : Dother.length = seg.records.length),
                  (∀ j : Fin seg.records.length, laterCollectionReadout s seg.records[j.val] =
                      some (Dother[j.val]'(by omega))) → Dother = Dword)
            | _ => False)
    | _ => True := by
  classical
  intro R s
  split
  next r0 q0 beta hstate =>
    intro hlater W n e A V d
    have hbound : e ≤ R.length :=
      ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_length_le rewards C_star C_h z b
    have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
    have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
    have hlen' : R.length = p.T - s := hlen
    have hB := ReferenceCompleteLaterLiveOutsideCutoffBoundary.complete_later_live_outside_cutoff_boundary
      rate rewards C_star C_h z b
    dsimp only at hB
    split at hB
    next rB qB betaB hBstate =>
      have hfields := CoordinatorConfiguration.live.inj (hBstate.symm.trans hstate)
      have hrB : rB = r0 := hfields.1
      have hqB := hfields.2.1
      have hbetaB := hfields.2.2
      subst rB
      cases hqB
      subst betaB
      obtain ⟨rE, qE, hp, hlast, hin, hvalues, halt⟩ := hB hlater
      refine ⟨hbound, by omega, rE, qE, hp, hlast, hin, hvalues, ?_⟩
      rcases halt with hterminal | ⟨he, chosen, hdispatch, hprep, hcut⟩
      · exact Or.inl hterminal
      · refine Or.inr ⟨he, chosen, hdispatch, hprep, ?_⟩
        cases chosen with
        | cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending hnone selected =>
          obtain ⟨hdate, hscan, seg, I, hat, hentry, hpay, hledger, hI, hIeq, hchecked,
            harm, hsigma, hcutoff, hfreeze, hbase, hne, hpart, hexit, hfold, _houtside, _hassigned, _hrest⟩ := hcut
          have hinitSeg : I.checkedStart rate = .success seg.context.preLedger := by rw [hledger]; exact hchecked
          have hsigSeg : I.sigma = seg.context.payload.sigma.val + 1 := by rw [hpay]; exact hsigma
          have hdateI : I.cutoff = s + e + 1 := hcutoff.trans hdate
          have hscanI : I.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val r0.payload.sigma
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) := hcutoff.trans hscan
          obtain ⟨Dword, hD, hcover, hmap, hsync, hunique⟩ :=
            segment_calendar_word rewards C_star C_h z b e seg I hat hinitSeg hsigSeg hdateI
              (by rw [hpay]; exact hscanI) (by rw [hpay]; exact hlater)
          have hchosen : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true := by
            rw [hentry]
            unfold ReferenceCollectionPhaseHistory.cutoffChosen
            have hprepare : (prepare (R[e]'he).input).coordinator = (R[e]'he).output.preparation.coordinator := by
              rw [(R[e]'he).output_eq]; rfl
            rw [hprepare, hprep]
          have hpartlen := congrArg List.length hpart
          simp only [List.length_append, List.length_drop] at hpartlen
          have hv : e + seg.records.length ≤ R.length := by omega
          refine ⟨hdate, hscan, seg, I, Dword, hD, hat, hentry, hpay, hledger,
            hI, hIeq, hchecked, harm, hsigma, hdateI, hscanI, hfreeze, hbase,
            hchosen, hne, hpart, hexit, hfold, hv, by omega, ?_, hmap, ?_, hunique⟩
          · simpa only [hpay, hledger] using hcover
          · simpa only [hledger] using hsync
        | _ => exact hcut
    next hother => exact False.elim (hother r0 q0 beta hstate)
  all_goals trivial

end Bandits.Support.ReferenceCompleteLaterCollectionCalendarWord

end
