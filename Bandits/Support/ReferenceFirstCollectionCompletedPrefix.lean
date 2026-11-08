/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionEpochAlignment

import Mathlib.Data.List.TakeWhile

/-!
# Completed prefix of the actual first collection window

The source-facing first cutoff and the actual physical run are those of
`ReferenceFirstCollectionEpochAlignment`. This module links its computed
segment to the full raw collection window: successful extractions form an
initial prefix, and the segment's original remainder is exactly the rest of
that raw window followed by the untouched physical suffix.

Mathematical sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,
192-233,246-295`, `sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`. This is an
internal completed-prefix and calendar linkage; it does not establish the raw
observation history, incoming context at a later choice, queue or score truth,
domain survival, or a regret conclusion.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCollectionSegmentExtraction
open Bandits.Support.ReferenceCollectionPhaseHistory
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ActualReferenceInitializationBlock
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.BootstrapPrivateRoundStreams

namespace Bandits.Support.ReferenceFirstCollectionCompletedPrefix

variable {p : ConstructorDimensions.Parameters}

private theorem choice_none_of_laterChosen
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hlater : ReferenceCollectionPhaseHistory.laterChosen x = true) :
    ReferenceCollectionSegmentExtraction.choice x = none := by
  unfold ReferenceCollectionPhaseHistory.laterChosen at hlater
  unfold ReferenceCollectionSegmentExtraction.choice
  by_cases hselection : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none
  · simp [hselection]
  · simp only [hselection, ↓reduceIte]
    cases hdispatch : (ReferenceActivePhysicalStep.prepare x).coordinator with
    | first outcome =>
        rw [hdispatch] at hlater
        simp at hlater
    | live registers owned base outcome =>
        cases outcome <;> rw [hdispatch] at hlater
        all_goals simp at hlater
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;> rw [hdispatch] at hlater
        all_goals simp at hlater
        all_goals simp only [ReferenceCollectionSegmentExtraction.choiceOfCut]
    | invalidCollectionCutoff =>
        rw [hdispatch] at hlater
        simp at hlater
    | dagger =>
        rw [hdispatch] at hlater
        simp at hlater

private theorem continuing_not_laterChosen
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hcontinuing : ReferenceCollectionSegmentExtraction.continuing record = true) :
    ReferenceCollectionPhaseHistory.laterChosen record.input = false := by
  unfold ReferenceCollectionSegmentExtraction.continuing at hcontinuing
  cases hextract : ReferenceCollectionSegmentExtraction.extractRound record with
  | none => simp [hextract] at hcontinuing
  | some completed =>
      have hchoice :=
        (ReferenceCollectionSegmentExtraction.actual_collection_round_checked
          record completed hextract).1
      by_cases hlater : ReferenceCollectionPhaseHistory.laterChosen record.input = true
      · have hnone := choice_none_of_laterChosen record.input hlater
        rw [hchoice] at hnone
        contradiction
      · exact Bool.eq_false_of_not_eq_true hlater

private theorem takeWhile_prefix_of_implication {α : Type*}
    (P Q : α → Bool) (himp : ∀ a, P a = true → Q a = true)
    (records : List α) : records.takeWhile P <+: records.takeWhile Q := by
  induction records with
  | nil => exact ⟨_, rfl⟩
  | cons head tail ih =>
      by_cases hP : P head = true
      · have hQ := himp head hP
        obtain ⟨rest, hrest⟩ := ih
        refine ⟨rest, ?_⟩
        simp only [List.takeWhile_cons_of_pos hP, List.takeWhile_cons_of_pos hQ]
        exact congrArg (List.cons head) hrest
      · refine ⟨(head :: tail).takeWhile Q, ?_⟩
        simp [List.takeWhile_cons_of_neg hP]

/-- The actual first-collection segment is the completed prefix of the entire
raw collection window. The source inputs are the original source input and
whole reward table used by the admitted epoch alignment. Source-round numbers
are one based: an actual physical input with stored time `t` is source round
`t + 1`. The first physical record after the raw window is exposed only with
its literal index and `laterChosen` tag; no context at that boundary is
asserted. -/
theorem actual_first_collection_completed_prefix
    (rate : ReferenceFirstCollectionEpochAlignment.RateInput p)
    (source : ReferenceFirstCollectionEpochAlignment.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let Erun := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow Erun.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow Erun.records w
    let u := s + w + 1
    ∃ (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
      (seg : ReferenceCollectionSegmentExtraction.Segment rate),
      Erun.records = ReferenceFirstLiveConfirmationHistory.firstLiveWindow Erun.records ++ cut :: suffix ∧
      seg.entry = cut ∧
      ReferenceCollectionSegmentExtraction.segmentAt Erun.records w = some seg ∧
      B = cut :: suffix.takeWhile
        (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) ∧
      seg.records <+: B ∧
      seg.records = B.take seg.records.length ∧
      B = seg.records ++ B.drop seg.records.length ∧
      seg.records.length ≤ B.length ∧
      (∀ hlen : seg.records.length ≤ B.length, ∀ k : Fin seg.records.length,
        B[k.val]'(Nat.lt_of_lt_of_le k.isLt hlen) = seg.records[k.val] ∧
          Erun.records[w + k.val]? = some seg.records[k.val] ∧
          seg.records[k.val].input.time.val + 1 = u + k.val) ∧
      (∀ record ∈ seg.records, ∃ completed,
        ReferenceCollectionSegmentExtraction.extractRound record = some completed ∧
          completed.input.round = record.input.time) ∧
      seg.inputs.length = seg.records.length ∧
      seg.inputs.map (fun input => input.round.val + 1) =
        (List.range seg.records.length).map (fun k => u + k) ∧
      seg.remaining = B.drop seg.records.length ++ Erun.records.drop (w + B.length) ∧
      (ReferenceCollectionSegmentExtraction.extractRound cut = none →
        seg.records = [] ∧ seg.remaining = Erun.records.drop w) ∧
      match Erun.records.drop (w + B.length) with
      | [] => True
      | boundary :: _ =>
          Erun.records[w + B.length]? = some boundary ∧
            ReferenceCollectionPhaseHistory.laterChosen boundary.input = true := by
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let Erun := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow Erun.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow Erun.records w
  let u := s + w + 1
  rcases ReferenceFirstCollectionEpochAlignment.actual_first_collection_segment
      rate source rewards C_star C_h count hcross hspan hshort with
    ⟨cut, suffix, registers, owned, base, choice, initializer, seg,
      hsplit, hcutTime, hchoice, hpayload, hinitializer, hchoiceInitializer,
      hsigma, hcutoff, hfreeze, hfreezeGrid, hbase, hassignment, hchecked,
      hkpos, hcutoffSpan, hgridLower, hgridUpper, hfirstCutoff, hsegmentAt,
      hentry, hcontext, hrecords, hremaining, hpartition, hwindow⟩
  have hsplit' : Erun.records =
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow Erun.records ++ cut :: suffix := by
    simpa [Erun] using hsplit
  have hdrop : Erun.records.drop w = cut :: suffix := by
    rw [hsplit']
    simp [w]
  have hwindow' : B = cut :: suffix.takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) := by
    simpa [B, Erun, w] using hwindow
  have hsegmentAt : ReferenceCollectionSegmentExtraction.segmentAt Erun.records w = some seg := by
    simpa [Erun, w] using hsegmentAt
  have hentry' : seg.entry = cut := hentry
  have hshapeRecords :
      seg.records = (if (ReferenceCollectionSegmentExtraction.extractRound cut).isSome
        then cut :: suffix.takeWhile ReferenceCollectionSegmentExtraction.continuing else []) := by
    simpa [hentry'] using hrecords
  have hshapeRemaining :
      seg.remaining = (if (ReferenceCollectionSegmentExtraction.extractRound cut).isSome
        then suffix.dropWhile ReferenceCollectionSegmentExtraction.continuing else cut :: suffix) := by
    simpa [hentry'] using hremaining
  have hprefixTail : suffix.takeWhile ReferenceCollectionSegmentExtraction.continuing <+:
      suffix.takeWhile (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) :=
    takeWhile_prefix_of_implication
      ReferenceCollectionSegmentExtraction.continuing
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
      (fun record h => by
        have htag := continuing_not_laterChosen record h
        simp [htag]) suffix
  have hprefix : seg.records <+: B := by
    by_cases hfailed : ReferenceCollectionSegmentExtraction.extractRound cut = none
    · have hrecordsNil : seg.records = [] := by
        rw [hshapeRecords]
        simp [hfailed]
      rw [hrecordsNil]
      exact ⟨B, by simp⟩
    · have hextract : (ReferenceCollectionSegmentExtraction.extractRound cut).isSome = true := by
        cases h : ReferenceCollectionSegmentExtraction.extractRound cut with
        | none => exact (hfailed h).elim
        | some completed => rfl
      have hrecords' : seg.records = cut ::
          suffix.takeWhile ReferenceCollectionSegmentExtraction.continuing := by
        rw [hshapeRecords]
        simp [hextract]
      rcases hprefixTail with ⟨middle, hmiddle⟩
      refine ⟨middle, ?_⟩
      rw [hrecords', hwindow']
      exact congrArg (List.cons cut) hmiddle
  have hprefixKeep := hprefix
  rcases hprefix with ⟨middle, hmiddle⟩
  let tail := suffix.dropWhile (fun record =>
    !ReferenceCollectionPhaseHistory.laterChosen record.input)
  have hbody : B ++ tail = Erun.records.drop w := by
    change B ++ suffix.dropWhile
        (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) =
      Erun.records.drop w
    rw [hwindow', hdrop]
    simp only [List.cons_append, List.takeWhile_append_dropWhile]
  have hpartition' : seg.records ++ seg.remaining = Erun.records.drop w := by
    simpa [Erun, w] using hpartition
  have hcancel : seg.remaining = middle ++ tail := by
    apply List.append_cancel_left
    calc
      seg.records ++ seg.remaining = Erun.records.drop w := hpartition'
      _ = B ++ tail := hbody.symm
      _ = (seg.records ++ middle) ++ tail := by rw [← hmiddle]
      _ = seg.records ++ (middle ++ tail) := List.append_assoc _ _ _
  have hdropMiddle : B.drop seg.records.length = middle := by
    rw [← hmiddle]
    simp
  have hdropTail : Erun.records.drop (w + B.length) = tail := by
    calc
      Erun.records.drop (w + B.length) = (Erun.records.drop w).drop B.length := by
        rw [← List.drop_drop]
      _ = (B ++ tail).drop B.length := by rw [← hbody]
      _ = tail := by simp
  have hlen : seg.records.length ≤ B.length := hprefixKeep.length_le
  have hrecordsTake : seg.records = B.take seg.records.length := by
    rw [← hmiddle]
    simp
  have hBsplit : B = seg.records ++ B.drop seg.records.length := by
    calc
      B = seg.records ++ middle := hmiddle.symm
      _ = seg.records ++ B.drop seg.records.length := by rw [hdropMiddle]
  have hlookupTime :=
    ReferenceFirstCollectionEpochAlignment.actual_first_collection_window_time
      rate source rewards C_star C_h count hcross hspan hshort
  have hlink : ∀ hlen : seg.records.length ≤ B.length,
      ∀ k : Fin seg.records.length,
      B[k.val]'(Nat.lt_of_lt_of_le k.isLt hlen) = seg.records[k.val] ∧
        Erun.records[w + k.val]? = some seg.records[k.val] ∧
        seg.records[k.val].input.time.val + 1 = u + k.val := by
    intro hlen k
    have hkB : k.val < B.length := Nat.lt_of_lt_of_le k.isLt hlen
    have hprefixGet := (List.prefix_iff_getElem?).mp hprefixKeep k.val k.isLt
    have hBeq : B[k.val] = seg.records[k.val] := by
      have hBget : B[k.val]? = some B[k.val] := by simp [hkB]
      exact Option.some.inj (hBget.symm.trans hprefixGet)
    have htimeB := hlookupTime ⟨k.val, hkB⟩
    have hrecord : Erun.records[w + k.val]? = some B[k.val] := by
      simpa [Erun, w] using htimeB.1
    have hsource : B[k.val].input.time.val + 1 = u + k.val := by
      simpa [s, Erun, w, u] using htimeB.2
    refine ⟨hBeq, ?_, ?_⟩
    · simpa [hBeq] using hrecord
    · simpa [hBeq] using hsource
  have hsegmentBranch := ReferenceCollectionSegmentExtraction.segmentAt_branch
    Erun.records w seg hsegmentAt
  have hrawSegment := hsegmentBranch.1
  have hgood : ∀ record ∈ seg.records,
      (ReferenceCollectionSegmentExtraction.extractRound record).isSome = true :=
    ReferenceCollectionSegmentExtraction.segment_all_completed (Erun.records.drop w) seg hrawSegment
  have hphysical : ∀ record ∈ seg.records, ∃ completed,
      ReferenceCollectionSegmentExtraction.extractRound record = some completed ∧
        completed.input.round = record.input.time := by
    intro record hmem
    cases hextract : ReferenceCollectionSegmentExtraction.extractRound record with
    | none =>
        have hsome := hgood record hmem
        simp [hextract] at hsome
    | some completed =>
        exact ⟨completed, rfl,
          (ReferenceCollectionSegmentExtraction.actual_collection_round_checked
            record completed hextract).2.1⟩
  have hinputCount := ReferenceCollectionSegmentExtraction.segment_input_count
    (Erun.records.drop w) seg hrawSegment
  have hinputsCalendar := ReferenceCollectionSegmentExtraction.inputs_calendar
    seg.records hgood
  have hinputTimes : seg.inputs.map (fun input => input.round.val + 1) =
      seg.records.map (fun record => record.input.time.val + 1) := by
    calc
      seg.inputs.map (fun input => input.round.val + 1) =
          (seg.inputs.map fun input => input.round.val).map Nat.succ := by
            simp [ReferenceCollectionSegmentExtraction.Segment.inputs,
              ReferenceCollectionSegmentExtraction.inputs, List.map_map]
      _ = (seg.records.map fun record => record.input.time.val).map Nat.succ := by
            exact congrArg (List.map Nat.succ) hinputsCalendar
      _ = seg.records.map (fun record => record.input.time.val + 1) := by
            simp [List.map_map, Nat.succ_eq_add_one]
  have htimeMap : seg.records.map (fun record => record.input.time.val + 1) =
      (List.range seg.records.length).map (fun k => u + k) := by
    apply List.ext_getElem
    · simp
    · intro i hiLeft hiRight
      have hi : i < seg.records.length := by simpa using hiLeft
      have h := (hlink hlen ⟨i, hi⟩).2.2
      simpa using h
  have hcalendar := hinputTimes.trans htimeMap
  have hfailed : ReferenceCollectionSegmentExtraction.extractRound cut = none →
      seg.records = [] ∧ seg.remaining = Erun.records.drop w := by
    intro hcutFailed
    have hrecordsNil : seg.records = [] := by
      rw [hshapeRecords]
      simp [hcutFailed]
    have hremainingAll : seg.remaining = cut :: suffix := by
      rw [hshapeRemaining]
      simp [hcutFailed]
    constructor
    · exact hrecordsNil
    · rw [hremainingAll, ← hdrop]
  have hboundaryTail : Erun.records.drop (w + B.length) = tail := by
    exact hdropTail
  have hboundary : match Erun.records.drop (w + B.length) with
      | [] => True
      | boundary :: _ => Erun.records[w + B.length]? = some boundary ∧
          ReferenceCollectionPhaseHistory.laterChosen boundary.input = true := by
    rw [hboundaryTail]
    change match suffix.dropWhile
        (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) with
      | [] => True
      | boundary :: _ => Erun.records[w + B.length]? = some boundary ∧
          ReferenceCollectionPhaseHistory.laterChosen boundary.input = true
    cases htail : suffix.dropWhile
        (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) with
    | nil => simp
    | cons boundary rest =>
        have hnot : ¬ (!ReferenceCollectionPhaseHistory.laterChosen boundary.input = true) := by
          have hlenTail : 0 < (suffix.dropWhile
              (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)).length := by
            simp [htail]
          have hget := List.dropWhile_get_zero_not
            (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
            suffix hlenTail
          simpa [htail] using hget
        have htag : ReferenceCollectionPhaseHistory.laterChosen boundary.input = true := by
          cases h : ReferenceCollectionPhaseHistory.laterChosen boundary.input with
          | false => simp [h] at hnot
          | true => rfl
        have hhead : (Erun.records.drop (w + B.length))[0]? = some boundary := by
          rw [hboundaryTail]
          change (suffix.dropWhile
            (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input))[0]? =
              some boundary
          simp [htail]
        have hindex : Erun.records[w + B.length]? = some boundary := by
          simpa [List.getElem?_drop] using hhead
        constructor
        · exact hindex
        · exact htag
  exact ⟨cut, suffix, seg, hsplit', hentry', hsegmentAt, hwindow', hprefixKeep,
    hrecordsTake, hBsplit, hlen, hlink, hphysical, hinputCount, hcalendar,
    hcancel.trans (by rw [hdropMiddle, hdropTail]), hfailed, hboundary⟩

end Bandits.Support.ReferenceFirstCollectionCompletedPrefix

end
