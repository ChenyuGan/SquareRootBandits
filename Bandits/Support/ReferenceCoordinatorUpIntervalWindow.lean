/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCoordinatorUpPhysicalCall
public import Bandits.Support.WaitedWordWindow

import Mathlib.Data.List.TakeDrop
import Lean.Elab.Tactic.Omega

/-!
# Actual coordinator UP replay across a physical interval

The physical input and coordinator receiver call come from
`sources/zip4/manuscript/05_binary_transport.tex:36-53,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:277-284,327-348`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,151-157`.

This module cuts two runs of the existing physical horizon at their shared
calendar preRun, replays the actual retained UP diagnostics on the interval,
and adapts that interval to the deterministic two-batch decoder geometry. The
positive-count and initial-bank chronology conditions remain explicit local
inputs. No sender truth, fixed encoded word, receiver acceptance, service
bound, unique solution, or source-decoding claim is made.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCoordinatorUpDecoderReplay
open Bandits.Support.ReferenceUpDecoderBankInvariant
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.AffineBatchDecoder

namespace Bandits.Support.ReferenceCoordinatorUpIntervalWindow

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

/-- A no-call coordinate in the administrative trace. It has no physical
interpretation; actual call coordinates are filled from retained diagnostics. -/
def administrativeNoCallInput : AffineBatchDecoder.RoundInput (AffineBatchDecoder.width p) :=
  { selected := false
    receiverEnabled := false
    sample := (fun _ => 0, 0)
    roundedReward := 0 }

/-- Project one physical record to the focal channel's administrative input.
When another follower was selected the original sample and observation stay
visible, while the focal selected flag is false. -/
def recordFocalInput
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) : AffineBatchDecoder.RoundInput (AffineBatchDecoder.width p) :=
  match record.output.coordinator.up with
  | none => administrativeNoCallInput
  | some diagnostic =>
      let input := ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput diagnostic
      if diagnostic.input.selectedFollower = i then input else { input with selected := false }

/-- The trace is defined by literal calls found at their actual physical
coordinates. Unmatched coordinates are administrative no-ops. -/
def actualUpCallTrace
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1)) : AffineBatchDecoder.Trace p :=
  fun time =>
    match records.find? (fun record => decide (record.input.time = time)) with
    | none => administrativeNoCallInput
    | some record => recordFocalInput record i

/-- The exact interval suffix of the longer actual horizon run. -/
def intervalRecords
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hspan : start + b ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :=
  (ReferenceActivePhysicalHorizon.run initial rows selected rewards start b hspan hmode).records.drop a

/-- The actual `Fin T` round coordinates carried by the interval records. -/
def intervalRounds
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hspan : start + b ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    List (Fin p.T) :=
  (intervalRecords initial rows selected rewards start a b hspan hmode).map
    (fun record => record.input.time)

private theorem foldRounds_records_prefix
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (origin : ℕ)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial origin)
    (entries : List (ReferenceActivePhysicalHorizon.CalendarEntry p origin))
    (acc : ReferenceActivePhysicalHorizon.Run initial) :
    acc.records =
      (entries.foldl
        (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards origin hmode) acc).records.take
          acc.records.length := by
  induction entries generalizing acc with
  | nil => simp
  | cons entry entries ih =>
      simp only [List.foldl_cons]
      let first := ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards
        origin hmode acc entry
      have hfirst : first.records = acc.records ++
          [⟨ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards origin
              hmode acc entry,
            ReferenceActivePhysicalStep.step
              (ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards origin
                hmode acc entry), rfl⟩] := rfl
      have hlen : first.records.length = acc.records.length + 1 := by
        simp [hfirst]
      have htail := ih first
      calc
        acc.records = first.records.take acc.records.length := by
          rw [hfirst, List.take_append_of_le_length (by omega)]
          simp
        _ = (entries.foldl
              (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards origin hmode)
              first).records.take acc.records.length := by
          rw [htail]
          rw [List.take_take, Nat.min_eq_left (by omega)]

private theorem foldCalendar_records_prefix
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (origin intervalStart count : ℕ) (horigin : origin ≤ intervalStart)
    (hspan : intervalStart + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial origin)
    (acc : ReferenceActivePhysicalHorizon.Run initial) :
    acc.records =
      (ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards origin
        intervalStart count horigin hspan hmode acc).records.take acc.records.length := by
  exact foldRounds_records_prefix initial rows selected rewards origin hmode
    (ReferenceActivePhysicalHorizon.calendarEntries origin intervalStart count horigin hspan) acc

private theorem connected_append_split
    {initial final : ReferenceActivePhysicalStep.State p rate}
    (left right : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hchain : ReferenceActivePhysicalHorizon.Connected initial (left ++ right) final) :
    ∃ middle, ReferenceActivePhysicalHorizon.Connected initial left middle ∧
      ReferenceActivePhysicalHorizon.Connected middle right final := by
  induction left generalizing initial with
  | nil =>
      refine ⟨initial, ?_, ?_⟩
      · simp [ReferenceActivePhysicalHorizon.Connected]
      · simpa using hchain
  | cons head tail ih =>
      simp only [List.cons_append, ReferenceActivePhysicalHorizon.Connected] at hchain ⊢
      rcases hchain with ⟨hhead, htail⟩
      obtain ⟨middle, hleft, hright⟩ := ih htail
      exact ⟨middle, ⟨hhead, hleft⟩, hright⟩

private theorem connected_final_unique
    {initial leftFinal rightFinal : ReferenceActivePhysicalStep.State p rate}
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hleft : ReferenceActivePhysicalHorizon.Connected initial records leftFinal)
    (hright : ReferenceActivePhysicalHorizon.Connected initial records rightFinal) :
    leftFinal = rightFinal := by
  induction records generalizing initial leftFinal rightFinal with
  | nil =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hleft hright
      exact hleft.trans hright.symm
  | cons head tail ih =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hleft hright
      exact ih hleft.2 hright.2

private theorem connected_successors_not_dagger
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hordinary : final.coordinator ≠ .dagger) :
    ∀ record, record ∈ records → record.output.next.coordinator ≠ .dagger := by
  induction records generalizing initial final with
  | nil =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hchain
      subst final
      simp
  | cons head tail ih =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hchain
      rcases hchain with ⟨_, htail⟩
      have hhead : head.output.next.coordinator ≠ .dagger := by
        intro hdagger
        exact hordinary
          (ReferenceActivePhysicalHorizon.Connected.coordinator_dagger htail hdagger).1
      intro record hrecord
      rcases List.mem_cons.mp hrecord with rfl | htailmem
      · exact hhead
      · exact ih htail hordinary record htailmem

/-- The longer run's first `a` records are exactly the actual shorter run;
the drop is the physical suffix, and its state chain starts at the computed
preRun endpoint. Endpoint ordinaryness propagates to the preRun and records. -/
theorem run_interval_cut
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hab : a ≤ b) (hspan : start + b ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start b
      hspan hmode).finalState.coordinator ≠ .dagger) :
    let preRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
      (by omega) hmode
    let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start b
      hspan hmode
    preRun.records = full.records.take a ∧
      full.records = preRun.records ++ full.records.drop a ∧
      ReferenceActivePhysicalHorizon.Connected preRun.finalState (full.records.drop a)
        full.finalState ∧
      ReferenceUpDecoderBankInvariant.upBankInvariant preRun.finalState ∧
      preRun.finalState.coordinator ≠ .dagger ∧
      (∀ record, record ∈ full.records →
        ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state) ∧
      (∀ record, record ∈ full.records → record.output.next.coordinator ≠ .dagger) := by
  let preRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
    (by omega) hmode
  let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start b hspan hmode
  have happend := ReferenceActivePhysicalHorizon.run_append initial rows selected rewards
    start a (b - a) (by omega) hmode
  have hfullAppend : full = ReferenceActivePhysicalHorizon.foldCalendar initial rows selected
      rewards start (start + a) (b - a) (by omega) (by omega) hmode preRun := by
    simpa [full, preRun, Nat.add_sub_of_le hab] using happend
  have hprefixRecords : preRun.records = full.records.take a := by
    calc
      preRun.records =
          (ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards start
            (start + a) (b - a) (by omega) (by omega) hmode preRun).records.take
              preRun.records.length :=
        foldCalendar_records_prefix initial rows selected rewards start (start + a) (b - a)
          (by omega) (by omega) hmode preRun
      _ = full.records.take a := by
        rw [← hfullAppend]
        have hlen := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
          rewards start a (by omega) hmode
        rw [hlen]
  have hdecomp : full.records = preRun.records ++ full.records.drop a := by
    calc
      full.records = full.records.take a ++ full.records.drop a :=
        (List.take_append_drop a full.records).symm
      _ = preRun.records ++ full.records.drop a := by rw [← hprefixRecords]
  have hfullChain : ReferenceActivePhysicalHorizon.Connected initial
      (preRun.records ++ full.records.drop a) full.finalState := by
    rw [← hdecomp]
    exact full.connected
  obtain ⟨middle, hprefixChain, hsuffixChain⟩ := connected_append_split
    preRun.records (full.records.drop a) hfullChain
  have hmiddle : middle = preRun.finalState :=
    connected_final_unique preRun.records hprefixChain preRun.connected
  subst middle
  have hinvariantPrefix :
      ReferenceUpDecoderBankInvariant.upBankInvariant preRun.finalState := by
    exact ReferenceUpDecoderBankInvariant.run_prefix_upBankInvariant initial rows selected
      rewards start b hspan hmode hinitial a (by omega)
  have hinvariantRecords : ∀ record, record ∈ full.records →
      ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state := by
    intro record hrecord
    exact ReferenceUpDecoderBankInvariant.run_record_input_upBankInvariant initial rows selected
      rewards start b hspan hmode hinitial record hrecord
  have hprefixOrdinary : preRun.finalState.coordinator ≠ .dagger := by
    intro hdagger
    exact hordinary
      (ReferenceActivePhysicalHorizon.Connected.coordinator_dagger hsuffixChain hdagger).1
  have hsuccessorsOrdinary := connected_successors_not_dagger full.connected hordinary
  refine ⟨hprefixRecords, hdecomp, hsuffixChain, hinvariantPrefix, hprefixOrdinary,
    hinvariantRecords, ?_⟩
  intro record hrecord
  exact hsuccessorsOrdinary record hrecord

/-- Actual interval replay preserves the full UP bank, including pending and
completed entries, and appends exactly the interval's retained positive
entries to each channel's collected history. -/
theorem run_interval_upDecoderBank_replay
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hab : a ≤ b) (hspan : start + b ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start b
      hspan hmode).finalState.coordinator ≠ .dagger)
    (i : Fin (p.m - 1)) :
    let preRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
      (by omega) hmode
    let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start b
      hspan hmode
    let interval := full.records.drop a
    full.finalState.upDecoderBank = ReferenceCoordinatorUpDecoderReplay.replay
      preRun.finalState.upDecoderBank
        (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics interval) ∧
      AffineBatchDecoder.collected (full.finalState.upDecoderBank i) =
        AffineBatchDecoder.collected (preRun.finalState.upDecoderBank i) ++
          ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries interval i := by
  let preRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
    (by omega) hmode
  let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start b hspan hmode
  let interval := full.records.drop a
  have hcut := run_interval_cut initial rows selected rewards start a b hab hspan hmode
    hinitial hordinary
  have hprefixOrdinary : preRun.finalState.coordinator ≠ .dagger := by
    exact hcut.2.2.2.2.1
  have hprefixReplay := ReferenceCoordinatorUpDecoderReplay.run_upDecoderBank_replay
    initial rows selected rewards start a (by omega) hmode hinitial hprefixOrdinary
  have hfullReplay := ReferenceCoordinatorUpDecoderReplay.run_upDecoderBank_replay
    initial rows selected rewards start b hspan hmode hinitial hordinary
  have hfullCollected := ReferenceCoordinatorUpDecoderReplay.run_collected_upPositiveEntries
    initial rows selected rewards start b hspan hmode hinitial hordinary i
  have hprefixCollected := ReferenceCoordinatorUpDecoderReplay.run_collected_upPositiveEntries
    initial rows selected rewards start a (by omega) hmode hinitial hprefixOrdinary i
  have hrecords : full.records = preRun.records ++ interval := by
    exact hcut.2.1
  have hdiagnostics :
      ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics full.records =
        ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics preRun.records ++
          ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics interval := by
    simp [ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics, hrecords]
  have hreplaySplit :
      ReferenceCoordinatorUpDecoderReplay.replay initial.upDecoderBank
        (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics full.records) =
      ReferenceCoordinatorUpDecoderReplay.replay
        (ReferenceCoordinatorUpDecoderReplay.replay initial.upDecoderBank
          (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics preRun.records))
        (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics interval) := by
    rw [hdiagnostics]
    simp [ReferenceCoordinatorUpDecoderReplay.replay, List.foldl_append]
  have hpositiveSplit :
      ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries full.records i =
        ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries preRun.records i ++
          ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries interval i := by
    simp [ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries, hrecords,
      List.flatMap_append]
  refine ⟨?_, ?_⟩
  · calc
      full.finalState.upDecoderBank =
          ReferenceCoordinatorUpDecoderReplay.replay initial.upDecoderBank
            (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics full.records) := hfullReplay
      _ = ReferenceCoordinatorUpDecoderReplay.replay
            (ReferenceCoordinatorUpDecoderReplay.replay initial.upDecoderBank
              (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics preRun.records))
            (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics interval) := hreplaySplit
      _ = ReferenceCoordinatorUpDecoderReplay.replay preRun.finalState.upDecoderBank
            (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics interval) := by
          rw [← hprefixReplay]
  · calc
      AffineBatchDecoder.collected (full.finalState.upDecoderBank i) =
          AffineBatchDecoder.collected (initial.upDecoderBank i) ++
            ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries full.records i :=
        hfullCollected
      _ = (AffineBatchDecoder.collected (initial.upDecoderBank i) ++
            ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries preRun.records i) ++
            ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries interval i := by
        rw [hpositiveSplit]
        simp [List.append_assoc]
      _ = AffineBatchDecoder.collected (preRun.finalState.upDecoderBank i) ++
            ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries interval i := by
        rw [← hprefixCollected]

/-- The dropped records occupy the exact contiguous calendar `[start+a,start+b)`. -/
theorem run_interval_calendar
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hab : a ≤ b) (hspan : start + b ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start b
      hspan hmode).finalState.coordinator ≠ .dagger) :
    (intervalRecords initial rows selected rewards start a b hspan hmode).map
        (fun record => record.input.time.val) =
      ReferenceActivePhysicalHorizon.calendar (start + a) (b - a) := by
  let preRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
    (by omega) hmode
  let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start b hspan hmode
  let interval := full.records.drop a
  have hcut := run_interval_cut initial rows selected rewards start a b hab hspan hmode
    hinitial hordinary
  have hfullValues := ReferenceActivePhysicalHorizon.run_time_values initial rows selected
    rewards start b hspan hmode
  have hprefixValues := ReferenceActivePhysicalHorizon.run_time_values initial rows selected
    rewards start a (by omega) hmode
  have hdecomp : full.records = preRun.records ++ interval := hcut.2.1
  have hmap : ReferenceActivePhysicalHorizon.calendar start b =
      ReferenceActivePhysicalHorizon.calendar start a ++
        interval.map (fun record => record.input.time.val) := by
    calc
      _ = full.records.map (fun record => record.input.time.val) := hfullValues.symm
      _ = (preRun.records ++ interval).map (fun record => record.input.time.val) := by
        rw [hdecomp]
      _ = preRun.records.map (fun record => record.input.time.val) ++
          interval.map (fun record => record.input.time.val) := by
        simp only [List.map_append]
      _ = _ := by rw [hprefixValues]
  have hcalendarSplit : ReferenceActivePhysicalHorizon.calendar start b =
      ReferenceActivePhysicalHorizon.calendar start a ++
        ReferenceActivePhysicalHorizon.calendar (start + a) (b - a) := by
    rw [← Nat.add_sub_of_le hab]
    simp [ReferenceActivePhysicalHorizon.calendar]
  have htail := (List.append_right_injective
    (ReferenceActivePhysicalHorizon.calendar start a)) (hcalendarSplit.symm.trans hmap)
  simpa [preRun, full, interval, intervalRecords] using htail.symm

/-- Actual interval round coordinates are increasing, including the empty
interval case. -/
theorem run_interval_rounds_chronological
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hab : a ≤ b) (hspan : start + b ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start b
      hspan hmode).finalState.coordinator ≠ .dagger) :
    (intervalRounds initial rows selected rewards start a b hspan hmode).Pairwise
      (fun earlier later => earlier.val < later.val) := by
  have hcalendar : (ReferenceActivePhysicalHorizon.calendar (start + a) (b - a)).Pairwise
      (fun earlier later => earlier < later) := by
    simpa [ReferenceActivePhysicalHorizon.calendar] using
      (List.pairwise_lt_range' (s := start + a) (n := b - a) (step := 1)
        (by decide : 0 < 1))
  have hvalues := run_interval_calendar initial rows selected rewards start a b hab hspan
    hmode hinitial hordinary
  have hnat : ((intervalRecords initial rows selected rewards start a b hspan hmode).map
      (fun record => record.input.time.val)).Pairwise (fun earlier later => earlier < later) := by
    rw [hvalues]
    exact hcalendar
  unfold intervalRounds
  apply List.pairwise_map.mp
  simpa [Function.comp_def] using hnat

private theorem interval_records_chronological
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hab : a ≤ b) (hspan : start + b ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start b
      hspan hmode).finalState.coordinator ≠ .dagger) :
    (intervalRecords initial rows selected rewards start a b hspan hmode).Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val) := by
  have hrounds := run_interval_rounds_chronological initial rows selected rewards start a b hab
    hspan hmode hinitial hordinary
  have htimePair :
      ((intervalRecords initial rows selected rewards start a b hspan hmode).map
        (fun record => record.input.time.val)).Pairwise (fun earlier later => earlier < later) := by
    rw [run_interval_calendar initial rows selected rewards start a b hab hspan hmode hinitial
      hordinary]
    simpa [ReferenceActivePhysicalHorizon.calendar] using
      (List.pairwise_lt_range' (s := start + a) (n := b - a) (step := 1)
        (by decide : 0 < 1))
  exact List.pairwise_map.mp htimePair

/-- Every actual dropped record has its literal timestamp in the half-open
interval. This is derived from the horizon's exact calendar, not from a
diagnostic projection. -/
theorem run_interval_record_time_bounds
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hab : a ≤ b) (hspan : start + b ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start b
      hspan hmode).finalState.coordinator ≠ .dagger)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : record ∈ intervalRecords initial rows selected rewards start a b hspan hmode) :
    start + a ≤ record.input.time.val ∧ record.input.time.val < start + b := by
  have hmem : record.input.time.val ∈
      (intervalRecords initial rows selected rewards start a b hspan hmode).map
        (fun current => current.input.time.val) :=
    List.mem_map.mpr ⟨record, hrecord, rfl⟩
  rw [run_interval_calendar initial rows selected rewards start a b hab hspan hmode hinitial
    hordinary] at hmem
  have hmem' : record.input.time.val ∈ List.range' (start + a) (b - a) 1 := by
    simpa [ReferenceActivePhysicalHorizon.calendar] using hmem
  obtain ⟨offset, hoffset, heq⟩ := List.mem_range'.mp hmem'
  constructor <;> omega

/-- The actual typed round list inherits the same half-open bounds as the
records from which it was projected. -/
theorem run_interval_round_time_bounds
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hab : a ≤ b) (hspan : start + b ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start b
      hspan hmode).finalState.coordinator ≠ .dagger)
    (time : Fin p.T)
    (htime : time ∈ intervalRounds initial rows selected rewards start a b hspan hmode) :
    start + a ≤ time.val ∧ time.val < start + b := by
  change time ∈ (intervalRecords initial rows selected rewards start a b hspan hmode).map
    (fun record => record.input.time) at htime
  obtain ⟨record, hrecord, hrecordTime⟩ := List.mem_map.mp htime
  have hbounds := run_interval_record_time_bounds initial rows selected rewards start a b hab
    hspan hmode hinitial hordinary record hrecord
  have hval := congrArg Fin.val hrecordTime
  omega

/-- With an empty initial collected list, every pre-interval pending entry
comes from an actual positive call before `start+a`; the UP bank invariant
alone does not supply this chronological seed clause. -/
theorem run_interval_pending_older_of_empty_seed
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hab : a ≤ b) (hspan : start + b ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start b
      hspan hmode).finalState.coordinator ≠ .dagger)
    (i : Fin (p.m - 1))
    (hseed : AffineBatchDecoder.collected (initial.upDecoderBank i) = []) :
    let preRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
      (by omega) hmode
    ∀ (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)),
      entry ∈ (preRun.finalState.upDecoderBank i).pending →
      ∀ time ∈ intervalRounds initial rows selected rewards start a b hspan hmode,
        entry.time.val < time.val := by
  dsimp only
  let preRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
    (by omega) hmode
  have hcut := run_interval_cut initial rows selected rewards start a b hab hspan hmode
    hinitial hordinary
  have hpreOrdinary : preRun.finalState.coordinator ≠ .dagger := hcut.2.2.2.2.1
  have hcollected := ReferenceCoordinatorUpDecoderReplay.run_collected_upPositiveEntries
    initial rows selected rewards start a (by omega) hmode hinitial hpreOrdinary i
  have hchronology := ReferenceCoordinatorUpDecoderReplay.run_upPositiveEntries_chronology
    initial rows selected rewards start a (by omega) hmode hinitial hpreOrdinary i
  have hpositiveTimes := hchronology.2
  intro entry hentry time htime
  have hcol : entry ∈ AffineBatchDecoder.collected (preRun.finalState.upDecoderBank i) := by
    change entry ∈
      (preRun.finalState.upDecoderBank i).completed.flatten ++
        (preRun.finalState.upDecoderBank i).pending
    exact List.mem_append_right
      (preRun.finalState.upDecoderBank i).completed.flatten hentry
  have hcollected' :
      AffineBatchDecoder.collected (preRun.finalState.upDecoderBank i) =
        AffineBatchDecoder.collected (initial.upDecoderBank i) ++
          ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries preRun.records i := by
    simpa [preRun] using hcollected
  rw [hseed] at hcollected'
  simp only [List.nil_append] at hcollected'
  rw [hcollected'] at hcol
  have hbefore := (hpositiveTimes entry hcol).2
  have hinterval := run_interval_round_time_bounds initial rows selected rewards start a b hab
    hspan hmode hinitial hordinary time htime
  omega

/-- Strictly chronological records make the record at a represented time the
unique result of the trace's search. -/
private theorem find_record_at_time
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hchronological : records.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : record ∈ records) :
    records.find? (fun candidate => decide (candidate.input.time = record.input.time)) =
      some record := by
  induction records with
  | nil => simp at hrecord
  | cons head tail ih =>
      rcases List.mem_cons.mp hrecord with hhead | htail
      · subst record
        simp
      · have hpair := List.pairwise_cons.mp hchronological
        have hlt : head.input.time.val < record.input.time.val := hpair.1 record htail
        have hneq : head.input.time ≠ record.input.time := by
          intro heq
          have hval := congrArg Fin.val heq
          omega
        have hnot : decide (head.input.time = record.input.time) = false := by
          simp [hneq]
        simp [hnot, ih hpair.2 htail]

/-- At any record coordinate the trace returns exactly that record's focal
projection, including its saved sample and rounded coordinator observation. -/
theorem actualUpCallTrace_at_record
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1))
    (hchronological : records.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : record ∈ records) :
    actualUpCallTrace records i record.input.time = recordFocalInput record i := by
  simp [actualUpCallTrace, find_record_at_time records hchronological record hrecord]

/-- The retained physical input fields are the exact checked receiver input
and the original full-table UP sample. Its focal eligibility is precisely the
source reception gate together with the positive rounded own observation. -/
theorem record_retained_up_actual_call
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : record.output.coordinator.up = some diagnostic) :
    ∃ ledger,
      ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some ledger ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger) = true ∧
      diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger ∧
      diagnostic.decoderAfter = (CoordinatorUpReception.decoderTransition
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger)).1 ∧
      diagnostic.input.time = record.input.time ∧
      diagnostic.input.selectedFollower =
        CoordinatorUpMeasurability.selectedFollowerIndex
          ((record.input.rows record.input.selected).2 record.input.time) ∧
      diagnostic.input.affineSample =
        ((record.input.rows record.input.selected).2 record.input.time).2
          (1, CoordinatorUpMeasurability.selectedChannelFollower
            ((record.input.rows record.input.selected).2 record.input.time)) ∧
      diagnostic.input.ownObservation =
        (ReferenceActivePhysicalStep.prepare record.input).feedback.feedback
          (ActiveRoundActions.coordinator p.two_le_m) ∧
      (ReferenceActivePhysicalStep.prepare record.input).feedback.feedback
          (ActiveRoundActions.coordinator p.two_le_m) =
        (if FiniteBanditModel.collisionFreeFor
            (ReferenceActivePhysicalStep.prepare record.input).arms.actions
              (ActiveRoundActions.coordinator p.two_le_m) then
          record.input.rewards record.input.time
            ((ReferenceActivePhysicalStep.prepare record.input).arms.actions
              (ActiveRoundActions.coordinator p.two_le_m))
        else 0) ∧
      (ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput diagnostic).receiverEnabled = true ∧
      (ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput diagnostic).sample =
        diagnostic.input.affineSample ∧
      (ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput diagnostic).roundedReward =
        CoordinatorUpReception.roundedObservationValue p diagnostic.input.ownObservation ∧
      (AffineBatchDecoder.eligible
        (ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput diagnostic) ↔
        CoordinatorUpReception.receptionGate diagnostic.input ∧
          0 < CoordinatorUpReception.roundedObservationValue p
            diagnostic.input.ownObservation) ∧
      record.output.ownEntries (ActiveRoundActions.coordinator p.two_le_m) =
        (record.output.preparation.arms.actions
          (ActiveRoundActions.coordinator p.two_le_m),
          ActualInitializationPhysicalStep.observationOfGrid p
            (record.output.preparation.feedback.feedback
              (ActiveRoundActions.coordinator p.two_le_m))) := by
  classical
  obtain ⟨ledger, hsite, hcheck, hinput, hafter⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input record diagnostic hdiagnostic
  obtain ⟨ledger', hsite', hledger, hbank, htime, hobs, hfollower, hsample, hslot,
      henabled, hselected, hroundSample, hroundReward, hfeedback⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields
      record diagnostic hdiagnostic
  have hledgerEq : ledger' = ledger := by
    have hsome : some ledger' = some ledger := hsite'.symm.trans hsite
    exact Option.some.inj hsome
  subst ledger'
  have hown := ReferenceCoordinatorUpPhysicalCall.record_retained_up_own_entry record
  refine ⟨ledger, hsite, hcheck, hinput, hafter, htime, hfollower, hsample, hobs,
    hfeedback, ?_, ?_, ?_, ?_, hown⟩
  · exact henabled
  · exact hroundSample
  · simpa [ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput, hobs] using
      hroundReward
  · exact ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput_eligible_iff diagnostic

private theorem record_positive_projection
    (trace : AffineBatchDecoder.Trace p)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (_hrecord : record ∈ records)
    (htrace : trace record.input.time = recordFocalInput record i) :
    ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries record i =
      AffineBatchDecoder.positiveAt p trace record.input.time := by
  cases hdiagnostic : record.output.coordinator.up with
  | none =>
      have hnot : ¬ AffineBatchDecoder.eligible (trace record.input.time) := by
        rw [htrace]
        simp [recordFocalInput, hdiagnostic, administrativeNoCallInput,
          AffineBatchDecoder.eligible]
      simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
        hdiagnostic, AffineBatchDecoder.positiveAt, hnot]
  | some diagnostic =>
      obtain ⟨_, _, _, _, _, htime, _, _, _, _, _, _, _, _, _⟩ :=
        record_retained_up_actual_call record diagnostic hdiagnostic
      by_cases hselected : diagnostic.input.selectedFollower = i
      · have hcurrent : trace diagnostic.input.time =
            CoordinatorUpReception.roundInput diagnostic.input := by
          rw [htime]
          simpa [recordFocalInput, hdiagnostic, hselected,
            ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput] using htrace
        have htraceAt : trace record.input.time =
            CoordinatorUpReception.roundInput diagnostic.input := by
          rw [← htime]
          exact hcurrent
        simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
          ReferenceCoordinatorUpDecoderReplay.retainedUpFollower,
          ReferenceCoordinatorUpDecoderReplay.retainedUpTime,
          ReferenceCoordinatorUpDecoderReplay.constantInputTrace,
          hdiagnostic, hselected, htime, AffineBatchDecoder.positiveAt,
          AffineBatchDecoder.entry, htraceAt]
      · have hnot : ¬ AffineBatchDecoder.eligible (trace record.input.time) := by
          rw [htrace]
          simp [recordFocalInput, hdiagnostic, hselected,
            ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput,
            AffineBatchDecoder.eligible]
        simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
          ReferenceCoordinatorUpDecoderReplay.retainedUpFollower,
          hdiagnostic, hselected, AffineBatchDecoder.positiveAt, hnot]

private theorem trace_positives_eq_retained
    (trace : AffineBatchDecoder.Trace p)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1))
    (htrace : ∀ record, record ∈ records →
      trace record.input.time = recordFocalInput record i) :
    AffineBatchDecoder.positives p trace
      (records.map (fun record => record.input.time)) =
        ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries records i := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      change AffineBatchDecoder.positives p trace
        (record.input.time :: rest.map (fun record => record.input.time)) = _
      have hhead := record_positive_projection trace (record :: rest) i record (by simp)
        (htrace record (by simp))
      have htail : ∀ current, current ∈ rest →
          trace current.input.time = recordFocalInput current i := by
        intro current hcurrent
        exact htrace current (by simp [hcurrent])
      rw [AffineBatchDecoder.positives_cons]
      simp [ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries,
        hhead, ih htail]

/-- Filtering the actual interval trace gives exactly the saved positive
entries, with their original finite timestamps and affine samples. -/
theorem actual_trace_positives_eq_retained
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1))
    (hchronological : records.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val)) :
    AffineBatchDecoder.positives p (actualUpCallTrace records i)
      (records.map (fun record => record.input.time)) =
        ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries records i := by
  apply trace_positives_eq_retained (actualUpCallTrace records i) records i
  intro record hrecord
  exact actualUpCallTrace_at_record records i hchronological record hrecord

/-- The focal actual trace over the computed physical suffix has exactly the
retained positive entries, including the saved own grid sample and finite
call timestamp. -/
theorem run_interval_actual_trace_positives_eq_retained
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hab : a ≤ b) (hspan : start + b ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start b
      hspan hmode).finalState.coordinator ≠ .dagger)
    (i : Fin (p.m - 1)) :
    AffineBatchDecoder.positives p
        (actualUpCallTrace
          (intervalRecords initial rows selected rewards start a b hspan hmode) i)
        (intervalRounds initial rows selected rewards start a b hspan hmode) =
      ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
        (intervalRecords initial rows selected rewards start a b hspan hmode) i := by
  exact actual_trace_positives_eq_retained _ i
    (interval_records_chronological initial rows selected rewards start a b hab hspan hmode
      hinitial hordinary)

private theorem run_trace_eq_replay_channel
    (trace : AffineBatchDecoder.Trace p)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1))
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (htrace : ∀ record, record ∈ records →
      trace record.input.time = recordFocalInput record i)
    (hwell : CoordinatorUpReception.decoderStateWellFormed p (bank i)) :
    AffineBatchDecoder.run p trace (records.map (fun record => record.input.time)) (bank i) =
      (ReferenceCoordinatorUpDecoderReplay.replay bank
        (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics records)) i := by
  induction records generalizing bank with
  | nil => rfl
  | cons record rest ih =>
      have hrecordTrace := htrace record (by simp)
      have hstep : AffineBatchDecoder.step p trace (bank i) record.input.time =
          (ReferenceCoordinatorUpDecoderReplay.replayRecord bank record) i := by
        cases hdiagnostic : record.output.coordinator.up with
        | none =>
            have hnot : ¬ AffineBatchDecoder.eligible (trace record.input.time) := by
              rw [hrecordTrace]
              simp [recordFocalInput, hdiagnostic, administrativeNoCallInput,
                AffineBatchDecoder.eligible]
            have hineligible := AffineBatchDecoder.step_ineligible p trace (bank i)
              record.input.time hwell.1 hnot
            simpa [ReferenceCoordinatorUpDecoderReplay.replayRecord, hdiagnostic] using
              hineligible
        | some diagnostic =>
            by_cases hselected : diagnostic.input.selectedFollower = i
            · have hcurrent : trace record.input.time =
                  CoordinatorUpReception.roundInput diagnostic.input := by
                simpa [recordFocalInput, hdiagnostic, hselected,
                  ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput] using hrecordTrace
              obtain ⟨_, _, _, _, _, htime, _, _, _, _, _, _, _, _, _⟩ :=
                record_retained_up_actual_call record diagnostic hdiagnostic
              have hdecode := ReferenceCoordinatorUpDecoderReplay.decodeStep_constantInput_of_current_eq
                trace (bank i) record.input.time diagnostic.input hcurrent
              calc
                AffineBatchDecoder.step p trace (bank i) record.input.time =
                    (AffineBatchDecoder.decodeStep p trace (bank i) record.input.time).1 := rfl
                _ = (AffineBatchDecoder.decodeStep p
                      (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
                      (bank i) record.input.time).1 := by rw [hdecode]
                _ = (ReferenceCoordinatorUpDecoderReplay.replayRecord bank record) i := by
                  simp [ReferenceCoordinatorUpDecoderReplay.replayRecord,
                    ReferenceCoordinatorUpDecoderReplay.replayOne, hdiagnostic, hselected,
                    ReferenceCoordinatorUpDecoderReplay.retainedUpFollower,
                    ReferenceCoordinatorUpDecoderReplay.retainedUpTime, htime]
            · have hnot : ¬ AffineBatchDecoder.eligible (trace record.input.time) := by
                rw [hrecordTrace]
                simp [recordFocalInput, hdiagnostic, hselected,
                  ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput,
                  AffineBatchDecoder.eligible]
              have hineligible := AffineBatchDecoder.step_ineligible p trace (bank i)
                record.input.time hwell.1 hnot
              have htime' : diagnostic.input.selectedFollower ≠ i := hselected
              simpa [ReferenceCoordinatorUpDecoderReplay.replayRecord,
                ReferenceCoordinatorUpDecoderReplay.replayOne, hdiagnostic,
                ReferenceCoordinatorUpDecoderReplay.retainedUpFollower,
                htime'.symm] using hineligible
      have hstepSpec := AffineBatchDecoder.step_spec p trace (bank i) record.input.time
        hwell.1 hwell.2
      have hnextWell : CoordinatorUpReception.decoderStateWellFormed p
          ((ReferenceCoordinatorUpDecoderReplay.replayRecord bank record) i) := by
        rw [← hstep]
        exact ⟨hstepSpec.1, hstepSpec.2.1⟩
      have htraceTail : ∀ current, current ∈ rest →
          trace current.input.time = recordFocalInput current i := by
        intro current hcurrent
        exact htrace current (by simp [hcurrent])
      have htail := ih (ReferenceCoordinatorUpDecoderReplay.replayRecord bank record)
        htraceTail hnextWell
      have hfold :
          ReferenceCoordinatorUpDecoderReplay.replay bank
            (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics (record :: rest)) =
          ReferenceCoordinatorUpDecoderReplay.replay
            (ReferenceCoordinatorUpDecoderReplay.replayRecord bank record)
            (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics rest) := by
        calc
          _ = (record :: rest).foldl ReferenceCoordinatorUpDecoderReplay.replayRecord bank :=
            ReferenceCoordinatorUpDecoderReplay.replay_records_eq_fold bank (record :: rest)
          _ = rest.foldl ReferenceCoordinatorUpDecoderReplay.replayRecord
                (ReferenceCoordinatorUpDecoderReplay.replayRecord bank record) := rfl
          _ = _ := (ReferenceCoordinatorUpDecoderReplay.replay_records_eq_fold
            (ReferenceCoordinatorUpDecoderReplay.replayRecord bank record) rest).symm
      calc
        AffineBatchDecoder.run p trace
            ((record :: rest).map (fun record => record.input.time)) (bank i) =
            AffineBatchDecoder.run p trace (rest.map (fun record => record.input.time))
              ((ReferenceCoordinatorUpDecoderReplay.replayRecord bank record) i) := by
                change AffineBatchDecoder.run p trace
                  (record.input.time :: rest.map (fun record => record.input.time)) (bank i) = _
                calc
                  _ = AffineBatchDecoder.run p trace
                      (rest.map (fun record => record.input.time))
                      (AffineBatchDecoder.step p trace (bank i) record.input.time) := rfl
                  _ = _ := by rw [hstep]
        _ = (ReferenceCoordinatorUpDecoderReplay.replay
              (ReferenceCoordinatorUpDecoderReplay.replayRecord bank record)
              (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics rest)) i := htail
        _ = (ReferenceCoordinatorUpDecoderReplay.replay bank
              (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics (record :: rest))) i := by
                rw [hfold]

/-- The reusable decoder-fold congruence for the actual on-call trace. Its
only trace values used by the fold are the projections of actual records. -/
theorem actualUpCallTrace_run_eq_replay
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1))
    (hchronological : records.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val))
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (hwell : CoordinatorUpReception.decoderStateWellFormed p (bank i)) :
    AffineBatchDecoder.run p (actualUpCallTrace records i)
        (records.map (fun record => record.input.time)) (bank i) =
      (ReferenceCoordinatorUpDecoderReplay.replay bank
        (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics records)) i := by
  apply run_trace_eq_replay_channel (actualUpCallTrace records i) records i bank _ hwell
  intro record hrecord
  exact actualUpCallTrace_at_record records i hchronological record hrecord

/-- The focal actual decoder fold on the interval is the channel stored by
the longer physical run. This combines actual-call congruence with the full
bank replay; no caller-supplied trace or intermediate state link is used. -/
theorem run_interval_focal_decoder_fold
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hab : a ≤ b) (hspan : start + b ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start b
      hspan hmode).finalState.coordinator ≠ .dagger)
    (i : Fin (p.m - 1)) :
    let preRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
      (by omega) hmode
    let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start b
      hspan hmode
    let interval := full.records.drop a
    AffineBatchDecoder.run p (actualUpCallTrace interval i)
        (interval.map (fun record => record.input.time)) (preRun.finalState.upDecoderBank i) =
      full.finalState.upDecoderBank i := by
  let preRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
    (by omega) hmode
  let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start b hspan hmode
  let interval := full.records.drop a
  have hcut := run_interval_cut initial rows selected rewards start a b hab hspan hmode
    hinitial hordinary
  have hwellBank : CoordinatorUpReception.decoderBankWellFormed p preRun.finalState.upDecoderBank :=
    hcut.2.2.2.1.1
  have hrecordsChronological := interval_records_chronological initial rows selected rewards
    start a b hab hspan hmode hinitial hordinary
  have hfold := actualUpCallTrace_run_eq_replay interval i hrecordsChronological
    preRun.finalState.upDecoderBank (hwellBank i)
  have hbank := run_interval_upDecoderBank_replay initial rows selected rewards start a b hab
    hspan hmode hinitial hordinary i
  change AffineBatchDecoder.run p (actualUpCallTrace interval i)
      (interval.map (fun record => record.input.time)) (preRun.finalState.upDecoderBank i) =
    full.finalState.upDecoderBank i
  calc
    _ = (ReferenceCoordinatorUpDecoderReplay.replay preRun.finalState.upDecoderBank
        (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics interval)) i := hfold
    _ = full.finalState.upDecoderBank i := by
      exact (congrArg (fun bank => bank i) hbank.1).symm

private theorem mem_of_mem_drop_list {α : Type} (values : List α) (count : ℕ)
    {value : α} (hvalue : value ∈ values.drop count) : value ∈ values := by
  induction count generalizing values with
  | zero => simpa using hvalue
  | succ count ih =>
      cases values with
      | nil => simp at hvalue
      | cons head tail =>
          exact List.mem_cons_of_mem head (ih tail (by simpa using hvalue))

private theorem decoder_run_append (trace : AffineBatchDecoder.Trace p)
    (left right : List (Fin p.T))
    (state : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) :
    AffineBatchDecoder.run p trace (left ++ right) state =
      AffineBatchDecoder.run p trace right (AffineBatchDecoder.run p trace left state) := by
  induction left generalizing state with
  | nil => rfl
  | cons time left ih =>
      calc
        AffineBatchDecoder.run p trace ((time :: left) ++ right) state =
            AffineBatchDecoder.run p trace (left ++ right)
              (AffineBatchDecoder.step p trace state time) := rfl
        _ = AffineBatchDecoder.run p trace right
              (AffineBatchDecoder.run p trace left (AffineBatchDecoder.step p trace state time)) :=
            ih _
        _ = AffineBatchDecoder.run p trace right
              (AffineBatchDecoder.run p trace (time :: left) state) := by
            rw [AffineBatchDecoder.run]

private theorem decoder_run_ineligible_suffix (trace : AffineBatchDecoder.Trace p)
    (suffix : List (Fin p.T))
    (state : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hsmall : state.pending.length < AffineBatchDecoder.quota p)
    (hineligible : ∀ time, time ∈ suffix → ¬ AffineBatchDecoder.eligible (trace time)) :
    AffineBatchDecoder.run p trace suffix state = state := by
  induction suffix generalizing state with
  | nil => rfl
  | cons time suffix ih =>
      have hstep := AffineBatchDecoder.step_ineligible p trace state time hsmall
        (hineligible time (by simp))
      calc
        AffineBatchDecoder.run p trace (time :: suffix) state =
            AffineBatchDecoder.run p trace suffix (AffineBatchDecoder.step p trace state time) := rfl
        _ = AffineBatchDecoder.run p trace suffix state := by rw [hstep]
        _ = state := ih state hsmall (by
          intro current hcurrent
          exact hineligible current (by simp [hcurrent]))

/-- The actual interval's conditional two-batch producer. The only count
condition is the literal number of eligible positive inputs; the old pending
timestamps are derived separately from the genuinely empty initial collected
history. The final positive call is located in the physical round list, and
its raw decoder output is exactly `batchOutput` of the actual second window. -/
theorem run_interval_two_batch_window
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hab : a ≤ b) (hspan : start + b ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start b
      hspan hmode).finalState.coordinator ≠ .dagger)
    (i : Fin (p.m - 1))
    (hseed : AffineBatchDecoder.collected (initial.upDecoderBank i) = [])
    (hpositiveCount :
      (AffineBatchDecoder.positives p
        (actualUpCallTrace
          (intervalRecords initial rows selected rewards start a b hspan hmode) i)
        (intervalRounds initial rows selected rewards start a b hspan hmode)).length =
      AffineBatchDecoder.quota p -
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
          (by omega) hmode).finalState.upDecoderBank i).pending.length +
          AffineBatchDecoder.quota p) :
    let preRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
      (by omega) hmode
    let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start b
      hspan hmode
    let interval := full.records.drop a
    let trace := actualUpCallTrace interval i
    let rounds := intervalRounds initial rows selected rewards start a b hspan hmode
    let positive := AffineBatchDecoder.positives p trace rounds
    let channel := preRun.finalState.upDecoderBank i
    let window := positive.drop
      (AffineBatchDecoder.quota p - channel.pending.length)
    ∃ (first : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
      (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
      (index : Fin rounds.length),
      AffineBatchDecoder.run p trace rounds channel =
        ⟨[], channel.completed ++ [first, window]⟩ ∧
      AffineBatchDecoder.run p trace rounds channel = full.finalState.upDecoderBank i ∧
      first = channel.pending ++ positive.take
        (AffineBatchDecoder.quota p - channel.pending.length) ∧
      first.length = AffineBatchDecoder.quota p ∧
      window.length = AffineBatchDecoder.quota p ∧
      window.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
      (∀ entry, entry ∈ channel.pending → entry ∉ window) ∧
      positive.length ≤ 2 * AffineBatchDecoder.quota p ∧
      (∀ entry, entry ∈ window →
        start + a ≤ entry.time.val ∧ entry.time.val < start + b) ∧
      last ∈ window ∧
      AffineBatchDecoder.decisionTime window = some last.time ∧
      rounds.get index = last.time ∧
      AffineBatchDecoder.eligible (trace last.time) ∧
      last.sample = (trace last.time).sample ∧
      (∀ entry, entry ∈ window → entry.time.val ≤ last.time.val) ∧
      (AffineBatchDecoder.decodeStep p trace
        (AffineBatchDecoder.run p trace (rounds.take index.val) channel) last.time).2 =
          AffineBatchDecoder.batchOutput window := by
  classical
  let preRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
    (by omega) hmode
  let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start b hspan hmode
  let interval := full.records.drop a
  let trace := actualUpCallTrace interval i
  let rounds := intervalRounds initial rows selected rewards start a b hspan hmode
  let positive := AffineBatchDecoder.positives p trace rounds
  let channel := preRun.finalState.upDecoderBank i
  have hcut := run_interval_cut initial rows selected rewards start a b hab hspan hmode
    hinitial hordinary
  have hwellBank : CoordinatorUpReception.decoderBankWellFormed p preRun.finalState.upDecoderBank :=
    hcut.2.2.2.1.1
  have hwell := hwellBank i
  let window := WaitedWordWindow.secondPositiveWindow p trace rounds channel.pending hwell.1
  have hroundsChronological : rounds.Pairwise
      (fun earlier later => earlier.val < later.val) := by
    exact run_interval_rounds_chronological initial rows selected rewards start a b hab hspan
      hmode hinitial hordinary
  have hpendingOlder := run_interval_pending_older_of_empty_seed initial rows selected rewards
    start a b hab hspan hmode hinitial hordinary i hseed
  have hwindowPackage := WaitedWordWindow.run_two_batch_window p trace rounds channel hwell.1
    (by
      change positive.length = AffineBatchDecoder.quota p - channel.pending.length +
        AffineBatchDecoder.quota p
      exact hpositiveCount)
    hroundsChronological hpendingOlder
  obtain ⟨first, hrun, hfirst, hfirstLen, hwindowLen, hwindowChronological,
    hpendingDisjoint, hcountBound⟩ := hwindowPackage
  have hwindowBounds : ∀ entry, entry ∈ window →
      start + a ≤ entry.time.val ∧ entry.time.val < start + b := by
    intro entry hentry
    have hpositive : entry ∈ positive := by
      change entry ∈ positive.drop _ at hentry
      exact mem_of_mem_drop_list positive _ hentry
    obtain ⟨htime, _, _⟩ :=
      (AffineBatchDecoder.mem_positives_iff p trace rounds entry).mp hpositive
    exact run_interval_round_time_bounds initial rows selected rewards start a b hab hspan hmode
      hinitial hordinary entry.time htime
  have hwindowNonempty : window ≠ [] := by
    intro hempty
    have hwindowLength : window.length = AffineBatchDecoder.quota p := by
      simpa [window, WaitedWordWindow.secondPositiveWindow] using hwindowLen
    simp [hempty] at hwindowLength
    have hquotaPositive := AffineBatchDecoder.quota_pos p
    omega
  let last := window.getLast hwindowNonempty
  have hlastWindow : last ∈ window := by
    simp only [last]
    exact List.getLast_mem hwindowNonempty
  have hlastPositive : last ∈ positive := by
    have hmemDrop : last ∈ positive.drop
        (AffineBatchDecoder.quota p - channel.pending.length) := by
      simpa [last, window, WaitedWordWindow.secondPositiveWindow] using hlastWindow
    exact mem_of_mem_drop_list positive _ hmemDrop
  obtain ⟨hlastRound, hlastEligible, hlastSample⟩ :=
    (AffineBatchDecoder.mem_positives_iff p trace rounds last).mp hlastPositive
  have hindexExists : ∃ x ∈ rounds, x = last.time := ⟨last.time, hlastRound, rfl⟩
  obtain ⟨index, hindexRound⟩ := List.exists_mem_iff_get.mp hindexExists
  have hdecision : AffineBatchDecoder.decisionTime window = some last.time := by
    simp only [last, AffineBatchDecoder.decisionTime, List.getLast?_map,
      List.getLast?_eq_some_getLast hwindowNonempty, Option.map_some]
  have hwindowMax : ∀ entry, entry ∈ window → entry.time.val ≤ last.time.val := by
    have hpairLe := hwindowChronological.imp (fun h => Nat.le_of_lt h)
    intro entry hentry
    have hle := hpairLe.rel_getLast hentry
    simpa only [last] using hle
  let earlierRounds := rounds.take index.val
  let suffix := rounds.drop (index.val + 1)
  have htake : rounds.take (index.val + 1) = earlierRounds ++ [rounds.get index] := by
    exact (List.take_append_getElem index.isLt).symm
  have hsplit : rounds = earlierRounds ++ [last.time] ++ suffix := by
    calc
      rounds = rounds.take (index.val + 1) ++ rounds.drop (index.val + 1) :=
        (List.take_append_drop (index.val + 1) rounds).symm
      _ = (earlierRounds ++ [rounds.get index]) ++ suffix := by rw [htake]
      _ = earlierRounds ++ [last.time] ++ suffix := by rw [hindexRound]
  have hpositivePairwise : positive.Pairwise
      (fun earlier later => earlier.time.val < later.time.val) := by
    change (((rounds.filter (fun time => decide (AffineBatchDecoder.eligible (trace time)))).map
      (AffineBatchDecoder.entry p trace)).Pairwise
        (fun earlier later => earlier.time.val < later.time.val))
    apply List.pairwise_map.mpr
    simpa only [AffineBatchDecoder.entry, AffineBatchDecoder.Entry.time] using
      hroundsChronological.filter _
  have hpositiveSplit : positive = positive.take
      (AffineBatchDecoder.quota p - channel.pending.length) ++ window := by
    dsimp [window, WaitedWordWindow.secondPositiveWindow]
    exact (List.take_append_drop _ _).symm
  have hwindowDecomp : window.dropLast ++ [last] = window :=
    List.dropLast_append_getLast hwindowNonempty
  have hpositiveEnds : positive =
      (positive.take (AffineBatchDecoder.quota p - channel.pending.length) ++
        window.dropLast) ++ [last] := by
    calc
      positive = positive.take (AffineBatchDecoder.quota p - channel.pending.length) ++ window :=
        hpositiveSplit
      _ = (positive.take (AffineBatchDecoder.quota p - channel.pending.length) ++
          window.dropLast) ++ [last] := by
        calc
          _ = positive.take (AffineBatchDecoder.quota p - channel.pending.length) ++
              (window.dropLast ++ [last]) :=
            congrArg (fun values =>
              positive.take (AffineBatchDecoder.quota p - channel.pending.length) ++ values)
              hwindowDecomp.symm
          _ = _ := by rw [List.append_assoc]
  have hpositiveNonempty : positive ≠ [] := List.ne_nil_of_mem hlastPositive
  have hlastPositiveEq : positive.getLast hpositiveNonempty = last := by
    have hlastOption : positive.getLast? = some last := by
      rw [hpositiveEnds]
      simp
    have hlastOption' := List.getLast?_eq_some_getLast hpositiveNonempty
    rw [hlastOption'] at hlastOption
    exact Option.some.inj hlastOption
  have hpositiveMax : ∀ entry, entry ∈ positive → entry.time.val ≤ last.time.val := by
    have hpairLe := hpositivePairwise.imp (fun h => Nat.le_of_lt h)
    intro entry hentry
    have hle := hpairLe.rel_getLast hentry
    simpa only [hlastPositiveEq] using hle
  have hnoPositiveSuffix : ∀ time, time ∈ suffix → ¬ AffineBatchDecoder.eligible (trace time) := by
    intro time htime heligible
    obtain ⟨suffixIndex, hsuffixIndex, hsuffixGet⟩ :=
      (List.exists_mem_iff_getElem).mp ⟨time, htime, rfl⟩
    have hglobalBound : index.val + 1 + suffixIndex < rounds.length := by
      have hlength := hsuffixIndex
      simp [suffix, List.length_drop] at hlength
      omega
    have hglobalGet : rounds[index.val + 1 + suffixIndex]'hglobalBound = time := by
      simpa [suffix, List.getElem_drop] using hsuffixGet.symm
    have htimeAfter : last.time.val < time.val := by
      have hlt : index < ⟨index.val + 1 + suffixIndex, hglobalBound⟩ := by
        exact Fin.mk_lt_mk.mpr (by omega)
      have hpair := hroundsChronological.rel_get_of_lt hlt
      have hglobalFin : rounds.get ⟨index.val + 1 + suffixIndex, hglobalBound⟩ = time := by
        simpa only [List.get_eq_getElem] using hglobalGet
      rw [hindexRound, hglobalFin] at hpair
      exact hpair
    have hpositiveAt :
        AffineBatchDecoder.entry p trace time ∈ positive := by
      apply List.mem_map.mpr
      refine ⟨time, ?_, rfl⟩
      exact List.mem_filter.mpr ⟨mem_of_mem_drop_list rounds (index.val + 1) htime,
        decide_eq_true heligible⟩
    have hmax := hpositiveMax _ hpositiveAt
    have hmaxTime : time.val ≤ last.time.val := by
      simpa [AffineBatchDecoder.entry] using hmax
    omega
  have hstateBeforeSmall :
      (AffineBatchDecoder.run p trace earlierRounds channel).pending.length <
        AffineBatchDecoder.quota p := by
    have hspec := AffineBatchDecoder.run_spec p trace earlierRounds channel hwell.1 hwell.2
    exact hspec.1
  have hstepSpec := AffineBatchDecoder.step_spec p trace
    (AffineBatchDecoder.run p trace earlierRounds channel) last.time hstateBeforeSmall
    (AffineBatchDecoder.run_spec p trace earlierRounds channel hwell.1 hwell.2).2.1
  have hsuffixNoop := decoder_run_ineligible_suffix trace suffix
    (AffineBatchDecoder.step p trace (AffineBatchDecoder.run p trace earlierRounds channel) last.time)
    hstepSpec.1 hnoPositiveSuffix
  have hstepFinal :
      AffineBatchDecoder.step p trace (AffineBatchDecoder.run p trace earlierRounds channel) last.time =
        ⟨[], channel.completed ++ [first, window]⟩ := by
    calc
      _ = AffineBatchDecoder.run p trace suffix
          (AffineBatchDecoder.step p trace (AffineBatchDecoder.run p trace earlierRounds channel)
            last.time) := hsuffixNoop.symm
      _ = AffineBatchDecoder.run p trace rounds channel := by
        calc
          _ = AffineBatchDecoder.run p trace ([last.time] ++ suffix)
              (AffineBatchDecoder.run p trace earlierRounds channel) := by
            calc
              _ = AffineBatchDecoder.run p trace suffix
                    (AffineBatchDecoder.run p trace [last.time]
                      (AffineBatchDecoder.run p trace earlierRounds channel)) := rfl
              _ = _ := (decoder_run_append trace [last.time] suffix
                (AffineBatchDecoder.run p trace earlierRounds channel)).symm
          _ = AffineBatchDecoder.run p trace
              (earlierRounds ++ [last.time] ++ suffix) channel :=
            (by simpa [List.append_assoc] using
              (decoder_run_append trace earlierRounds ([last.time] ++ suffix) channel).symm)
          _ = AffineBatchDecoder.run p trace rounds channel := by rw [hsplit]
      _ = _ := hrun
  have hstepPending :
      (AffineBatchDecoder.step p trace (AffineBatchDecoder.run p trace earlierRounds channel) last.time).pending
        = [] := by rw [hstepFinal]
  have hquotaReached :
      (AffineBatchDecoder.run p trace earlierRounds channel).pending.length + 1 =
        AffineBatchDecoder.quota p := by
    by_cases hsmall : (AffineBatchDecoder.run p trace earlierRounds channel).pending.length + 1 <
        AffineBatchDecoder.quota p
    · have hbad :
          (AffineBatchDecoder.run p trace earlierRounds channel).pending ++
              [AffineBatchDecoder.entry p trace last.time] = [] := by
        have hbad := hstepPending
        simp [AffineBatchDecoder.step, AffineBatchDecoder.positiveAt, hlastEligible,
          List.length_append, hsmall] at hbad
      have hlength := congrArg List.length hbad
      simp only [List.length_append, List.length_cons, List.length_nil] at hlength
      omega
    · have hle : (AffineBatchDecoder.run p trace earlierRounds channel).pending.length + 1 ≤
        AffineBatchDecoder.quota p := by omega
      omega
  have hcomplete := AffineBatchDecoder.step_complete p trace
        (AffineBatchDecoder.run p trace earlierRounds channel) last.time hlastEligible hquotaReached
  rw [hcomplete] at hstepFinal
  let actualBatch := (AffineBatchDecoder.run p trace earlierRounds channel).pending ++
    [AffineBatchDecoder.entry p trace last.time]
  have hcompletedEq := congrArg AffineBatchDecoder.State.completed hstepFinal
  have hcompletedEq' :
      (AffineBatchDecoder.run p trace earlierRounds channel).completed ++ [actualBatch] =
        channel.completed ++ [first, window] := by
    simpa [actualBatch] using hcompletedEq
  have hbatch : actualBatch = window := by
    have hlastEq : some actualBatch = some window := by
      calc
        some actualBatch =
            ((AffineBatchDecoder.run p trace earlierRounds channel).completed ++ [actualBatch]).getLast? := by
          simp [actualBatch]
        _ = (channel.completed ++ [first, window]).getLast? := by
          rw [hcompletedEq']
        _ = some window := by simp
    exact Option.some.inj hlastEq
  have hraw : (AffineBatchDecoder.decodeStep p trace
      (AffineBatchDecoder.run p trace earlierRounds channel) last.time).2 =
        AffineBatchDecoder.batchOutput window := by
    have hbatch' :
        (AffineBatchDecoder.run p trace earlierRounds channel).pending ++
          [AffineBatchDecoder.entry p trace last.time] = window := by
      simpa [actualBatch] using hbatch
    rw [AffineBatchDecoder.decodeStep_complete p trace
      (AffineBatchDecoder.run p trace earlierRounds channel) last.time hlastEligible hquotaReached,
      hbatch']
  have hfold := run_interval_focal_decoder_fold initial rows selected rewards start a b hab hspan
    hmode hinitial hordinary i
  refine ⟨first, last, index, ?_, ?_, hfirst, hfirstLen, hwindowLen, hwindowChronological,
    hpendingDisjoint, hcountBound, hwindowBounds, hlastWindow, hdecision, hindexRound,
    hlastEligible, hlastSample, hwindowMax, ?_⟩
  · simpa [trace, rounds, preRun, full, interval, channel, window,
      WaitedWordWindow.secondPositiveWindow] using hrun
  · simpa [trace, rounds, preRun, full, interval, channel, intervalRounds,
      intervalRecords] using hfold
  · simpa [trace, rounds, preRun, full, interval, channel, earlierRounds, window,
      WaitedWordWindow.secondPositiveWindow] using hraw

end Bandits.Support.ReferenceCoordinatorUpIntervalWindow

end
