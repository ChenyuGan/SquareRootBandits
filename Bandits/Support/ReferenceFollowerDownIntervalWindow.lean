/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFollowerDownDecoderReplay
public import Bandits.Support.WaitedWordWindow

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.Intervals

/-!
# Actual DOWN decoder geometry on one interval

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-48,50-53`,
`sources/zip4/manuscript/06_interruptions.tex:248-275,327-348`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,151-157`.

All interval calls and positives below are projections of one actual
`ReferenceActivePhysicalHorizon.run`.  The interval theorem retains the whole
actual decoder bank at its left boundary, including completed batches and old
pending entries.  It asserts only conditional observation-count geometry.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ReferenceFollowerDecoderChronology
open Bandits.Support.ReferenceFollowerDownDecoderReplay
open Bandits.Support.AffineBatchDecoder

namespace Bandits.Support.ReferenceFollowerDownIntervalWindow

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev State := ReferenceActivePhysicalHorizon.State
abbrev FollowerState := ReferencePrelaunchFollower.State
abbrev Memory := ActiveFollowerLifecycle.LocalMemory
abbrev Record := ReferenceFollowerDownDecoderReplay.Record
abbrev Call := ReferenceFollowerDownDecoderReplay.Call

private theorem foldCalendar_records_extends
    {p : Parameters} {rate : RateInput p}
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (origin : ℕ)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial origin)
    (entries : List (ReferenceActivePhysicalHorizon.CalendarEntry p origin))
    (acc : ReferenceActivePhysicalHorizon.Run initial) :
    ∃ suffix,
      (entries.foldl (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards
        origin hmode) acc).records = acc.records ++ suffix := by
  classical
  induction entries generalizing acc with
  | nil => exact ⟨[], by simp⟩
  | cons entry rest ih =>
      simp only [List.foldl_cons]
      obtain ⟨suffix, hsuffix⟩ := ih
        (acc := ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards
          origin hmode acc entry)
      let input := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards
        origin hmode acc entry
      let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
        ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩
      have hround :
          (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards
            origin hmode acc entry).records = acc.records ++ [record] := by
        rfl
      refine ⟨record :: suffix, ?_⟩
      rw [hsuffix, hround]
      simp [List.append_assoc]

private theorem connected_split_append
    {p : Parameters} {rate : RateInput p}
    {initial middle final : ReferenceActivePhysicalHorizon.State p rate}
    {left : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    {right : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hwhole : ReferenceActivePhysicalHorizon.Connected initial (left ++ right) final)
    (hleft : ReferenceActivePhysicalHorizon.Connected initial left middle) :
    ReferenceActivePhysicalHorizon.Connected middle right final := by
  induction left generalizing initial middle final with
  | nil =>
      simp only [List.nil_append, ReferenceActivePhysicalHorizon.Connected] at hwhole hleft ⊢
      subst middle
      exact hwhole
  | cons record rest ih =>
      simp only [List.cons_append, ReferenceActivePhysicalHorizon.Connected] at hwhole hleft ⊢
      rcases hwhole with ⟨_, hwhole⟩
      rcases hleft with ⟨_, hleft⟩
      exact ih hwhole hleft

/-- Under an ordinary endpoint, actual DOWN calls cover every record in
order and retain each record timestamp. -/
theorem actualDownCalls_map_records
    {p : Parameters} {rate : RateInput p}
    (i : Fin (p.m - 1))
    (records : List (Record p rate))
    (hordinary : ∀ record ∈ records,
      ∃ choice memory,
        ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i =
          .ordinary choice memory) :
    (ReferenceFollowerDownDecoderReplay.actualDownCalls i records).map Prod.fst =
      records.map (fun record => record.input.time) := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      obtain ⟨choice, memory, hchoice⟩ := hordinary record (by simp)
      have hcall := ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary
        record i choice memory hchoice
      have htail : ∀ current ∈ rest,
          ∃ choice memory,
            ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration current i =
              .ordinary choice memory := by
        intro current hmem
        exact hordinary current (by simp [hmem])
      have htailMap :
          (List.filterMap (ReferenceFollowerDownDecoderReplay.actualDownCall i) rest).map Prod.fst =
            rest.map (fun current => current.input.time) := by
        simpa only [ReferenceFollowerDownDecoderReplay.actualDownCalls] using ih htail
      simp only [ReferenceFollowerDownDecoderReplay.actualDownCalls,
        List.filterMap_cons, hcall, List.map_cons]
      rw [htailMap]
      simp only [ReferenceFollowerDownDecoderReplay.preparedChoiceTime_eq_recordTime]

/-- A total administrative extension of a finite call list. Its value has
physical input meaning only at timestamps of calls in the list. -/
noncomputable def administrativeIntervalTrace
    {p : Parameters} (calls : List (Call p)) (fallback : Call p) :
    AffineBatchDecoder.Trace p := fun t =>
  match calls.find? (fun call => decide (call.1 = t)) with
  | some call => ActiveFollowerDownAcceptance.currentInputExtension p call.2 t
  | none => ActiveFollowerDownAcceptance.currentInputExtension p fallback.2 t

private theorem findCall_eq_some_of_pairwise
    {p : Parameters} {calls : List (Call p)}
    (hpair : calls.Pairwise (fun first second => first.1.val < second.1.val))
    (call : Call p) (hcall : call ∈ calls) :
    calls.find? (fun other => decide (other.1 = call.1)) = some call := by
  induction calls with
  | nil => simp at hcall
  | cons first rest ih =>
      cases hpair with
      | cons hhead htail =>
          rcases List.mem_cons.mp hcall with hEq | hmem
          · subst call
            simp [List.find?]
          · have hlt := hhead call hmem
            have hneq : first.1 ≠ call.1 := by
              intro heq
              have hval := congrArg Fin.val heq
              rw [hval] at hlt
              exact (Nat.lt_irrefl _) hlt
            simp [List.find?, hneq, ih htail hmem]

/-- On every listed call timestamp, the administrative extension agrees
with that call's literal current input. -/
theorem administrativeIntervalTrace_on_call
    {p : Parameters} {calls : List (Call p)} {fallback call : Call p}
    (hpair : calls.Pairwise (fun first second => first.1.val < second.1.val))
    (hcall : call ∈ calls) :
    administrativeIntervalTrace calls fallback call.1 =
      ActiveFollowerDownAcceptance.currentInputExtension p call.2 call.1 := by
  simp [administrativeIntervalTrace, findCall_eq_some_of_pairwise hpair call hcall]

/-- Folding actual stamped inputs agrees with the existing affine decoder
run whenever the trace agrees at every listed call. -/
theorem foldDownCalls_eq_run
    {p : Parameters} {calls : List (Call p)}
    (tr : AffineBatchDecoder.Trace p)
    (hcurrent : ∀ call ∈ calls,
      tr call.1 = ActiveFollowerDownAcceptance.currentInputExtension p call.2 call.1)
    (batch : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) :
    ReferenceFollowerDownDecoderReplay.foldDownCalls calls batch =
      AffineBatchDecoder.run p tr (calls.map Prod.fst) batch := by
  induction calls generalizing batch with
  | nil => rfl
  | cons call rest ih =>
      have htail : ∀ current ∈ rest,
          tr current.1 = ActiveFollowerDownAcceptance.currentInputExtension p current.2 current.1 := by
        intro current hmem
        exact hcurrent current (by simp [hmem])
      have hstep :
          ReferenceFollowerDownDecoderReplay.replayDownCall batch call =
            AffineBatchDecoder.step p tr batch call.1 := by
        calc
          ReferenceFollowerDownDecoderReplay.replayDownCall batch call =
              (AffineBatchDecoder.decodeStep p
                (ActiveFollowerDownAcceptance.currentInputExtension p call.2)
                batch call.1).1 := rfl
          _ = (AffineBatchDecoder.decodeStep p tr batch call.1).1 :=
            congrArg Prod.fst
              (ActiveFollowerDownAcceptance.decodeStep_depends_on_current_input p
                (ActiveFollowerDownAcceptance.currentInputExtension p call.2) tr
                batch call.1 (hcurrent call (by simp)).symm)
          _ = AffineBatchDecoder.step p tr batch call.1 := rfl
      simp only [ReferenceFollowerDownDecoderReplay.foldDownCalls, List.foldl_cons]
      rw [hstep]
      exact ih htail _

/-- The positive-entry projection of the stamped calls agrees with the
decoder's positive projection under the same on-call input congruence. -/
theorem positiveCallEntries_eq_positives
    {p : Parameters} {calls : List (Call p)}
    (tr : AffineBatchDecoder.Trace p)
    (hcurrent : ∀ call ∈ calls,
      tr call.1 = ActiveFollowerDownAcceptance.currentInputExtension p call.2 call.1) :
    ReferenceFollowerDownDecoderReplay.positiveCallEntries calls =
      AffineBatchDecoder.positives p tr (calls.map Prod.fst) := by
  induction calls with
  | nil => rfl
  | cons call rest ih =>
      have htail : ∀ current ∈ rest,
          tr current.1 = ActiveFollowerDownAcceptance.currentInputExtension p current.2 current.1 := by
        intro current hmem
        exact hcurrent current (by simp [hmem])
      change AffineBatchDecoder.positiveAt p
          (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1 ++
        ReferenceFollowerDownDecoderReplay.positiveCallEntries rest =
          AffineBatchDecoder.positives p tr
            (call.1 :: (rest.map Prod.fst))
      rw [AffineBatchDecoder.positives_cons]
      have hpositiveAt : AffineBatchDecoder.positiveAt p
          (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1 =
            AffineBatchDecoder.positiveAt p tr call.1 := by
        unfold AffineBatchDecoder.positiveAt AffineBatchDecoder.entry
        rw [← hcurrent call (by simp)]
      rw [hpositiveAt, ih htail]

private theorem pairwise_suffix
    {α : Type} {R : α → α → Prop} (earlierList laterList : List α)
    (h : List.Pairwise R (earlierList ++ laterList)) : List.Pairwise R laterList := by
  induction earlierList with
  | nil => simpa using h
  | cons head rest ih =>
      cases h with
      | cons _ htail => exact ih htail

private theorem mem_drop_of_mem
    {α : Type} {items : List α} {count : ℕ} {item : α}
    (hitem : item ∈ items.drop count) : item ∈ items := by
  induction count generalizing items with
  | zero => simpa using hitem
  | succ count ih =>
      cases items with
      | nil => simp at hitem
      | cons head rest =>
          exact List.mem_cons_of_mem head (ih (by simpa using hitem))

private theorem decoderRun_append
    {p : Parameters} (tr : AffineBatchDecoder.Trace p)
    (left right : List (Fin p.T))
    (state : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) :
    AffineBatchDecoder.run p tr (left ++ right) state =
      AffineBatchDecoder.run p tr right (AffineBatchDecoder.run p tr left state) := by
  induction left generalizing state with
  | nil => rfl
  | cons time rest ih =>
      simp only [List.cons_append, AffineBatchDecoder.run]
      exact ih _

private theorem decoderRun_ineligible
    {p : Parameters} (tr : AffineBatchDecoder.Trace p)
    (rounds : List (Fin p.T))
    (state : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hpending : state.pending.length < AffineBatchDecoder.quota p)
    (hineligible : ∀ time ∈ rounds, ¬ AffineBatchDecoder.eligible (tr time)) :
    AffineBatchDecoder.run p tr rounds state = state := by
  induction rounds generalizing state with
  | nil => rfl
  | cons time rest ih =>
      have hhead := hineligible time (by simp)
      have htail : ∀ current ∈ rest, ¬ AffineBatchDecoder.eligible (tr current) := by
        intro current hcurrent
        exact hineligible current (by simp [hcurrent])
      simp only [AffineBatchDecoder.run,
        AffineBatchDecoder.step_ineligible p tr state time hpending hhead]
      exact ih state hpending htail

/-- A two-batch replay has a last positive call in its second batch; the
call is maximal in timestamp and its actual decoder output is that batch. -/
theorem two_batch_last_positive_output
    (p : Parameters) (calls : List (Call p))
    (trace : AffineBatchDecoder.Trace p)
    (hcurrent : ∀ call ∈ calls,
      trace call.1 = ActiveFollowerDownAcceptance.currentInputExtension p call.2 call.1)
    (hcallPair : calls.Pairwise (fun first second => first.1.val < second.1.val))
    (bank : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hbank : ReferenceFollowerDecoderChronology.downBatchWellFormed bank)
    (positives : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hpositives : ReferenceFollowerDownDecoderReplay.positiveCallEntries calls = positives)
    (hpositivePair : positives.Pairwise
      (fun earlier later => earlier.time.val < later.time.val))
    (first window : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hwindow : window = positives.drop (AffineBatchDecoder.quota p - bank.pending.length))
    (hwindowLen : window.length = AffineBatchDecoder.quota p)
    (hrun : AffineBatchDecoder.run p trace (calls.map Prod.fst) bank =
      ⟨[], bank.completed ++ [first, window]⟩) :
    ∃ index call entry,
      index < calls.length ∧
      calls = calls.take index ++ call :: calls.drop (index + 1) ∧
      entry ∈ window ∧ entry ∈ positives ∧
      (∀ other ∈ window, other.time.val ≤ entry.time.val) ∧
      entry.time = call.1 ∧ AffineBatchDecoder.eligible (trace call.1) ∧
      let before := AffineBatchDecoder.run p trace ((calls.take index).map Prod.fst) bank
      (AffineBatchDecoder.decodeStep p trace before call.1).2 =
        AffineBatchDecoder.batchOutput window := by
  have hq := AffineBatchDecoder.quota_pos p
  have hwindowNe : window ≠ [] := by
    intro hnil
    rw [hnil, List.length_nil] at hwindowLen
    omega
  let last := window.getLast hwindowNe
  have hlastWindow : last ∈ window := by
    simp [last]
  have hlastPositive : last ∈ positives := by
    have hlastDrop : last ∈ positives.drop
        (AffineBatchDecoder.quota p - bank.pending.length) := by
      rw [← hwindow]
      exact hlastWindow
    exact mem_drop_of_mem hlastDrop
  have hlastBound : ∀ entry ∈ positives, entry.time.val ≤ last.time.val := by
    intro entry hentry
    let count := AffineBatchDecoder.quota p - bank.pending.length
    have hsplit : positives.take count ++ window = positives := by
      rw [hwindow, List.take_append_drop]
    have hpairSplit : (positives.take count ++ window).Pairwise
        (fun earlier later => earlier.time.val < later.time.val) := by
      rw [hsplit]
      exact hpositivePair
    have hmemSplit : entry ∈ positives.take count ++ window := by
      rw [hsplit]
      exact hentry
    rcases List.mem_append.mp hmemSplit with hleft | hright
    · obtain ⟨_, _, hcross⟩ := List.pairwise_append.mp hpairSplit
      exact Nat.le_of_lt (hcross entry hleft last hlastWindow)
    · by_cases heq : entry = last
      · simp [heq]
      · have hdrop : entry ∈ window.dropLast :=
          List.mem_dropLast_of_mem_of_ne_getLast hright heq
        have hwindowPair : window.Pairwise
            (fun earlier later => earlier.time.val < later.time.val) := by
          rw [hwindow]
          exact hpositivePair.sublist (List.drop_sublist _ _)
        exact Nat.le_of_lt (hwindowPair.rel_dropLast_getLast hdrop)
  have hlastPcall : last ∈ ReferenceFollowerDownDecoderReplay.positiveCallEntries calls := by
    rw [hpositives]
    exact hlastPositive
  obtain ⟨call, hcall, hentry⟩ := List.mem_flatMap.mp hlastPcall
  have hcallEligible : AffineBatchDecoder.eligible (trace call.1) := by
    rw [hcurrent call hcall]
    unfold AffineBatchDecoder.positiveAt at hentry
    split at hentry
    · assumption
    · simp at hentry
  have hentryEq : last = AffineBatchDecoder.entry p trace call.1 := by
    have hinputEligible : AffineBatchDecoder.eligible
        (ActiveFollowerDownAcceptance.currentInputExtension p call.2 call.1) := by
      rw [← hcurrent call hcall]
      exact hcallEligible
    have hentryCurrent : last = AffineBatchDecoder.entry p
        (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1 := by
      unfold AffineBatchDecoder.positiveAt at hentry
      simp [hinputEligible] at hentry
      exact hentry
    calc
      last = AffineBatchDecoder.entry p
          (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1 := hentryCurrent
      _ = AffineBatchDecoder.entry p trace call.1 := by
        simp [AffineBatchDecoder.entry, ← hcurrent call hcall]
  have htimeEq : last.time = call.1 := by
    exact congrArg AffineBatchDecoder.Entry.time hentryEq
  obtain ⟨index, hindex, hget⟩ := List.getElem_of_mem hcall
  have hsplit : calls = calls.take index ++ call :: calls.drop (index + 1) := by
    have htakesplit : calls.take (index + 1) = calls.take index ++ [calls[index]] :=
      (List.take_append_getElem hindex).symm
    calc
      calls = calls.take (index + 1) ++ calls.drop (index + 1) :=
        (List.take_append_drop (index + 1) calls).symm
      _ = calls.take index ++ call :: calls.drop (index + 1) := by
        rw [htakesplit, hget]
        simp
  have hpairRight : (call :: calls.drop (index + 1)).Pairwise
      (fun first second => first.1.val < second.1.val) := by
    have hpairSplit : (calls.take index ++ call :: calls.drop (index + 1)).Pairwise
        (fun first second => first.1.val < second.1.val) := by rw [← hsplit]; exact hcallPair
    exact (List.pairwise_append.mp hpairSplit).2.1
  have hcallTail : ∀ later ∈ calls.drop (index + 1), call.1.val < later.1.val := by
    intro later hlater
    have hcons := hpairRight
    simp only [List.pairwise_cons] at hcons
    exact hcons.1 later hlater
  have hrounds : calls.map Prod.fst = (calls.take index).map Prod.fst ++
      call.1 :: (calls.drop (index + 1)).map Prod.fst := by
    simpa [List.map_append] using congrArg (List.map Prod.fst) hsplit
  let preCalls := calls.take index
  let suffix := calls.drop (index + 1)
  let before := AffineBatchDecoder.run p trace (preCalls.map Prod.fst) bank
  have htailIneligible : ∀ later ∈ suffix,
      ¬ AffineBatchDecoder.eligible (trace later.1) := by
    intro later hlater heligible
    have hnewCall : AffineBatchDecoder.entry p trace later.1 ∈
        ReferenceFollowerDownDecoderReplay.positiveCallEntries calls := by
      apply List.mem_flatMap.mpr
      have hlaterCall : later ∈ calls := mem_drop_of_mem hlater
      refine ⟨later, hlaterCall, ?_⟩
      have hinputEligible : AffineBatchDecoder.eligible
          (ActiveFollowerDownAcceptance.currentInputExtension p later.2 later.1) := by
        rw [← hcurrent later hlaterCall]
        exact heligible
      have hentryEq : AffineBatchDecoder.entry p trace later.1 =
          AffineBatchDecoder.entry p
            (ActiveFollowerDownAcceptance.currentInputExtension p later.2) later.1 := by
        simp [AffineBatchDecoder.entry, hcurrent later hlaterCall]
      simp only [AffineBatchDecoder.positiveAt, hinputEligible, ↓reduceIte]
      exact List.mem_singleton.mpr hentryEq
    have hnew : AffineBatchDecoder.entry p trace later.1 ∈ positives := by
      rw [← hpositives]
      exact hnewCall
    have hbound := hlastBound _ hnew
    have hlt := hcallTail later hlater
    have hentryTime : (AffineBatchDecoder.entry p trace later.1).time = later.1 := rfl
    omega
  have hbeforeWell := AffineBatchDecoder.run_spec p trace (preCalls.map Prod.fst) bank
    hbank.1 hbank.2
  have hbeforeBound : before.pending.length < AffineBatchDecoder.quota p := by
    simpa [before] using hbeforeWell.1
  have hstepBound : (AffineBatchDecoder.step p trace before call.1).pending.length <
      AffineBatchDecoder.quota p := by
    exact (AffineBatchDecoder.run_spec p trace [call.1] before hbeforeWell.1 hbeforeWell.2.1).1
  have hafterRun : AffineBatchDecoder.run p trace (calls.map Prod.fst) bank =
      AffineBatchDecoder.step p trace before call.1 := by
    have hroundsSplit : calls.map Prod.fst =
        (preCalls.map Prod.fst) ++ ([call.1] ++ suffix.map Prod.fst) := by
      simpa [preCalls, suffix, List.append_assoc] using hrounds
    calc
      AffineBatchDecoder.run p trace (calls.map Prod.fst) bank =
          AffineBatchDecoder.run p trace
            ((preCalls.map Prod.fst) ++ ([call.1] ++ suffix.map Prod.fst)) bank := by
        rw [hroundsSplit]
      _ = AffineBatchDecoder.run p trace ([call.1] ++ suffix.map Prod.fst) before :=
        decoderRun_append trace (preCalls.map Prod.fst)
          ([call.1] ++ suffix.map Prod.fst) bank
      _ = AffineBatchDecoder.run p trace (suffix.map Prod.fst)
          (AffineBatchDecoder.step p trace before call.1) := by
        rw [decoderRun_append]
        rfl
      _ = AffineBatchDecoder.step p trace before call.1 :=
        decoderRun_ineligible trace (suffix.map Prod.fst)
          (AffineBatchDecoder.step p trace before call.1) hstepBound (by
            intro time htime heligible
            obtain ⟨later, hlater, rfl⟩ := List.mem_map.mp htime
            exact htailIneligible later hlater heligible)
  have hafterShape : AffineBatchDecoder.step p trace before call.1 =
      ⟨[], bank.completed ++ [first, window]⟩ := hafterRun.symm.trans hrun
  have hquota : before.pending.length + 1 = AffineBatchDecoder.quota p := by
    by_contra hnot
    have hlt : before.pending.length + 1 < AffineBatchDecoder.quota p := by
      omega
    have hstepPending : (AffineBatchDecoder.step p trace before call.1).pending =
        before.pending ++ [AffineBatchDecoder.entry p trace call.1] := by
      simp [AffineBatchDecoder.step, AffineBatchDecoder.positiveAt, hcallEligible, hlt]
    have hnil := congrArg AffineBatchDecoder.State.pending hafterShape
    rw [hstepPending] at hnil
    simp at hnil
  have hstepComplete := AffineBatchDecoder.decodeStep_complete p trace before call.1
    hcallEligible hquota
  have hbatchEq : before.pending ++ [AffineBatchDecoder.entry p trace call.1] = window := by
    have hcompleted : before.completed ++
        [before.pending ++ [AffineBatchDecoder.entry p trace call.1]] =
        bank.completed ++ [first, window] := by
      have hstates := congrArg AffineBatchDecoder.State.completed hafterShape
      simpa [AffineBatchDecoder.step_complete p trace before call.1 hcallEligible hquota] using
        hstates
    have hlastOpt := congrArg List.getLast? hcompleted
    have hleftLast : (before.completed ++
        [before.pending ++ [AffineBatchDecoder.entry p trace call.1]]).getLast? =
        some (before.pending ++ [AffineBatchDecoder.entry p trace call.1]) := by simp
    have hrightLast : (bank.completed ++ [first, window]).getLast? = some window := by simp
    rw [hleftLast, hrightLast] at hlastOpt
    exact Option.some.inj hlastOpt
  have hbatchEq' : (AffineBatchDecoder.run p trace
      ((calls.take index).map Prod.fst) bank).pending ++
        [AffineBatchDecoder.entry p trace call.1] = window := by
    simpa [before, preCalls] using hbatchEq
  refine ⟨index, call, last, hindex, hsplit, hlastWindow, hlastPositive, ?_, htimeEq,
    hcallEligible, ?_⟩
  · intro other hother
    have hdrop : other ∈ positives.drop
        (AffineBatchDecoder.quota p - bank.pending.length) := by
      rw [← hwindow]
      exact hother
    exact hlastBound other (mem_drop_of_mem hdrop)
  have hraw := congrArg Prod.snd hstepComplete
  rw [hbatchEq'] at hraw
  exact hraw

theorem run_interval_downBatch_replay
    (p : Parameters) (rate : RateInput p)
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hab : a ≤ b) (hspan : start + b ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hseed : ReferenceFollowerDecoderChronology.downBatchSeed initial start)
    (i : Fin (p.m - 1))
    (stateB : ReferencePrelaunchFollower.State p rate.eta)
    (memoryB : ActiveFollowerLifecycle.LocalMemory p)
    (hordinaryB :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start b hspan hmode).finalState.followers i = .ordinary stateB memoryB) :
    ∃ stateA : ReferencePrelaunchFollower.State p rate.eta,
      ∃ memoryA : ActiveFollowerLifecycle.LocalMemory p,
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards
          start a (by omega) hmode).finalState.followers i = .ordinary stateA memoryA ∧
        (let R_a := ReferenceActivePhysicalHorizon.run initial rows selected rewards
          start a (by omega) hmode
         let R_b := ReferenceActivePhysicalHorizon.run initial rows selected rewards
          start b hspan hmode
         let I := R_b.records.drop a
         let C_ab := ReferenceFollowerDownDecoderReplay.actualDownCalls i I
         let P_ab := ReferenceFollowerDownDecoderReplay.actualDownPositives i I
         let B_a := stateA.downBatch
         let B_b := stateB.downBatch
         R_a.records = R_b.records.take a ∧
         C_ab.Pairwise (fun first second => first.1.val < second.1.val) ∧
         (C_ab.map Prod.fst).map Fin.val =
           ReferenceActivePhysicalHorizon.calendar (start + a) (b - a) ∧
         B_b = ReferenceFollowerDownDecoderReplay.foldDownCalls C_ab B_a ∧
         AffineBatchDecoder.collected B_b =
           AffineBatchDecoder.collected B_a ++ P_ab ∧
         B_a.pending.length < AffineBatchDecoder.quota p ∧
         (∀ entry ∈ B_a.pending, entry.time.val < start + a) ∧
         P_ab.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
         (∀ entry ∈ P_ab, start + a ≤ entry.time.val ∧ entry.time.val < start + b)) := by
  let R_a := ReferenceActivePhysicalHorizon.run initial rows selected rewards
    start a (by omega) hmode
  let R_b := ReferenceActivePhysicalHorizon.run initial rows selected rewards
    start b hspan hmode
  have hsum : a + (b - a) = b := by omega
  have happend := ReferenceActivePhysicalHorizon.run_append initial rows selected rewards
    start a (b - a) (by omega) hmode
  have happend' : R_b = ReferenceActivePhysicalHorizon.foldCalendar initial rows selected
      rewards start (start + a) (b - a) (by omega) (by omega) hmode R_a := by
    simpa [R_a, R_b, hsum] using happend
  let suffixEntries := ReferenceActivePhysicalHorizon.calendarEntries (p := p) start
    (start + a) (b - a) (by omega) (by omega)
  obtain ⟨suffix, hrecordsFold⟩ := foldCalendar_records_extends initial rows selected
    rewards start hmode suffixEntries R_a
  have hrecordsFold' :
      (ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards start
        (start + a) (b - a) (by omega) (by omega) hmode R_a).records =
        R_a.records ++ suffix := by
    simpa [ReferenceActivePhysicalHorizon.foldCalendar, suffixEntries] using hrecordsFold
  have hrecords : R_b.records = R_a.records ++ suffix := by
    rw [happend']
    exact hrecordsFold'
  have hlenA := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
    rewards start a (by omega) hmode
  have hlenA' : R_a.records.length = a := by simpa [R_a] using hlenA
  have hprefix : R_a.records = R_b.records.take a := by
    rw [hrecords]
    rw [List.take_append]
    have htaken : R_a.records.take a = R_a.records :=
      List.take_of_length_le (le_of_eq hlenA')
    simp [htaken, hlenA']
  have hinterval : R_b.records.drop a = suffix := by
    rw [hrecords, List.drop_append, hlenA']
    have hdropA : R_a.records.drop a = [] := by
      exact List.drop_eq_nil_of_le (le_of_eq hlenA')
    simp [hdropA]
  have hconnectedB := ReferenceActivePhysicalHorizon.run_connected initial rows selected
    rewards start b hspan hmode
  have hconnectedA := ReferenceActivePhysicalHorizon.run_connected initial rows selected
    rewards start a (by omega) hmode
  have hconnectedSuffix : ReferenceActivePhysicalHorizon.Connected R_a.finalState suffix
      R_b.finalState := by
    apply connected_split_append (middle := R_a.finalState) (left := R_a.records)
    · rw [← hrecords]
      simpa [R_b] using hconnectedB
    · exact hconnectedA
  have hordinaryA : ∃ stateA memoryA,
      R_a.finalState.followers i = .ordinary stateA memoryA := by
    cases hstate : R_a.finalState.followers i with
    | dagger =>
        have hdagger := hconnectedSuffix.follower_dagger i hstate
        rw [hdagger.1] at hordinaryB
        cases hordinaryB
    | ordinary stateA memoryA => exact ⟨stateA, memoryA, rfl⟩
  obtain ⟨stateA, memoryA, hstateA⟩ := hordinaryA
  obtain ⟨initialFollower, initialMemory, hinitial, _, _, _, _⟩ := hseed i
  have hmodeA := ReferenceFollowerDecoderChronology.run_downBatch_spec
    initial rows selected rewards start a (by omega) hmode hseed i stateA memoryA hstateA
  have hreplayA := ReferenceFollowerDownDecoderReplay.run_downBatch_replay
    initial rows selected rewards start a (by omega) hmode hseed i initialFollower initialMemory
    hinitial stateA memoryA hstateA
  have hreplayB := ReferenceFollowerDownDecoderReplay.run_downBatch_replay
    initial rows selected rewards start b hspan hmode hseed i initialFollower initialMemory
    hinitial stateB memoryB hordinaryB
  have hbank : stateB.downBatch =
      ReferenceFollowerDownDecoderReplay.foldDownCalls
        (ReferenceFollowerDownDecoderReplay.actualDownCalls i suffix) stateA.downBatch := by
    calc
      stateB.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCalls i R_b.records
          initialFollower.downBatch := hreplayB.1
      _ = ReferenceFollowerDownDecoderReplay.foldDownCalls
            (ReferenceFollowerDownDecoderReplay.actualDownCalls i suffix)
            (ReferenceFollowerDownDecoderReplay.replayDownCalls i R_a.records
              initialFollower.downBatch) := by
            simp [ReferenceFollowerDownDecoderReplay.replayDownCalls,
              ReferenceFollowerDownDecoderReplay.actualDownCalls, hrecords,
              ReferenceFollowerDownDecoderReplay.foldDownCalls, List.filterMap_append,
              List.foldl_append]
      _ = ReferenceFollowerDownDecoderReplay.foldDownCalls
            (ReferenceFollowerDownDecoderReplay.actualDownCalls i suffix) stateA.downBatch := by
            rw [← hreplayA.1]
  have hcollected : AffineBatchDecoder.collected stateB.downBatch =
      AffineBatchDecoder.collected stateA.downBatch ++
        ReferenceFollowerDownDecoderReplay.actualDownPositives i suffix := by
    calc
      AffineBatchDecoder.collected stateB.downBatch =
          AffineBatchDecoder.collected initialFollower.downBatch ++
            ReferenceFollowerDownDecoderReplay.actualDownPositives i R_b.records :=
        hreplayB.2.1
      _ = (AffineBatchDecoder.collected initialFollower.downBatch ++
            ReferenceFollowerDownDecoderReplay.actualDownPositives i R_a.records) ++
            ReferenceFollowerDownDecoderReplay.actualDownPositives i suffix := by
        simp [ReferenceFollowerDownDecoderReplay.actualDownPositives,
          ReferenceFollowerDownDecoderReplay.actualDownCalls, hrecords,
          List.filterMap_append, ReferenceFollowerDownDecoderReplay.positiveCallEntries,
          List.flatMap_append, List.append_assoc]
      _ = AffineBatchDecoder.collected stateA.downBatch ++
            ReferenceFollowerDownDecoderReplay.actualDownPositives i suffix := by
        rw [← hreplayA.2.1]
  have hcalendarSplit : ReferenceActivePhysicalHorizon.calendar start b =
      ReferenceActivePhysicalHorizon.calendar start a ++
        ReferenceActivePhysicalHorizon.calendar (start + a) (b - a) := by
    have hentries := ReferenceActivePhysicalHorizon.calendarEntries_append
      (p := p) start start a (b - a) le_rfl (by omega)
    have hfull := ReferenceActivePhysicalHorizon.calendarEntries_time_values
      (p := p) start start (a + (b - a)) le_rfl (by omega)
    have hleft := ReferenceActivePhysicalHorizon.calendarEntries_time_values
      (p := p) start start a le_rfl (by omega)
    have hright := ReferenceActivePhysicalHorizon.calendarEntries_time_values
      (p := p) start (start + a) (b - a) (by omega) (by omega)
    have hvalues' : ReferenceActivePhysicalHorizon.calendar start (a + (b - a)) =
        ReferenceActivePhysicalHorizon.calendar start a ++
          ReferenceActivePhysicalHorizon.calendar (start + a) (b - a) := by
      calc
        ReferenceActivePhysicalHorizon.calendar start (a + (b - a)) =
            (ReferenceActivePhysicalHorizon.calendarEntries (p := p) start start
              (a + (b - a)) le_rfl (by omega)).unattach := hfull.symm
        _ = (ReferenceActivePhysicalHorizon.calendarEntries (p := p) start start a
              le_rfl (by omega) ++
            ReferenceActivePhysicalHorizon.calendarEntries (p := p) start (start + a)
              (b - a) (by omega) (by omega)).unattach := by rw [hentries]
        _ = ReferenceActivePhysicalHorizon.calendar start a ++
            ReferenceActivePhysicalHorizon.calendar (start + a) (b - a) := by
          rw [List.unattach_append, hleft, hright]
    simpa [hsum] using hvalues'
  have hintervalTimes :
      suffix.map (fun record => record.input.time.val) =
        ReferenceActivePhysicalHorizon.calendar (start + a) (b - a) := by
    have htimesB := ReferenceActivePhysicalHorizon.run_time_values initial rows selected
      rewards start b hspan hmode
    have htimesSuffix :
        suffix.map (fun record => record.input.time.val) =
          (ReferenceActivePhysicalHorizon.calendar start b).drop a := by
      have hmap := congrArg (fun records : List (Record p rate) =>
        records.map (fun record => record.input.time.val)) hinterval
      have hrunTimes : R_b.records.map (fun record => record.input.time.val) =
          ReferenceActivePhysicalHorizon.calendar start b := by
        simpa [R_b] using htimesB
      simpa only [List.map_drop, hrunTimes] using hmap.symm
    rw [hcalendarSplit, List.drop_append] at htimesSuffix
    have hlenCalendarA :
        (ReferenceActivePhysicalHorizon.calendar start a).length = a := by
      simp [ReferenceActivePhysicalHorizon.calendar]
    have hdropCalendarA :
        (ReferenceActivePhysicalHorizon.calendar start a).drop a = [] := by
      exact List.drop_eq_nil_of_le (by omega)
    simpa [hdropCalendarA, hlenCalendarA] using htimesSuffix
  have hordinaryRecords : ∀ record ∈ suffix,
      ∃ choice choiceMemory,
        ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i =
          .ordinary choice choiceMemory := by
    intro record hrecord
    have hrecordAll : record ∈ R_b.records := by
      rw [hrecords]
      exact List.mem_append_right _ hrecord
    obtain ⟨choice, choiceMemory, hchoice, _⟩ :=
      (ReferenceFollowerDownDecoderReplay.run_downCall_calendar_correspondence
        initial rows selected rewards start b hspan hmode i stateB memoryB hordinaryB).2.2
        record hrecordAll
    exact ⟨choice, choiceMemory, hchoice⟩
  have hcallTimes :
      (ReferenceFollowerDownDecoderReplay.actualDownCalls i suffix).map Prod.fst =
        suffix.map (fun record => record.input.time) :=
    actualDownCalls_map_records i suffix hordinaryRecords
  have hcallTimesValues :
      ((ReferenceFollowerDownDecoderReplay.actualDownCalls i suffix).map Prod.fst).map
        Fin.val = ReferenceActivePhysicalHorizon.calendar (start + a) (b - a) := by
    calc
      _ = (suffix.map (fun record => record.input.time)).map Fin.val := by rw [hcallTimes]
      _ = suffix.map (fun record => record.input.time.val) := by simp
      _ = ReferenceActivePhysicalHorizon.calendar (start + a) (b - a) := hintervalTimes
  have hcalendarPair :
      (ReferenceActivePhysicalHorizon.calendar (start + a) (b - a)).Pairwise (· < ·) := by
    simp [ReferenceActivePhysicalHorizon.calendar, List.pairwise_lt_range']
  have hrecordPair : suffix.Pairwise
      (fun first second => first.input.time.val < second.input.time.val) := by
    have hmapPair :
        (suffix.map (fun record => record.input.time.val)).Pairwise (· < ·) := by
      rw [hintervalTimes]
      exact hcalendarPair
    exact List.pairwise_map.mp hmapPair
  have hcallPair : (ReferenceFollowerDownDecoderReplay.actualDownCalls i suffix).Pairwise
      (fun first second => first.1.val < second.1.val) := by
    have hroundPair :
        ((ReferenceFollowerDownDecoderReplay.actualDownCalls i suffix).map Prod.fst).Pairwise
          (fun first second => first.val < second.val) := by
      rw [hcallTimes]
      apply List.pairwise_map.mpr
      exact hrecordPair
    simpa only [List.pairwise_map] using hroundPair
  have hpositiveSplit :
      ReferenceFollowerDownDecoderReplay.actualDownPositives i R_b.records =
        ReferenceFollowerDownDecoderReplay.actualDownPositives i R_a.records ++
          ReferenceFollowerDownDecoderReplay.actualDownPositives i suffix := by
    simp [ReferenceFollowerDownDecoderReplay.actualDownPositives,
      ReferenceFollowerDownDecoderReplay.actualDownCalls, hrecords,
      List.filterMap_append, ReferenceFollowerDownDecoderReplay.positiveCallEntries,
      List.flatMap_append]
  have hcollectedFinal : AffineBatchDecoder.collected stateB.downBatch =
      AffineBatchDecoder.collected stateA.downBatch ++
        ReferenceFollowerDownDecoderReplay.actualDownPositives i suffix := hcollected
  have hchronB := hreplayB.2.2.1
  change (AffineBatchDecoder.collected stateB.downBatch).Pairwise
    (fun earlier later => earlier.time.val < later.time.val) at hchronB
  rw [hcollectedFinal] at hchronB
  have hpositiveChron := pairwise_suffix
    (AffineBatchDecoder.collected stateA.downBatch)
    (ReferenceFollowerDownDecoderReplay.actualDownPositives i suffix) hchronB
  have hpendingBound := hmodeA.1.1.1
  have hpendingTimes : ∀ entry ∈ stateA.downBatch.pending,
      entry.time.val < start + a := by
    intro entry hentry
    have hcol : entry ∈ AffineBatchDecoder.collected stateA.downBatch := by
      rw [AffineBatchDecoder.collected]
      exact List.mem_append_right _ hentry
    exact hmodeA.1.2.2 entry hcol
  have hpositiveTimes : ∀ entry ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i suffix,
      start + a ≤ entry.time.val ∧ entry.time.val < start + b := by
    intro entry hentry
    have hcol : entry ∈ AffineBatchDecoder.collected stateB.downBatch := by
      rw [hcollectedFinal]
      exact List.mem_append_right _ hentry
    have hupper := hreplayB.2.2.2 entry hcol
    have hround : entry.time ∈ (ReferenceFollowerDownDecoderReplay.actualDownCalls i suffix).map Prod.fst := by
      unfold ReferenceFollowerDownDecoderReplay.actualDownPositives
        ReferenceFollowerDownDecoderReplay.positiveCallEntries at hentry
      obtain ⟨call, hcall, hpositive⟩ := List.mem_flatMap.mp hentry
      have htime : entry.time = call.1 := by
        classical
        by_cases hEligible : AffineBatchDecoder.eligible
            (ActiveFollowerDownAcceptance.currentInputExtension p call.2 call.1)
        · have hsingleton : AffineBatchDecoder.positiveAt p
              (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1 =
              [AffineBatchDecoder.entry p
                (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1] := by
            simp [AffineBatchDecoder.positiveAt, hEligible]
          rw [hsingleton] at hpositive
          have heq := List.mem_singleton.mp hpositive
          exact congrArg AffineBatchDecoder.Entry.time heq
        · simp [AffineBatchDecoder.positiveAt, hEligible] at hpositive
      rw [htime]
      exact List.mem_map.mpr ⟨call, hcall, rfl⟩
    have htimeMem : entry.time.val ∈ ReferenceActivePhysicalHorizon.calendar
        (start + a) (b - a) := by
      have hmem : entry.time.val ∈
          ((ReferenceFollowerDownDecoderReplay.actualDownCalls i suffix).map Prod.fst).map
            (fun time : Fin p.T => time.val) := by
        exact List.mem_map.mpr ⟨entry.time, hround, rfl⟩
      simpa only [hcallTimesValues] using hmem
    have hmemRange : entry.time.val ∈ List.range' (start + a) (b - a) 1 := by
      simpa only [ReferenceActivePhysicalHorizon.calendar] using htimeMem
    obtain ⟨offset, hoffset, htime⟩ := List.mem_range'.mp hmemRange
    rw [htime]
    constructor <;> omega
  refine ⟨stateA, memoryA, hstateA, ?_⟩
  change R_a.records = R_b.records.take a ∧
    (ReferenceFollowerDownDecoderReplay.actualDownCalls i (R_b.records.drop a)).Pairwise
      (fun first second => first.1.val < second.1.val) ∧
    ((ReferenceFollowerDownDecoderReplay.actualDownCalls i (R_b.records.drop a)).map
      Prod.fst).map Fin.val = ReferenceActivePhysicalHorizon.calendar (start + a) (b - a) ∧
    stateB.downBatch = ReferenceFollowerDownDecoderReplay.foldDownCalls
      (ReferenceFollowerDownDecoderReplay.actualDownCalls i (R_b.records.drop a))
      stateA.downBatch ∧
    AffineBatchDecoder.collected stateB.downBatch =
      AffineBatchDecoder.collected stateA.downBatch ++
        ReferenceFollowerDownDecoderReplay.actualDownPositives i (R_b.records.drop a) ∧
    stateA.downBatch.pending.length < AffineBatchDecoder.quota p ∧
    (∀ entry ∈ stateA.downBatch.pending, entry.time.val < start + a) ∧
    (ReferenceFollowerDownDecoderReplay.actualDownPositives i (R_b.records.drop a)).Pairwise
      (fun earlier later => earlier.time.val < later.time.val) ∧
    (∀ entry ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i (R_b.records.drop a),
      start + a ≤ entry.time.val ∧ entry.time.val < start + b)
  refine ⟨hprefix, ?_, ?_, ?_, ?_, hpendingBound,
    hpendingTimes, ?_, ?_⟩
  · simpa [hinterval] using hcallPair
  · simpa [hinterval] using hcallTimesValues
  · simpa [hinterval] using hbank
  · simpa [hinterval] using hcollected
  · simpa [hinterval] using hpositiveChron
  · simpa [hinterval] using hpositiveTimes

/-- Conditional two-batch window for the very same interval calls produced by
one actual physical run.  The count equation is the only progress selector;
the trace extension is administrative and is consulted only at listed calls.
-/
theorem run_interval_down_two_batch_window
    (p : Parameters) (rate : RateInput p)
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hab : a ≤ b) (hspan : start + b ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hseed : ReferenceFollowerDecoderChronology.downBatchSeed initial start)
    (i : Fin (p.m - 1))
    (stateB : ReferencePrelaunchFollower.State p rate.eta)
    (memoryB : ActiveFollowerLifecycle.LocalMemory p)
    (hordinaryB :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start b hspan hmode).finalState.followers i = .ordinary stateB memoryB) :
    ∃ stateA : ReferencePrelaunchFollower.State p rate.eta,
      ∃ memoryA : ActiveFollowerLifecycle.LocalMemory p,
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards
          start a (by omega) hmode).finalState.followers i = .ordinary stateA memoryA ∧
        (let I := (ReferenceActivePhysicalHorizon.run initial rows selected rewards
          start b hspan hmode).records.drop a
         let calls := ReferenceFollowerDownDecoderReplay.actualDownCalls i I
         let positives := ReferenceFollowerDownDecoderReplay.actualDownPositives i I
         let first := stateA.downBatch.pending ++ positives.take
           (AffineBatchDecoder.quota p - stateA.downBatch.pending.length)
         let window := positives.drop
           (AffineBatchDecoder.quota p - stateA.downBatch.pending.length)
         (positives.length = AffineBatchDecoder.quota p -
           stateA.downBatch.pending.length + AffineBatchDecoder.quota p) →
         stateB.downBatch = ⟨[], stateA.downBatch.completed ++ [first, window]⟩ ∧
         first.length = AffineBatchDecoder.quota p ∧
         window.length = AffineBatchDecoder.quota p ∧
         window.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
         (∀ entry ∈ stateA.downBatch.pending, entry ∉ window) ∧
         (∀ entry ∈ window, entry ∈ positives ∧
           start + a ≤ entry.time.val ∧ entry.time.val < start + b) ∧
         (∃ trace : AffineBatchDecoder.Trace p,
           (∀ call ∈ calls,
             trace call.1 = ActiveFollowerDownAcceptance.currentInputExtension p call.2 call.1) ∧
           ∃ index call entry,
           index < calls.length ∧
           calls = calls.take index ++ call :: calls.drop (index + 1) ∧
           entry ∈ window ∧ entry.time = call.1 ∧
           (∀ other ∈ window, other.time.val ≤ entry.time.val) ∧
           AffineBatchDecoder.eligible (trace call.1) ∧
           (AffineBatchDecoder.decodeStep p trace
             (AffineBatchDecoder.run p trace ((calls.take index).map Prod.fst)
               stateA.downBatch) call.1).2 = AffineBatchDecoder.batchOutput window)) := by
  let R_a := ReferenceActivePhysicalHorizon.run initial rows selected rewards
    start a (by omega) hmode
  let R_b := ReferenceActivePhysicalHorizon.run initial rows selected rewards
    start b hspan hmode
  let interval := R_b.records.drop a
  let calls := ReferenceFollowerDownDecoderReplay.actualDownCalls i interval
  let positives := ReferenceFollowerDownDecoderReplay.actualDownPositives i interval
  obtain ⟨stateA, memoryA, hstateA, hfacts⟩ := run_interval_downBatch_replay
    p rate initial rows selected rewards start a b hab hspan hmode hseed i stateB memoryB
    hordinaryB
  rcases hfacts with
    ⟨hprefix, hcallPair, hcallCalendar, hbank, hcollected, hpending, hpendingTime,
      hpositivePair, hpositiveTime⟩
  refine ⟨stateA, memoryA, hstateA, ?_⟩
  dsimp only
  intro hcount
  have hselector : positives.length =
      AffineBatchDecoder.quota p - stateA.downBatch.pending.length +
        AffineBatchDecoder.quota p := hcount
  have hpositiveNonempty : positives ≠ [] := by
    intro hempty
    have hzero : 0 = AffineBatchDecoder.quota p - stateA.downBatch.pending.length +
        AffineBatchDecoder.quota p := by
      simpa [hempty] using hselector
    have hq := AffineBatchDecoder.quota_pos p
    have hgap := Nat.sub_pos_of_lt hpending
    omega
  have hcallNonempty : calls ≠ [] := by
    intro hempty
    have hnil : positives = [] := by
      change ReferenceFollowerDownDecoderReplay.positiveCallEntries calls = []
      rw [hempty]
      rfl
    exact hpositiveNonempty hnil
  obtain ⟨fallback, hfallback⟩ := List.exists_mem_of_ne_nil calls hcallNonempty
  let trace := administrativeIntervalTrace calls fallback
  have hcurrent : ∀ call ∈ calls,
      trace call.1 = ActiveFollowerDownAcceptance.currentInputExtension p call.2 call.1 := by
    intro call hcall
    exact administrativeIntervalTrace_on_call hcallPair hcall
  have hfold := foldDownCalls_eq_run trace hcurrent stateA.downBatch
  have hpositives := positiveCallEntries_eq_positives trace hcurrent
  have hposEq : positives = AffineBatchDecoder.positives p trace (calls.map Prod.fst) := by
    change ReferenceFollowerDownDecoderReplay.positiveCallEntries calls = _
    exact hpositives
  have hpendingOlder : ∀ entry ∈ stateA.downBatch.pending, ∀ time ∈ calls.map Prod.fst,
      entry.time.val < time.val := by
    intro entry hentry time htime
    have htimeVal : time.val ∈ (calls.map Prod.fst).map Fin.val :=
      List.mem_map.mpr ⟨time, htime, rfl⟩
    rw [hcallCalendar] at htimeVal
    have hrange : time.val ∈ List.range' (start + a) (b - a) 1 := by
      simpa only [ReferenceActivePhysicalHorizon.calendar] using htimeVal
    obtain ⟨offset, hoffset, htimeValEq⟩ := List.mem_range'.mp hrange
    rw [htimeValEq]
    have hold := hpendingTime entry hentry
    omega
  have hwindow := WaitedWordWindow.run_two_batch_window p trace (calls.map Prod.fst)
    stateA.downBatch hpending (by rw [← hposEq]; exact hselector) (by
      simpa [List.pairwise_map] using hcallPair) hpendingOlder
  rcases hwindow with ⟨first, hrun, hfirst, hfirstLen, hwindowLen, hwindowPair,
    hpendingDisjoint, _⟩
  have hbankRun : stateB.downBatch =
      AffineBatchDecoder.run p trace (calls.map Prod.fst) stateA.downBatch := by
    calc
      stateB.downBatch = ReferenceFollowerDownDecoderReplay.foldDownCalls calls
          stateA.downBatch := by
        simpa [R_b, interval] using hbank
      _ = AffineBatchDecoder.run p trace (calls.map Prod.fst) stateA.downBatch := hfold
  have hwindowEq :
      WaitedWordWindow.secondPositiveWindow p trace (calls.map Prod.fst)
        stateA.downBatch.pending hpending = positives.drop
          (AffineBatchDecoder.quota p - stateA.downBatch.pending.length) := by
    simp only [WaitedWordWindow.secondPositiveWindow]
    rw [← hposEq]
  have hfirstActual : first = stateA.downBatch.pending ++ positives.take
      (AffineBatchDecoder.quota p - stateA.downBatch.pending.length) := by
    simpa only [← hposEq] using hfirst
  have hrunShape : stateB.downBatch =
      ⟨[], stateA.downBatch.completed ++
        [first, positives.drop (AffineBatchDecoder.quota p - stateA.downBatch.pending.length)]⟩ := by
    calc
      stateB.downBatch = AffineBatchDecoder.run p trace (calls.map Prod.fst)
          stateA.downBatch := hbankRun
      _ = ⟨[], stateA.downBatch.completed ++
          [first, WaitedWordWindow.secondPositiveWindow p trace (calls.map Prod.fst)
            stateA.downBatch.pending hpending]⟩ := hrun
      _ = _ := by rw [hwindowEq]
  have hwindowFromInterval : ∀ entry ∈ positives.drop
      (AffineBatchDecoder.quota p - stateA.downBatch.pending.length),
      entry ∈ positives ∧ start + a ≤ entry.time.val ∧ entry.time.val < start + b := by
    intro entry hentry
    have hmem := mem_drop_of_mem hentry
    exact ⟨hmem, hpositiveTime entry hmem⟩
  have hwell : ReferenceFollowerDecoderChronology.downBatchWellFormed stateA.downBatch :=
    (ReferenceFollowerDecoderChronology.run_downBatch_spec initial rows selected rewards
      start a (by omega) hmode hseed i stateA memoryA hstateA).1.1
  have hpositiveCallEq : ReferenceFollowerDownDecoderReplay.positiveCallEntries calls = positives := by
    calc
      ReferenceFollowerDownDecoderReplay.positiveCallEntries calls =
          AffineBatchDecoder.positives p trace (calls.map Prod.fst) := hpositives
      _ = positives := hposEq.symm
  have hrunDrop : AffineBatchDecoder.run p trace (calls.map Prod.fst) stateA.downBatch =
      ⟨[], stateA.downBatch.completed ++
        [first, positives.drop (AffineBatchDecoder.quota p - stateA.downBatch.pending.length)]⟩ := by
    simpa only [hwindowEq] using hrun
  obtain ⟨index, call, entry, hindex, hsplit, hentry, hentryPositive, hlast,
      hentryTime, hcallEligible, hraw⟩ := two_batch_last_positive_output p calls trace
        hcurrent hcallPair stateA.downBatch hwell positives hpositiveCallEq hpositivePair
        first (positives.drop (AffineBatchDecoder.quota p - stateA.downBatch.pending.length))
        rfl (by simpa [hwindowEq] using hwindowLen) hrunDrop
  change stateB.downBatch =
      ⟨[], stateA.downBatch.completed ++
        [stateA.downBatch.pending ++ positives.take
          (AffineBatchDecoder.quota p - stateA.downBatch.pending.length),
         positives.drop (AffineBatchDecoder.quota p - stateA.downBatch.pending.length)]⟩ ∧
    (stateA.downBatch.pending ++ positives.take
      (AffineBatchDecoder.quota p - stateA.downBatch.pending.length)).length =
        AffineBatchDecoder.quota p ∧
    (positives.drop (AffineBatchDecoder.quota p - stateA.downBatch.pending.length)).length =
        AffineBatchDecoder.quota p ∧
    (positives.drop (AffineBatchDecoder.quota p - stateA.downBatch.pending.length)).Pairwise
      (fun earlier later => earlier.time.val < later.time.val) ∧
    (∀ entry ∈ stateA.downBatch.pending,
      entry ∉ positives.drop (AffineBatchDecoder.quota p - stateA.downBatch.pending.length)) ∧
    (∀ entry ∈ positives.drop (AffineBatchDecoder.quota p - stateA.downBatch.pending.length),
      entry ∈ positives ∧ start + a ≤ entry.time.val ∧ entry.time.val < start + b) ∧
    (∃ trace : AffineBatchDecoder.Trace p,
      (∀ call ∈ calls,
        trace call.1 = ActiveFollowerDownAcceptance.currentInputExtension p call.2 call.1) ∧
      ∃ index call entry,
        index < calls.length ∧
        calls = calls.take index ++ call :: calls.drop (index + 1) ∧
        entry ∈ positives.drop (AffineBatchDecoder.quota p - stateA.downBatch.pending.length) ∧
        entry.time = call.1 ∧
        (∀ other ∈ positives.drop
          (AffineBatchDecoder.quota p - stateA.downBatch.pending.length),
          other.time.val ≤ entry.time.val) ∧
        AffineBatchDecoder.eligible (trace call.1) ∧
        (AffineBatchDecoder.decodeStep p trace
          (AffineBatchDecoder.run p trace ((calls.take index).map Prod.fst)
            stateA.downBatch) call.1).2 =
              AffineBatchDecoder.batchOutput
                (positives.drop (AffineBatchDecoder.quota p - stateA.downBatch.pending.length)))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfirstActual] at hrunShape
    exact hrunShape
  · rw [← hfirstActual]
    exact hfirstLen
  · rw [hwindowEq] at hwindowLen
    exact hwindowLen
  · rw [hwindowEq] at hwindowPair
    exact hwindowPair
  · intro entry hentry hmemWindow
    apply hpendingDisjoint entry hentry
    rw [hwindowEq]
    exact hmemWindow
  · exact hwindowFromInterval
  · refine ⟨trace, hcurrent, index, call, entry, hindex, hsplit, ?_, hentryTime,
      hlast, hcallEligible, hraw⟩
    simpa [hwindowEq] using hentry

/-- Locate the last positive of the conditional second batch at its real
physical record, replay that record's prefix bank, and recover the retained
constructor cut. The sole extra premise is the local interval observation
count selector. -/
theorem run_actualLaunched_interval_downBatch_replay
    (p : Parameters)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : ReferenceActivePhysicalStep.RateInput p) (C_star C_h : ℝ)
    (boundary : ReferenceInitializationRun.Boundary p)
    (hboundary : boundary.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock boundary hboundary))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock boundary hboundary) actual
      boundary past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      boundary hboundary i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          boundary hboundary).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          boundary hboundary)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      boundary hboundary i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock boundary hboundary) source rewards actual.C_star
      actual.C_h (ActualInitializationRun.foldBlock p rate
        (ReferenceInitializationRun.nextBlock boundary hboundary) source rewards actual)).disposition =
          .launched launch learnerSeed)
    (rows : CompletePublicTable.CompleteRows p)
    (a intervalEnd : ℕ) (ha : a ≤ intervalEnd)
    (hspan : BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock boundary hboundary) + intervalEnd ≤ p.T)
    (i : Fin (p.m - 1))
    (stateB : ReferencePrelaunchFollower.State p rate.eta)
    (memoryB : ActiveFollowerLifecycle.LocalMemory p)
    (hordinaryB : (ReferenceActivePhysicalHorizon.run
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h
        boundary hboundary actual past hr hdown hclean hforce launch learnerSeed hlaunched)
      rows (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      (BootstrapObservedFollower.blockStop p
        (ReferenceInitializationRun.nextBlock boundary hboundary))
      intervalEnd hspan (by
        intro j
        exact ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
          source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce
          launch learnerSeed hlaunched j)).finalState.followers i = .ordinary stateB memoryB) :
    ∃ initialFollower initialMemory stateA memoryA,
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h
        boundary hboundary actual past hr hdown hclean hforce launch learnerSeed hlaunched).followers i =
          .ordinary initialFollower initialMemory ∧
      (ReferenceActivePhysicalHorizon.run
        (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h
          boundary hboundary actual past hr hdown hclean hforce launch learnerSeed hlaunched)
        rows (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (BootstrapObservedFollower.blockStop p
          (ReferenceInitializationRun.nextBlock boundary hboundary))
        a (by omega) (by
          intro j
          exact ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
            source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce
            launch learnerSeed hlaunched j)).finalState.followers i = .ordinary stateA memoryA ∧
      (let R_a := ReferenceActivePhysicalHorizon.run
          (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h
            boundary hboundary actual past hr hdown hclean hforce launch learnerSeed hlaunched)
          rows (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          (BootstrapObservedFollower.blockStop p
            (ReferenceInitializationRun.nextBlock boundary hboundary)) a (by omega) (by
              intro j
              exact ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
                source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce
                launch learnerSeed hlaunched j)
       let R_b := ReferenceActivePhysicalHorizon.run
          (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h
            boundary hboundary actual past hr hdown hclean hforce launch learnerSeed hlaunched)
          rows (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          (BootstrapObservedFollower.blockStop p
            (ReferenceInitializationRun.nextBlock boundary hboundary)) intervalEnd hspan (by
              intro j
              exact ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
                source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce
                launch learnerSeed hlaunched j)
       let I := R_b.records.drop a
       let C_ab := ReferenceFollowerDownDecoderReplay.actualDownCalls i I
       let P_ab := ReferenceFollowerDownDecoderReplay.actualDownPositives i I
       R_a.records = R_b.records.take a ∧
       C_ab.Pairwise (fun first second => first.1.val < second.1.val) ∧
       (C_ab.map Prod.fst).map Fin.val =
         ReferenceActivePhysicalHorizon.calendar
           (BootstrapObservedFollower.blockStop p
             (ReferenceInitializationRun.nextBlock boundary hboundary) + a)
           (intervalEnd - a) ∧
       stateB.downBatch = ReferenceFollowerDownDecoderReplay.foldDownCalls C_ab stateA.downBatch ∧
       AffineBatchDecoder.collected stateB.downBatch =
         AffineBatchDecoder.collected stateA.downBatch ++ P_ab ∧
       stateA.downBatch.pending.length < AffineBatchDecoder.quota p ∧
       (∀ entry ∈ stateA.downBatch.pending,
         entry.time.val < BootstrapObservedFollower.blockStop p
           (ReferenceInitializationRun.nextBlock boundary hboundary) + a) ∧
       P_ab.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
       (∀ entry ∈ P_ab,
         BootstrapObservedFollower.blockStop p
           (ReferenceInitializationRun.nextBlock boundary hboundary) + a ≤ entry.time.val ∧
         entry.time.val < BootstrapObservedFollower.blockStop p
           (ReferenceInitializationRun.nextBlock boundary hboundary) + intervalEnd)) ∧
      stateB.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCalls i
        (ReferenceActivePhysicalHorizon.run
          (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h
            boundary hboundary actual past hr hdown hclean hforce launch learnerSeed hlaunched)
          rows (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          (BootstrapObservedFollower.blockStop p
            (ReferenceInitializationRun.nextBlock boundary hboundary)) intervalEnd hspan (by
              intro j
              exact ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
                source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce
                launch learnerSeed hlaunched j)).records initialFollower.downBatch := by
  let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
    C_star C_h boundary hboundary actual past hr hdown hclean hforce launch learnerSeed hlaunched
  let start := BootstrapObservedFollower.blockStop p
    (ReferenceInitializationRun.nextBlock boundary hboundary)
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start := by
    intro j
    exact ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
      source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce
      launch learnerSeed hlaunched j
  have hseed := ReferenceFollowerDecoderChronology.ofActualLaunchedBoundary_downBatchSeed
    source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce launch
    learnerSeed hlaunched
  obtain ⟨initialFollower, initialMemory, hinitial, hfullReplay, hfullCollected, _, _⟩ :=
    ReferenceFollowerDownDecoderReplay.run_downBatch_replay_ofActualLaunchedBoundary
      source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce launch
      learnerSeed hlaunched rows intervalEnd hspan i stateB memoryB (by simpa [initial, start] using
        hordinaryB)
  obtain ⟨stateA, memoryA, hstateA, hinterval⟩ := run_interval_downBatch_replay
    p rate initial rows (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    start a intervalEnd ha hspan hmode hseed i stateB memoryB
      (by simpa [initial, start] using hordinaryB)
  refine ⟨initialFollower, initialMemory, stateA, memoryA, hinitial, ?_, ?_, hfullReplay⟩
  · simpa [initial, start] using hstateA
  · simpa [initial, start] using hinterval

end Bandits.Support.ReferenceFollowerDownIntervalWindow
