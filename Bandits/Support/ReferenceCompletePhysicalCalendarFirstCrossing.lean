/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompletePhysicalCalendarQueueTruth
public import Bandits.Support.ReferenceOriginalCalendarCarriedStoppedEnergy
public import Bandits.Support.UnstoppedRecordedQueueComparison

/-!
# Actual physical calendar first queue crossing

This module identifies the literal first integer backlog threshold on the
complete actual physical suffix with the original numerical overflow event.
The physical replay continues through the suffix after its first crossing.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput)
open ReferenceFirstCollectionRenewalIncomingQueueMeasurability (stateReadout)
open scoped Classical

namespace Bandits.Support.ReferenceCompletePhysicalCalendarFirstCrossing

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)
local notation "X" => SourceInput p
local notation "Input" => RecordedQueueRun.RoundInput p.K
variable (z : SourceInput p)
local notation "R" => ReferenceCompletePhysicalHistory.completeSuffixRecords
  rate z rewards C_star C_h
local notation "s" => ReferenceCompletePhysicalHistory.physicalStart
  rate z rewards C_star C_h
local notation "QP" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "W" => ReferenceCompletePhysicalCalendarQueueTruth.actualPhysicalWord
  rate rewards C_star C_h z

/-- The actual physical source event `E_queue`: some original post-update
calendar boundary has an arm whose integer backlog is strictly above the
source cap `D / 32`.  The replay is the actual whole suffix replay, even after
the analytical first crossing. -/
public def physicalFirstOverflowEvent : Set X :=
  {x | ∃ h : ℕ, 1 ≤ h ∧ h ≤
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate x rewards C_star C_h).length ∧
    ∃ a : Fin p.K,
      32 * (ReferenceCompletePhysicalCalendarQueueTruth.sourceCalendarReplay
        rate rewards C_star C_h x a h).2 >
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).D}

private theorem firstOverflowPrefix_le_length_iff
    (q : RecordedQueueRun.Parameters) (xs : List Input) :
    UnstoppedRecordedQueueComparison.firstOverflowPrefix q xs ≤ xs.length ↔
      ∃ n, 1 ≤ n ∧ n ≤ xs.length ∧
        UnstoppedRecordedQueueComparison.replay_crosses_overflow q xs n := by
  classical
  by_cases h : ∃ n, 1 ≤ n ∧ n ≤ xs.length ∧
      UnstoppedRecordedQueueComparison.replay_crosses_overflow q xs n
  · have heq : UnstoppedRecordedQueueComparison.firstOverflowPrefix q xs = Nat.find h := by
      simp [UnstoppedRecordedQueueComparison.firstOverflowPrefix, h]
    rw [heq]
    constructor
    · intro _
      exact h
    · intro _
      exact Nat.find_spec h |>.2.1
  · have heq : UnstoppedRecordedQueueComparison.firstOverflowPrefix q xs = xs.length + 1 := by
      simp [UnstoppedRecordedQueueComparison.firstOverflowPrefix, h]
    rw [heq]
    constructor
    · intro hle
      omega
    · intro hex
      exact (h hex).elim

private theorem firstOverflowPrefix_le_of_crossing
    (q : RecordedQueueRun.Parameters) (xs : List Input) (n : ℕ)
    (hn : 1 ≤ n) (hnle : n ≤ xs.length)
    (hcross : UnstoppedRecordedQueueComparison.replay_crosses_overflow q xs n) :
    UnstoppedRecordedQueueComparison.firstOverflowPrefix q xs ≤ n := by
  classical
  let hex : ∃ k, 1 ≤ k ∧ k ≤ xs.length ∧
      UnstoppedRecordedQueueComparison.replay_crosses_overflow q xs k :=
    ⟨n, hn, hnle, hcross⟩
  have hmin := Nat.find_min' hex ⟨hn, hnle, hcross⟩
  simpa [UnstoppedRecordedQueueComparison.firstOverflowPrefix, hex] using hmin

private theorem replay_crossing_pos
    (q : RecordedQueueRun.Parameters) (xs : List Input) (n : ℕ)
    (hcross : UnstoppedRecordedQueueComparison.replay_crosses_overflow q xs n) :
    0 < n := by
  by_contra hn
  have hn0 : n = 0 := by omega
  subst n
  rcases hcross with ⟨a, h⟩
  simp [UnstoppedRecordedQueueComparison.unstoppedReplay,
    QueueReplay.replay] at h

private theorem firstOverflowPrefix_eq_length_add_one_of_no_crossing
    (q : RecordedQueueRun.Parameters) (xs : List Input)
    (h : ¬ ∃ n, 1 ≤ n ∧ n ≤ xs.length ∧
      UnstoppedRecordedQueueComparison.replay_crosses_overflow q xs n) :
    UnstoppedRecordedQueueComparison.firstOverflowPrefix q xs = xs.length + 1 := by
  classical
  simp [UnstoppedRecordedQueueComparison.firstOverflowPrefix, h]

private theorem actual_disabled_arrival_zero
    (L : List Input)
    (hL : L.length = (R).length)
    (hraw : ReferenceCompletePhysicalCalendarQueueTruth.physicalRawWord rate W =
      L.map (fun c => (c.enabled,
        RecordedQueueRun.quantizedArrival QP c)))
    (i : ℕ) (hi : i < L.length) (a : Fin p.K)
    (hdisabled : L[i].enabled = false) :
    RecordedQueueRun.quantizedArrival QP L[i] a = 0 := by
  let k : Fin (R).length := ⟨i, by omega⟩
  have hW : i < (W).length := by
    rw [ReferenceCompletePhysicalCalendarQueueTruth.actualPhysicalWord_length]
    exact k.isLt
  have hrawAt := congrArg (fun xs : List (Bool × (Fin p.K → ℕ)) => xs[i]?) hraw
  simp only [ReferenceCompletePhysicalCalendarQueueTruth.physicalRawWord,
    List.getElem?_map] at hrawAt
  rw [List.getElem?_eq_getElem hW, List.getElem?_eq_getElem hi] at hrawAt
  simp only [Option.map_some] at hrawAt
  have hpair := Option.some.inj hrawAt
  have hflag : (W[i]'hW).enabled = false := by
    have h := congrArg Prod.fst hpair
    exact h.trans hdisabled
  obtain ⟨_, hzero⟩ :=
    ReferenceCompletePhysicalCalendarQueueTruth.actualPhysicalWord_disabled
      rate rewards C_star C_h z k hflag
  have harr := congrArg (fun x : Bool × (Fin p.K → ℕ) => x.2 a) hpair
  exact harr.symm.trans (hzero a)

private theorem unstoppedRecord_map_eq_rawCalendar
    (L : List Input)
    (hzero : ∀ (i : ℕ) (hi : i < L.length) (a : Fin p.K),
      (L[i]'hi).enabled = false →
        RecordedQueueRun.quantizedArrival QP (L[i]'hi) a = 0)
    (a : Fin p.K) :
    L.map (fun c => UnstoppedRecordedQueueComparison.unstoppedRecord QP c a) =
      ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a L := by
  apply List.ext_getElem
  · simp [ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar]
  · intro i hi hj
    have hiL : i < L.length := by simpa only [List.length_map] using hi
    simp only [List.getElem_map,
      ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar]
    cases hflag : (L[i]'hiL).enabled
    · simp [UnstoppedRecordedQueueComparison.unstoppedRecord, hflag,
        hzero i hiL a hflag]
    · simp [UnstoppedRecordedQueueComparison.unstoppedRecord, hflag]

private theorem actual_source_replay_eq_unstopped
    (L : List Input)
    (hL : L.length = (R).length)
    (hraw : ReferenceCompletePhysicalCalendarQueueTruth.physicalRawWord rate W =
      L.map (fun c => (c.enabled,
        RecordedQueueRun.quantizedArrival QP c)))
    (hcalendar : ∀ h a,
      ReferenceCompletePhysicalCalendarQueueTruth.sourceCalendarReplay
          rate rewards C_star C_h z a h =
        ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L a h)
    (h : ℕ) (a : Fin p.K) :
    ReferenceCompletePhysicalCalendarQueueTruth.sourceCalendarReplay
        rate rewards C_star C_h z a h =
      UnstoppedRecordedQueueComparison.unstoppedReplay QP L h a := by
  have hzero : ∀ (i : ℕ) (hi : i < L.length) (arm : Fin p.K),
      (L[i]'hi).enabled = false →
        RecordedQueueRun.quantizedArrival QP (L[i]'hi) arm = 0 := by
    intro i hi arm hdisabled
    exact actual_disabled_arrival_zero rate rewards C_star C_h z L hL hraw i hi arm hdisabled
  have hmap := unstoppedRecord_map_eq_rawCalendar rate L hzero a
  rw [hcalendar h a]
  have htake :
      (L.take h).map
          (fun c => (c.enabled, RecordedQueueRun.quantizedArrival QP c a)) =
        (L.take h).map
          (fun c => UnstoppedRecordedQueueComparison.unstoppedRecord QP c a) := by
    have hh := congrArg (fun xs : List (Bool × ℕ) => xs.take h) hmap
    simpa only [List.map_take, ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar]
      using hh.symm
  change QueueReplay.replay (4 * rate.n) (0, 0)
      ((L.take h).map
        (fun c => (c.enabled, RecordedQueueRun.quantizedArrival QP c a))) =
    QueueReplay.replay (4 * (QP).n) (0, 0)
      ((L.take h).map
        (fun c => UnstoppedRecordedQueueComparison.unstoppedRecord QP c a))
  rw [htake]
  rfl


private theorem actual_launch_word_comparison
    (active : ReferenceActivePhysicalStep.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active) :
    ∃ L : List Input,
      L.length = (R).length ∧
      ReferenceCompletePhysicalCalendarQueueTruth.physicalRawWord rate W =
        L.map (fun c => (c.enabled, RecordedQueueRun.quantizedArrival QP c)) ∧
      (∀ h a, ReferenceCompletePhysicalCalendarQueueTruth.sourceCalendarReplay
          rate rewards C_star C_h z a h =
        ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L a h) ∧
      ∀ h a, ReferenceCompletePhysicalCalendarQueueTruth.sourceCalendarReplay
          rate rewards C_star C_h z a h =
        UnstoppedRecordedQueueComparison.unstoppedReplay QP L h a := by
  have hword := ReferenceCompletePhysicalCalendarQueueTruth.complete_physical_calendar_word
    rate rewards C_star C_h z
  rw [hlaunch] at hword
  rcases hword with ⟨L, hlen, _hmetadata, _hprefix, _hview, hraw, hcalendar⟩
  refine ⟨L, hlen, hraw, hcalendar, ?_⟩
  intro h a
  exact actual_source_replay_eq_unstopped rate rewards C_star C_h z L hlen hraw
    hcalendar h a

private theorem physical_event_iff_first_prefix
    (L : List Input) (hL : L.length = (R).length)
    (hraw : ReferenceCompletePhysicalCalendarQueueTruth.physicalRawWord rate W =
      L.map (fun c => (c.enabled, RecordedQueueRun.quantizedArrival QP c)))
    (hcalendar : ∀ h a,
      ReferenceCompletePhysicalCalendarQueueTruth.sourceCalendarReplay
          rate rewards C_star C_h z a h =
        ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L a h) :
    z ∈ physicalFirstOverflowEvent rate rewards C_star C_h ↔
      UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L ≤ L.length := by
  constructor
  · intro hevent
    change ∃ h, 1 ≤ h ∧ h ≤ (R).length ∧ ∃ a : Fin p.K,
      32 * (ReferenceCompletePhysicalCalendarQueueTruth.sourceCalendarReplay
        rate rewards C_star C_h z a h).2 > (QP).D at hevent
    rcases hevent with ⟨h, hpos, hbound, a, hqueue⟩
    have hReplay := actual_source_replay_eq_unstopped rate rewards C_star C_h z
      L hL hraw hcalendar h a
    have hcross : UnstoppedRecordedQueueComparison.replay_crosses_overflow QP L h := by
      refine ⟨a, ?_⟩
      rw [← hReplay]
      exact hqueue
    apply (firstOverflowPrefix_le_length_iff QP L).2
    exact ⟨h, hpos, by omega, hcross⟩
  · intro hfirst
    have hcross := UnstoppedRecordedQueueComparison.replay_crosses_overflow_at_first
      QP L hfirst
    rcases hcross with ⟨a, hqueue⟩
    have hbound : UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L ≤ (R).length := by
      omega
    have hReplay := actual_source_replay_eq_unstopped rate rewards C_star C_h z
      L hL hraw hcalendar
      (UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L) a
    refine ⟨UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L,
      UnstoppedRecordedQueueComparison.first_overflow_prefix_pos QP L, hbound, a, ?_⟩
    rw [hReplay]
    exact hqueue

private theorem observed_event_iff_first_prefix
    (L : List Input) (hL : L.length = (R).length)
    (hpref : ∀ h, h ≤ (R).length →
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + h) z = some (L.take h)) :
    z ∈ ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent
        rate rewards C_star C_h ↔
      UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L ≤ L.length := by
  constructor
  · intro hevent
    change ∃ n, n ≤ p.T ∧ ∃ o :
        ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h n z = some o ∧
      ∃ a : Fin p.K,
        ((o.1 a).2 : ℝ) / ((QP).n : ℝ) > 1 / (32 * rate.eta.val) at hevent
    rcases hevent with ⟨n, hnT, o, hread, a, hthreshold⟩
    have hinputsSome : ∃ cells,
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h n z = some cells := by
      unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout at hread
      cases hi : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h n z with
      | none => simp [hi] at hread
      | some cells => exact ⟨cells, rfl⟩
    obtain ⟨cells, hinputs⟩ := hinputsSome
    have hlaunchN := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
      rate rewards C_star C_h n z cells hinputs
    have hsle : s ≤ n := hlaunchN.2
    have hRlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate z rewards C_star C_h
    have hindex : n - s ≤ (R).length := by rw [hRlen]; omega
    have hindexL : n - s ≤ L.length := by
      calc
        n - s ≤ (R).length := hindex
        _ = L.length := hL.symm
    have hinputs' := hpref (n - s) hindex
    have hdate : s + (n - s) = n := by omega
    have hinputs'' : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h n z = some (L.take (n - s)) := by
      simpa only [hdate] using hinputs'
    have hread' : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h n z = some (stateReadout
          (RecordedQueueRun.run QP (L.take (n - s)))) := by
      simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
        hinputs'', Option.map_some]
    have ho : o = stateReadout (RecordedQueueRun.run QP (L.take (n - s))) :=
      Option.some.inj (hread.symm.trans hread')
    have hcmp := UnstoppedRecordedQueueComparison.prefix_state_comparison
      QP L (n - s) hindexL
    have hnorm : ((UnstoppedRecordedQueueComparison.unstoppedReplay QP L
          (min (n - s) (UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L)) a).2 : ℝ) /
        ((QP).n : ℝ) > 1 / (32 * rate.eta.val) := by
      rw [← hcmp.1 a]
      simpa only [ho, stateReadout] using hthreshold
    have hnormQ :
        ((UnstoppedRecordedQueueComparison.unstoppedReplay QP L
          (min (n - s) (UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L)) a).2 : ℝ) /
          ((QP).n : ℝ) > 1 / (32 * (QP).eta) := by
      simpa [ReferenceFirstLaunchNumericalCell.queueParameters] using hnorm
    have hcross := (UnstoppedRecordedQueueComparison.replay_crosses_overflow_iff_normalized
      QP L (min (n - s) (UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L))).2
        ⟨a, hnormQ⟩
    by_cases hH : UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L ≤ n - s
    · omega
    · have hlt : n - s < UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L :=
        Nat.lt_of_not_ge hH
      rw [Nat.min_eq_left (Nat.le_of_lt hlt)] at hcross
      have hnpos := replay_crossing_pos QP L (n - s) hcross
      have hnot := UnstoppedRecordedQueueComparison.not_replay_crosses_overflow_before_first
        QP L (n - s) (Nat.succ_le_of_lt hnpos) hindexL hlt
      exact (hnot hcross).elim
  · intro hfirst
    have hRlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate z rewards C_star C_h
    have hbound : UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L ≤ (R).length := by
      rw [← hL]
      exact hfirst
    have hLlenT : L.length = p.T - s := by rw [hL, hRlen]
    have hsT := ReferenceCompletePhysicalHistory.physicalStart_le_T
      rate z rewards C_star C_h
    have hdateBound : s + UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L ≤ p.T := by
      omega
    have hcross := UnstoppedRecordedQueueComparison.replay_crosses_overflow_at_first
      QP L hfirst
    have hnorm := (UnstoppedRecordedQueueComparison.replay_crosses_overflow_iff_normalized
      QP L (UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L)).1 hcross
    rcases hnorm with ⟨a, hthreshold⟩
    let H := UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L
    have hinputs := hpref H hbound
    have hread : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h (s + H) z = some (stateReadout
          (RecordedQueueRun.run QP (L.take H))) := by
      simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
        hinputs, Option.map_some]
    have hcmp := UnstoppedRecordedQueueComparison.prefix_state_comparison QP L H hfirst
    have hthreshold' :
        ((RecordedQueueRun.run QP (L.take H)).registers a).2 / ((QP).n : ℝ) >
          1 / (32 * rate.eta.val) := by
      have hregs := hcmp.1 a
      rw [hregs]
      simp only [H, Nat.min_self]
      simpa [ReferenceFirstLaunchNumericalCell.queueParameters] using hthreshold
    change ∃ n, n ≤ p.T ∧ ∃ o :
        ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h n z = some o ∧
      ∃ a : Fin p.K,
        ((o.1 a).2 : ℝ) / ((QP).n : ℝ) > 1 / (32 * rate.eta.val)
    exact ⟨s + H, hdateBound,
      stateReadout (RecordedQueueRun.run QP (L.take H)), hread, a, hthreshold'⟩

private theorem first_prefix_has_readout_crossing
    (L : List Input)
    (hL : L.length = (R).length)
    (hpref : ∀ h, h ≤ (R).length →
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + h) z = some (L.take h))
    (H : ℕ)
    (hH : H = UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L)
    (hbound : H ≤ L.length) :
    ∃ o : ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h (s + H) z = some o ∧
      ∃ a : Fin p.K,
        ((o.1 a).2 : ℝ) / ((QP).n : ℝ) > 1 / (32 * rate.eta.val) := by
  have hcross := UnstoppedRecordedQueueComparison.replay_crosses_overflow_at_first
    QP L (by simpa [hH] using hbound)
  have hnorm := (UnstoppedRecordedQueueComparison.replay_crosses_overflow_iff_normalized
    QP L H).1 (by simpa [hH] using hcross)
  rcases hnorm with ⟨a, hthreshold⟩
  have hRbound : H ≤ (R).length := by rw [← hL]; exact hbound
  have hinputs := hpref H hRbound
  have hread : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
      rate rewards C_star C_h (s + H) z = some (stateReadout
        (RecordedQueueRun.run QP (L.take H))) := by
    simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
      hinputs, Option.map_some]
  have hcmp := UnstoppedRecordedQueueComparison.prefix_state_comparison QP L H hbound
  have hthreshold' :
      ((RecordedQueueRun.run QP (L.take H)).registers a).2 / ((QP).n : ℝ) >
        1 / (32 * rate.eta.val) := by
    have hregs := hcmp.1 a
    rw [hregs]
    simp only [hH, Nat.min_self]
    have hthreshold' := hthreshold
    rw [hH] at hthreshold'
    simpa [ReferenceFirstLaunchNumericalCell.queueParameters] using hthreshold'
  exact ⟨stateReadout (RecordedQueueRun.run QP (L.take H)), hread, a, hthreshold'⟩

private theorem first_update_date_eq_first_prefix
    (L : List Input) (hL : L.length = (R).length)
    (hpref : ∀ h, h ≤ (R).length →
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + h) z = some (L.take h))
    (H : ℕ)
    (hH : H = UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L)
    (hbound : H ≤ L.length)
    (q : Fin p.T)
    (hq : z ∈ ReferenceOriginalNumericalFirstOverflowLocator.firstOverflowUpdateAt
      rate rewards C_star C_h q) :
    s ≤ q.val ∧ q.val - s + 1 = H := by
  rcases hq with ⟨Lq, r, c, a, _hinputs, hs, _hslt, hlenLq, hinputsNext,
    _hlookup, _htime, _hactualRecord, _hcell, _hphase, _hread, hreadNext,
    _hpriorFlag, _henabled, _hflag, hthreshold, _hprior, _hpresent,
    hleast, _htransition⟩
  change s ≤ q.val at hs
  have hlenLq' : Lq.length = q.val - s := by
    simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] using hlenLq
  let j := q.val + 1 - s
  have hjpos : 1 ≤ j := by dsimp [j]; omega
  have hRlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate z rewards C_star C_h
  have hjboundR : j ≤ (R).length := by
    dsimp [j]
    rw [hRlen]
    omega
  have hjboundL : j ≤ L.length := by
    calc
      j ≤ (R).length := hjboundR
      _ = L.length := hL.symm
  have hjdate : s + j = q.val + 1 := by dsimp [j]; omega
  have hinputsActual := hpref j hjboundR
  rw [hjdate] at hinputsActual
  have happend : Lq ++ [c] = L.take j :=
    Option.some.inj (hinputsNext.symm.trans hinputsActual)
  have hjlength : j = Lq.length + 1 := by
    dsimp [j]
    rw [hlenLq']
    omega
  have hreadActual : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
      rate rewards C_star C_h (q.val + 1) z = some (stateReadout
        (RecordedQueueRun.run QP (L.take j))) := by
    have hinputsAt := hinputsActual
    simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
      hinputsAt, Option.map_some]
  have hstateEq : stateReadout (RecordedQueueRun.run QP (L.take j)) =
      stateReadout (RecordedQueueRun.step QP (RecordedQueueRun.run QP Lq) c) :=
    Option.some.inj (hreadActual.symm.trans hreadNext)
  have hregs : (RecordedQueueRun.run QP (L.take j)).registers a =
      (RecordedQueueRun.step QP (RecordedQueueRun.run QP Lq) c).registers a := by
    have h := congrArg (fun o : ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K => o.1 a)
      hstateEq
    simpa only [stateReadout] using h
  have hthresholdRun :
      ((RecordedQueueRun.run QP (L.take j)).registers a).2 / ((QP).n : ℝ) >
        1 / (32 * rate.eta.val) := by
    have hthresholdStep :
        ((RecordedQueueRun.step QP (RecordedQueueRun.run QP Lq) c).registers a).2 /
          ((QP).n : ℝ) > 1 / (32 * rate.eta.val) := by
      simpa only [stateReadout] using hthreshold
    rw [hregs]
    exact hthresholdStep
  have hcmp := UnstoppedRecordedQueueComparison.prefix_state_comparison QP L j hjboundL
  have hnormQ :
      ((UnstoppedRecordedQueueComparison.unstoppedReplay QP L
        (min j (UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L)) a).2 : ℝ) /
        ((QP).n : ℝ) > 1 / (32 * (QP).eta) := by
    rw [← hcmp.1 a]
    simpa [ReferenceFirstLaunchNumericalCell.queueParameters] using hthresholdRun
  have hcross := (UnstoppedRecordedQueueComparison.replay_crosses_overflow_iff_normalized
    QP L (min j (UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L))).2
      ⟨a, hnormQ⟩
  have hfirst_le_j : H ≤ j := by
    by_cases hHj : H ≤ j
    · exact hHj
    · have hjltH : j < H := Nat.lt_of_not_ge hHj
      have hmin : min j (UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L) = j := by
        rw [← hH]
        exact Nat.min_eq_left (Nat.le_of_lt hjltH)
      rw [hmin] at hcross
      have hjltFirst : j < UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L := by
        simpa only [hH] using hjltH
      have hnot := UnstoppedRecordedQueueComparison.not_replay_crosses_overflow_before_first
        QP L j hjpos hjboundL hjltFirst
      exact (hnot hcross).elim
  have hfirst_least : j ≤ H := by
    by_contra hjH
    have hHltj : H < j := Nat.lt_of_not_ge hjH
    have hfirstReadout := first_prefix_has_readout_crossing rate rewards C_star C_h z
      L hL hpref H hH hbound
    have hdateEarlier : s + H < q.val + 1 := by
      dsimp [j] at hHltj
      omega
    exact (hleast (s + H) hdateEarlier) hfirstReadout
  have hjH : j = H := Nat.le_antisymm hfirst_least hfirst_le_j
  dsimp [j] at hjH
  exact ⟨hs, by omega⟩

private theorem completeSuffixRecord_time_at
    (k : Fin (R).length) :
    (R[k.val]).input.time.val = s + k.val := by
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have hRlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate z rewards C_star C_h
  have hcalLen :
      (ReferenceActivePhysicalHorizon.calendar s (p.T - s)).length = (R).length := by
    rw [ReferenceActivePhysicalHorizon.calendar, List.length_range', ← hRlen]
  have hcalendarIndex : k.val <
      (ReferenceActivePhysicalHorizon.calendar s (p.T - s)).length := by
    rw [hcalLen]
    exact k.isLt
  have hr := List.getElem?_eq_getElem k.isLt
  have hlookup := congrArg (fun xs : List ℕ => xs[k.val]?) htimes
  rw [List.getElem?_map, hr] at hlookup
  rw [List.getElem?_eq_getElem hcalendarIndex] at hlookup
  have hcaldate :
      (ReferenceActivePhysicalHorizon.calendar s (p.T - s))[k.val] = s + k.val := by
    simp only [ReferenceActivePhysicalHorizon.calendar, List.getElem_range'_1]
  rw [hcaldate] at hlookup
  exact Option.some.inj hlookup

/-- The integer physical event on the actual complete suffix is exactly the
original numerical detector event. The launch/no-launch split is discharged
from the actual source construction inside this theorem. -/
public theorem physicalFirstOverflowEvent_eq_observedNumericalOverflowEvent :
    physicalFirstOverflowEvent rate rewards C_star C_h =
      ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent
        rate rewards C_star C_h := by
  classical
  ext x
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate x rewards C_star C_h with
  | none =>
      have hword := ReferenceCompletePhysicalCalendarQueueTruth.complete_physical_calendar_word
        rate rewards C_star C_h x
      rw [hlaunch] at hword
      rcases hword with ⟨hW, hsT, habsent⟩
      have hWlen : (ReferenceCompletePhysicalCalendarQueueTruth.actualPhysicalWord
          rate rewards C_star C_h x).length = 0 := by rw [hW]; rfl
      have hRlen :
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate x rewards C_star C_h).length = 0 := by
        rw [← ReferenceCompletePhysicalCalendarQueueTruth.actualPhysicalWord_length rate rewards
          C_star C_h x]
        exact hWlen
      constructor
      · intro hevent
        change ∃ h, 1 ≤ h ∧ h ≤
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate x rewards C_star C_h).length ∧
          ∃ a : Fin p.K,
            32 * (ReferenceCompletePhysicalCalendarQueueTruth.sourceCalendarReplay
              rate rewards C_star C_h x a h).2 >
                (ReferenceFirstLaunchNumericalCell.queueParameters rate).D at hevent
        rcases hevent with ⟨h, hpos, hbound, a, hqueue⟩
        omega
      · intro hevent
        change ∃ n, n ≤ p.T ∧ ∃ o :
            ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K,
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
            rate rewards C_star C_h n x = some o ∧
          ∃ a : Fin p.K,
            ((o.1 a).2 : ℝ) /
              ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
                1 / (32 * rate.eta.val) at hevent
        rcases hevent with ⟨n, hn, o, hread, a, hthreshold⟩
        have hpref := habsent n
        unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout at hread
        rw [hpref] at hread
        cases hread
  | some active =>
      have hword := ReferenceCompletePhysicalCalendarQueueTruth.complete_physical_calendar_word
        rate rewards C_star C_h x
      rw [hlaunch] at hword
      rcases hword with ⟨L, hL, _hmetadata, hpref, _hview, hraw, hcalendar⟩
      have hphys := physical_event_iff_first_prefix rate rewards C_star C_h x
        L hL hraw hcalendar
      have hnum := observed_event_iff_first_prefix rate rewards C_star C_h x L hL hpref
      exact hphys.trans hnum.symm

/-- The same actual physical event is the terminal carried-energy threshold
event. This is deterministic and adds no tail probability estimate. -/
public theorem physicalFirstOverflowEvent_eq_terminalCarriedEnergy :
    physicalFirstOverflowEvent rate rewards C_star C_h =
      {z | ∃ a : Fin p.K,
        Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
          ReferenceOriginalCalendarCarriedStoppedEnergy.backlogCap rate) <
          ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
            rate rewards C_star C_h p.T a z} := by
  rw [physicalFirstOverflowEvent_eq_observedNumericalOverflowEvent]
  exact ReferenceOriginalCalendarCarriedStoppedEnergy.observedNumericalOverflowEvent_eq_terminalCarriedEnergy
    rate rewards C_star C_h

/-- Full deterministic first-crossing characterization on the actual original
source. In the launched branch, `H` is exactly the least physical integer
crossing. The whole actual suffix continues to be represented after `H`, while
the original numerical run is stopped at its inclusive detecting update. -/
public theorem actual_physical_first_overflow_characterization (x : SourceInput p) :
    match ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate x rewards C_star C_h with
    | none =>
        ReferenceCompletePhysicalCalendarQueueTruth.actualPhysicalWord
            rate rewards C_star C_h x = [] ∧
        ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h = p.T ∧
        (∀ n, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h n x = none) ∧
        x ∉ physicalFirstOverflowEvent rate rewards C_star C_h ∧
        x ∉ ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent
          rate rewards C_star C_h
    | some _ =>
        ∃ L : List Input, ∃ H : ℕ,
          L.length =
            (ReferenceCompletePhysicalHistory.completeSuffixRecords rate x rewards C_star C_h).length ∧
          H = UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L ∧
          (H ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate x rewards C_star C_h).length ↔
              x ∈ physicalFirstOverflowEvent rate rewards C_star C_h) ∧
          (H = (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate x rewards C_star C_h).length + 1 ↔
            x ∉ physicalFirstOverflowEvent rate rewards C_star C_h) ∧
          (∀ h, h ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate x rewards C_star C_h).length → ∀ a : Fin p.K,
            ReferenceCompletePhysicalCalendarQueueTruth.sourceCalendarReplay
              rate rewards C_star C_h x a (min h H) =
            (RecordedQueueRun.run QP (L.take h)).registers a) ∧
          (∀ k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate x rewards C_star C_h).length,
            let physical := (ReferenceCompletePhysicalCalendarQueueTruth.actualPhysicalWord
              rate rewards C_star C_h x).get
                ⟨k.val, by
                  rw [ReferenceCompletePhysicalCalendarQueueTruth.actualPhysicalWord_length]
                  exact k.isLt⟩
            ∃ c : Input,
              ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
                ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                  rate x rewards C_star C_h).get k) = some c ∧
              physical.record = (ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate x rewards C_star C_h).get k ∧
              physical.time = ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate x rewards C_star C_h).get k).input.time ∧
              physical.enabled = c.enabled ∧ physical.marker = c.recordedArm ∧
              physical.reward = c.reward ∧ physical.rateVector = c.rate ∧
              (∀ a, physical.marker = some a → ∃ owner : Fin p.m,
                physical.owns owner a ∧
                ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                  rate x rewards C_star C_h).get k).output.preparation.arms.actions owner = a ∧
                ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                  rate x rewards C_star C_h).get k).gridFeedback owner =
                  ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                    rate x rewards C_star C_h).get k).input.rewards
                    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                      rate x rewards C_star C_h).get k).input.time a) ∧
              (∀ a, physical.arrival a =
                RecordedQueueRun.quantizedArrival QP c a)) ∧
          (ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h = p.T →
            L = [] ∧
            ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
              rate rewards C_star C_h p.T x = some [] ∧ H = 1) ∧
          (H ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate x rewards C_star C_h).length →
            ∃ q : Fin p.T,
              q.val = ReferenceCompletePhysicalHistory.physicalStart
                rate x rewards C_star C_h + H - 1 ∧
              q.val + 1 = ReferenceCompletePhysicalHistory.physicalStart
                rate x rewards C_star C_h + H ∧
              x ∈ ReferenceOriginalNumericalFirstOverflowLocator.firstOverflowUpdateAt
                rate rewards C_star C_h q) := by
  classical
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate x rewards C_star C_h with
  | none =>
      have hword := ReferenceCompletePhysicalCalendarQueueTruth.complete_physical_calendar_word
        rate rewards C_star C_h x
      rw [hlaunch] at hword
      rcases hword with ⟨hW, hsT, habsent⟩
      have hWlen : (ReferenceCompletePhysicalCalendarQueueTruth.actualPhysicalWord
          rate rewards C_star C_h x).length = 0 := by rw [hW]; rfl
      have hRlen :
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate x rewards C_star C_h).length = 0 := by
        rw [← ReferenceCompletePhysicalCalendarQueueTruth.actualPhysicalWord_length rate rewards
          C_star C_h x]
        exact hWlen
      have hnoPhysical : x ∉ physicalFirstOverflowEvent rate rewards C_star C_h := by
        intro hevent
        change ∃ h, 1 ≤ h ∧ h ≤
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate x rewards C_star C_h).length ∧
          ∃ a : Fin p.K,
            32 * (ReferenceCompletePhysicalCalendarQueueTruth.sourceCalendarReplay
              rate rewards C_star C_h x a h).2 >
                (ReferenceFirstLaunchNumericalCell.queueParameters rate).D at hevent
        rcases hevent with ⟨h, hpos, hbound, a, hqueue⟩
        omega
      have hnoNumerical : x ∉
          ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent
            rate rewards C_star C_h := by
        intro hevent
        change ∃ n, n ≤ p.T ∧ ∃ o :
            ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K,
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
            rate rewards C_star C_h n x = some o ∧
          ∃ a : Fin p.K,
            ((o.1 a).2 : ℝ) /
              ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
                1 / (32 * rate.eta.val) at hevent
        rcases hevent with ⟨n, hn, o, hread, a, hthreshold⟩
        unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout at hread
        rw [habsent n] at hread
        cases hread
      exact ⟨hW, hsT, habsent, hnoPhysical, hnoNumerical⟩
  | some active =>
      have hword := ReferenceCompletePhysicalCalendarQueueTruth.complete_physical_calendar_word
        rate rewards C_star C_h x
      rw [hlaunch] at hword
      rcases hword with ⟨L, hL, _hmetadata, hpref, _hview, hraw, hcalendar⟩
      let H := UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L
      have hphysicalIff0 := physical_event_iff_first_prefix rate rewards C_star C_h x
        L hL hraw hcalendar
      have hphysicalIff : H ≤
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate x rewards C_star C_h).length ↔
            x ∈ physicalFirstOverflowEvent rate rewards C_star C_h := by
        constructor
        · intro hfinite
          have hfiniteL :
              UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L ≤ L.length := by
            simpa only [H, ← hL] using hfinite
          exact hphysicalIff0.mpr hfiniteL
        · intro hevent
          have hfiniteL := hphysicalIff0.mp hevent
          simpa only [H, hL] using hfiniteL
      have hnoCross : H = (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate x rewards C_star C_h).length + 1 ↔
            x ∉ physicalFirstOverflowEvent rate rewards C_star C_h := by
        constructor
        · intro hH hevent
          have hfinite := hphysicalIff.2 hevent
          rw [hH] at hfinite
          omega
        · intro hNoEvent
          have hNoFinite : ¬ H ≤
              (ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate x rewards C_star C_h).length := by
            intro hfinite
            exact hNoEvent (hphysicalIff.1 hfinite)
          have hNoCrossing : ¬ ∃ n, 1 ≤ n ∧ n ≤ L.length ∧
              UnstoppedRecordedQueueComparison.replay_crosses_overflow QP L n := by
            intro hex
            have hfinite := (firstOverflowPrefix_le_length_iff QP L).2 hex
            have hfiniteR : H ≤
                (ReferenceCompletePhysicalHistory.completeSuffixRecords
                  rate x rewards C_star C_h).length := by
              simpa only [H, hL] using hfinite
            exact hNoFinite hfiniteR
          have hHfirst := firstOverflowPrefix_eq_length_add_one_of_no_crossing
            QP L hNoCrossing
          calc
            H = UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L := rfl
            _ = L.length + 1 := hHfirst
            _ = (ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate x rewards C_star C_h).length + 1 := by rw [hL]
      refine ⟨L, H, hL, rfl, hphysicalIff, hnoCross, ?_, ?_, ?_, ?_⟩
      · intro h hh a
        have hleL : h ≤ L.length := by
          calc
            h ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate x rewards C_star C_h).length := hh
            _ = L.length := hL.symm
        have hstop := UnstoppedRecordedQueueComparison.prefix_state_comparison QP L h
          hleL
        have hphysical := actual_source_replay_eq_unstopped rate rewards C_star C_h x
          L hL hraw hcalendar (min h H) a
        calc
          ReferenceCompletePhysicalCalendarQueueTruth.sourceCalendarReplay
              rate rewards C_star C_h x a (min h H) =
              UnstoppedRecordedQueueComparison.unstoppedReplay QP L (min h H) a := hphysical
          _ = (RecordedQueueRun.run QP (L.take h)).registers a := (hstop.1 a).symm
      · intro k
        exact ReferenceCompletePhysicalCalendarQueueTruth.actualPhysicalWord_characterization
          rate rewards C_star C_h x k
      · intro hsT
        have hRlen :
            (ReferenceCompletePhysicalHistory.completeSuffixRecords rate x rewards C_star C_h).length = 0 := by
          rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length, hsT]
          simp
        have hLzero : L.length = 0 := by rw [hL, hRlen]
        have hnil : L = [] := List.eq_nil_of_length_eq_zero hLzero
        have hinputs := hpref 0 (by simp [hRlen])
        have hinputsT : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
            rate rewards C_star C_h p.T x = some [] := by
          simpa only [hsT, Nat.add_zero, List.take_zero] using hinputs
        have hpositive : 0 < H := by
          rw [show H = UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L by rfl]
          exact UnstoppedRecordedQueueComparison.first_overflow_prefix_pos QP L
        have hNoEvent : x ∉ physicalFirstOverflowEvent rate rewards C_star C_h := by
          intro hevent
          have hfinite := hphysicalIff.2 hevent
          rw [hRlen] at hfinite
          exact (not_le_of_gt hpositive) hfinite
        have hHone : H = 1 := by
          have h := (hnoCross).2 hNoEvent
          rw [hRlen] at h
          simpa using h
        exact ⟨hnil, hinputsT, hHone⟩
      · intro hfinite
        have hEvent := hphysicalIff.1 hfinite
        have hLfinite : H ≤ L.length := by
          calc
            H ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate x rewards C_star C_h).length := hfinite
            _ = L.length := hL.symm
        have hpositive : 0 < H := by
          rw [show H = UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L by rfl]
          exact UnstoppedRecordedQueueComparison.first_overflow_prefix_pos QP L
        let k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate x rewards C_star C_h).length := ⟨H - 1, by omega⟩
        let q : Fin p.T :=
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate x rewards C_star C_h).get k).input.time
        have hdate : q.val =
            ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h + H - 1 := by
          have htime : q.val =
              ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h + k.val :=
            completeSuffixRecord_time_at rate rewards C_star C_h x k
          dsimp only [k, Fin.val_mk] at htime
          omega
        have hObserved :=
          show x ∈ ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent
            rate rewards C_star C_h from by
              rw [← physicalFirstOverflowEvent_eq_observedNumericalOverflowEvent
                rate rewards C_star C_h]
              exact hEvent
        have hUnion : x ∈ ⋃ q' : Fin p.T,
            ReferenceOriginalNumericalFirstOverflowLocator.firstOverflowUpdateAt
              rate rewards C_star C_h q' := by
          rw [← ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent_eq_firstOverflowUpdateUnion
            rate rewards C_star C_h]
          exact hObserved
        obtain ⟨q', hq'⟩ := Set.mem_iUnion.mp hUnion
        have ⟨hqstart, hqdate⟩ := first_update_date_eq_first_prefix rate rewards C_star C_h x
          L hL hpref H rfl hLfinite q' hq'
        have hqval : q'.val =
            ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h + H - 1 := by
          omega
        have hqeq : q' = q := Fin.ext (by rw [hdate, hqval])
        have hmember : x ∈
            ReferenceOriginalNumericalFirstOverflowLocator.firstOverflowUpdateAt
              rate rewards C_star C_h q := by
          simpa [hqeq] using hq'
        have hpost : q.val + 1 =
            ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h + H := by
          omega
        exact ⟨q, hdate, hpost, hmember⟩

end Bandits.Support.ReferenceCompletePhysicalCalendarFirstCrossing

end
