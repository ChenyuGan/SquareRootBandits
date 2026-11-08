/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteInstallationCollectionPrefixNumericalTruth

import Mathlib.Tactic

/-!
# First numerical overflow observation on the original optional prefix

This module locates the first observed normalized backlog threshold in the
literal original-source optional prefix.  The detector retains the actual
dated physical record and its actual LIVE or COLLECTION numerical cell,
including the update that first sets the stopped-run overflow flag.  This is
only an observation event; it makes no claim about a physical error event,
physical-site inclusion, or a stochastic recorder bound.

Source evidence: ZIP4 `04_slow_fast_learner.tex:157-188,245-288`,
`06_interruptions.tex:355-426`, and
`appendix_a_local_protocol.tex:28-64` under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Bandits.Support ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput)
open ReferenceFirstCollectionRenewalIncomingQueueMeasurability (stateReadout)
open ReferenceSourcePrefixHistoryFiltration (actualLaunchBy actualRecord)
open scoped Classical

namespace Bandits.Support.ReferenceOriginalNumericalFirstOverflowLocator

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
local notation "Input" => RecordedQueueRun.RoundInput p.K
local notation "Readout" => ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K

private abbrev prefixReadoutAt
    (rate0 : ReferenceActivePhysicalStep.RateInput p)
    (rewards0 : ActualInitializationPhysicalStep.GridRewardTable p)
    (Cstar0 Ch0 : ℝ) (n : ℕ) (z : SourceInput p) :=
  ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
    rate0 rewards0 Cstar0 Ch0 n z

private abbrev prefixInputsAt
    (rate0 : ReferenceActivePhysicalStep.RateInput p)
    (rewards0 : ActualInitializationPhysicalStep.GridRewardTable p)
    (Cstar0 Ch0 : ℝ) (n : ℕ) (z : SourceInput p) :=
  ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
    rate0 rewards0 Cstar0 Ch0 n z

private abbrev sourceRecordsAt
    (rate0 : ReferenceActivePhysicalStep.RateInput p)
    (rewards0 : ActualInitializationPhysicalStep.GridRewardTable p)
    (Cstar0 Ch0 : ℝ) (z : SourceInput p) :=
  ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
    rate0 rewards0 Cstar0 Ch0 z

private abbrev sourceStartAt
    (rate0 : ReferenceActivePhysicalStep.RateInput p)
    (rewards0 : ActualInitializationPhysicalStep.GridRewardTable p)
    (Cstar0 Ch0 : ℝ) (z : SourceInput p) :=
  ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
    rate0 rewards0 Cstar0 Ch0 z
/-- The actual normalized-backlog threshold observed in a present original
optional prefix.  Missing inputs remain missing; this is not identified with
the manuscript's physical event `E_queue`. -/
@[expose] public def observedNumericalOverflowEvent
    (rate0 : ReferenceActivePhysicalStep.RateInput p)
    (rewards0 : ActualInitializationPhysicalStep.GridRewardTable p)
    (Cstar0 Ch0 : ℝ) : Set (SourceInput p) :=
  {z | ∃ n : ℕ, n ≤ p.T ∧ ∃ o : Readout,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
      rate0 rewards0 Cstar0 Ch0 n z = some o ∧
    ∃ a : Fin p.K,
      ((o.1 a).2 : ℝ) /
        (ReferenceFirstLaunchNumericalCell.queueParameters rate0).n >
          1 / (32 * rate0.eta.val)}

/-- A per-date witness to the first actual overflow update.  The earlier-prefix
condition is restricted to prefixes that are genuinely present, and the
presence interval ends at the detector. -/
@[expose] public def firstOverflowUpdateAt
    (rate0 : ReferenceActivePhysicalStep.RateInput p)
    (rewards0 : ActualInitializationPhysicalStep.GridRewardTable p)
    (Cstar0 Ch0 : ℝ) (q : Fin p.T) : Set (SourceInput p) :=
  {z | ∃ (L : List Input)
      (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate0))
      (c : Input) (a : Fin p.K),
    let s := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
      rate0 rewards0 Cstar0 Ch0 z
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate0 rewards0 Cstar0 Ch0 q.val z = some L ∧
    s ≤ q.val ∧ s < q.val + 1 ∧ L.length = q.val - s ∧
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate0 rewards0 Cstar0 Ch0 (q.val + 1) z = some (L ++ [c]) ∧
    (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
      rate0 rewards0 Cstar0 Ch0 z)[q.val - s]? = some r ∧ r.input.time = q ∧
    actualRecord rate0 rewards0 Cstar0 Ch0 q z = some r ∧
    ReferenceFirstCollectionCurrentRetainedGate.cell0 rate0 r = some c ∧
    (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c ∨
      (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = none ∧
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c)) ∧
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
      rate0 rewards0 Cstar0 Ch0 q.val z =
        some (stateReadout (RecordedQueueRun.run
          (ReferenceFirstLaunchNumericalCell.queueParameters rate0) L)) ∧
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
      rate0 rewards0 Cstar0 Ch0 (q.val + 1) z = some
      (stateReadout (RecordedQueueRun.step
        (ReferenceFirstLaunchNumericalCell.queueParameters rate0)
        (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate0) L) c)) ∧
    (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate0) L).overflow = false ∧ c.enabled = true ∧
    (RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate0)
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate0) L) c).overflow = true ∧
    (((stateReadout (RecordedQueueRun.step
        (ReferenceFirstLaunchNumericalCell.queueParameters rate0)
        (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate0) L) c)).1 a).2 : ℝ) /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate0).n : ℝ) >
          1 / (32 * rate0.eta.val) ∧
    (∀ k, s ≤ k → k ≤ q.val → ∀ Lk,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate0 rewards0 Cstar0 Ch0 k z = some Lk →
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate0) Lk).overflow = false) ∧
    (∀ k, s ≤ k → k ≤ q.val + 1 → ∃ Lk,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate0 rewards0 Cstar0 Ch0 k z = some Lk ∧ Lk.length = k - s) ∧
    (∀ m, m < q.val + 1 →
      ¬ ∃ o : Readout,
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
          rate0 rewards0 Cstar0 Ch0 m z = some o ∧
        ∃ a : Fin p.K, ((o.1 a).2 : ℝ) /
          ((ReferenceFirstLaunchNumericalCell.queueParameters rate0).n : ℝ) >
            1 / (32 * rate0.eta.val)) ∧
    (∀ i : Fin p.K,
      (RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate0)
        (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate0) L) c).registers i =
        QueueReplay.transition
          (4 * (ReferenceFirstLaunchNumericalCell.queueParameters rate0).n)
          ((RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate0) L).registers i)
          (RecordedQueueRun.acceptedRecord
            (ReferenceFirstLaunchNumericalCell.queueParameters rate0)
            (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate0) L) c i))}

private theorem mapM_id_eq_map_some {α : Type*} :
    ∀ {slots : List (Option α)} {cells : List α},
      slots.mapM id = some cells → slots = cells.map some := by
  intro slots
  induction slots with
  | nil =>
      intro cells h
      cases cells <;> simp [List.mapM_nil] at h ⊢
  | cons slot slots ih =>
      intro cells h
      cases slot with
      | none => simp [List.mapM_cons] at h
      | some cell =>
          cases ht : slots.mapM id with
          | none => simp [List.mapM_cons, ht] at h
          | some tail =>
              have hc : cell :: tail = cells := by
                simpa [List.mapM_cons, ht] using h
              cases hc
              have htail := ih ht
              simp [htail]

private theorem mapM_id_map_some {α : Type*} (cells : List α) :
    (cells.map some).mapM id = some cells := by
  induction cells with
  | nil => rfl
  | cons cell cells ih => simp [List.mapM_cons, ih]

private theorem prefixInputs_slots (n : ℕ) (z : X) (L : List Input)
    (hnT : n ≤ p.T)
    (hL : prefixInputsAt rate rewards C_star C_h n z = some L) :
    ((sourceRecordsAt rate rewards C_star C_h z).take
      (n - sourceStartAt rate rewards C_star C_h z)).map
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = L.map some := by
  let s := sourceStartAt rate rewards C_star C_h z
  let R := sourceRecordsAt rate rewards C_star C_h z
  have hlaunch :=
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
      rate rewards C_star C_h n z L hL
  have hlenR := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate z rewards C_star C_h
  have hlenR' : R.length = p.T - s := by
    simpa only [R, s, sourceRecordsAt, sourceStartAt,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] using hlenR
  have htakeN : n - s ≤ R.length := by
    rw [hlenR']
    omega
  have hmap : ((R.take (n - s)).map
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).mapM id = some L := by
    simpa only [prefixInputsAt, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
      if_pos hlaunch, R, s, sourceRecordsAt, sourceStartAt,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] using hL
  have hslots := mapM_id_eq_map_some hmap
  simpa only [R, s] using hslots

private theorem prefixInputs_from_present_full (n k : ℕ) (z : X)
    (hnT : n ≤ p.T) (hsk : sourceStartAt rate rewards C_star C_h z ≤ k) (hkn : k ≤ n)
    (L : List Input) (hL : prefixInputsAt rate rewards C_star C_h n z = some L) :
    ∃ Lk : List Input,
      prefixInputsAt rate rewards C_star C_h k z = some Lk ∧
      Lk = L.take (k - sourceStartAt rate rewards C_star C_h z) ∧
      Lk.length = k - sourceStartAt rate rewards C_star C_h z := by
  let s := sourceStartAt rate rewards C_star C_h z
  let R := sourceRecordsAt rate rewards C_star C_h z
  have hlaunch :=
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
      rate rewards C_star C_h n z L hL
  have hslots := prefixInputs_slots rate rewards C_star C_h n z L hnT hL
  have hlenR := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate z rewards C_star C_h
  have hlenR' : R.length = p.T - s := by
    simpa only [R, s, sourceRecordsAt, sourceStartAt,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] using hlenR
  have htakeN : n - s ≤ R.length := by rw [hlenR']; omega
  have hLlength : L.length = n - s := by
    have hlen := congrArg List.length hslots
    simp only [List.length_map] at hlen
    rw [List.length_take, Nat.min_eq_left htakeN] at hlen
    exact hlen.symm
  have hkslot : (R.take (k - s)).map
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) =
        ((R.take (n - s)).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).take (k - s) := by
    let f := ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
    calc
      (R.take (k - s)).map f = (R.take (min (k - s) (n - s))).map f := by
        rw [Nat.min_eq_left (by omega)]
      _ = ((R.take (n - s)).map f).take (k - s) := by
        rw [← List.map_take, List.take_take]
  have hmapK : ((R.take (k - s)).map
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).mapM id =
        some (L.take (k - s)) := by
    rw [hkslot, hslots]
    simpa only [List.map_take] using mapM_id_map_some (L.take (k - s))
  have hlaunchK : actualLaunchBy rate rewards C_star C_h k z :=
    ⟨hlaunch.1, hsk⟩
  have hprefixK : prefixInputsAt rate rewards C_star C_h k z =
      some (L.take (k - s)) := by
    simpa only [prefixInputsAt, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
      if_pos hlaunchK, R, s, sourceRecordsAt, sourceStartAt,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] using hmapK
  refine ⟨L.take (k - s), hprefixK, rfl, ?_⟩
  rw [List.length_take, Nat.min_eq_left (by rw [hLlength]; omega)]

private theorem sourceRecord_at_date (z : X) (s t : ℕ)
    (hs : s = sourceStartAt rate rewards C_star C_h z)
    (hst : s ≤ t) (htT : t < p.T) :
    ∃ r : Record, (sourceRecordsAt rate rewards C_star C_h z)[t - s]? =
      some r ∧ r.input.time.val = t := by
  let R := sourceRecordsAt rate rewards C_star C_h z
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate z rewards C_star C_h
  have hlenR : R.length = p.T - s := by
    have hlen' := hlen
    change (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards
      C_star C_h).length = p.T -
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h at hlen'
    simpa only [R, sourceRecordsAt, sourceStartAt,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart, hs] using hlen'
  have hi : t - s < R.length := by rw [hlenR]; omega
  have htimeMap := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have htime : R.map (fun r => r.input.time.val) =
      ReferenceActivePhysicalHorizon.calendar s (p.T - s) := by
    simpa only [R, sourceRecordsAt, sourceStartAt,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart, hs] using htimeMap
  let r : Record := R[t - s]
  have hr : R[t - s]? = some r := List.getElem?_eq_getElem hi
  have hiCal : t - s < (ReferenceActivePhysicalHorizon.calendar s (p.T - s)).length := by
    rw [ReferenceActivePhysicalHorizon.calendar, List.length_range']
    omega
  have htimeLookup := congrArg (fun xs : List ℕ => xs[t - s]?) htime
  rw [List.getElem?_map, hr] at htimeLookup
  rw [List.getElem?_eq_getElem hiCal] at htimeLookup
  have htimeRange :
      (ReferenceActivePhysicalHorizon.calendar s (p.T - s))[t - s] = s + (t - s) := by
    simpa only [ReferenceActivePhysicalHorizon.calendar, List.getElem_range'_1]
  rw [htimeRange] at htimeLookup
  have htimeValue : r.input.time.val = s + (t - s) :=
    Option.some.inj htimeLookup
  refine ⟨r, ?_, ?_⟩
  · simpa only [R, r] using hr
  · omega

private def numericalCrossing
    (rate0 : ReferenceActivePhysicalStep.RateInput p)
    (rewards0 : ActualInitializationPhysicalStep.GridRewardTable p)
    (Cstar0 Ch0 : ℝ) (n : ℕ) (z : SourceInput p) : Prop :=
  ∃ o : Readout,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
      rate0 rewards0 Cstar0 Ch0 n z = some o ∧
    ∃ a : Fin p.K,
      ((o.1 a).2 : ℝ) /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate0).n : ℝ) >
          1 / (32 * rate0.eta.val)

/-- The source launch is the only possible start of this initialized run. -/
private theorem no_threshold_at_launch (z : X) (s : ℕ)
    (hs : s = sourceStartAt rate rewards C_star C_h z)
    (hlaunch : actualLaunchBy rate rewards C_star C_h s z) :
    ¬ numericalCrossing rate rewards C_star C_h s z := by
  intro hcross
  rcases hcross with ⟨o, ho, a, hthreshold⟩
  have hlaunch' : actualLaunchBy rate rewards C_star C_h
      (sourceStartAt rate rewards C_star C_h z) z := by simpa only [hs] using hlaunch
  have hinputs : prefixInputsAt rate rewards C_star C_h s z = some [] := by
    rw [hs]
    simp only [prefixInputsAt, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
      if_pos hlaunch', Nat.sub_self, List.take_zero, List.map_nil,
      List.mapM_nil]
    rfl
  have hinputs' : prefixInputsAt rate rewards C_star C_h
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h z) z =
        some [] := by
    simpa only [hs] using hinputs
  have hobs : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
      rate rewards C_star C_h
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h z) z =
      some (stateReadout (RecordedQueueRun.run Q [])) := by
    simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
      hinputs', Option.map_some]
  rw [hs, hobs] at ho
  have ho' : o = stateReadout (RecordedQueueRun.run Q []) := Option.some.inj ho.symm
  have hregs : ((stateReadout (RecordedQueueRun.run Q [])).1 a).2 = 0 := by
    simp [stateReadout, RecordedQueueRun.run, RecordedQueueRun.execute,
      RecordedQueueRun.initialState]
  have heta : 0 < rate.eta.val := rate.eta.property
  have hpos : 0 < 1 / (32 * rate.eta.val) :=
    one_div_pos.mpr (by positivity)
  have hthreshold0 : (0 : ℝ) / ((Q).n : ℝ) > 1 / (32 * rate.eta.val) := by
    simpa only [ho', hregs, Nat.cast_zero] using hthreshold
  have hthreshold1 : (0 : ℝ) > 1 / (32 * rate.eta.val) := by
    simpa using hthreshold0
  exact (not_lt_of_ge (le_of_lt hpos)) hthreshold1

private theorem prefixReadout_present_inputs (n : ℕ) (z : X) (o : Readout)
    (ho : prefixReadoutAt rate rewards C_star C_h n z = some o) :
    ∃ L : List Input, prefixInputsAt rate rewards C_star C_h n z = some L ∧
      o = stateReadout (RecordedQueueRun.run Q L) := by
  unfold prefixReadoutAt ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout at ho
  cases hinputs : prefixInputsAt rate rewards C_star C_h n z with
  | none => simp [hinputs] at ho
  | some L =>
      simp only [hinputs, Option.map_some, Option.some.injEq] at ho
      refine ⟨L, ?_, ho.symm⟩
      simpa only [prefixInputsAt] using hinputs

/-- The first observed numerical threshold has one unique earliest date and
one actual adjacent source transition there.  Every prefix from launch through
the detector is reconstructed from the witnessed full `mapM` prefix; later
optional prefixes are unconstrained. -/
public theorem observedNumericalOverflowEvent_eq_firstOverflowUpdateUnion :
    observedNumericalOverflowEvent rate rewards C_star C_h =
      ⋃ q : Fin p.T, firstOverflowUpdateAt rate rewards C_star C_h q := by
  classical
  ext z
  constructor
  · intro hz
    change ∃ n : ℕ, n ≤ p.T ∧ ∃ o : Readout, prefixReadoutAt rate rewards C_star C_h n z = some o ∧
      ∃ a : Fin p.K,
        ((o.1 a).2 : ℝ) / ((Q).n : ℝ) > 1 / (32 * rate.eta.val) at hz
    rcases hz with ⟨n, hnT, o, ho, a, hthreshold⟩
    let hex : ∃ m, numericalCrossing rate rewards C_star C_h m z :=
      ⟨n, o, ho, a, hthreshold⟩
    let n0 := Nat.find hex
    have hcross0 : numericalCrossing rate rewards C_star C_h n0 z :=
      Nat.find_spec hex
    have hleast (m : ℕ) (hm : m < n0) :
        ¬ numericalCrossing rate rewards C_star C_h m z :=
      Nat.find_min hex hm
    have hn0le : n0 ≤ n := Nat.find_min' hex ⟨o, ho, a, hthreshold⟩
    have hn0T : n0 ≤ p.T := hn0le.trans hnT
    obtain ⟨o0, ho0, a0, hthreshold0⟩ := hcross0
    have hcrossAtN0 : numericalCrossing rate rewards C_star C_h n0 z :=
      ⟨o0, ho0, a0, hthreshold0⟩
    obtain ⟨Ln, hLn, _ho0run⟩ := prefixReadout_present_inputs
      rate rewards C_star C_h n0 z o0 ho0
    have hlaunch :=
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
        rate rewards C_star C_h n0 z Ln hLn
    let s := sourceStartAt rate rewards C_star C_h z
    have hlaunchS : actualLaunchBy rate rewards C_star C_h s z :=
      ⟨hlaunch.1, le_rfl⟩
    have hnoS : ¬ numericalCrossing rate rewards C_star C_h s z :=
      no_threshold_at_launch rate rewards C_star C_h z s rfl hlaunchS
    have hsn : s < n0 := by
      have hsourceLE : s ≤ n0 := by
        simpa only [s, sourceStartAt,
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] using hlaunch.2
      by_contra hnot
      have heq : n0 = s := by omega
      apply hnoS
      simpa only [heq] using hcrossAtN0
    let q : Fin p.T := ⟨n0 - 1, by omega⟩
    have hqdate : q.val = n0 - 1 := rfl
    have hqnext : q.val + 1 = n0 := by dsimp [q]; omega
    have hsQ : s ≤ q.val := by dsimp [q]; omega
    obtain ⟨L, hLq, _hLtake, hLlength⟩ :=
      prefixInputs_from_present_full rate rewards C_star C_h n0 q.val z
        hn0T hsQ (by omega) Ln hLn
    obtain ⟨r, hr, hrt⟩ := sourceRecord_at_date
      rate rewards C_star C_h z s q.val rfl hsQ q.isLt
    have hrtq : r.input.time = q := by
      apply Fin.ext
      dsimp only [q]
      omega
    have hactual : actualRecord rate rewards C_star C_h q z = some r := by
      change (if ReferenceCompletePhysicalHistory.physicalStart rate z rewards
          C_star C_h ≤ q.val then
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards
            C_star C_h)[q.val - ReferenceCompletePhysicalHistory.physicalStart
              rate z rewards C_star C_h]? else none) = some r
      rw [if_pos (by simpa only [s,
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] using hsQ)]
      simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart, s] using hr
    have hslots := prefixInputs_slots rate rewards C_star C_h n0 z Ln hn0T hLn
    have hlenR := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate z rewards C_star C_h
    have hlenR' : (sourceRecordsAt rate rewards C_star C_h z).length = p.T - s := by
      simpa only [sourceRecordsAt, sourceStartAt,
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart, s] using hlenR
    have htakeN : n0 - s ≤ (sourceRecordsAt rate rewards C_star C_h z).length := by
      rw [hlenR']
      omega
    have hlenLn : Ln.length = n0 - s := by
      have hlen := congrArg List.length hslots
      simp only [List.length_map] at hlen
      rw [List.length_take, Nat.min_eq_left htakeN] at hlen
      exact hlen.symm
    let ix := q.val - s
    have hixN : ix < n0 - s := by
      dsimp [ix]
      omega
    have hixR : ix < (sourceRecordsAt rate rewards C_star C_h z).length := by
      rw [hlenR']
      dsimp [ix]
      omega
    have hridx : (sourceRecordsAt rate rewards C_star C_h z)[ix] = r := by
      dsimp only [ix]
      exact (List.getElem?_eq_some_iff.mp hr).2
    have hixTake : ix < ((sourceRecordsAt rate rewards C_star C_h z).take (n0 - s)).length := by
      rw [List.length_take, Nat.min_eq_left htakeN]
      exact hixN
    have hrTake : ((sourceRecordsAt rate rewards C_star C_h z).take (n0 - s))[ix] = r := by
      simpa only [List.getElem_take, hridx]
    have hixLn : ix < Ln.length := by rw [hlenLn]; exact hixN
    have hslotActual? :
        (((sourceRecordsAt rate rewards C_star C_h z).take (n0 - s)).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate))[ix]? =
          some (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r) := by
      rw [List.getElem?_map]
      have hrTake? :
          ((sourceRecordsAt rate rewards C_star C_h z).take (n0 - s))[ix]? = some r :=
        (List.getElem?_eq_getElem hixTake).trans (congrArg some hrTake)
      rw [hrTake?]
      rfl
    have hslotFromLn? :
        (((sourceRecordsAt rate rewards C_star C_h z).take (n0 - s)).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate))[ix]? =
          some (some (Ln[ix]'hixLn)) := by
      have hslotsS :
          ((sourceRecordsAt rate rewards C_star C_h z).take (n0 - s)).map
            (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) =
            (List.map some Ln) := by simpa only [s] using hslots
      have hget := congrArg (fun xs : List (Option Input) => xs[ix]?) hslotsS
      simpa only [List.getElem?_map, List.getElem?_eq_getElem hixLn,
        Option.map_some] using hget
    let c : Input := Ln[ix]
    have hc : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
      have hslotsEq := hslotActual?.symm.trans hslotFromLn?
      have hcell : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r =
          some (Ln[ix]'hixLn) := Option.some.inj hslotsEq
      simpa only [c] using hcell
    have hnext :=
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_append_one
        rate rewards C_star C_h q.val z L hLq r c hr hc
    have hjoin : Ln = L ++ [c] := by
      apply Option.some.inj
      have hnextN0 : prefixInputsAt rate rewards C_star C_h n0 z = some (L ++ [c]) := by
        simpa only [hqnext] using hnext
      exact hLn.symm.trans hnextN0
    have hPq : prefixReadoutAt rate rewards C_star C_h q.val z =
        some (stateReadout (RecordedQueueRun.run Q L)) := by
      simp only [prefixReadoutAt, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
        hLq, Option.map_some]
    have hPnext : prefixReadoutAt rate rewards C_star C_h n0 z =
        some (stateReadout (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c)) := by
      have hnextN0 : prefixInputsAt rate rewards C_star C_h n0 z = some (L ++ [c]) := by
        simpa only [hqnext] using hnext
      simp only [prefixReadoutAt, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
        hnextN0, Option.map_some]
      rw [ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one]
    have hoeq : o0 =
        stateReadout (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c) := by
      exact Option.some.inj (ho0.symm.trans hPnext)
    have hthresholdStep :
      (((stateReadout (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c)).1 a0).2 : ℝ) /
          ((Q).n : ℝ) > 1 / (32 * rate.eta.val) := by
      rw [← hoeq]
      exact hthreshold0
    have hthresholdRun :
        StoppedQueueBound.normalizedBacklog Q
          (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c) a0 >
            1 / (32 * (Q).eta) := by
      simpa [StoppedQueueBound.normalizedBacklog,
        ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout,
        ReferenceFirstLaunchNumericalCell.queueParameters] using hthresholdStep
    have hcutoff :
        32 * ((RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c).registers a0).2 > (Q).D :=
      (StoppedQueueBound.normalized_backlog_gt_iff_cutoff Q
        (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c) a0).1 hthresholdRun
    have hrunNext : (RecordedQueueRun.run Q (L ++ [c])).overflow = true := by
      apply (StoppedQueueBound.run_overflow_iff_terminal_threshold Q (L ++ [c])).2
      refine ⟨a0, ?_⟩
      simpa only [ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one]
        using hthresholdRun
    have hstepFlag :
        (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c).overflow = true := by
      rw [ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one] at hrunNext
      exact hrunNext
    have hleastReadout (m : ℕ) (hm : m < n0) :
        ¬ ∃ o : Readout, prefixReadoutAt rate rewards C_star C_h m z = some o ∧ ∃ a : Fin p.K,
          ((o.1 a).2 : ℝ) / ((Q).n : ℝ) > 1 / (32 * rate.eta.val) := by
      exact hleast m hm
    have hpriorAll (k : ℕ) (hsk : s ≤ k) (hkq : k ≤ q.val)
        (Lk : List Input) (hLk : prefixInputsAt rate rewards C_star C_h k z = some Lk) :
        (RecordedQueueRun.run Q Lk).overflow = false := by
      cases hflag : (RecordedQueueRun.run Q Lk).overflow with
      | false => rfl
      | true =>
          obtain ⟨ak, hbacklog⟩ :=
            (StoppedQueueBound.run_overflow_iff_terminal_threshold Q Lk).1 hflag
          have hread : prefixReadoutAt rate rewards C_star C_h k z =
              some (stateReadout (RecordedQueueRun.run Q Lk)) := by
            simp only [prefixReadoutAt,
              ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
              hLk, Option.map_some]
          have htk :
              (((stateReadout (RecordedQueueRun.run Q Lk)).1 ak).2 : ℝ) /
                ((Q).n : ℝ) > 1 / (32 * rate.eta.val) := by
            simpa [StoppedQueueBound.normalizedBacklog,
              ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout,
              ReferenceFirstLaunchNumericalCell.queueParameters] using hbacklog
          have hkn : k < n0 := by rw [← hqnext]; omega
          exact False.elim (hleastReadout k hkn
            ⟨stateReadout (RecordedQueueRun.run Q Lk), hread, ak, htk⟩)
    have hprior : (RecordedQueueRun.run Q L).overflow = false :=
      hpriorAll q.val hsQ le_rfl L hLq
    have hstateInvariant :
        (RecordedQueueRun.run Q L).overflow = true ↔
          ∃ i : Fin p.K, 32 * ((RecordedQueueRun.run Q L).registers i).2 > (Q).D := by
      simpa only [StoppedQueueBound.normalized_backlog_gt_iff_cutoff] using
        (StoppedQueueBound.run_overflow_iff_terminal_threshold Q L)
    have hnoCutoff : ¬ ∃ i : Fin p.K,
        32 * ((RecordedQueueRun.run Q L).registers i).2 > (Q).D := by
      intro h
      have htrue := hstateInvariant.mpr h
      rw [hprior] at htrue
      cases htrue
    have henabled : c.enabled = true := by
      cases hcEnabled : c.enabled with
      | true => rfl
      | false =>
          have hstepCutoff := (RecordedQueueRun.step_overflow_iff_cutoff Q
            (RecordedQueueRun.run Q L) c hstateInvariant).1 hstepFlag
          obtain ⟨i, hi⟩ := hstepCutoff
          have hregs := (RecordedQueueRun.step_disabled_preserves Q
            (RecordedQueueRun.run Q L) c hcEnabled i).1
          exact False.elim (hnoCutoff ⟨i, by rw [hregs] at hi; exact hi⟩)
    have hphase :
        ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c ∨
        (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = none ∧
          ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c) := by
      unfold ReferenceFirstCollectionCurrentRetainedGate.cell0 at hc
      cases hlive : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r with
      | none =>
          have hcoll : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c := by
            simpa [hlive] using hc
          exact Or.inr ⟨rfl, hcoll⟩
      | some live =>
          have heq : live = c := Option.some.inj (by simpa [hlive] using hc)
          exact Or.inl (by simpa only [heq] using hlive)
    have hretains := RecordedQueueRun.step_retains_first_overflow_update Q
      (RecordedQueueRun.run Q L) c hprior hstepFlag
    have hpresent : ∀ k, s ≤ k → k ≤ q.val + 1 → ∃ Lk,
        prefixInputsAt rate rewards C_star C_h k z = some Lk ∧ Lk.length = k - s := by
      intro k hsk hkn
      obtain ⟨Lk, hLk, _hTake, hlength⟩ :=
        prefixInputs_from_present_full rate rewards C_star C_h n0 k z
          hn0T hsk (by rw [hqnext] at hkn; exact hkn) Ln hLn
      exact ⟨Lk, hLk, hlength⟩
    have hupdateLeast : ∀ m, m < q.val + 1 →
        ¬ ∃ o : Readout, prefixReadoutAt rate rewards C_star C_h m z = some o ∧ ∃ a : Fin p.K,
          ((o.1 a).2 : ℝ) / ((Q).n : ℝ) > 1 / (32 * rate.eta.val) := by
      intro m hm
      exact hleastReadout m (by simpa only [hqnext] using hm)
    have htransition := hretains.2
    refine Set.mem_iUnion.mpr ⟨q, ?_⟩
    simp only [firstOverflowUpdateAt, Set.mem_setOf_eq]
    refine ⟨L, r, c, a0, ?_⟩
    exact ⟨hLq, hsQ, by rw [hqnext]; exact hsn, hLlength,
      by simpa only [hqnext] using hnext, hr, hrtq, hactual, hc,
      hphase, hPq, by simpa only [hqnext] using hPnext, hprior, henabled,
      hstepFlag, hthresholdStep, hpriorAll, hpresent, hupdateLeast, htransition⟩
  · intro hz
    rw [Set.mem_iUnion] at hz
    obtain ⟨q, hq⟩ := hz
    simp only [firstOverflowUpdateAt, Set.mem_setOf_eq] at hq
    rcases hq with ⟨L, r, c, a, _hL, _hs, _hslt, _hlen, _hnext, _hr, _htime, _hactual,
      _hcell, _hphase, _hPq, hPnext, _hprior, _henabled, _hflag, hthreshold,
      _hearlier, _hpresent, _hleast, _htransition⟩
    change ∃ n : ℕ, n ≤ p.T ∧ ∃ o : Readout, prefixReadoutAt rate rewards C_star C_h n z = some o ∧
      ∃ a : Fin p.K,
        ((o.1 a).2 : ℝ) / ((Q).n : ℝ) > 1 / (32 * rate.eta.val)
    refine ⟨q.val + 1, ?_, stateReadout
      (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c), hPnext, a, ?_⟩
    · omega
    · exact hthreshold

/-- The observation event is Borel on the original source space.  Each
fixed-date readout is measured by the existing stopped-energy telescope API;
only countable readouts and dates are unioned here. -/
public theorem measurableSet_observedNumericalOverflowEvent :
    MeasurableSet (observedNumericalOverflowEvent rate rewards C_star C_h) := by
  have hrepresentation : observedNumericalOverflowEvent rate rewards C_star C_h =
      ⋃ n : ℕ, ⋃ o : Readout, ⋃ a : Fin p.K,
        if n ≤ p.T ∧
          ((o.1 a).2 : ℝ) / ((Q).n : ℝ) > 1 / (32 * rate.eta.val)
        then {z | prefixReadoutAt rate rewards C_star C_h n z = some o} else ∅ := by
    ext z
    constructor
    · intro hz
      change ∃ n : ℕ, n ≤ p.T ∧ ∃ o : Readout, prefixReadoutAt rate rewards C_star C_h n z = some o ∧
        ∃ a : Fin p.K,
          ((o.1 a).2 : ℝ) / ((Q).n : ℝ) > 1 / (32 * rate.eta.val) at hz
      rcases hz with ⟨n, hn, o, ho, a, hthreshold⟩
      refine Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨o,
        Set.mem_iUnion.mpr ⟨a, ?_⟩⟩⟩
      rw [if_pos ⟨hn, hthreshold⟩]
      exact ho
    · intro hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨n, hz⟩ := hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨o, hz⟩ := hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨a, hz⟩ := hz
      split_ifs at hz with htest
      · exact ⟨n, htest.1, o, hz, a, htest.2⟩
      · exact (Set.notMem_empty z hz).elim
  rw [hrepresentation]
  refine MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun o =>
    MeasurableSet.iUnion fun a => ?_
  split_ifs with htest
  · exact (ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_prefixReadout
      rate rewards C_star C_h n) (measurableSet_singleton (some o))
  · exact MeasurableSet.empty

end Bandits.Support.ReferenceOriginalNumericalFirstOverflowLocator

end
