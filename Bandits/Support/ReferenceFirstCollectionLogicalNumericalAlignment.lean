/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstNextInvocationJointLift

import Mathlib.Tactic

/-!
# Numerical provenance of the generated first-collection history

The numerical word is the unique complete word of the original physical
source. Calendar dates, rather than the number of generated logical cells,
index its stopped queue run. Disabled collection dates remain in every arm's
accepted-record array.

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215`, and `08_main_theorem.tex:78-109`.
These are internal deterministic alignment results, not a manuscript closure.
-/

@[expose] public section

noncomputable section

open scoped Classical
open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceActualCollectionHiddenRefreshPath
open ReferenceFirstLaunchNumericalCell (queueParameters)
open ReferenceCompletePhysicalHistory (physicalStart completeSuffixRecords)
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix (prefixInputs)
open ReferenceFirstCollectionLogicalPrefixExtension
open ReferenceFirstCollectionOneRoundLogicalCell (actualPast actualPast_spec actualInput
  actualInput_spec firstCollection)
open ReferenceLaterCollectionSourceReadoutMeasurability (numericalCoordinates)

namespace Bandits.Support.ReferenceFirstCollectionLogicalNumericalAlignment

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

local instance sourceMeasurableSpace : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local notation "Q" => queueParameters rate
local notation "start " z:max => physicalStart rate z rewards C_star C_h
local notation "records " z:max => completeSuffixRecords rate z rewards C_star C_h
local notation "liveWord " z:max =>
  ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z
local notation "liveCells " za:max => firstLiveChronologicalPrefix rate rewards C_star C_h za
local notation "stateAt" => extendedPrefixStateAux rate rewards C_star C_h

/-- The actual first call fixes the original launch and the cutoff date. -/
theorem firstCall_dates (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t) :
    start z ≤ u.val ∧ u.val < t.val ∧
      collectionStart rate rewards C_star C_h z = u.val ∧
      (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing.isSome = true := by
  obtain ⟨hc, _hs, _hshort, _f, _head, _valid, _D, _L, hsu, hut, hu, _⟩ :=
    ReferenceFirstCollectionCurrentRetainedGate.firstCell_prefix_coverage
      rate rewards C_star C_h u t z hz
  exact ⟨hsu, hut, hu.symm, hc⟩

/-- No launch witness is an input to the alignment. It is produced from the
genuine first-invocation event. -/
theorem firstCall_launch (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t) :
    ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active := by
  have hc := (firstCall_dates rate rewards C_star C_h u t z hz).2.2.2
  have his := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate z rewards C_star C_h).2 hc
  cases h : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none => simp only [h, Option.isSome_none, Bool.false_eq_true] at his
  | some active => exact ⟨active, rfl⟩

/-- Every genuine calendar boundary reads a prefix of the same unique word. -/
theorem originalWord_calendar_prefix (z : SourceInput p)
    (hlaunch : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active)
    (n : Fin (p.T + 1)) (hsn : start z ≤ n.val) :
    let W := actualOriginalWord rate rewards C_star C_h z hlaunch
    W.length = p.T - start z ∧ n.val - start z ≤ W.length ∧
      prefixInputs rate rewards C_star C_h n.val z = some (W.take (n.val - start z)) := by
  have hlen := actualOriginalWord_length rate rewards C_star C_h z hlaunch
  rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] at hlen
  have hn : n.val - start z ≤ (records z).length := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    exact Nat.sub_le_sub_right (Nat.le_of_lt_succ n.isLt) _
  refine ⟨hlen, by rw [hlen]; exact Nat.sub_le_sub_right (Nat.le_of_lt_succ n.isLt) _, ?_⟩
  have hp := actualOriginalWord_prefix rate rewards C_star C_h z hlaunch
    (n.val - start z) hn
  simpa only [Nat.add_sub_of_le hsn] using hp

/-- The complete word's cells are the actual original record readouts.
This also identifies the unique word used by the global presence producer. -/
theorem originalWord_record_map (z : SourceInput p)
    (hlaunch : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active) :
    (records z).map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) =
      (actualOriginalWord rate rewards C_star C_h z hlaunch).map some := by
  have hc := ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_cells
    rate rewards C_star C_h z
  rw [Classical.choose_spec hlaunch] at hc
  obtain ⟨L, hlen, hmap, hp, _⟩ := hc
  have hfull := hp (records z).length le_rfl
  have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  have hdate : start z + (records z).length = p.T := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    omega
  rw [hdate, ← hlen, List.take_length] at hfull
  have hLW : L = actualOriginalWord rate rewards C_star C_h z hlaunch :=
    Option.some.inj (hfull.symm.trans (actualOriginalWord_spec rate rewards C_star C_h z hlaunch))
  simpa only [hLW] using hmap

/-- Public actual-prefix and actual-input producers identify collection
cells with the same original word, without an extra supplied history. -/
theorem originalWord_collection_data (z : SourceInput p)
    (hlaunch : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active)
    (q : Fin p.T) (r : Record rate)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r)
    (hm : r ∈ firstCollection (rate := rate) rewards C_star C_h z) :
    let W := actualOriginalWord rate rewards C_star C_h z hlaunch
    ∃ hk : q.val - start z < W.length,
      start z ≤ q.val ∧ r.input.time = q ∧
      actualPast rewards C_star C_h z q r hr hm = W.take (q.val - start z) ∧
      actualInput rewards C_star C_h z q r hr hm = W[q.val - start z]'hk := by
  have hstart := collectionStart_le_of_actualDomain rate rewards C_star C_h q z ⟨r, hr, hm⟩
  have hsq : start z ≤ q.val := by
    dsimp only [collectionStart] at hstart
    omega
  let W := actualOriginalWord rate rewards C_star C_h z hlaunch
  have hmap := originalWord_record_map rate rewards C_star C_h z hlaunch
  have hlookup : (records z)[q.val - start z]? = some r := by
    simpa only [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hsq] using hr
  obtain ⟨hkR, _⟩ := List.getElem?_eq_some_iff.mp hlookup
  have hk : q.val - start z < W.length := by
    rw [actualOriginalWord_length]
    exact hkR
  have hp := (originalWord_calendar_prefix rate rewards C_star C_h z hlaunch
    q.castSucc hsq).2.2
  simp only [Fin.val_castSucc] at hp
  rw [ReferenceFirstCollectionCorrectedFutureRetainedMoment.prefixInputs_eq_pastCells,
    actualPast_spec rewards C_star C_h z q r hr hm] at hp
  have he := congrArg (fun xs => xs[q.val - start z]?) hmap
  rw [List.getElem?_map, hlookup, Option.map_some, actualInput_spec rewards C_star C_h z q r hr hm,
    List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some] at he
  obtain ⟨_call, htime, _⟩ :=
    ReferenceFirstCollectionOneRoundLogicalCell.actual_data rewards C_star C_h z q r hr hm
  exact ⟨hk, hsq, htime, Option.some.inj hp, Option.some.inj (Option.some.inj he)⟩

/-- The literal first-LIVE numerical word is the initial segment of the
same original word. The collection head is outside this segment. -/
theorem firstCall_liveWord (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t) :
    let hlaunch := firstCall_launch rate rewards C_star C_h u t z hz
    liveWord z = (actualOriginalWord rate rewards C_star C_h z hlaunch).take (u.val - start z) := by
  obtain ⟨hc, _hs, _hshort, _f, _head, _valid, D, L, hsu, hut, hu,
    _htotal, _hpending, _hrecord, _hchoice, _hDlen, _hhead, _hslots, hsplit, hL, _⟩ :=
    ReferenceFirstCollectionCurrentRetainedGate.firstCell_prefix_coverage
      rate rewards C_star C_h u t z hz
  let W := actualOriginalWord rate rewards C_star C_h z
    (firstCall_launch rate rewards C_star C_h u t z hz)
  have hc' : (ReferenceCompletePhysicalHistory.generatedBoundary
      rate z rewards C_star C_h).crossing.isSome = true := hc
  have hv : liveWord z ++ D = L := by
    simpa only [ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells,
      dite_eq_left hc'] using hsplit.symm
  have hp := (originalWord_calendar_prefix rate rewards C_star C_h z
    (firstCall_launch rate rewards C_star C_h u t z hz) t.castSucc (hsu.trans hut.le)).2.2
  simp only [Fin.val_castSucc] at hp
  rw [ReferenceFirstCollectionCorrectedFutureRetainedMoment.prefixInputs_eq_pastCells, hL] at hp
  have hLW : L = W.take (t.val - start z) := Option.some.inj hp
  have hVlen : (liveWord z).length = u.val - start z := by
    rw [wholeFirstLiveCells_length]
    change u.val = start z +
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z).length at hu
    omega
  have htake := congrArg (fun xs => xs.take (u.val - start z)) (hv.trans hLW)
  rw [← hVlen, List.take_left] at htake
  rw [List.take_take, hVlen, Nat.min_eq_left (Nat.sub_le_sub_right hut.le _)] at htake
  exact htake

/-- The real launch has an empty generated logical history. -/
theorem firstCall_generatedPast_at_launch (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :
    extendedPast rate rewards C_star C_h
      ⟨start z, Nat.lt_succ_of_le (ReferenceCompletePhysicalHistory.physicalStart_le_T
        rate z rewards C_star C_h)⟩ (z, a) = [] := by
  have hd := firstCall_dates rate rewards C_star C_h u t z hz
  have h := extendedPrefixStateAux_before_collectionStart rate rewards C_star C_h
    (start z) (ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h)
    z a (by rw [hd.2.2.1]; exact hd.1)
  simpa only [extendedPast,
    ReferenceFirstLiveChronologicalPrefixCausality.calendarPast_eq_take_elapsed,
    Nat.sub_self, List.take_zero] using h

private theorem live_cell_time (z : SourceInput p)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (k : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z).length) :
    ((liveCells (z, a))[k.val]'(by rw [firstLiveChronologicalPrefix_length]; exact k.isLt)).time.val =
      start z + k.val := by
  rw [ReferenceFirstLiveChronologicalPrefixCausality.firstLiveChronologicalPrefix_cellTime]
  have hp : ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z <+: records z := List.takeWhile_prefix _
  have hkR := k.isLt.trans_le hp.length_le
  have hr : (records z)[k.val]? = some
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z)[k.val] := by
    rw [List.getElem?_eq_getElem hkR, ← hp.getElem k.isLt]
  exact ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate z rewards C_star C_h k.val _ hr

/-- Full numerical alignment of a LIVE entry with its original calendar
word entry, including all-arm accepted arrivals and service. -/
theorem firstCall_live_cell_data (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (k : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z).length) :
    let W := actualOriginalWord rate rewards C_star C_h z
      (firstCall_launch rate rewards C_star C_h u t z hz)
    let e := (liveCells (z, a))[k.val]'(by rw [firstLiveChronologicalPrefix_length]; exact k.isLt)
    ∃ hk : k.val < W.length,
      e.time.val = start z + k.val ∧ e.time.val < u.val ∧
      e.numerical = numericalCoordinates W[k.val] ∧
      e.before = RecordedQueueRun.run Q (W.take k.val) ∧
      e.after = RecordedQueueRun.run Q (W.take (k.val + 1)) ∧
      e.arrivals = RecordedQueueRun.acceptedRecord Q e.before W[k.val] ∧
      e.service = (fun j => RecordedQueueRun.recordService (4 * (Q).n)
        (e.before.registers j) (e.arrivals j)) ∧
      ∀ j, e.service j ≤ 4 * (Q).n ∧ e.after.registers j =
        QueueReplay.transition (4 * (Q).n) (e.before.registers j) (e.arrivals j) := by
  dsimp only
  let W := actualOriginalWord rate rewards C_star C_h z
    (firstCall_launch rate rewards C_star C_h u t z hz)
  have hd := firstCall_dates rate rewards C_star C_h u t z hz
  have hw : (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z).length = u.val - start z := by
    have h := hd.2.2.1
    change start z + (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z).length = u.val at h
    omega
  have hkw : k.val < u.val - start z := by rw [← hw]; exact k.isLt
  have hWlen := (originalWord_calendar_prefix rate rewards C_star C_h z
    (firstCall_launch rate rewards C_star C_h u t z hz) u.castSucc hd.1).2.1
  have hk : k.val < W.length := hkw.trans_le hWlen
  have hv := firstCall_liveWord rate rewards C_star C_h u t z hz
  have htake (m : ℕ) (hm : m ≤ u.val - start z) :
      (liveWord z).take m = W.take m := by
    rw [hv, List.take_take, Nat.min_eq_left hm]
  have hround : (liveWord z)[k.val]'(by rw [wholeFirstLiveCells_length]; exact k.isLt) = W[k.val] := by
    simp only [hv, List.getElem_take]
    rfl
  have htime := live_cell_time rate rewards C_star C_h z a k
  have hstates := firstLiveChronologicalPrefix_queue_states rate rewards C_star C_h z a k
  dsimp only at hstates
  rw [htake _ hkw.le, htake _ (by omega)] at hstates
  have hnumerical := congrArg (fun L => L[k.val]?)
    (firstLiveChronologicalPrefix_numerical rate rewards C_star C_h z a)
  simp only [ReferenceFirstLiveOverflowReadout.wholeFirstLiveCellReadout,
    List.getElem?_map, List.getElem?_eq_getElem (show k.val < (liveCells (z, a)).length by
      rw [firstLiveChronologicalPrefix_length]; exact k.isLt),
    List.getElem?_eq_getElem (show k.val < (liveWord z).length by
      rw [wholeFirstLiveCells_length]; exact k.isLt), Option.map_some] at hnumerical
  have hnum := Option.some.inj hnumerical
  rw [hround] at hnum
  have hall := firstLiveChronologicalPrefix_all_arm_update rate rewards C_star C_h z a k
  dsimp only at hall
  rw [hround] at hall
  refine ⟨hk, htime, by omega, hnum, hstates.1, hstates.2, ?_, ?_, ?_⟩
  · funext j
    exact (hall j).1
  · funext j
    exact (hall j).2.1
  · intro j
    exact (hall j).2.2

private theorem run_disabled_step
    (L : List (RecordedQueueRun.RoundInput p.K))
    (c : RecordedQueueRun.RoundInput p.K) (hc : c.enabled = false) :
    let S := RecordedQueueRun.run Q L
    (RecordedQueueRun.step Q S c).registers = S.registers ∧
      (RecordedQueueRun.step Q S c).overflow = S.overflow ∧
      ∀ j, (RecordedQueueRun.step Q S c).records j = S.records j ++ [(false, 0)] := by
  dsimp only
  have hh := ReferenceFirstCollectionRenewalFutureNumericalPrefix.disabled_step_registers_and_records
    rate (RecordedQueueRun.run Q L) c hc
  refine ⟨hh.1, ?_, fun j => congrFun hh.2 j⟩
  apply Bool.eq_iff_iff.mpr
  have hafter := RecordedQueueRun.run_overflow_iff_cutoff Q (L ++ [c])
  rw [RecordedSlowRefresh.run_append_singleton, hh.1] at hafter
  exact hafter.trans (RecordedQueueRun.run_overflow_iff_cutoff Q L).symm

private theorem disabled_interval_completion
    (W : List (RecordedQueueRun.RoundInput p.K)) (m n : ℕ)
    (hmn : m ≤ n) (hn : n ≤ W.length)
    (hdisabled : ∀ k (hk : k < W.length), m ≤ k → k < n → W[k].enabled = false) :
    let A := RecordedQueueRun.run Q (W.take m)
    let B := RecordedQueueRun.run Q (W.take n)
    B.registers = A.registers ∧ B.overflow = A.overflow ∧
      ∀ j, B.records j = A.records j ++ List.replicate (n - m) (false, 0) := by
  revert hn hdisabled
  induction hmn with
  | refl =>
      intro _ _
      exact ⟨rfl, rfl, fun j => by simp only [Nat.sub_self, List.replicate_zero, List.append_nil]⟩
  | @step n hmn ih =>
      intro hn hdisabled
      have hk : n < W.length := by omega
      have hi := ih (by omega) (fun k hk hmk hkn => hdisabled k hk hmk (by omega))
      have hs := run_disabled_step rate (W.take n) W[n] (hdisabled n hk hmn (by omega))
      dsimp only at hi hs ⊢
      rw [← List.take_append_getElem hk, RecordedSlowRefresh.run_append_singleton]
      refine ⟨hs.1.trans hi.1, hs.2.1.trans hi.2.1, ?_⟩
      intro j
      rw [hs.2.2 j, hi.2.2 j, List.append_assoc]
      have hd : n + 1 - m = (n - m) + 1 := Nat.sub_add_comm hmn
      rw [hd, List.replicate_succ']

private theorem live_prefix_chronology (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (n : ℕ) (hn : n ≤ p.T) (hnu : n ≤ u.val) :
    let H := (stateAt n hn (z, a)).2
    H.Pairwise (fun e f => e.time.val < f.time.val) ∧
      (∀ e ∈ H, start z ≤ e.time.val ∧ e.time.val < n) ∧
      ∀ q : Fin p.T, start z ≤ q.val → q.val < n → ∃ e ∈ H, e.time = q := by
  have hd := firstCall_dates rate rewards C_star C_h u t z hz
  have hlist := extendedPrefixStateAux_before_collectionStart rate rewards C_star C_h
    n hn z a (by rw [hd.2.2.1]; exact hnu)
  rw [ReferenceFirstLiveChronologicalPrefixCausality.calendarPast_eq_take_elapsed] at hlist
  dsimp only
  rw [hlist]
  have hlen : (liveCells (z, a)).length = u.val - start z := by
    rw [firstLiveChronologicalPrefix_length]
    have h := hd.2.2.1
    change start z + ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength
      rate rewards C_star C_h z = u.val at h
    change ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength
      rate rewards C_star C_h z = u.val - start z
    omega
  have htime (k : ℕ) (hk : k < (liveCells (z, a)).length) :
      ((liveCells (z, a))[k]).time.val = start z + k :=
    live_cell_time rate rewards C_star C_h z a
      ⟨k, by simpa only [firstLiveChronologicalPrefix_length,
        ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hk⟩
  refine ⟨?_, ?_, ?_⟩
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have hi' : i < (liveCells (z, a)).length := by
      simp only [List.length_take] at hi
      omega
    have hj' : j < (liveCells (z, a)).length := by
      simp only [List.length_take] at hj
      omega
    simp only [List.getElem_take, htime i hi', htime j hj']
    omega
  · intro e he
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp he
    have hk' : k < (liveCells (z, a)).length := by
      simp only [List.length_take] at hk
      omega
    have hkn : k < n - start z := by
      simp only [List.length_take] at hk
      omega
    simp only [List.getElem_take, htime k hk']
    omega
  · intro q hsq hqn
    have hk : q.val - start z < ((liveCells (z, a)).take (n - start z)).length := by
      rw [List.length_take, hlen]
      omega
    refine ⟨((liveCells (z, a)).take (n - start z))[q.val - start z]'hk,
      List.getElem_mem hk, ?_⟩
    apply Fin.ext
    simp only [List.getElem_take]
    rw [htime (q.val - start z) (by rw [hlen]; omega)]
    omega

private theorem generatedPast_chronology_aux (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :
    ∀ n (hn : n ≤ p.T), n ≤ t.val →
      let W := actualOriginalWord rate rewards C_star C_h z
        (firstCall_launch rate rewards C_star C_h u t z hz)
      let H := (stateAt n hn (z, a)).2
      H.Pairwise (fun e f => e.time.val < f.time.val) ∧
        (∀ e ∈ H, start z ≤ e.time.val ∧ e.time.val < n) ∧
        ∀ q : Fin p.T, start z ≤ q.val → q.val < n →
          (q.val < u.val ∨ ∃ hk : q.val - start z < W.length, W[q.val - start z].enabled = true) →
          ∃ e ∈ H, e.time = q := by
  intro n
  induction n with
  | zero =>
      intro hn _
      exact ⟨by change ([] : List (LogicalCell p rate)).Pairwise _; simp,
        fun _ h => (List.not_mem_nil h).elim,
        fun q _ h => (Nat.not_lt_zero q.val h).elim⟩
  | succ n ih =>
      intro hn hnt
      dsimp only
      by_cases hnu : n + 1 ≤ u.val
      · have h := live_prefix_chronology rate rewards C_star C_h u t z hz a (n + 1) hn hnu
        exact ⟨h.1, h.2.1, fun q hs hq _ => h.2.2 q hs hq⟩
      have hd := firstCall_dates rate rewards C_star C_h u t z hz
      let q : Fin p.T := ⟨n, Nat.lt_of_succ_le hn⟩
      have hdom := actualDomain_of_collection_interval rate rewards C_star C_h q z
        (by rw [hd.2.2.1]; dsimp only [q]; omega)
        (by rw [ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary_on_firstCell
          rate rewards C_star C_h u t z hz]; dsimp only [q]; omega)
      obtain ⟨r, hr, hm⟩ := hdom
      obtain ⟨U, _hU, hstep⟩ := generated_collection_step rate rewards C_star C_h q z a r hr hm
      let I := actualInput rewards C_star C_h z q r hr hm
      let e := ReferenceFirstCollectionOneRoundLogicalCell.cellWithScalar rewards C_star C_h z q r hr hm U
        (ReferenceFirstLiveCalendarMarkedTransition.labelZero a)
        (ReferenceSourceFastScalarDisintegration.sourceFastScalar p q z) (a (q, 1))
      let H := (stateAt n (Nat.le_of_succ_le hn) (z, a)).2
      have heTime : e.time = q := rfl
      have hp := ih (Nat.le_of_succ_le hn) (by omega)
      have hw := originalWord_collection_data rate rewards C_star C_h z
        (firstCall_launch rate rewards C_star C_h u t z hz) q r hr hm
      obtain ⟨hkW, hsq, _htime, _hpast, hinput⟩ := hw
      change I = _ at hinput
      change stateAt (n + 1) hn (z, a) =
        if I.enabled then (some e.nextSlowSet, H ++ [e])
        else stateAt n (Nat.le_of_succ_le hn) (z, a) at hstep
      cases hc : I.enabled with
      | false =>
          simp only [hc, Bool.false_eq_true, ite_false] at hstep
          rw [hstep]
          refine ⟨hp.1, fun f hf => ⟨(hp.2.1 f hf).1, by have hb := (hp.2.1 f hf).2; omega⟩, ?_⟩
          intro v hsv hvn hgood
          have hvold : v.val < n := by
            by_contra h
            have hvq : v = q := Fin.ext (by dsimp only [q]; omega)
            subst v
            rcases hgood with hgood | ⟨hk, hgood⟩
            · dsimp only [q] at hgood
              omega
            · rw [← hinput, hc] at hgood
              cases hgood
          exact hp.2.2 v hsv hvold hgood
      | true =>
          simp only [hc, ite_true] at hstep
          rw [hstep]
          refine ⟨?_, ?_, ?_⟩
          · apply List.pairwise_append.mpr
            refine ⟨hp.1, by simp, ?_⟩
            intro f hf g hg
            have hge : g = e := List.mem_singleton.mp hg
            rw [hge, heTime]
            exact (hp.2.1 f hf).2
          · intro f hf
            rcases List.mem_append.mp hf with hf | hf
            · exact ⟨(hp.2.1 f hf).1, by have hb := (hp.2.1 f hf).2; omega⟩
            · have hfe : f = e := List.mem_singleton.mp hf
              rw [hfe, heTime]
              exact ⟨hsq, by dsimp only [q]; omega⟩
          · intro v hsv hvn hgood
            by_cases hvold : v.val < n
            · obtain ⟨f, hf, hfv⟩ := hp.2.2 v hsv hvold hgood
              exact ⟨f, List.mem_append_left _ hf, hfv⟩
            · have hvq : v = q := Fin.ext (by dsimp only [q]; omega)
              exact ⟨e, List.mem_append_right _ (List.mem_singleton_self e), heTime.trans hvq.symm⟩

/-- The generated history has strictly increasing actual dates in the
original interval. Every LIVE date and every enabled collection date is
represented, including enabled cells whose accepted record is zero. -/
theorem firstCall_generatedPast_chronology (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (n : Fin (p.T + 1)) (hnt : n.val ≤ t.val) :
    let W := actualOriginalWord rate rewards C_star C_h z
      (firstCall_launch rate rewards C_star C_h u t z hz)
    let H := extendedPast rate rewards C_star C_h n (z, a)
    H.Pairwise (fun e f => e.time.val < f.time.val) ∧
      (∀ e ∈ H, start z ≤ e.time.val ∧ e.time.val < n.val) ∧
      ∀ q : Fin p.T, start z ≤ q.val → q.val < n.val →
        (q.val < u.val ∨ ∃ hk : q.val - start z < W.length, W[q.val - start z].enabled = true) →
        ∃ e ∈ H, e.time = q :=
  generatedPast_chronology_aux rate rewards C_star C_h u t z hz a n.val
    (Nat.le_of_lt_succ n.isLt) hnt

/-- Each actual generated entry uses the original word at its real
timestamp, with its entire canonical before/after state and all-arm update. -/
theorem firstCall_generatedPast_cell_data (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (n : Fin (p.T + 1)) (e : LogicalCell p rate)
    (he : e ∈ extendedPast rate rewards C_star C_h n (z, a)) :
    let W := actualOriginalWord rate rewards C_star C_h z
      (firstCall_launch rate rewards C_star C_h u t z hz)
    ∃ hk : e.time.val - start z < W.length,
      e.numerical = numericalCoordinates W[e.time.val - start z] ∧
      e.before = RecordedQueueRun.run Q (W.take (e.time.val - start z)) ∧
      e.after = RecordedQueueRun.run Q (W.take (e.time.val + 1 - start z)) ∧
      e.arrivals = RecordedQueueRun.acceptedRecord Q e.before W[e.time.val - start z] ∧
      e.service = (fun j => RecordedQueueRun.recordService (4 * (Q).n)
        (e.before.registers j) (e.arrivals j)) ∧
      ∀ j, e.service j ≤ 4 * (Q).n ∧ e.after.registers j =
        QueueReplay.transition (4 * (Q).n) (e.before.registers j) (e.arrivals j) := by
  dsimp only
  by_cases hlive : e ∈ liveCells (z, a)
  · obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp hlive
    have hkw : k < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h z).length := by
      simpa only [firstLiveChronologicalPrefix_length,
        ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hk
    have h := firstCall_live_cell_data rate rewards C_star C_h u t z hz a ⟨k, hkw⟩
    dsimp only at h
    rw [hke] at h
    obtain ⟨hkW, htime, _hbeforecut, hnum, hbefore, hafter, harr, hservice, hall⟩ := h
    have hi : e.time.val - start z = k := by omega
    have hi' : e.time.val + 1 - start z = k + 1 := by omega
    rw [hi, hi']
    exact ⟨hkW, hnum, hbefore, hafter, harr, hservice, hall⟩
  · obtain ⟨q, r, hr, hm, _U, _hqn, _hU, _henabled, htime, _hphysical,
      hnum, hbefore, hafter, harr, hservice, _hslow, _hfast, _hproposal, _hnext, hall⟩ :=
      generated_collection_cell_fields rate rewards C_star C_h n z a e he hlive
    obtain ⟨hk, hsq, _hrtime, hpast, hinput⟩ := originalWord_collection_data
      rate rewards C_star C_h z (firstCall_launch rate rewards C_star C_h u t z hz)
      q r hr hm
    rw [hinput] at hnum
    rw [hpast] at hbefore
    rw [hpast, hinput] at hafter harr hservice
    have hrun : RecordedQueueRun.step Q
        (RecordedQueueRun.run Q ((actualOriginalWord rate rewards C_star C_h z
          (firstCall_launch rate rewards C_star C_h u t z hz)).take (q.val - start z)))
        (actualOriginalWord rate rewards C_star C_h z
          (firstCall_launch rate rewards C_star C_h u t z hz))[q.val - start z] =
        RecordedQueueRun.run Q ((actualOriginalWord rate rewards C_star C_h z
          (firstCall_launch rate rewards C_star C_h u t z hz)).take (q.val + 1 - start z)) := by
      rw [Nat.sub_add_comm hsq, ← List.take_append_getElem hk,
        RecordedSlowRefresh.run_append_singleton]
    rw [htime]
    refine ⟨hk, hnum, hbefore, hafter.trans hrun, ?_, ?_, hall⟩
    · rw [hbefore]
      exact harr
    · rw [hbefore, harr]
      exact hservice

/-- The actual installation's strict-past readout is the completed original
calendar run, including the accepted records at omitted logical dates. -/
theorem firstCall_installationNumericalBefore
    (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t) :
    let W := actualOriginalWord rate rewards C_star C_h z
      (firstCall_launch rate rewards C_star C_h u t z hz)
    let S := RecordedQueueRun.run Q (W.take (t.val - start z))
    ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
      rate rewards C_star C_h control0 t z = some (S.registers, S.overflow, S.records) := by
  have hd := firstCall_dates rate rewards C_star C_h u t z hz
  have hp := (originalWord_calendar_prefix rate rewards C_star C_h z
    (firstCall_launch rate rewards C_star C_h u t z hz) t.castSucc (hd.1.trans hd.2.1.le)).2.2
  simp only [Fin.val_castSucc] at hp
  rw [ReferenceFirstCollectionCorrectedFutureRetainedMoment.prefixInputs_eq_pastCells] at hp
  rw [ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore_eq_original,
    ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?, hp]
  rfl

/-- Whole-vector insertion retains the full numerical prestate because it
retains the first coordinate of the accepted observation. -/
theorem installationNumericalBefore_insertVector
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : SourceInput p) (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (v : AssignmentParameterFibreKernel.AssignmentVector p) :
    ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
      rate rewards C_star C_h control0 t
      (ReferenceFirstNextInvocationJointLift.insertedSource t z v) =
    ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
      rate rewards C_star C_h control0 t z := by
  have hp := congrArg Prod.fst
    (ReferenceFirstNextInvocationJointLift.nextInvocationPrefix_insertVector
      rate rewards C_star C_h t control0 z a v)
  exact congrArg (ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
    rate rewards C_star C_h t) hp

/-- An actual first collection has a positive LIVE history, derived from
the actual collection domain at its cutoff head. -/
theorem firstCall_launch_lt_cutoff (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t) : start z < u.val := by
  have hd := firstCall_dates rate rewards C_star C_h u t z hz
  have hdom := actualDomain_of_collection_interval rate rewards C_star C_h u z
    (by rw [hd.2.2.1])
    (by rw [ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary_on_firstCell
      rate rewards C_star C_h u t z hz]; exact hd.2.1)
  have hpos := firstLiveLength_pos_of_actualDomain rate rewards C_star C_h u z hdom
  have hdate := hd.2.2.1
  change start z + ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength
    rate rewards C_star C_h z = u.val at hdate
  omega

/-- Empty generated histories occur exactly at or before the real launch,
through the first invocation. -/
theorem firstCall_generatedPast_empty_iff (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (n : Fin (p.T + 1)) (hnt : n.val ≤ t.val) :
    extendedPast rate rewards C_star C_h n (z, a) = [] ↔ n.val ≤ start z := by
  have hp := firstCall_generatedPast_chronology rate rewards C_star C_h u t z hz a n hnt
  constructor
  · intro he
    by_contra hn
    have hd := firstCall_dates rate rewards C_star C_h u t z hz
    let q : Fin p.T := ⟨start z, hd.1.trans_lt u.isLt⟩
    obtain ⟨e, hem, _⟩ := hp.2.2 q le_rfl (by dsimp only [q]; omega)
      (Or.inl (firstCall_launch_lt_cutoff rate rewards C_star C_h u t z hz))
    rw [he] at hem
    exact List.not_mem_nil hem
  · intro hn
    cases hH : extendedPast rate rewards C_star C_h n (z, a) with
    | nil => rfl
    | cons e es =>
        have hb := hp.2.1 e (by rw [hH]; exact List.mem_cons_self)
        omega

/-- The actual last generated cell requires precisely the omitted calendar
records. Registers and overflow agree, while every arm's old records remain
as an unchanged prefix followed by the real number of disabled dates. -/
theorem firstCall_generatedPast_last_completion (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (n : Fin (p.T + 1)) (hnt : n.val ≤ t.val)
    (hne : extendedPast rate rewards C_star C_h n (z, a) ≠ []) :
    let W := actualOriginalWord rate rewards C_star C_h z
      (firstCall_launch rate rewards C_star C_h u t z hz)
    let S := RecordedQueueRun.run Q (W.take (n.val - start z))
    ∃ e : LogicalCell p rate,
      (extendedPast rate rewards C_star C_h n (z, a)).getLast? = some e ∧
      e ∈ extendedPast rate rewards C_star C_h n (z, a) ∧
      start z ≤ e.time.val ∧ e.time.val + 1 ≤ n.val ∧
      (∀ q : Fin p.T, e.time.val + 1 ≤ q.val → q.val < n.val →
        ∃ hk : q.val - start z < W.length, W[q.val - start z].enabled = false) ∧
      S.registers = e.after.registers ∧ S.overflow = e.after.overflow ∧
      ∀ j, S.records j = e.after.records j ++
        List.replicate (n.val - (e.time.val + 1)) (false, 0) := by
  dsimp only
  let W := actualOriginalWord rate rewards C_star C_h z
    (firstCall_launch rate rewards C_star C_h u t z hz)
  let H := extendedPast rate rewards C_star C_h n (z, a)
  have hp := firstCall_generatedPast_chronology rate rewards C_star C_h u t z hz a n hnt
  cases hl : H.getLast? with
  | none => exact (hne (List.getLast?_eq_none_iff.mp hl)).elim
  | some e =>
      obtain ⟨pre, hpre⟩ := List.getLast?_eq_some_iff.mp hl
      have he : e ∈ H := by rw [hpre]; exact List.mem_append_right _ (List.mem_singleton_self e)
      have hb := hp.2.1 e he
      have hmax : ∀ f ∈ H, f.time.val ≤ e.time.val := by
        have hpair := hp.1
        change H.Pairwise _ at hpair
        rw [hpre, List.pairwise_append] at hpair
        intro f hf
        rw [hpre, List.mem_append, List.mem_singleton] at hf
        rcases hf with hf | rfl
        · exact (hpair.2.2 f hf e (List.mem_singleton_self e)).le
        · exact le_rfl
      have hdisabled : ∀ q : Fin p.T, e.time.val + 1 ≤ q.val → q.val < n.val →
          ∃ hk : q.val - start z < W.length, W[q.val - start z].enabled = false := by
        intro q heq hqn
        have hsq : start z ≤ q.val := by omega
        have hlen := (originalWord_calendar_prefix rate rewards C_star C_h z
          (firstCall_launch rate rewards C_star C_h u t z hz) n (by omega)).1
        have hk : q.val - start z < W.length := by
          rw [hlen]
          have hqT := q.isLt
          omega
        refine ⟨hk, ?_⟩
        cases hflag : W[q.val - start z].enabled with
        | false => rfl
        | true =>
            obtain ⟨f, hf, htime⟩ := hp.2.2 q hsq hqn (Or.inr ⟨hk, hflag⟩)
            have hfmax := hmax f hf
            rw [htime] at hfmax
            omega
      have hlen := (originalWord_calendar_prefix rate rewards C_star C_h z
        (firstCall_launch rate rewards C_star C_h u t z hz) n (by omega)).2.1
      have hcomp := disabled_interval_completion rate W (e.time.val + 1 - start z)
        (n.val - start z) (by omega) hlen (by
          intro k hk hmk hkn
          have hdate : start z + k < p.T := by
            have hnT := Nat.le_of_lt_succ n.isLt
            omega
          let q : Fin p.T := ⟨start z + k, hdate⟩
          obtain ⟨_hindex, hfalse⟩ := hdisabled q (by dsimp only [q]; omega)
            (by dsimp only [q]; omega)
          simpa only [q, Nat.add_sub_cancel_left] using hfalse)
      obtain ⟨_hk, _hnum, _hbefore, hafter, _harr, _hservice, _hall⟩ :=
        firstCall_generatedPast_cell_data rate rewards C_star C_h u t z hz a n e he
      dsimp only at hcomp
      change e.after = RecordedQueueRun.run Q (W.take (e.time.val + 1 - start z)) at hafter
      rw [← hafter] at hcomp
      have hgap : n.val - start z - (e.time.val + 1 - start z) = n.val - (e.time.val + 1) := by
        omega
      rw [hgap] at hcomp
      exact ⟨e, rfl, he, hb.1, by omega, hdisabled, hcomp.1, hcomp.2.1, hcomp.2.2⟩

/-- Adjacent actual generated cells splice by retaining every earlier
accepted record and padding precisely the intervening disabled dates. -/
theorem firstCall_generatedPast_adjacent_completion (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (n : Fin (p.T + 1)) (hnt : n.val ≤ t.val) (k : ℕ)
    (hk : k + 1 < (extendedPast rate rewards C_star C_h n (z, a)).length) :
    let W := actualOriginalWord rate rewards C_star C_h z
      (firstCall_launch rate rewards C_star C_h u t z hz)
    let H := extendedPast rate rewards C_star C_h n (z, a)
    let earlier := H[k]'(by change k < (extendedPast rate rewards C_star C_h n (z, a)).length; omega)
    let later := H[k + 1]
    earlier.time.val < later.time.val ∧
      (∀ q : Fin p.T, earlier.time.val + 1 ≤ q.val → q.val < later.time.val →
        ∃ hi : q.val - start z < W.length, W[q.val - start z].enabled = false) ∧
      later.before.registers = earlier.after.registers ∧
      later.before.overflow = earlier.after.overflow ∧
      ∀ j, later.before.records j = earlier.after.records j ++
        List.replicate (later.time.val - (earlier.time.val + 1)) (false, 0) := by
  dsimp only
  let W := actualOriginalWord rate rewards C_star C_h z
    (firstCall_launch rate rewards C_star C_h u t z hz)
  let H := extendedPast rate rewards C_star C_h n (z, a)
  have hk0 : k < H.length := by
    change k < (extendedPast rate rewards C_star C_h n (z, a)).length
    omega
  let earlier := H[k]'hk0
  let later := H[k + 1]'hk
  have hp := firstCall_generatedPast_chronology rate rewards C_star C_h u t z hz a n hnt
  have horder := List.pairwise_iff_getElem.mp hp.1
  have hlt : earlier.time.val < later.time.val := horder k (k + 1) hk0 hk (by omega)
  have he := hp.2.1 earlier (List.getElem_mem hk0)
  have hl := hp.2.1 later (List.getElem_mem hk)
  have hdisabled : ∀ q : Fin p.T, earlier.time.val + 1 ≤ q.val → q.val < later.time.val →
      ∃ hi : q.val - start z < W.length, W[q.val - start z].enabled = false := by
    intro q heq hql
    have hsq : start z ≤ q.val := by omega
    have hWlen := (originalWord_calendar_prefix rate rewards C_star C_h z
      (firstCall_launch rate rewards C_star C_h u t z hz) n (by omega)).1
    have hi : q.val - start z < W.length := by
      rw [hWlen]
      have hqT := q.isLt
      omega
    refine ⟨hi, ?_⟩
    cases hflag : W[q.val - start z].enabled with
    | false => rfl
    | true =>
        obtain ⟨f, hf, htime⟩ := hp.2.2 q hsq (by omega) (Or.inr ⟨hi, hflag⟩)
        obtain ⟨i, hiH, hif⟩ := List.mem_iff_getElem.mp hf
        have hifTime : H[i].time.val = q.val :=
          (congrArg (fun c : LogicalCell p rate => c.time.val) hif).trans (congrArg Fin.val htime)
        by_cases hik : i < k
        · have ho := horder i k hiH hk0 hik
          change H[i].time.val < earlier.time.val at ho
          rw [hifTime] at ho
          omega
        by_cases hki : k + 1 < i
        · have ho := horder (k + 1) i hk hiH hki
          change later.time.val < H[i].time.val at ho
          rw [hifTime] at ho
          omega
        have hicases : i = k ∨ i = k + 1 := by omega
        rcases hicases with rfl | rfl
        · change earlier.time.val = q.val at hifTime
          omega
        · change later.time.val = q.val at hifTime
          omega
  have hWlen := (originalWord_calendar_prefix rate rewards C_star C_h z
    (firstCall_launch rate rewards C_star C_h u t z hz) n (by omega)).1
  have hcomp := disabled_interval_completion rate W (earlier.time.val + 1 - start z)
    (later.time.val - start z) (by omega) (by rw [hWlen]; omega) (by
      intro i hi hmi hin
      have hdate : start z + i < p.T := by
        have hT := later.time.isLt
        omega
      let q : Fin p.T := ⟨start z + i, hdate⟩
      obtain ⟨_hq, hfalse⟩ := hdisabled q (by dsimp only [q]; omega) (by dsimp only [q]; omega)
      simpa only [q, Nat.add_sub_cancel_left] using hfalse)
  obtain ⟨_hi, _hnum, _hbefore, hafter, _harr, _hservice, _hall⟩ :=
    firstCall_generatedPast_cell_data rate rewards C_star C_h u t z hz a n earlier (List.getElem_mem hk0)
  obtain ⟨_hi', _hnum', hbefore', _hafter', _harr', _hservice', _hall'⟩ :=
    firstCall_generatedPast_cell_data rate rewards C_star C_h u t z hz a n later (List.getElem_mem hk)
  dsimp only at hcomp
  rw [← hafter, ← hbefore'] at hcomp
  have hgap : later.time.val - start z - (earlier.time.val + 1 - start z) =
      later.time.val - (earlier.time.val + 1) := by omega
  rw [hgap] at hcomp
  exact ⟨hlt, hdisabled, hcomp.1, hcomp.2.1, hcomp.2.2⟩

private theorem cell0_coordinates (r : Record rate) :
    (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r).map numericalCoordinates =
      (ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r).map (Sum.elim id id) := by
  have hp := ReferenceCompleteNumericalBranchObservation.branch_readout_projections rate 0 r
  rw [ReferenceFirstCollectionCurrentRetainedGate.cell0, Option.map_or]
  have hl := congrArg Prod.fst hp
  have hr := congrArg Prod.snd hp
  change ReferenceCompleteNumericalBranchObservation.leftProjection _ =
    (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).map numericalCoordinates at hl
  change ReferenceCompleteNumericalBranchObservation.rightProjection _ =
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).map numericalCoordinates at hr
  rw [← hl, ← hr]
  cases h : ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r with
  | none => rfl
  | some c => cases c <;> rfl

private theorem originalWord_coordinates_datePrefix (z : SourceInput p)
    (hlaunch : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active)
    (n : ℕ) (hn : n ≤ p.T) :
    ((actualOriginalWord rate rewards C_star C_h z hlaunch).take (n - start z)).map
        (fun c => some (numericalCoordinates c)) =
      (ReferenceCompleteObservationPrefixInformation.datePrefix rate n
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h z)).map (fun e => e.2.2.map (Sum.elim id id)) := by
  have hm := congrArg (fun xs => xs.take (n - start z))
    (originalWord_record_map rate rewards C_star C_h z hlaunch)
  simp only [← List.map_take] at hm
  have hc := congrArg (List.map (Option.map numericalCoordinates)) hm
  simp only [List.map_map, Function.comp_def, Option.map_some] at hc
  rw [← hc, ReferenceCompleteObservationPrefixInformation.datePrefix_eq_take
    rate rewards C_star C_h n hn]
  simp only [ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
    ReferenceCompleteNumericalBranchObservation.branchCalendar, List.map_take, List.map_map,
    Function.comp_def]
  apply congrArg (List.take (n - start z))
  apply List.map_congr_left
  intro r _
  exact cell0_coordinates rate r

private theorem originalWord_strictPast_eq
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z z' : SourceInput p)
    (hz : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active)
    (hz' : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z' rewards C_star C_h = some active)
    (hp : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z') :
    (actualOriginalWord rate rewards C_star C_h z hz).take (t.val - start z) =
      (actualOriginalWord rate rewards C_star C_h z' hz').take (t.val - start z') := by
  have hd := ReferenceCompleteObservationPrefixInformation.datePrefix_factor
    rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt) z
  have hd' := ReferenceCompleteObservationPrefixInformation.datePrefix_factor
    rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt) z'
  rw [hp] at hd
  have hc := congrArg (fun L => L.map (fun e => e.2.2.map (Sum.elim id id))) (hd.trans hd'.symm)
  rw [← originalWord_coordinates_datePrefix rate rewards C_star C_h z hz t.val (Nat.le_of_lt t.isLt),
    ← originalWord_coordinates_datePrefix rate rewards C_star C_h z' hz' t.val (Nat.le_of_lt t.isLt)] at hc
  apply List.map_injective_iff.mpr _ hc
  intro c d h
  have he := Option.some.inj h
  cases c
  cases d
  simp_all only [numericalCoordinates, Prod.mk.injEq]

/-- A whole current assignment-vector insertion retains the actual first
call. This assertion makes no success or preoverflow assumption. -/
theorem firstCall_insertVector_mem (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t)
    (v : AssignmentParameterFibreKernel.AssignmentVector p) :
    ReferenceFirstNextInvocationJointLift.insertedSource t z v ∈
      ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell rate rewards C_star C_h u t := by
  change ReferenceFirstCollectionRenewalVectorInsertion.insert t z v ∈ _
  rw [ReferenceFirstCollectionRenewalVectorInsertion.insert_eq_replaceSelectedControlSuffix]
  exact (ReferenceFirstCollectionRenewalPastLocality.actualCollectionCallCell_iff_replaceSelectedControlSuffix
    rate rewards C_star C_h z u t _).mp hz

/-- The two original complete words agree on their strict-past prefixes.
No invariance of the inserted current entry or of a future suffix is claimed. -/
theorem firstCall_insertVector_strictPast
    (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (v : AssignmentParameterFibreKernel.AssignmentVector p) :
    let z' := ReferenceFirstNextInvocationJointLift.insertedSource t z v
    let hz' := firstCall_insertVector_mem rate rewards C_star C_h u t z hz v
    (actualOriginalWord rate rewards C_star C_h z'
      (firstCall_launch rate rewards C_star C_h u t z' hz')).take (t.val - start z') =
    (actualOriginalWord rate rewards C_star C_h z
      (firstCall_launch rate rewards C_star C_h u t z hz)).take (t.val - start z) := by
  have hp := congrArg Prod.fst
    (ReferenceFirstNextInvocationJointLift.nextInvocationPrefix_insertVector
      rate rewards C_star C_h t control0 z a v)
  exact originalWord_strictPast_eq rate rewards C_star C_h control0 t _ _
    (firstCall_launch rate rewards C_star C_h u t _
      (firstCall_insertVector_mem rate rewards C_star C_h u t z hz v))
    (firstCall_launch rate rewards C_star C_h u t z hz) hp

private theorem stateReadout_injective : Function.Injective
    (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout (K := p.K)) := by
  intro S R h
  cases S
  cases R
  simp_all only [ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout, Prod.mk.injEq]

private theorem firstCall_installationEvent (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t) :
    z ∈ ReferenceRankInstallationRecorderFoundation.installationEvent rate rewards C_star C_h 0 t := by
  apply Set.mem_iUnion.mpr
  refine ⟨u, ?_⟩
  apply (ReferenceCollectionRankCellPhysicalTransport.mem_rankCell_iff_originalTags
    rate rewards C_star C_h 0 u t z).mpr
  rw [ReferenceCollectionSamplerChronology.nthCollectionCall_zero]
  exact hz

/-- On the actual inserted source, the internally produced installation
prestate is the completed old run. The current numerical input comes from
the inserted source's own complete word. -/
theorem firstCall_insertVector_numericalUpdate
    (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (v : AssignmentParameterFibreKernel.AssignmentVector p) :
    let z' := ReferenceFirstNextInvocationJointLift.insertedSource t z v
    let hz' := firstCall_insertVector_mem rate rewards C_star C_h u t z hz v
    let W := actualOriginalWord rate rewards C_star C_h z
      (firstCall_launch rate rewards C_star C_h u t z hz)
    let W' := actualOriginalWord rate rewards C_star C_h z'
      (firstCall_launch rate rewards C_star C_h u t z' hz')
    let S := RecordedQueueRun.run Q (W.take (t.val - start z))
    ∃ (before : RecordedQueueRun.RunState p.K) (c : RecordedQueueRun.RoundInput p.K),
      before = S ∧ c.enabled = true ∧ W'[t.val - start z']? = some c ∧
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
        rate rewards C_star C_h control0 t z' = some (S.registers, S.overflow, S.records) ∧
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationRawArrivals
        rate rewards C_star C_h t z' = some (RecordedQueueRun.quantizedArrival Q c) ∧
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
        rate rewards C_star C_h control0 t z' =
        some (ReferenceFirstLivePostUpdateProposalLaw.numericalUpdateFields rate
          (S.registers, S.overflow, S.records) (RecordedQueueRun.quantizedArrival Q c)) := by
  dsimp only
  let z' := ReferenceFirstNextInvocationJointLift.insertedSource t z v
  have hz' := firstCall_insertVector_mem rate rewards C_star C_h u t z hz v
  have hi := firstCall_installationEvent rate rewards C_star C_h u t z' hz'
  have hb := (installationNumericalBefore_insertVector rate rewards C_star C_h control0 t z a v).trans
    (firstCall_installationNumericalBefore rate rewards C_star C_h control0 u t z hz)
  obtain ⟨before, _current, _henabled, hbefore, _hraw, _hstep⟩ :=
    ReferenceRankInstallationPostUpdateProposalLaw.installationEvent_numericalUpdate_eq_step
      rate rewards C_star C_h control0 0 t z' hi
  have hstate := stateReadout_injective
    (Option.some.inj (hbefore.symm.trans hb))
  obtain ⟨L, c, hword, _hrestoration, henabled, hcurrent, _hnext, _hbefore', hraw, _hupdate⟩ :=
    ReferenceRankInstallationPostUpdateProposalLaw.installationEvent_originalNumericalUpdate
      rate rewards C_star C_h control0 0 t z' hi
  have hLW : L = actualOriginalWord rate rewards C_star C_h z'
      (firstCall_launch rate rewards C_star C_h u t z' hz') :=
    Option.some.inj (hword.symm.trans (actualOriginalWord_spec rate rewards C_star C_h z'
      (firstCall_launch rate rewards C_star C_h u t z' hz')))
  rw [hLW] at hcurrent
  refine ⟨before, c, hstate, henabled, hcurrent, hb, hraw, ?_⟩
  rw [ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate,
    ReferenceRankInstallationPostUpdateProposalLaw.numericalUpdateFromReadouts, hb, hraw]
  rfl

/-- Joint source-derived completion through the first invocation. The same
original word serves every boundary, and the empty branch is the real zero
launch. In the nonempty branch the padding count is a calendar-time gap. -/
theorem firstCall_generatedPast_numerical_completion
    (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :
    ∃ hlaunch : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h = some active,
      let W := actualOriginalWord rate rewards C_star C_h z hlaunch
      let s : Fin (p.T + 1) := ⟨start z, Nat.lt_succ_of_le
        (ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h)⟩
      start z ≤ u.val ∧ u.val < t.val ∧ W.length = p.T - start z ∧
      prefixInputs rate rewards C_star C_h p.T z = some W ∧
      extendedPast rate rewards C_star C_h s (z, a) = [] ∧
      (∀ n : Fin (p.T + 1), start z ≤ n.val → n.val ≤ t.val →
        let H := extendedPast rate rewards C_star C_h n (z, a)
        let S := RecordedQueueRun.run Q (W.take (n.val - start z))
        n.val - start z ≤ W.length ∧
        prefixInputs rate rewards C_star C_h n.val z = some (W.take (n.val - start z)) ∧
        H.Pairwise (fun e f => e.time.val < f.time.val) ∧
        (∀ e ∈ H, start z ≤ e.time.val ∧ e.time.val < n.val) ∧
        (∀ e ∈ H, ∃ hk : e.time.val - start z < W.length,
          e.numerical = numericalCoordinates W[e.time.val - start z] ∧
          e.before = RecordedQueueRun.run Q (W.take (e.time.val - start z)) ∧
          e.after = RecordedQueueRun.run Q (W.take (e.time.val + 1 - start z)) ∧
          e.arrivals = RecordedQueueRun.acceptedRecord Q e.before W[e.time.val - start z] ∧
          e.service = (fun j => RecordedQueueRun.recordService (4 * (Q).n)
            (e.before.registers j) (e.arrivals j)) ∧
          ∀ j, e.service j ≤ 4 * (Q).n ∧ e.after.registers j =
            QueueReplay.transition (4 * (Q).n) (e.before.registers j) (e.arrivals j)) ∧
        ((H = [] ∧ n.val = start z ∧ S = RecordedQueueRun.initialState p.K) ∨
          ∃ e, H.getLast? = some e ∧ e ∈ H ∧ start z ≤ e.time.val ∧ e.time.val + 1 ≤ n.val ∧
            (∀ q : Fin p.T, e.time.val + 1 ≤ q.val → q.val < n.val →
              ∃ hk : q.val - start z < W.length, W[q.val - start z].enabled = false) ∧
            S.registers = e.after.registers ∧ S.overflow = e.after.overflow ∧
            ∀ j, S.records j = e.after.records j ++
              List.replicate (n.val - (e.time.val + 1)) (false, 0))) ∧
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
        rate rewards C_star C_h control0 t z =
        some ((RecordedQueueRun.run Q (W.take (t.val - start z))).registers,
          (RecordedQueueRun.run Q (W.take (t.val - start z))).overflow,
          (RecordedQueueRun.run Q (W.take (t.val - start z))).records) := by
  refine ⟨firstCall_launch rate rewards C_star C_h u t z hz, ?_⟩
  dsimp only
  have hd := firstCall_dates rate rewards C_star C_h u t z hz
  refine ⟨hd.1, hd.2.1, ?_, actualOriginalWord_spec rate rewards C_star C_h z _,
    firstCall_generatedPast_at_launch rate rewards C_star C_h u t z hz a, ?_,
    firstCall_installationNumericalBefore rate rewards C_star C_h control0 u t z hz⟩
  · rw [actualOriginalWord_length, ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
  · intro n hsn hnt
    have hw := originalWord_calendar_prefix rate rewards C_star C_h z
      (firstCall_launch rate rewards C_star C_h u t z hz) n hsn
    have hp := firstCall_generatedPast_chronology rate rewards C_star C_h u t z hz a n hnt
    refine ⟨hw.2.1, hw.2.2, hp.1, hp.2.1,
      fun e he => firstCall_generatedPast_cell_data rate rewards C_star C_h u t z hz a n e he, ?_⟩
    by_cases hne : extendedPast rate rewards C_star C_h n (z, a) = []
    · left
      have hns := (firstCall_generatedPast_empty_iff rate rewards C_star C_h u t z hz a n hnt).mp hne
      have heq : n.val = start z := Nat.le_antisymm hns hsn
      refine ⟨hne, heq, ?_⟩
      rw [heq, Nat.sub_self, List.take_zero]
      rfl
    · exact Or.inr (firstCall_generatedPast_last_completion rate rewards C_star C_h u t z hz a n hnt hne)

/-- The accepted renewal incoming list is exactly the strict-past segment
of the same original word, including all disabled calendar dates. -/
theorem renewalIncoming_prefix_eq_original (u t : Fin p.T)
    (z : ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t) :
    ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells rate rewards C_star C_h u t z =
      (actualOriginalWord rate rewards C_star C_h z.val
        (firstCall_launch rate rewards C_star C_h u t z.val z.property.1)).take (t.val - start z.val) := by
  have hm := congrArg (fun xs => xs.take (t.val - start z.val))
    (originalWord_record_map rate rewards C_star C_h z.val
      (firstCall_launch rate rewards C_star C_h u t z.val z.property.1))
  simp only [← List.map_take] at hm
  change ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
    rate rewards C_star C_h u t t.val z = _ at hm
  have hc := ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells_rawJoinedPrefix
    rate rewards C_star C_h u t t.val (Nat.le_of_lt t.isLt) z
  rw [hm] at hc
  have hp := ReferenceFirstCollectionRenewalSourceCurrentPrefix.pastCells_rawPrefix_join
    rate rewards C_star C_h u t z
  change ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarRawJoinedPrefix
    rate rewards C_star C_h u t t.val z = _ at hp
  have he := hc.trans hp
  simp only [List.map_map, Function.comp_def, Option.map_some] at he
  symm
  apply List.map_injective_iff.mpr _ he
  intro c d h
  have hcd := Option.some.inj h
  cases c
  cases d
  simp_all only [ReferenceCompleteNumericalBranchObservation.encodeNumerical,
    ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates, Prod.mk.injEq]

private theorem firstCall_insertVector_last_completion
    (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (v : AssignmentParameterFibreKernel.AssignmentVector p) :
    let W := actualOriginalWord rate rewards C_star C_h z
      (firstCall_launch rate rewards C_star C_h u t z hz)
    let S := RecordedQueueRun.run Q (W.take (t.val - start z))
    ∃ e, (extendedPast rate rewards C_star C_h t.castSucc (z, a)).getLast? = some e ∧
      (extendedPast rate rewards C_star C_h t.castSucc
        (ReferenceFirstNextInvocationJointLift.insertedSource t z v, a)).getLast? = some e ∧
      e.time.val + 1 ≤ t.val ∧ S.registers = e.after.registers ∧ S.overflow = e.after.overflow ∧
      ∀ j, S.records j = e.after.records j ++ List.replicate (t.val - (e.time.val + 1)) (false, 0) := by
  have hd := firstCall_dates rate rewards C_star C_h u t z hz
  have hne : extendedPast rate rewards C_star C_h t.castSucc (z, a) ≠ [] := by
    intro he
    have hb := (firstCall_generatedPast_empty_iff rate rewards C_star C_h u t z hz a t.castSucc le_rfl).mp he
    simp only [Fin.val_castSucc] at hb
    omega
  obtain ⟨e, hlast, _hem, _hs, hdate, _hdisabled, hreg, hover, hrecords⟩ :=
    firstCall_generatedPast_last_completion rate rewards C_star C_h u t z hz a t.castSucc le_rfl hne
  have hH := congrArg (fun o : Observation rate => o.2.2)
    (ReferenceFirstNextInvocationJointLift.nextInvocationPrefix_insertVector
      rate rewards C_star C_h t control0 z a v)
  exact ⟨e, hlast, (congrArg List.getLast? hH).trans hlast, hdate, hreg, hover, hrecords⟩

/-- Numerical completion on the literal nonrenewed lift. The full accepted
observation and path, all old coordinates, and the original event mass are
retained. The current input belongs to the inserted source. -/
theorem nonrenewedLift_numerical_completion
    (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T) :
    ∀ᵐ (wv : (ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t ×
      ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) ×
      AssignmentParameterFibreKernel.AssignmentVector p)
        ∂ReferenceFirstNextInvocationJointLift.nonrenewedLiftLaw rate rewards C_star C_h u t control0,
      let z : SourceInput p := wv.1.1.val
      let a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p := wv.1.2
      let z' : SourceInput p := ReferenceFirstNextInvocationJointLift.insertedSource t z wv.2
      let hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
        rate rewards C_star C_h u t := wv.1.1.property.1
      let hz' : z' ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
        rate rewards C_star C_h u t :=
        (ReferenceFirstNextInvocationJointLift.insertEvent rate rewards C_star C_h u t wv.1.1 wv.2).property.1
      let W := actualOriginalWord rate rewards C_star C_h z (firstCall_launch rate rewards C_star C_h u t z hz)
      let W' := actualOriginalWord rate rewards C_star C_h z' (firstCall_launch rate rewards C_star C_h u t z' hz')
      let S := RecordedQueueRun.run Q (W.take (t.val - start z))
      ReferenceFirstNextInvocationJointLift.nextInvocationObservation rate rewards C_star C_h u t control0
        (ReferenceFirstNextInvocationJointLift.insertEvent rate rewards C_star C_h u t wv.1.1 wv.2, a) =
        ReferenceFirstNextInvocationJointLift.nextInvocationObservation rate rewards C_star C_h u t control0 wv.1 ∧
      W'.take (t.val - start z') = W.take (t.val - start z) ∧
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
        rate rewards C_star C_h control0 t z' = some (S.registers, S.overflow, S.records) ∧
      (∃ c, c.enabled = true ∧ W'[t.val - start z']? = some c ∧
        ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationRawArrivals
          rate rewards C_star C_h t z' = some (RecordedQueueRun.quantizedArrival Q c) ∧
        ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
          rate rewards C_star C_h control0 t z' =
          some (ReferenceFirstLivePostUpdateProposalLaw.numericalUpdateFields rate
            (S.registers, S.overflow, S.records) (RecordedQueueRun.quantizedArrival Q c))) ∧
      ∃ e, (extendedPast rate rewards C_star C_h t.castSucc (z, a)).getLast? = some e ∧
        (extendedPast rate rewards C_star C_h t.castSucc (z', a)).getLast? = some e ∧
        e.time.val + 1 ≤ t.val ∧ S.registers = e.after.registers ∧ S.overflow = e.after.overflow ∧
        ∀ j, S.records j = e.after.records j ++ List.replicate (t.val - (e.time.val + 1)) (false, 0) := by
  apply Filter.Eventually.of_forall
  intro wv
  dsimp only
  have hz := wv.1.1.property.1
  obtain ⟨_before, c, _hbefore, henabled, hcurrent, hb, hraw, hupdate⟩ :=
    firstCall_insertVector_numericalUpdate rate rewards C_star C_h control0 u t
      wv.1.1.val hz wv.1.2 wv.2
  exact ⟨ReferenceFirstNextInvocationJointLift.nextInvocationObservation_insertVector
      rate rewards C_star C_h u t control0 wv.1.1 wv.1.2 wv.2,
    firstCall_insertVector_strictPast rate rewards C_star C_h control0 u t wv.1.1.val hz wv.1.2 wv.2,
    hb, ⟨c, henabled, hcurrent, hraw, hupdate⟩,
    firstCall_insertVector_last_completion rate rewards C_star C_h control0 u t wv.1.1.val hz wv.1.2 wv.2⟩

/-- The same numerical provenance on the literal renewal lift. Label zero,
the complete original private arrays, and the generated old list remain
joint in the accepted observation; the renewal draw is its existing draw. -/
theorem renewalLift_numerical_completion
    (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T) :
    ∀ᵐ wv ∂ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw rate rewards C_star C_h u t,
      let z : SourceInput p := wv.1.1.val
      let a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p := wv.1.2
      let z' : SourceInput p := (ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t wv).2.val
      let hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
        rate rewards C_star C_h u t := wv.1.1.property.1
      let hz' : z' ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
        rate rewards C_star C_h u t :=
        (ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t wv).2.property.1
      let W := actualOriginalWord rate rewards C_star C_h z (firstCall_launch rate rewards C_star C_h u t z hz)
      let W' := actualOriginalWord rate rewards C_star C_h z' (firstCall_launch rate rewards C_star C_h u t z' hz')
      let S := RecordedQueueRun.run Q (W.take (t.val - start z))
      extendedObservation rate rewards C_star C_h control0 t.castSucc (z', a) =
        extendedObservation rate rewards C_star C_h control0 t.castSucc (z, a) ∧
      W'.take (t.val - start z') = W.take (t.val - start z) ∧
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
        rate rewards C_star C_h control0 t z' = some (S.registers, S.overflow, S.records) ∧
      (∃ c, c.enabled = true ∧ W'[t.val - start z']? = some c ∧
        ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationRawArrivals
          rate rewards C_star C_h t z' = some (RecordedQueueRun.quantizedArrival Q c) ∧
        ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
          rate rewards C_star C_h control0 t z' =
          some (ReferenceFirstLivePostUpdateProposalLaw.numericalUpdateFields rate
            (S.registers, S.overflow, S.records) (RecordedQueueRun.quantizedArrival Q c))) ∧
      ∃ e, (extendedPast rate rewards C_star C_h t.castSucc (z, a)).getLast? = some e ∧
        (extendedPast rate rewards C_star C_h t.castSucc (z', a)).getLast? = some e ∧
        e.time.val + 1 ≤ t.val ∧ S.registers = e.after.registers ∧ S.overflow = e.after.overflow ∧
        ∀ j, S.records j = e.after.records j ++ List.replicate (t.val - (e.time.val + 1)) (false, 0) := by
  apply Filter.Eventually.of_forall
  intro wv
  have ho := ReferenceFirstNextInvocationJointLift.renewal_pair_oldObservation
    rate rewards C_star C_h u t control0 wv
  dsimp only [ReferenceFirstCollectionRenewalInstallationCoupling.pair] at ho ⊢
  simp only [ReferenceFirstCollectionRenewalVectorInsertion.put_val] at ho ⊢
  have hz := wv.1.1.property.1
  obtain ⟨_before, c, _hbefore, henabled, hcurrent, hb, hraw, hupdate⟩ :=
    firstCall_insertVector_numericalUpdate rate rewards C_star C_h control0 u t
      wv.1.1.val hz wv.1.2 wv.2
  exact ⟨ho,
    firstCall_insertVector_strictPast rate rewards C_star C_h control0 u t wv.1.1.val hz wv.1.2 wv.2,
    hb, ⟨c, henabled, hcurrent, hraw, hupdate⟩,
    firstCall_insertVector_last_completion rate rewards C_star C_h control0 u t wv.1.1.val hz wv.1.2 wv.2⟩

/-- On the existing unnormalized renewal pair law, accepted incoming-prefix
invariance identifies both sources' incoming lists with the old original
word. It also retains the same complete generated old observation. -/
theorem renewalPairLaw_numerical_completion
    (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T) :
    ∀ᵐ b ∂ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw rate rewards C_star C_h u t,
      let z := b.1.1.val
      let W := actualOriginalWord rate rewards C_star C_h z
        (firstCall_launch rate rewards C_star C_h u t z b.1.1.property.1)
      ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells rate rewards C_star C_h u t b.2 =
        W.take (t.val - start z) ∧
      ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming rate rewards C_star C_h u t b.2 =
        RecordedQueueRun.run Q (W.take (t.val - start z)) ∧
      extendedObservation rate rewards C_star C_h control0 t.castSucc (b.2.val, b.1.2) =
        extendedObservation rate rewards C_star C_h control0 t.castSucc (z, b.1.2) := by
  have he := ReferenceFirstCollectionRenewalInstallationCoupling.pair_measurableEmbedding rate rewards C_star C_h u t
  have hs := MeasureTheory.ae_map_mem_range he.measurableSet_range he.measurable.aemeasurable
    (μ := ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw rate rewards C_star C_h u t)
  change ∀ᵐ b ∂ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw rate rewards C_star C_h u t,
    b ∈ Set.range (ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t) at hs
  filter_upwards [ReferenceFirstCollectionRenewalIncomingQueuePrefix.ae_actual_incoming_factor
    rate rewards C_star C_h u t control0, hs] with b hb hsupport
  have hprefix := hb.1.trans
    (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming_prefix_suffix
      rate rewards C_star C_h u t control0 b.1.1).symm
  have hword := hprefix.trans (renewalIncoming_prefix_eq_original rate rewards C_star C_h u t b.1.1)
  refine ⟨hword, congrArg (RecordedQueueRun.run Q) hword, ?_⟩
  obtain ⟨wv, rfl⟩ := hsupport
  exact ReferenceFirstNextInvocationJointLift.renewal_pair_oldObservation rate rewards C_star C_h u t control0 wv

/-- Every arm's accepted-record array counts actual calendar dates, even
when no logical cell was appended on some of those dates. -/
theorem originalWord_records_length (z : SourceInput p)
    (hlaunch : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active)
    (n : Fin (p.T + 1)) (hsn : start z ≤ n.val) (j : Fin p.K) :
    ((RecordedQueueRun.run Q
      ((actualOriginalWord rate rewards C_star C_h z hlaunch).take (n.val - start z))).records j).length =
      n.val - start z := by
  have hb := (originalWord_calendar_prefix rate rewards C_star C_h z hlaunch n hsn).2.1
  simpa only [RecordedQueueRun.run, RecordedQueueRun.initialState, List.length_nil, Nat.zero_add,
    List.length_take, Nat.min_eq_left hb] using
    RecordedEpisodeStability.execute_records_length Q
      ((actualOriginalWord rate rewards C_star C_h z hlaunch).take (n.val - start z))
      (RecordedQueueRun.initialState p.K) j

/-- Before and after histories at each actual generated cell have the full
elapsed calendar lengths, rather than the generated-list index. -/
theorem firstCall_generatedPast_record_lengths (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (n : Fin (p.T + 1)) (hnt : n.val ≤ t.val) (e : LogicalCell p rate)
    (he : e ∈ extendedPast rate rewards C_star C_h n (z, a)) (j : Fin p.K) :
    (e.before.records j).length = e.time.val - start z ∧
      (e.after.records j).length = e.time.val + 1 - start z := by
  have hs := (firstCall_generatedPast_chronology rate rewards C_star C_h u t z hz a n hnt).2.1 e he |>.1
  obtain ⟨_hk, _hnum, hbefore, hafter, _harr, _hservice, _hall⟩ :=
    firstCall_generatedPast_cell_data rate rewards C_star C_h u t z hz a n e he
  rw [hbefore, hafter]
  exact ⟨originalWord_records_length rate rewards C_star C_h z
      (firstCall_launch rate rewards C_star C_h u t z hz) e.time.castSucc hs j,
    originalWord_records_length rate rewards C_star C_h z
      (firstCall_launch rate rewards C_star C_h u t z hz) e.time.succ (by simpa only [Fin.val_succ] using hs.trans (Nat.le_succ _)) j⟩

/-- Full-state equality is valid at a last-cell successor boundary. A
nonzero omitted-date gap instead requires `last_completion`'s padding. -/
theorem firstCall_generatedPast_noGap_state (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (n : Fin (p.T + 1)) (hnt : n.val ≤ t.val) (e : LogicalCell p rate)
    (hlast : (extendedPast rate rewards C_star C_h n (z, a)).getLast? = some e)
    (hdate : e.time.val + 1 = n.val) :
    RecordedQueueRun.run Q ((actualOriginalWord rate rewards C_star C_h z
      (firstCall_launch rate rewards C_star C_h u t z hz)).take (n.val - start z)) = e.after := by
  have hne : extendedPast rate rewards C_star C_h n (z, a) ≠ [] := by
    intro h
    rw [h] at hlast
    cases hlast
  obtain ⟨f, hlastf, _hf, _hsf, _hfn, _hdisabled, hreg, hover, hrecords⟩ :=
    firstCall_generatedPast_last_completion rate rewards C_star C_h u t z hz a n hnt hne
  have hfe : f = e := Option.some.inj (hlastf.symm.trans hlast)
  subst f
  apply stateReadout_injective
  apply Prod.ext hreg
  apply Prod.ext hover
  funext j
  simpa only [ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout,
    hdate, Nat.sub_self, List.replicate_zero, List.append_nil] using hrecords j

/-- The inserted current source entry drives the literal all-arm canonical
step from the completed prestate. The first detecting update is included. -/
theorem firstCall_insertVector_numericalUpdate_eq_step
    (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (v : AssignmentParameterFibreKernel.AssignmentVector p) :
    let z' := ReferenceFirstNextInvocationJointLift.insertedSource t z v
    let W' := actualOriginalWord rate rewards C_star C_h z'
      (firstCall_launch rate rewards C_star C_h u t z'
        (firstCall_insertVector_mem rate rewards C_star C_h u t z hz v))
    let W := actualOriginalWord rate rewards C_star C_h z
      (firstCall_launch rate rewards C_star C_h u t z hz)
    let S := RecordedQueueRun.run Q (W.take (t.val - start z))
    ∃ c : RecordedQueueRun.RoundInput p.K,
      c.enabled = true ∧ W'[t.val - start z']? = some c ∧
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
        rate rewards C_star C_h control0 t z' = some (S.registers, S.overflow, S.records) ∧
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
        rate rewards C_star C_h control0 t z' = some
          { raw := RecordedQueueRun.quantizedArrival Q c
            beforeRegisters := S.registers
            beforeOverflow := S.overflow
            beforeRecords := S.records
            accepted := RecordedQueueRun.acceptedRecord Q S c
            service := fun j => RecordedQueueRun.recordService (4 * rate.n)
              (S.registers j) (RecordedQueueRun.acceptedRecord Q S c j)
            afterRegisters := (RecordedQueueRun.step Q S c).registers
            afterOverflow := (RecordedQueueRun.step Q S c).overflow
            afterRecords := (RecordedQueueRun.step Q S c).records } := by
  obtain ⟨_before, c, _hbefore, henabled, hcurrent, hb, _hraw, hupdate⟩ :=
    firstCall_insertVector_numericalUpdate rate rewards C_star C_h control0 u t z hz a v
  refine ⟨c, henabled, hcurrent, hb, ?_⟩
  exact hupdate.trans (congrArg some
    (ReferenceFirstLivePostUpdateProposalLaw.numericalUpdateFields_eq_step rate _ c henabled))

end Bandits.Support.ReferenceFirstCollectionLogicalNumericalAlignment

end
