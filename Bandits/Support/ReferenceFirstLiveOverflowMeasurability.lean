/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveOverflowReadout

import Lean.Elab.Tactic.Omega

/-!
# Borel inclusive overflow readouts on the actual first-live window

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,246-264`,
`05_binary_transport.tex:354-431`, `06_interruptions.tex:246-296,355-408`,
`08_main_theorem.tex:29-42`, and `appendix_a_local_protocol.tex:28-64`.

The overflow index is measured from the actual all-arm arrival readout. Its
countable-list calculation is factored exactly through the existing unstopped
queue replay. Inclusive records are then taken from the original measured
first-live census, retaining the crossing update and its complete diagnostics.
The original-source results use the actual no-launch and elapsed-time launch
strata. They do not assert a global overflow law or stopping-time property.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open MeasureTheory

namespace Bandits.Support.ReferenceFirstLiveOverflowMeasurability

variable {p : Parameters}

private abbrev ArrivalCode (K : ℕ) := Bool × (Fin K → ℕ)

/-- The list space below is the existing length-and-index observation comap.
Its countable source type has measurable singletons in that inherited space. -/
private theorem measurableSingleton_listObservation {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (List α) := by
  have hinj : Function.Injective
      (ReferenceActiveHorizonMeasurability.listObservationCoordinates (α := α)) := by
    intro left right h
    apply List.ext_getElem?
    intro n
    have hn := congrFun (congrArg Prod.snd h) n
    change ReferenceActiveHorizonMeasurability.listObservationAt left n =
      ReferenceActiveHorizonMeasurability.listObservationAt right n at hn
    unfold ReferenceActiveHorizonMeasurability.listObservationAt at hn
    cases hl : left[n]? <;> cases hr : right[n]? <;> simp_all
  constructor
  intro records
  have heq : ({records} : Set (List α)) =
      ReferenceActiveHorizonMeasurability.listObservationCoordinates ⁻¹'
        {ReferenceActiveHorizonMeasurability.listObservationCoordinates records} := by
    ext other
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · intro h
      subst other
      rfl
    · intro h
      exact hinj h
  let : MeasurableSingletonClass (Unit ⊕ α) := ⟨fun tag => by
    cases tag with
    | inl value =>
        simpa only [Set.image_singleton] using
          (measurableSet_singleton value).inl_image
    | inr value =>
        simpa only [Set.image_singleton] using
          (measurableSet_singleton value).inr_image⟩
  rw [heq]
  exact (measurableSet_singleton _).preimage
    ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates

private instance arrivalCodeListMeasurableSingletonClass (K : ℕ) :
    MeasurableSingletonClass (List (ArrivalCode K)) :=
  measurableSingleton_listObservation (α := ArrivalCode K)

private def arrivalRecord {K : ℕ} (code : ArrivalCode K) (arm : Fin K) :
    Bool × ℕ :=
  if code.1 then (true, code.2 arm) else (false, 0)

private def arrivalReplay (q : RecordedQueueRun.Parameters)
    (codes : List (ArrivalCode p.K)) (n : ℕ) (arm : Fin p.K) : ℕ × ℕ :=
  QueueReplay.replay (4 * q.n) (0, 0)
    ((codes.take n).map fun code => arrivalRecord code arm)

private def arrivalReplayCrosses (q : RecordedQueueRun.Parameters)
    (codes : List (ArrivalCode p.K)) (n : ℕ) : Prop :=
  ∃ arm, 32 * (arrivalReplay q codes n arm).2 > q.D

private noncomputable def arrivalOverflowPrefix (q : RecordedQueueRun.Parameters)
    (codes : List (ArrivalCode p.K)) : ℕ := by
  classical
  exact if h : ∃ n, 1 ≤ n ∧ n ≤ codes.length ∧ arrivalReplayCrosses q codes n then
    Nat.find h else codes.length + 1

private def cellArrivalReadout (q : RecordedQueueRun.Parameters)
    (cells : List (RecordedQueueRun.RoundInput p.K)) : List (ArrivalCode p.K) :=
  cells.map fun cell =>
    (cell.enabled, fun arm => RecordedQueueRun.quantizedArrival q cell arm)

/-- The source replay uses exactly the enabled/whole-arm-arrival list, with
disabled records preserving queues and enabled zero arrivals still serving. -/
private theorem unstoppedReplay_eq_arrivalReplay
    (q : RecordedQueueRun.Parameters)
    (cells : List (RecordedQueueRun.RoundInput p.K)) (n : ℕ) (arm : Fin p.K) :
    UnstoppedRecordedQueueComparison.unstoppedReplay q cells n arm =
      arrivalReplay q (cellArrivalReadout q cells) n arm := by
  have hrecords :
      ((cellArrivalReadout q cells).take n).map (fun code => arrivalRecord code arm) =
        (cells.take n).map fun cell =>
          UnstoppedRecordedQueueComparison.unstoppedRecord q cell arm := by
    simp only [cellArrivalReadout, List.map_take, List.map_map, Function.comp_def]
    have hfun :
        (fun cell : RecordedQueueRun.RoundInput p.K =>
          arrivalRecord
            (cell.enabled, fun a => RecordedQueueRun.quantizedArrival q cell a) arm) =
        (fun cell => UnstoppedRecordedQueueComparison.unstoppedRecord q cell arm) := by
      funext cell
      cases cell
      rfl
    rw [hfun]
  change QueueReplay.replay (4 * q.n) (0, 0)
      ((cells.take n).map fun cell =>
        UnstoppedRecordedQueueComparison.unstoppedRecord q cell arm) =
    QueueReplay.replay (4 * q.n) (0, 0)
      (((cellArrivalReadout q cells).take n).map fun code => arrivalRecord code arm)
  rw [hrecords]

private theorem replay_crosses_iff_arrivalReadout
    (q : RecordedQueueRun.Parameters)
    (cells : List (RecordedQueueRun.RoundInput p.K)) (n : ℕ) :
    UnstoppedRecordedQueueComparison.replay_crosses_overflow q cells n ↔
      arrivalReplayCrosses q (cellArrivalReadout q cells) n := by
  unfold UnstoppedRecordedQueueComparison.replay_crosses_overflow arrivalReplayCrosses
  simp only [unstoppedReplay_eq_arrivalReplay]

/-- Exact factorization of the existing first-overflow search through the
countable all-arm arrival readout. -/
private theorem firstOverflowPrefix_eq_arrivalReadout
    (q : RecordedQueueRun.Parameters)
    (cells : List (RecordedQueueRun.RoundInput p.K)) :
    UnstoppedRecordedQueueComparison.firstOverflowPrefix q cells =
      arrivalOverflowPrefix q (cellArrivalReadout q cells) := by
  classical
  have hsearch :
      (∃ n, 1 ≤ n ∧ n ≤ cells.length ∧
        UnstoppedRecordedQueueComparison.replay_crosses_overflow q cells n) =
      (∃ n, 1 ≤ n ∧ n ≤ (cellArrivalReadout q cells).length ∧
        arrivalReplayCrosses q (cellArrivalReadout q cells) n) := by
    apply propext
    constructor
    · rintro ⟨n, hn, hlen, hcross⟩
      exact ⟨n, hn, by simpa [cellArrivalReadout] using hlen,
        (replay_crosses_iff_arrivalReadout q cells n).mp hcross⟩
    · rintro ⟨n, hn, hlen, hcross⟩
      exact ⟨n, hn, by simpa [cellArrivalReadout] using hlen,
        (replay_crosses_iff_arrivalReadout q cells n).mpr hcross⟩
  have hlen : cells.length = (cellArrivalReadout q cells).length := by
    simp [cellArrivalReadout]
  have hpred (n : ℕ) :
      (1 ≤ n ∧ n ≤ cells.length ∧
        UnstoppedRecordedQueueComparison.replay_crosses_overflow q cells n) ↔
      (1 ≤ n ∧ n ≤ (cellArrivalReadout q cells).length ∧
        arrivalReplayCrosses q (cellArrivalReadout q cells) n) := by
    simp only [hlen, replay_crosses_iff_arrivalReadout]
  unfold UnstoppedRecordedQueueComparison.firstOverflowPrefix arrivalOverflowPrefix
  by_cases h : ∃ n, 1 ≤ n ∧ n ≤ cells.length ∧
      UnstoppedRecordedQueueComparison.replay_crosses_overflow q cells n
  · have h' : ∃ n, 1 ≤ n ∧ n ≤ (cellArrivalReadout q cells).length ∧
        arrivalReplayCrosses q (cellArrivalReadout q cells) n :=
      hsearch.mp h
    rw [dite_eq_left h, dite_eq_left h']
    have hfind : Nat.find h = Nat.find h' :=
      Nat.find_congr' (fun {n} => hpred n)
    rw [hfind]
  · have h' : ¬ ∃ n, 1 ≤ n ∧ n ≤ (cellArrivalReadout q cells).length ∧
        arrivalReplayCrosses q (cellArrivalReadout q cells) n :=
      fun hq => h (hsearch.mpr hq)
    rw [dite_eq_right h, dite_eq_right h']
    rw [hlen]

private theorem firstOverflowPrefix_nil (q : RecordedQueueRun.Parameters) :
    UnstoppedRecordedQueueComparison.firstOverflowPrefix q
      ([] : List (RecordedQueueRun.RoundInput p.K)) = 1 := by
  classical
  unfold UnstoppedRecordedQueueComparison.firstOverflowPrefix
  have hnone : ¬ ∃ n, 1 ≤ n ∧ n ≤ ([] : List (RecordedQueueRun.RoundInput p.K)).length ∧
      UnstoppedRecordedQueueComparison.replay_crosses_overflow (K := p.K) q
        ([] : List (RecordedQueueRun.RoundInput p.K)) n := by
    rintro ⟨n, hn, hlen, _⟩
    simp at hlen
    omega
  rw [dite_eq_right hnone]
  simp

section Fiber

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (s count : ℕ) (hspan : s + count ≤ p.T)

/-- The actual first-live overflow prefix is Borel on the inherited launch
fibre. -/
theorem measurable_firstLiveOverflowPrefix :
    Measurable (ReferenceFirstLiveOverflowReadout.firstLiveOverflowPrefix
      rate rewards C_star C_h s count hspan) := by
  have hreadout : Measurable (fun x : ReferenceFirstLiveOverflowReadout.LaunchFiber
      rate rewards C_star C_h s =>
      cellArrivalReadout (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (ReferenceFirstLiveOverflowReadout.firstLiveCells
          rate rewards C_star C_h s count hspan x)) := by
    simpa only [cellArrivalReadout, ReferenceFirstLiveOverflowReadout.firstLiveCells,
      ReferenceFirstLiveOverflowReadout.firstLiveOverflowPrefix,
      RecordedQueueRun.quantizedArrival,
      ReferenceFirstLaunchNumericalCell.queueParameters] using
      ReferenceFirstLiveOverflowReadout.measurable_firstLiveArrivalReadout
        rate rewards C_star C_h s count hspan
  have hm : Measurable (fun codes : List (ArrivalCode p.K) =>
      arrivalOverflowPrefix
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) codes) :=
    measurable_of_countable _
  have heq :
      (fun x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s =>
        ReferenceFirstLiveOverflowReadout.firstLiveOverflowPrefix
          rate rewards C_star C_h s count hspan x) =
      (fun x => arrivalOverflowPrefix (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (cellArrivalReadout (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (ReferenceFirstLiveOverflowReadout.firstLiveCells
            rate rewards C_star C_h s count hspan x))) := by
    funext x
    exact firstOverflowPrefix_eq_arrivalReadout
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (ReferenceFirstLiveOverflowReadout.firstLiveCells
        rate rewards C_star C_h s count hspan x)
  change Measurable (fun x : ReferenceFirstLiveOverflowReadout.LaunchFiber
    rate rewards C_star C_h s =>
      ReferenceFirstLiveOverflowReadout.firstLiveOverflowPrefix
        rate rewards C_star C_h s count hspan x)
  rw [heq]
  exact hm.comp hreadout

/-- The inclusive prefix length is the measured minimum of live length and
the one-based overflow prefix. -/
theorem measurable_firstLiveInclusiveCount :
    Measurable (ReferenceFirstLiveOverflowReadout.firstLiveInclusiveCount
      rate rewards C_star C_h s count hspan) := by
  have hmin : Measurable (fun pair : ℕ × ℕ => min pair.1 pair.2) :=
    measurable_of_countable _
  change Measurable (fun x : ReferenceFirstLiveOverflowReadout.LaunchFiber
    rate rewards C_star C_h s =>
      min (ReferenceFirstLiveOverflowReadout.firstLiveLength
        rate rewards C_star C_h s count hspan x)
        (ReferenceFirstLiveOverflowReadout.firstLiveOverflowPrefix
          rate rewards C_star C_h s count hspan x))
  exact hmin.comp
    ((ReferenceFirstLiveOverflowReadout.measurable_firstLiveLength
      rate rewards C_star C_h s count hspan).prodMk
      (measurable_firstLiveOverflowPrefix rate rewards C_star C_h s count hspan))

private theorem measurable_list_take {X α : Type*} [MeasurableSpace X]
    [MeasurableSpace α] (records : X → List α) (hrecords : Measurable records)
    (n : X → ℕ) (hn : Measurable n) :
    Measurable (fun x => (records x).take (n x)) := by
  classical
  have hc := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp
    hrecords
  have hlen : Measurable (fun x => min (n x) (records x).length) :=
    (measurable_of_countable (fun v : ℕ × ℕ => min v.1 v.2)).comp
      (hn.prodMk (measurable_fst.comp hc))
  have ht : Measurable (fun x => fun j =>
      ReferenceActiveHorizonMeasurability.listObservationAt ((records x).take (n x)) j) := by
    apply measurable_pi_iff.mpr
    intro j
    have htag := (measurable_pi_apply j).comp (measurable_snd.comp hc)
    have h : Measurable (fun x => if j < n x then
        ReferenceActiveHorizonMeasurability.listObservationAt (records x) j
        else (Sum.inl () : Unit ⊕ α)) :=
      htag.ite (measurableSet_lt (measurable_const (a := j)) hn) measurable_const
    convert h using 1
    funext x
    unfold ReferenceActiveHorizonMeasurability.listObservationAt
    rw [List.getElem?_take]
    by_cases hj : j < n x
    · simp only [hj, ite_true]
    · simp only [hj, ite_false]
  apply measurable_comap_iff.mpr
  convert hlen.prodMk ht using 1
  funext x
  exact Prod.ext List.length_take rfl

/-- The measured uncut census, taken to the inclusive count, keeps the
crossing record and every diagnostic carried by that original record. -/
theorem measurable_firstLiveInclusiveCensus :
    Measurable (ReferenceFirstLiveOverflowReadout.firstLiveInclusiveCensus
      rate rewards C_star C_h s count hspan) := by
  have htake := measurable_list_take
    (fun x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s =>
      (ReferenceFirstLiveOverflowReadout.firstLiveWindow
        rate rewards C_star C_h s count hspan x).map
        ReferenceActiveHorizonMeasurability.roundRecordCode)
    (ReferenceFirstLiveOverflowReadout.measurable_firstLiveWindowCensus
      rate rewards C_star C_h s count hspan)
    (ReferenceFirstLiveOverflowReadout.firstLiveInclusiveCount
      rate rewards C_star C_h s count hspan)
    (measurable_firstLiveInclusiveCount rate rewards C_star C_h s count hspan)
  change Measurable (fun x : ReferenceFirstLiveOverflowReadout.LaunchFiber
    rate rewards C_star C_h s =>
      (ReferenceFirstLiveOverflowReadout.firstLiveWindow
        rate rewards C_star C_h s count hspan x).take
        (ReferenceFirstLiveOverflowReadout.firstLiveInclusiveCount
          rate rewards C_star C_h s count hspan x) |>.map
            ReferenceActiveHorizonMeasurability.roundRecordCode)
  convert htake using 1
  funext x
  rw [← List.map_take]

/-- The literal calendar overflow round is Borel, with `none` when the
one-based prefix is the no-crossing sentinel. -/
theorem measurable_firstLiveOverflowRound :
    Measurable (ReferenceFirstLiveOverflowReadout.firstLiveOverflowRound
      rate rewards C_star C_h s count hspan) := by
  have hround : Measurable (fun pair : ℕ × ℕ =>
      if pair.1 ≤ pair.2 then some (s + pair.1) else none) := measurable_of_countable _
  change Measurable (fun x : ReferenceFirstLiveOverflowReadout.LaunchFiber
    rate rewards C_star C_h s =>
      if ReferenceFirstLiveOverflowReadout.firstLiveOverflowPrefix
          rate rewards C_star C_h s count hspan x ≤
        ReferenceFirstLiveOverflowReadout.firstLiveLength
          rate rewards C_star C_h s count hspan x then
        some (s + ReferenceFirstLiveOverflowReadout.firstLiveOverflowPrefix
          rate rewards C_star C_h s count hspan x) else none)
  exact hround.comp
    ((measurable_firstLiveOverflowPrefix rate rewards C_star C_h s count hspan).prodMk
      (ReferenceFirstLiveOverflowReadout.measurable_firstLiveLength
        rate rewards C_star C_h s count hspan))

end Fiber

section OriginalSource

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- Measurability assembled over actual no-launch and elapsed-time launch
strata, with every stratum an inherited generated-launch fibre. -/
private theorem measurable_on_generated_fibers {Y : Type*} [MeasurableSpace Y]
    (f : BootstrapPrivateRoundStreams.SourceInput p → Y) (empty : Y)
    (hno : ∀ source, (ReferenceCompletePhysicalHistory.generatedBoundary
      rate source rewards C_star C_h).crossing = none → f source = empty)
    (hf : ∀ s : Fin (p.T + 1), Measurable
      (fun x : ReferenceFirstLiveOverflowReadout.LaunchFiber
        rate rewards C_star C_h s.val => f x.val)) : Measurable f := by
  let cover (tag : Option (Fin (p.T + 1))) :
      Set (BootstrapPrivateRoundStreams.SourceInput p) :=
    match tag with
    | none => {source | (ReferenceCompletePhysicalHistory.generatedBoundary
        rate source rewards C_star C_h).crossing = none}
    | some s =>
        {source | (ReferenceCompletePhysicalHistory.generatedBoundary
            rate source rewards C_star C_h).crossing.isSome = true ∧
          ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = s.val}
  have hm (tag) : MeasurableSet (cover tag) := by
    cases tag with
    | none =>
        exact ReferenceCorrectedLaunchMeasurability.measurableSet_generated_no_crossing
          rate rewards C_star C_h
    | some s =>
        change MeasurableSet {source : BootstrapPrivateRoundStreams.SourceInput p |
          (ReferenceCompletePhysicalHistory.generatedBoundary
              rate source rewards C_star C_h).crossing.isSome = true ∧
            ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = s.val}
        simpa [ReferenceCompletePhysicalHistory.generatedBoundary,
          ReferenceCompletePhysicalHistory.physicalStart,
          ReferenceCompletePhysicalHistory.generatedInput] using
          ReferenceCorrectedLaunchMeasurability.measurableSet_generated_launch_start_fiber
            rate rewards C_star C_h s.val
  have hc (source) : ∃ tag, source ∈ cover tag := by
    cases h : (ReferenceCompletePhysicalHistory.generatedBoundary
        rate source rewards C_star C_h).crossing with
    | none => exact ⟨none, h⟩
    | some crossing =>
        exact ⟨some ⟨ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h,
          Nat.lt_succ_of_le (ReferenceCompletePhysicalHistory.physicalStart_le_T
            rate source rewards C_star C_h)⟩, by
          simp only [cover, h, Option.isSome_some, true_and, Set.mem_ofPred_eq]⟩
  have hr (tag) : Measurable (fun x : cover tag => f x.val) := by
    cases tag with
    | none =>
        exact measurable_const' (fun x y =>
          (hno x.val x.property).trans (hno y.val y.property).symm)
    | some s =>
        change Measurable (fun x : ReferenceFirstLiveOverflowReadout.LaunchFiber
          rate rewards C_star C_h s.val => f x.val)
        exact hf s
  intro u hu
  have heq : f ⁻¹' u = ⋃ tag, (Subtype.val : cover tag → _) '' {x | f x.val ∈ u} := by
    ext source
    constructor
    · intro hx
      obtain ⟨tag, ht⟩ := hc source
      exact Set.mem_iUnion.mpr ⟨tag, ⟨source, ht⟩, hx, rfl⟩
    · intro hx
      obtain ⟨tag, htag⟩ := Set.mem_iUnion.mp hx
      obtain ⟨x, hxu, hxs⟩ := htag
      rw [← hxs]
      exact hxu
  rw [heq]
  exact MeasurableSet.iUnion (fun tag => MeasurableSet.subtype_image (hm tag) (hr tag hu))

/-- The exact original-source overflow prefix is Borel, including the genuine
empty no-launch branch. -/
theorem measurable_wholeFirstLiveOverflowPrefix :
    Measurable (ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowPrefix
      rate rewards C_star C_h) := by
  apply measurable_on_generated_fibers rate rewards C_star C_h _ 1
  · intro source hc
    have hcells := (ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
      rate rewards C_star C_h source hc).2.1
    rw [ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowPrefix, hcells]
    exact firstOverflowPrefix_nil (ReferenceFirstLaunchNumericalCell.queueParameters rate)
  · intro s
    have hreadouts := ReferenceFirstLiveOverflowReadout.wholeFirstLive_readouts_on_fiber
      rate rewards C_star C_h s
    have heq :
        (fun x : ReferenceFirstLiveOverflowReadout.LaunchFiber
          rate rewards C_star C_h s.val =>
          ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowPrefix
            rate rewards C_star C_h x.val) =
        ReferenceFirstLiveOverflowReadout.firstLiveOverflowPrefix
          rate rewards C_star C_h s.val (p.T - s.val)
            (ReferenceFirstLiveOverflowReadout.maximal_span s) := by
      funext x
      exact (hreadouts x).2.2.1
    rw [heq]
    exact measurable_firstLiveOverflowPrefix rate rewards C_star C_h s.val
      (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s)

/-- The exact original-source inclusive count is Borel; its no-launch value
is the minimum with the actual one-based empty-prefix sentinel. -/
theorem measurable_wholeFirstLiveInclusiveCount :
    Measurable (ReferenceFirstLiveOverflowReadout.wholeFirstLiveInclusiveCount
      rate rewards C_star C_h) := by
  apply measurable_on_generated_fibers rate rewards C_star C_h _ 0
  · intro source hc
    have hlength := (ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
      rate rewards C_star C_h source hc).2.2.1
    simp [ReferenceFirstLiveOverflowReadout.wholeFirstLiveInclusiveCount, hlength]
  · intro s
    have hreadouts := ReferenceFirstLiveOverflowReadout.wholeFirstLive_readouts_on_fiber
      rate rewards C_star C_h s
    have heq :
        (fun x : ReferenceFirstLiveOverflowReadout.LaunchFiber
          rate rewards C_star C_h s.val =>
          ReferenceFirstLiveOverflowReadout.wholeFirstLiveInclusiveCount
            rate rewards C_star C_h x.val) =
        ReferenceFirstLiveOverflowReadout.firstLiveInclusiveCount
          rate rewards C_star C_h s.val (p.T - s.val)
            (ReferenceFirstLiveOverflowReadout.maximal_span s) := by
      funext x
      exact (hreadouts x).2.2.2.1
    rw [heq]
    exact measurable_firstLiveInclusiveCount rate rewards C_star C_h s.val
      (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s)

/-- The exact original-source inclusive census is Borel in the existing
lossless `RoundRecordCode` list observation space. -/
theorem measurable_wholeFirstLiveInclusiveCensus :
    Measurable (ReferenceFirstLiveOverflowReadout.wholeFirstLiveInclusiveCensus
      rate rewards C_star C_h) := by
  apply measurable_on_generated_fibers rate rewards C_star C_h _ []
  · intro source hc
    exact (ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
      rate rewards C_star C_h source hc).2.2.2.1
  · intro s
    have hreadouts := ReferenceFirstLiveOverflowReadout.wholeFirstLive_readouts_on_fiber
      rate rewards C_star C_h s
    have heq :
        (fun x : ReferenceFirstLiveOverflowReadout.LaunchFiber
          rate rewards C_star C_h s.val =>
          ReferenceFirstLiveOverflowReadout.wholeFirstLiveInclusiveCensus
            rate rewards C_star C_h x.val) =
        ReferenceFirstLiveOverflowReadout.firstLiveInclusiveCensus
          rate rewards C_star C_h s.val (p.T - s.val)
            (ReferenceFirstLiveOverflowReadout.maximal_span s) := by
      funext x
      exact (hreadouts x).2.2.2.2.1
    rw [heq]
    exact measurable_firstLiveInclusiveCensus rate rewards C_star C_h s.val
      (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s)

/-- The exact original-source calendar overflow round is Borel, and is none
when launch is absent or the actual first-live prefix does not cross. -/
theorem measurable_wholeFirstLiveOverflowRound :
    Measurable (ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound
      rate rewards C_star C_h) := by
  apply measurable_on_generated_fibers rate rewards C_star C_h _ none
  · intro source hc
    exact (ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
      rate rewards C_star C_h source hc).2.2.2.2
  · intro s
    have hreadouts := ReferenceFirstLiveOverflowReadout.wholeFirstLive_readouts_on_fiber
      rate rewards C_star C_h s
    have heq :
        (fun x : ReferenceFirstLiveOverflowReadout.LaunchFiber
          rate rewards C_star C_h s.val =>
          ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound
            rate rewards C_star C_h x.val) =
        ReferenceFirstLiveOverflowReadout.firstLiveOverflowRound
          rate rewards C_star C_h s.val (p.T - s.val)
            (ReferenceFirstLiveOverflowReadout.maximal_span s) := by
      funext x
      exact (hreadouts x).2.2.2.2.2
    rw [heq]
    exact measurable_firstLiveOverflowRound rate rewards C_star C_h s.val
      (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s)

end OriginalSource

end Bandits.Support.ReferenceFirstLiveOverflowMeasurability

end
