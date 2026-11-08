/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Bandits Lean Project contributors
-/
module

public import Bandits.Support.ReferenceFirstLiveOriginalCalendarArrivalMoments
public import Bandits.Support.ReferenceFirstLiveRawPotentialBound

import Mathlib.Tactic

/-!
# Original-source signed first-live correction

The successor-marginal correction is the literal signed finite sum from the
actual first-live list. This module relates that exact sum to calendar
prefixes and integrates its deterministic upper bound under the original
source-input law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstLiveOriginalSignedCorrection

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ)

local notation "Q" => ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveQueue rate
local notation "u" => ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveRunAt rate rewards C_star C_h

/-- The incoming inclusion marginal of the same original first-live run at
calendar boundary `t`. -/
def thetaAt (t : Fin (p.T + 1)) (j : Fin p.K) (omega : SourceInput p) : ℝ :=
  ProductSetLaw.theta p.m
    (RecordedQueueRun.scoreWeight Q (u t.val omega)) j

/-- The accepted normalized backlog of the same first-live prefix at a calendar
boundary, using the public original calendar readout. -/
def backlogAt (t : Fin (p.T + 1)) (j : Fin p.K) (omega : SourceInput p) : ℝ :=
  ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt
    rate rewards C_star C_h j t.val omega

private abbrev CellReadout (p : Parameters) := ReferenceFirstLiveNumericalPrefixBorel.NumericalCellReadout p
private abbrev ArrivalCode (p : Parameters) := Bool × Option (Fin p.K) × (Fin p.K → ℕ)

private def cellCode (cell : CellReadout p) : ArrivalCode p :=
  (cell.1, (cell.2.1, fun i =>
    if cell.2.1 = some i then
      Nat.floor ((rate.n : ℝ) * cell.2.2.1 i / cell.2.2.2 i)
    else 0))

private theorem measurable_cellCode : Measurable (cellCode (p := p) rate) := by
  classical
  apply measurable_fst.prodMk
  apply (measurable_fst.comp measurable_snd).prodMk
  apply measurable_pi_iff.mpr
  intro i
  have hm : Measurable (fun cell : CellReadout p => cell.2.1) :=
    measurable_fst.comp measurable_snd
  have hy : Measurable (fun cell : CellReadout p => cell.2.2.1 i) :=
    (measurable_pi_apply i).comp
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hxi : Measurable (fun cell : CellReadout p => cell.2.2.2 i) :=
    (measurable_pi_apply i).comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hq : Measurable (fun cell : CellReadout p =>
      (rate.n : ℝ) * cell.2.2.1 i / cell.2.2.2 i) :=
    measurable_div.comp ((measurable_const.mul hy).prodMk hxi)
  exact (Nat.measurable_floor.comp hq).ite
    (MeasurableSet.preimage (measurableSet_singleton (some i)) hm)
    measurable_const

private def roundReadout (round : RecordedQueueRun.RoundInput p.K) : CellReadout p :=
  (round.enabled, (round.recordedArm, (round.reward, round.rate)))

private def roundCode (round : RecordedQueueRun.RoundInput p.K) : ArrivalCode p :=
  cellCode (p := p) rate (roundReadout round)

private def decodeCode (q : RecordedQueueRun.Parameters) (code : ArrivalCode p) :
    RecordedQueueRun.RoundInput p.K where
  enabled := code.1
  recordedArm := code.2.1
  reward := fun _ => 1
  rate := fun i => (q.n : ℝ) / ((code.2.2 i : ℝ) + 1 / 2)
  reward_nonneg := by intro i; norm_num
  reward_le_one := by intro i; norm_num
  rate_pos := by
    intro i
    apply div_pos (Nat.cast_pos.mpr q.n_pos)
    positivity

private theorem decodeCode_floor (q : RecordedQueueRun.Parameters)
    (code : ArrivalCode p) (i : Fin p.K) :
    Nat.floor ((q.n : ℝ) * (decodeCode (p := p) q code).reward i /
      (decodeCode (p := p) q code).rate i) = code.2.2 i := by
  have hn : 0 < (q.n : ℝ) := Nat.cast_pos.mpr q.n_pos
  have hnonneg : 0 ≤ (code.2.2 i : ℝ) + (1 / 2 : ℝ) := by positivity
  have hquot : (q.n : ℝ) * (decodeCode (p := p) q code).reward i /
      (decodeCode (p := p) q code).rate i = (code.2.2 i : ℝ) + (1 / 2 : ℝ) := by
    simp [decodeCode]
    field_simp [ne_of_gt hn,
      ne_of_gt (show 0 < (code.2.2 i : ℝ) + (1 / 2 : ℝ) by positivity)]
  rw [hquot]
  apply (Nat.floor_eq_iff hnonneg).2
  constructor <;> linarith

private theorem quantizedArrival_eq_decoded (round : RecordedQueueRun.RoundInput p.K)
    (i : Fin p.K) :
    RecordedQueueRun.quantizedArrival Q
      (decodeCode (p := p) Q (roundCode (p := p) rate round)) i =
      RecordedQueueRun.quantizedArrival Q round i := by
  have hmarker :
      (decodeCode (p := p) Q (roundCode (p := p) rate round)).recordedArm = round.recordedArm := by
    simp [decodeCode, roundCode, roundReadout, cellCode]
  rw [RecordedQueueRun.quantizedArrival, RecordedQueueRun.quantizedArrival, hmarker]
  by_cases hi : round.recordedArm = some i
  · simp only [hi]
    calc
      Nat.floor (((Q).n : ℝ) * (decodeCode (p := p) Q
          (roundCode (p := p) rate round)).reward i /
          (decodeCode (p := p) Q (roundCode (p := p) rate round)).rate i) =
        (roundCode (p := p) rate round).2.2 i :=
          decodeCode_floor (p := p) Q (roundCode (p := p) rate round) i
      _ = Nat.floor (((Q).n : ℝ) * round.reward i / round.rate i) := by
        simp [roundCode, roundReadout, cellCode, hi]
        rfl
  · simp [hi]

private theorem acceptedRecord_eq_decoded (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K) (i : Fin p.K) :
    RecordedQueueRun.acceptedRecord Q state
      (decodeCode (p := p) Q (roundCode (p := p) rate round)) i =
    RecordedQueueRun.acceptedRecord Q state round i := by
  have henabled : (decodeCode (p := p) Q (roundCode (p := p) rate round)).enabled = round.enabled := rfl
  cases hoverflow : state.overflow
  · cases hround : round.enabled
    · simp [RecordedQueueRun.acceptedRecord, hoverflow, hround, henabled]
    · simpa [RecordedQueueRun.acceptedRecord, hoverflow, hround, henabled] using
        congrArg (fun n => (true, n)) (quantizedArrival_eq_decoded (p := p) rate round i)
  · simp [RecordedQueueRun.acceptedRecord, hoverflow]

private theorem step_eq_decoded (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K) :
    RecordedQueueRun.step Q state (decodeCode (p := p) Q (roundCode (p := p) rate round)) =
      RecordedQueueRun.step Q state round := by
  cases state with
  | mk registers overflow records =>
      have hrecords :
          (fun i => RecordedQueueRun.acceptedRecord Q
            ⟨registers, overflow, records⟩
            (decodeCode (p := p) Q (roundCode (p := p) rate round)) i) =
          fun i => RecordedQueueRun.acceptedRecord Q
            ⟨registers, overflow, records⟩ round i := by
        funext i
        exact acceptedRecord_eq_decoded (p := p) rate
          ⟨registers, overflow, records⟩ round i
      simp [RecordedQueueRun.step, hrecords]

private theorem execute_eq_decoded (rounds : List (RecordedQueueRun.RoundInput p.K))
    (state : RecordedQueueRun.RunState p.K) :
    RecordedQueueRun.execute Q rounds state =
      RecordedQueueRun.execute Q (rounds.map (decodeCode (p := p) Q ∘ roundCode (p := p) rate)) state := by
  induction rounds generalizing state with
  | nil => rfl
  | cons round rounds ih =>
      change RecordedQueueRun.execute Q rounds (RecordedQueueRun.step Q state round) =
        RecordedQueueRun.execute Q
          (rounds.map (decodeCode (p := p) Q ∘ roundCode (p := p) rate))
          (RecordedQueueRun.step Q state
            (decodeCode (p := p) Q (roundCode (p := p) rate round)))
      rw [step_eq_decoded (p := p) rate state round]
      exact ih _

private theorem run_eq_decoded (rounds : List (RecordedQueueRun.RoundInput p.K)) :
    RecordedQueueRun.run Q rounds =
      RecordedQueueRun.run Q (rounds.map (decodeCode (p := p) Q ∘ roundCode (p := p) rate)) := by
  exact execute_eq_decoded (p := p) rate rounds (RecordedQueueRun.initialState p.K)

private def codedTheta (q : RecordedQueueRun.Parameters) (codes : List (ArrivalCode p))
    (j : Fin p.K) : ℝ :=
  ProductSetLaw.theta p.m
    (RecordedQueueRun.scoreWeight q
      (RecordedQueueRun.run q (codes.map (decodeCode (p := p) q)))) j

private instance sumMeasurableSingletonClass {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) := ⟨fun tag => by
      cases tag with
      | inl value =>
          simpa only [Set.image_singleton] using
            (measurableSet_singleton value).inl_image
      | inr value =>
          simpa only [Set.image_singleton] using
            (measurableSet_singleton value).inr_image⟩

private theorem measurableSingleton_listObservation {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (List α) := by
  have hinj : Function.Injective
      (ReferenceActiveHorizonMeasurability.listObservationCoordinates (α := α)) := by
    intro xs ys h
    apply List.ext_getElem?
    intro n
    have hn := congrFun (congrArg Prod.snd h) n
    change ReferenceActiveHorizonMeasurability.listObservationAt xs n =
      ReferenceActiveHorizonMeasurability.listObservationAt ys n at hn
    unfold ReferenceActiveHorizonMeasurability.listObservationAt at hn
    cases hx : xs[n]? <;> cases hy : ys[n]? <;> simp_all
  constructor
  intro xs
  have heq : ({xs} : Set (List α)) =
      ReferenceActiveHorizonMeasurability.listObservationCoordinates ⁻¹'
        {ReferenceActiveHorizonMeasurability.listObservationCoordinates xs} := by
    ext ys
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · intro h
      subst ys
      rfl
    · intro h
      exact hinj h
  let _ : MeasurableSingletonClass (Unit ⊕ α) := inferInstance
  rw [heq]
  exact (measurableSet_singleton _).preimage
    ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates

private instance arrivalCodeListMeasurableSingleton :
    MeasurableSingletonClass (List (ArrivalCode p)) := measurableSingleton_listObservation

private theorem measurable_from_countable_domain {X Y : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] (f : X → Y) : Measurable f := by
  intro s hs
  have heq : f ⁻¹' s = ⋃ x : X, ⋃ _hx : f x ∈ s, ({x} : Set X) := by
    ext x
    simp
  rw [heq]
  exact MeasurableSet.iUnion fun x =>
    MeasurableSet.iUnion fun _ => measurableSet_singleton x

private theorem measurable_codedTheta (q : RecordedQueueRun.Parameters)
    (j : Fin p.K) : Measurable (codedTheta (p := p) q · j) :=
  measurable_from_countable_domain (codedTheta (p := p) q · j)

private theorem measurable_list_take_const {X α : Type*}
    [MeasurableSpace X] [MeasurableSpace α]
    (records : X → List α) (hrecords : Measurable records) (n : ℕ) :
    Measurable (fun x => (records x).take n) := by
  classical
  have hc := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp hrecords
  have hn : Measurable (fun _ : X => n) := measurable_const
  have hlen : Measurable (fun x => min n (records x).length) :=
    (measurable_of_countable (fun v : ℕ × ℕ => min v.1 v.2)).comp
      (hn.prodMk (measurable_fst.comp hc))
  have hcoords : Measurable (fun x => fun j =>
      ReferenceActiveHorizonMeasurability.listObservationAt ((records x).take n) j) := by
    apply measurable_pi_iff.mpr
    intro j
    have htag := (measurable_pi_apply j).comp (measurable_snd.comp hc)
    have hcond : MeasurableSet {x : X | j < n} := by
      by_cases h : j < n
      · simp [h]
      · simp [h]
    have h : Measurable (fun x => if j < (fun _ : X => n) x then
        ReferenceActiveHorizonMeasurability.listObservationAt (records x) j
        else (Sum.inl () : Unit ⊕ α)) := htag.ite hcond measurable_const
    convert h using 1
    funext x
    unfold ReferenceActiveHorizonMeasurability.listObservationAt
    rw [List.getElem?_take]
    by_cases hj : j < n <;> simp [hj]
  apply measurable_comap_iff.mpr
  convert hlen.prodMk hcoords using 1
  funext x
  exact Prod.ext List.length_take rfl

private theorem measurable_on_generated_fibers {Y : Type*} [MeasurableSpace Y]
    (f : SourceInput p → Y) (empty : Y)
    (hno : ∀ source,
      (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h).crossing = none →
        f source = empty)
    (hf : ∀ s : Fin (p.T + 1), Measurable
      (fun x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s.val => f x.val)) :
    Measurable f := by
  let cover (tag : Option (Fin (p.T + 1))) : Set (SourceInput p) :=
    match tag with
    | none => {source | (ReferenceCompletePhysicalHistory.generatedBoundary
        rate source rewards C_star C_h).crossing = none}
    | some s => ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
        (rate := rate) rewards C_star C_h s.val
  have hm (tag) : MeasurableSet (cover tag) := by
    cases tag with
    | none =>
        change MeasurableSet {source : SourceInput p |
          (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h).crossing = none}
        simpa [ReferenceCompletePhysicalHistory.generatedBoundary,
          ReferenceCompletePhysicalHistory.generatedInput] using
          (ReferenceCorrectedLaunchMeasurability.measurableSet_generated_no_crossing
            rate rewards C_star C_h)
    | some s =>
        change MeasurableSet (ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
          (rate := rate) rewards C_star C_h s.val)
        exact ReferenceGeneratedDownAmbiguityMeasurability.measurableSet_generatedLaunchFiberSet
          (rate := rate) rewards C_star C_h s.val
  have hc (source) : ∃ tag, source ∈ cover tag := by
    cases h : (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h).crossing with
    | none => exact ⟨none, h⟩
    | some crossing =>
        exact ⟨some ⟨ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h,
          Nat.lt_succ_of_le (ReferenceCompletePhysicalHistory.physicalStart_le_T
            rate source rewards C_star C_h)⟩,
          by simp only [cover,
            ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet,
            h, Option.isSome_some, true_and, Set.mem_ofPred_eq]⟩
  have hr (tag) : Measurable (fun x : cover tag => f x.val) := by
    cases tag with
    | none => exact measurable_const' (fun x y => (hno x.val x.property).trans (hno y.val y.property).symm)
    | some s => exact hf s
  intro s hs
  have heq : f ⁻¹' s = ⋃ tag, (Subtype.val : cover tag → _) '' {x | f x.val ∈ s} := by
    ext x
    constructor
    · intro hx
      obtain ⟨tag, ht⟩ := hc x
      exact Set.mem_iUnion.mpr ⟨tag, ⟨x, ht⟩, hx, rfl⟩
    · intro hx
      obtain ⟨tag, htag⟩ := Set.mem_iUnion.mp hx
      obtain ⟨x, hxu, hxs⟩ := htag
      rw [← hxs]
      exact hxu
  rw [heq]
  exact MeasurableSet.iUnion fun tag => MeasurableSet.subtype_image (hm tag) (hr tag hs)

private theorem measurable_thetaAt_fiber (t : Fin (p.T + 1)) (j : Fin p.K)
    (s : Fin (p.T + 1)) :
    Measurable (fun x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s.val =>
      thetaAt rate rewards C_star C_h t j x.val) := by
  let n := t.val - s.val
  have hread := (ReferenceFirstLiveOverflowReadout.measurable_wholeFirstLiveCellReadout
    rate rewards C_star C_h).comp
      (measurable_subtype_coe : Measurable
        (Subtype.val : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s.val →
          SourceInput p))
  have hcodes := ReferenceActiveHorizonMeasurability.measurable_list_map _ hread
    (cellCode (p := p) rate) (measurable_cellCode (p := p) rate)
  have hprefix := measurable_list_take_const _ hcodes n
  have hcoded := (measurable_codedTheta (p := p) Q j).comp hprefix
  have heq : (fun x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s.val =>
      thetaAt rate rewards C_star C_h t j x.val) =
    fun x => codedTheta (p := p) Q
      (((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCellReadout rate rewards C_star C_h
          x.val).map (cellCode (p := p) rate)).take n) j := by
    funext x
    have hcells := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
      rate rewards C_star C_h s x
    have hreadouts := ReferenceFirstLiveOverflowReadout.wholeFirstLive_readouts_on_fiber
      rate rewards C_star C_h s x
    have helapsed := ReferenceFirstLiveOverflowReadout.launch_elapsed rate rewards C_star C_h s.val x
    have hstart : ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h = s.val := by
      simpa [ReferenceCompletePhysicalHistory.physicalStart,
        ReferenceCompletePhysicalHistory.generatedBoundary,
        ReferenceCompletePhysicalHistory.generatedInput] using helapsed
    change ProductSetLaw.theta p.m
      (RecordedQueueRun.scoreWeight Q
        (RecordedQueueRun.run Q
          ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h x.val).take
            (t.val - ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h)))) j = _
    rw [hstart, hcells.2]
    have hcode :
        (ReferenceFirstLiveOverflowReadout.firstLiveCellReadout rate rewards C_star C_h
          s.val (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x).map
            (cellCode (p := p) rate) =
        (ReferenceFirstLiveOverflowReadout.firstLiveCells rate rewards C_star C_h
          s.val (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x).map
            (roundCode (p := p) rate) := by
      simp [ReferenceFirstLiveOverflowReadout.firstLiveCellReadout,
        ReferenceFirstLiveOverflowReadout.firstLiveCells, roundCode, roundReadout]
    rw [hreadouts.2.1, hcode]
    rw [run_eq_decoded (p := p) rate
      ((ReferenceFirstLiveOverflowReadout.firstLiveCells rate rewards C_star C_h
        s.val (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x).take n)]
    simp [codedTheta, n, List.map_take, List.map_map, Function.comp_def]
  rw [heq]
  exact hcoded

private theorem measurable_thetaAt (t : Fin (p.T + 1)) (j : Fin p.K) :
    Measurable (thetaAt rate rewards C_star C_h t j) := by
  let initial : ℝ := ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight Q
    (RecordedQueueRun.initialState p.K)) j
  apply measurable_on_generated_fibers rate rewards C_star C_h
    (thetaAt rate rewards C_star C_h t j) initial
  · intro omega hno
    have hcells := ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
      rate rewards C_star C_h omega hno
    simp [thetaAt, ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveRunAt,
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells,
      hcells.2.1, RecordedQueueRun.run, RecordedQueueRun.execute,
      RecordedQueueRun.initialState, initial]
  · intro s
    exact measurable_thetaAt_fiber rate rewards C_star C_h t j s


/-- The calendar marginal is the literal list marginal of the same actual
first-live run, at the exact prefix length determined by its launch boundary. -/
theorem thetaAt_eq_firstWindowMarginal (t : Fin (p.T + 1)) (j : Fin p.K)
    (omega : SourceInput p) :
    thetaAt rate rewards C_star C_h t j omega =
      ReferenceFirstLiveRawPotentialBound.firstWindowMarginal
        rate rewards C_star C_h omega
        (t.val - ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart
          rate rewards C_star C_h omega) j := by
  rfl

/-- The public calendar backlog is exactly the successor prefix backlog used
by the literal all-length correction. -/
theorem backlogAt_eq_firstWindowNormalizedBacklog (t : Fin (p.T + 1))
    (j : Fin p.K) (omega : SourceInput p) :
    backlogAt rate rewards C_star C_h t j omega =
      ReferenceFirstLiveRawPotentialBound.firstWindowNormalizedBacklog
        rate rewards C_star C_h omega
        (t.val - ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart
          rate rewards C_star C_h omega) j := by
  rfl

/-- Exact calendar reindexing of the signed successor-marginal correction.
Every actual cell is carried by its calendar round, including the last
successor at boundary `T`. -/
theorem firstWindowMarginalBacklogCorrection_eq_calendar_sum
    (omega : SourceInput p) :
    ReferenceFirstLiveRawPotentialBound.firstWindowMarginalBacklogCorrection
        rate rewards C_star C_h omega =
      ∑ t : Fin p.T, ∑ j : Fin p.K,
        (thetaAt rate rewards C_star C_h t.succ j omega -
          thetaAt rate rewards C_star C_h t.castSucc j omega) *
            backlogAt rate rewards C_star C_h t.succ j omega := by
  classical
  let a := ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart
    rate rewards C_star C_h omega
  let L := ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells
    rate rewards C_star C_h omega
  let f := fun t : Fin p.T => ∑ j : Fin p.K,
    (thetaAt rate rewards C_star C_h t.succ j omega -
      thetaAt rate rewards C_star C_h t.castSucc j omega) *
        backlogAt rate rewards C_star C_h t.succ j omega
  let kept : Finset (Fin p.T) := Finset.univ.filter fun t =>
    a ≤ t.val ∧ t.val - a < L.length
  have hrestrict : (∑ t ∈ kept, f t) = ∑ t : Fin p.T, f t := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro t ht hnot
    have hnot' : ¬ (a ≤ t.val ∧ t.val - a < L.length) := by
      simpa only [kept, Finset.mem_filter, Finset.mem_univ, true_and] using hnot
    apply Finset.sum_eq_zero
    intro j hj
    have htheta :
        thetaAt rate rewards C_star C_h t.succ j omega =
          thetaAt rate rewards C_star C_h t.castSucc j omega := by
      change ProductSetLaw.theta p.m
        (RecordedQueueRun.scoreWeight
          (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveQueue rate)
          (RecordedQueueRun.run
            (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveQueue rate)
            ((ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells
                rate rewards C_star C_h omega).take
              (t.val + 1 - ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart
                rate rewards C_star C_h omega)))) j =
        ProductSetLaw.theta p.m
          (RecordedQueueRun.scoreWeight
            (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveQueue rate)
            (RecordedQueueRun.run
              (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveQueue rate)
              ((ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells
                  rate rewards C_star C_h omega).take
                (t.val - ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart
                  rate rewards C_star C_h omega)))) j
      by_cases hstart : a ≤ t.val
      · have hidx : L.length ≤ t.val - a := by
          have : ¬ t.val - a < L.length := fun h => hnot' ⟨hstart, h⟩
          omega
        have hidx0 :
            (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells
              rate rewards C_star C_h omega).length ≤
              t.val - ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart
                rate rewards C_star C_h omega := by
          simpa [a, L] using hidx
        have hidx1 :
            (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells
              rate rewards C_star C_h omega).length ≤
              t.val + 1 - ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart
                rate rewards C_star C_h omega := by omega
        rw [List.take_of_length_le hidx1, List.take_of_length_le hidx0]
      · have hzero0 :
            t.val - ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart
              rate rewards C_star C_h omega = 0 := by
          have : t.val < a := by omega
          simpa [a] using Nat.sub_eq_zero_of_le (Nat.le_of_lt this)
        have hzero1 :
            t.val + 1 - ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart
              rate rewards C_star C_h omega = 0 := by
          have : t.val + 1 ≤ a := by omega
          simpa [a] using Nat.sub_eq_zero_of_le this
        simp [hzero0, hzero1]
    rw [htheta]
    simp
  rw [← hrestrict]
  symm
  unfold ReferenceFirstLiveRawPotentialBound.firstWindowMarginalBacklogCorrection
  apply Finset.sum_bij (fun t ht =>
    (⟨t.val - a, (Finset.mem_filter.mp ht).2.2⟩ : Fin L.length))
  · intro t ht
    exact Finset.mem_univ _
  · intro t ht s hs heq
    have ht' := (Finset.mem_filter.mp ht).2.1
    have hs' := (Finset.mem_filter.mp hs).2.1
    have heq' := congrArg Fin.val heq
    apply Fin.ext
    dsimp only at heq'
    omega
  · intro k hk
    let t : Fin p.T := ⟨a + k.val, by
      have hspan := ReferenceFirstLiveOriginalCalendarArrivalMoments.firstLiveStart_add_length_le_T
        rate rewards C_star C_h omega
      change a + L.length ≤ p.T at hspan
      omega⟩
    refine ⟨t, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        dsimp only [t]
        rw [Nat.add_sub_cancel_left]
        exact ⟨Nat.le_add_right _ _, k.isLt⟩⟩
    · apply Fin.ext
      exact Nat.add_sub_cancel_left _ _
  · intro t ht
    have hstart := (Finset.mem_filter.mp ht).2.1
    have hidx := (Finset.mem_filter.mp ht).2.2
    dsimp only [f]
    apply Finset.sum_congr rfl
    intro j hj
    rw [thetaAt_eq_firstWindowMarginal, thetaAt_eq_firstWindowMarginal,
      backlogAt_eq_firstWindowNormalizedBacklog]
    simp only [Fin.val_succ, Fin.val_castSucc]
    have hsucc :
        t.val + 1 - ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart
          rate rewards C_star C_h omega =
        (t.val - ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart
          rate rewards C_star C_h omega) + 1 := by omega
    rw [hsucc]


private theorem thetaAt_mem_Icc (v : Fin (p.T + 1)) (j : Fin p.K)
    (omega : SourceInput p) : thetaAt rate rewards C_star C_h v j omega ∈ Set.Icc 0 1 := by
  have hw : ∀ i : Fin p.K, 0 < RecordedQueueRun.scoreWeight Q (u v.val omega) i :=
    RecordedPotentialStep.scoreWeight_pos Q (u v.val omega)
  have hpos : 0 < ProductSetLaw.theta p.m
      (RecordedQueueRun.scoreWeight Q (u v.val omega)) j :=
    ProductSetLaw.theta_pos _ _ (ConstructorDimensions.m_pos p) p.m_lt_K hw
  have hlt : ProductSetLaw.theta p.m
      (RecordedQueueRun.scoreWeight Q (u v.val omega)) j < 1 :=
    ProductSetLaw.theta_lt_one _ _ (ConstructorDimensions.m_pos p) p.m_lt_K hw
  exact ⟨by simpa [thetaAt] using hpos.le, by simpa [thetaAt] using hlt.le⟩

private theorem measurable_backlogAt (t : Fin (p.T + 1)) (j : Fin p.K) :
    Measurable (backlogAt rate rewards C_star C_h t j) :=
  ReferenceFirstLiveCalendarPrefixReadout.measurable_firstWindowBacklogAt
    rate rewards C_star C_h j t.val

private theorem integrable_calendarCorrectionTerm (t : Fin p.T) (j : Fin p.K) :
    Integrable
      (fun omega : SourceInput p =>
        (thetaAt rate rewards C_star C_h t.succ j omega -
          thetaAt rate rewards C_star C_h t.castSucc j omega) *
            backlogAt rate rewards C_star C_h t.succ j omega)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  let mu := BootstrapPrivateRoundStreams.sourceInputLaw p
  have hback : Integrable (backlogAt rate rewards C_star C_h t.succ j) mu := by
    change Integrable
      (ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt
        rate rewards C_star C_h j (t.val + 1)) mu
    exact ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowBacklogAt
      rate rewards C_star C_h j (t.val + 1)
  have hdelta : Measurable (fun omega : SourceInput p =>
      thetaAt rate rewards C_star C_h t.succ j omega -
        thetaAt rate rewards C_star C_h t.castSucc j omega) :=
    (measurable_thetaAt rate rewards C_star C_h t.succ j).sub
      (measurable_thetaAt rate rewards C_star C_h t.castSucc j)
  have hbound (omega : SourceInput p) :
      ‖thetaAt rate rewards C_star C_h t.succ j omega -
        thetaAt rate rewards C_star C_h t.castSucc j omega‖ ≤ 1 := by
    have hnext := thetaAt_mem_Icc rate rewards C_star C_h t.succ j omega
    have hnow := thetaAt_mem_Icc rate rewards C_star C_h t.castSucc j omega
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [hnext.1, hnow.2]
    · linarith [hnext.2, hnow.1]
  exact hback.bdd_mul hdelta.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

/-- The literal signed correction is integrable under the complete original
source-input law. -/
theorem integrable_firstWindowMarginalBacklogCorrection :
    Integrable
      (fun omega : SourceInput p =>
        ReferenceFirstLiveRawPotentialBound.firstWindowMarginalBacklogCorrection
          rate rewards C_star C_h omega)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  let mu := BootstrapPrivateRoundStreams.sourceInputLaw p
  have hcalendar : Integrable
      (fun omega : SourceInput p =>
        ∑ t : Fin p.T, ∑ j : Fin p.K,
          (thetaAt rate rewards C_star C_h t.succ j omega -
            thetaAt rate rewards C_star C_h t.castSucc j omega) *
              backlogAt rate rewards C_star C_h t.succ j omega) mu := by
    exact integrable_finsetSum Finset.univ fun t _ =>
      integrable_finsetSum Finset.univ fun j _ =>
        integrable_calendarCorrectionTerm rate rewards C_star C_h t j
  exact hcalendar.congr (Filter.Eventually.of_forall fun omega =>
    (firstWindowMarginalBacklogCorrection_eq_calendar_sum
      rate rewards C_star C_h omega).symm)

/-- The original-source mean bound for the signed all-successor correction. -/
theorem integral_firstWindowMarginalBacklogCorrection_le
    (control0 : TimeControl p) :
    (∫ omega : SourceInput p,
      ReferenceFirstLiveRawPotentialBound.firstWindowMarginalBacklogCorrection
        rate rewards C_star C_h omega
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
      ((16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * (p.m : ℝ)) *
        rate.eta.val * (p.T : ℝ) := by
  let mu := BootstrapPrivateRoundStreams.sourceInputLaw p
  let cost := fun omega : SourceInput p =>
    ∑ t : Fin p.T,
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
        rate rewards C_star C_h t omega
  let incomingList := fun omega : SourceInput p =>
    ∑ k : Fin (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells
        rate rewards C_star C_h omega).length,
      ∑ j : Fin p.K,
        RecordedQueueSummation.runMarginal
            (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveQueue rate) p.m
            (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells
              rate rewards C_star C_h omega) k.val j *
          ((RecordedQueueRun.acceptedArrival (RecordedQueueRun.acceptedRecord
            (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveQueue rate)
            (RecordedQueueRun.run
              (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveQueue rate)
              ((ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells
                rate rewards C_star C_h omega).take k.val))
            (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells
              rate rewards C_star C_h omega)[k.val] j) : ℝ) / (rate.n : ℝ))
  let incoming := fun omega : SourceInput p =>
    ∑ k : Fin (ReferenceFirstLiveRawPotentialBound.firstWindowCells
        rate rewards C_star C_h omega).length,
      ∑ i : Fin p.K,
        ReferenceFirstLiveRawPotentialBound.firstWindowMarginal
          rate rewards C_star C_h omega k.val i *
          ReferenceFirstLiveRawPotentialBound.firstWindowAcceptedArrival
            rate rewards C_star C_h omega k i
  have hcost : Integrable cost mu := by
    simpa [cost] using
      (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.integrable_retainedFiniteWeightedBacklogCost
        rate rewards C_star C_h control0)
  have hIncoming_eq (omega : SourceInput p) : incoming omega = incomingList omega := by
    simp [incoming, incomingList,
      ReferenceFirstLiveRawPotentialBound.firstWindowCells,
      ReferenceFirstLiveRawPotentialBound.firstWindowRun,
      ReferenceFirstLiveRawPotentialBound.firstWindowQueue,
      ReferenceFirstLiveRawPotentialBound.firstWindowMarginal,
      ReferenceFirstLiveRawPotentialBound.firstWindowAcceptedArrival]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro i hi
    rfl
  have hincomingList : Integrable incomingList mu := by
    simpa [incomingList] using
      (ReferenceFirstLiveOriginalCalendarArrivalMoments.integrable_firstWindowWeightedAcceptedArrival
        rate rewards C_star C_h control0)
  have hincoming : Integrable incoming mu :=
    hincomingList.congr (Filter.Eventually.of_forall fun omega => (hIncoming_eq omega).symm)
  have hcorrection :=
    integrable_firstWindowMarginalBacklogCorrection rate rewards C_star C_h
  have hright : Integrable (fun omega => 8 * rate.eta.val *
      (cost omega + incoming omega)) mu :=
    (hcost.add hincoming).const_mul (8 * rate.eta.val)
  have hpoint (omega : SourceInput p) :
      ReferenceFirstLiveRawPotentialBound.firstWindowMarginalBacklogCorrection
          rate rewards C_star C_h omega ≤
        8 * rate.eta.val * (cost omega + incoming omega) := by
    simpa [cost, incoming] using
      (ReferenceFirstLiveRawPotentialBound.firstWindowCorrection_le
        rate rewards C_star C_h omega)
  have hmono := integral_mono_ae hcorrection hright
    (Filter.Eventually.of_forall hpoint)
  have hbudget : (∫ omega, cost omega ∂mu) ≤
      (2 / 11 : ℝ) * (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (p.T : ℝ) := by
    simpa [cost,
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost] using
      (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.weightedBacklog_budget
        rate rewards C_star C_h control0)
  have hincomingMean : (∫ omega, incoming omega ∂mu) ≤ (p.m : ℝ) * (p.T : ℝ) := by
    calc
      (∫ omega, incoming omega ∂mu) = ∫ omega, incomingList omega ∂mu :=
        integral_congr_ae (Filter.Eventually.of_forall hIncoming_eq)
      _ ≤ (p.m : ℝ) * (p.T : ℝ) := by
        simpa [incomingList] using
          (ReferenceFirstLiveOriginalCalendarArrivalMoments.integral_firstWindowWeightedAcceptedArrival_le
            rate rewards C_star C_h control0)
  calc
    (∫ omega : SourceInput p,
        ReferenceFirstLiveRawPotentialBound.firstWindowMarginalBacklogCorrection
          rate rewards C_star C_h omega ∂mu) ≤
        ∫ omega, 8 * rate.eta.val * (cost omega + incoming omega) ∂mu := hmono
    _ = 8 * rate.eta.val *
        ((∫ omega, cost omega ∂mu) + ∫ omega, incoming omega ∂mu) := by
      rw [integral_const_mul, integral_add hcost hincoming]
    _ ≤ 8 * rate.eta.val *
        ((2 / 11 : ℝ) *
            (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
              (p.T : ℝ) + (p.m : ℝ) * (p.T : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hbudget hincomingMean) (by positivity [rate.eta.property])
    _ = ((16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * (p.m : ℝ)) *
        rate.eta.val * (p.T : ℝ) := by ring

end Bandits.Support.ReferenceFirstLiveOriginalSignedCorrection

end
