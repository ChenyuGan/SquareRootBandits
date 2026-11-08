/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveConditionalWeightedDrift
public import Bandits.Support.ReferenceFirstLiveOverflowReadout
public import Bandits.Support.ReferenceFirstLaunchCommonUpdateSource

import Mathlib.Tactic

/-!
# Actual first-live calendar prefix and queue readouts

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-318`,
`sources/zip4/manuscript/06_interruptions.tex:391-408,425-426`,
`sources/zip4/manuscript/07_public_setup.tex:145-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:78-104`.

The readouts below use the first-live queue inputs already computed from the
original complete source. They do not add a queue process or a source law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstLiveCalendarPrefixReadout

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable {p : Parameters}

/-- The canonical parameter of the existing recorded queue. -/
def queueParameters (rate : RateInput p) :=
  ReferenceFirstLaunchNumericalCell.queueParameters rate

/-- Weighted-square potential after the actual first-live cells before `v`. -/
def firstWindowPotentialAt (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (v : ℕ) (omega : SourceInput p) : ℝ :=
  RecordedWeightedDrift.weightedSquarePotential p.m (queueParameters rate)
    (RecordedQueueRun.run (queueParameters rate)
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).take
        (v - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h)))

/-- Weighted backlog after the same actual first-live prefix. -/
def firstWindowWeightedBacklogAt (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (v : ℕ) (omega : SourceInput p) : ℝ :=
  RecordedWeightedDrift.weightedBacklog p.m (queueParameters rate)
    (RecordedQueueRun.run (queueParameters rate)
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).take
        (v - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h)))

/-- One arm's normalized backlog after the same actual first-live prefix. -/
def firstWindowBacklogAt (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (j : Fin p.K) (v : ℕ) (omega : SourceInput p) : ℝ :=
  StoppedQueueBound.normalizedBacklog (queueParameters rate)
    (RecordedQueueRun.run (queueParameters rate)
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).take
        (v - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h))) j

private abbrev CellReadout (p : Parameters) :=
  ReferenceFirstLiveNumericalPrefixBorel.NumericalCellReadout p

private abbrev ArrivalCode (p : Parameters) := Bool × Option (Fin p.K) × (Fin p.K → ℕ)

private def firstWindowArrivalCode (rate : RateInput p) (cell : CellReadout p) : ArrivalCode p :=
  (cell.1, (cell.2.1, fun i =>
    if cell.2.1 = some i then Nat.floor ((rate.n : ℝ) * cell.2.2.1 i / cell.2.2.2 i)
    else 0))

private theorem measurable_firstWindowArrivalCode (rate : RateInput p) :
  Measurable (firstWindowArrivalCode rate) := by
  classical
  apply measurable_fst.prodMk
  apply (measurable_fst.comp measurable_snd).prodMk
  apply measurable_pi_iff.mpr
  intro i
  have hmarker : Measurable (fun cell : CellReadout p => cell.2.1) :=
    measurable_fst.comp measurable_snd
  have hreward : Measurable (fun cell : CellReadout p => cell.2.2.1 i) :=
    (measurable_pi_apply i).comp
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hrate : Measurable (fun cell : CellReadout p => cell.2.2.2 i) :=
    (measurable_pi_apply i).comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hquotient : Measurable (fun cell : CellReadout p =>
      (rate.n : ℝ) * cell.2.2.1 i / cell.2.2.2 i) :=
    measurable_div.comp ((measurable_const.mul hreward).prodMk hrate)
  have hfloor := Nat.measurable_floor.comp hquotient
  exact hfloor.ite
    (MeasurableSet.preimage (measurableSet_singleton (some i)) hmarker)
    measurable_const

private def roundReadout (round : RecordedQueueRun.RoundInput p.K) : CellReadout p :=
  (round.enabled, (round.recordedArm, (round.reward, round.rate)))

private def firstWindowArrivalCodeOfRound (rate : RateInput p)
    (round : RecordedQueueRun.RoundInput p.K) : ArrivalCode p :=
  firstWindowArrivalCode rate (roundReadout round)

private def decodeFirstWindowArrivalCode (q : RecordedQueueRun.Parameters)
    (code : ArrivalCode p) : RecordedQueueRun.RoundInput p.K where
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

private theorem decodeFirstWindowArrivalCode_floor
    (q : RecordedQueueRun.Parameters) (code : ArrivalCode p) (i : Fin p.K) :
    Nat.floor ((q.n : ℝ) *
      (decodeFirstWindowArrivalCode q code).reward i /
        (decodeFirstWindowArrivalCode q code).rate i) = code.2.2 i := by
  have hn : 0 < (q.n : ℝ) := Nat.cast_pos.mpr q.n_pos
  have ha : 0 ≤ (code.2.2 i : ℝ) + (1 / 2 : ℝ) := by positivity
  have hquotient : (q.n : ℝ) *
      (decodeFirstWindowArrivalCode q code).reward i /
        (decodeFirstWindowArrivalCode q code).rate i =
      (code.2.2 i : ℝ) + (1 / 2 : ℝ) := by
    simp [decodeFirstWindowArrivalCode]
    field_simp [ne_of_gt hn, ne_of_gt (show 0 < (code.2.2 i : ℝ) + (1 / 2 : ℝ) by positivity)]
  rw [hquotient]
  apply (Nat.floor_eq_iff ha).2
  constructor <;> linarith

private theorem quantizedArrival_eq_decoded (rate : RateInput p)
    (round : RecordedQueueRun.RoundInput p.K) (i : Fin p.K) :
    RecordedQueueRun.quantizedArrival (queueParameters rate)
        (decodeFirstWindowArrivalCode (queueParameters rate)
          (firstWindowArrivalCodeOfRound rate round)) i =
      RecordedQueueRun.quantizedArrival (queueParameters rate) round i := by
  have hmark :
      (decodeFirstWindowArrivalCode (queueParameters rate)
        (firstWindowArrivalCodeOfRound rate round)).recordedArm = round.recordedArm := by
    simp [decodeFirstWindowArrivalCode, firstWindowArrivalCodeOfRound,
      roundReadout, firstWindowArrivalCode]
  rw [RecordedQueueRun.quantizedArrival, RecordedQueueRun.quantizedArrival, hmark]
  by_cases hmarker : round.recordedArm = some i
  · simp only [hmarker]
    calc
      Nat.floor ((queueParameters rate).n *
          (decodeFirstWindowArrivalCode (queueParameters rate)
            (firstWindowArrivalCodeOfRound rate round)).reward i /
          (decodeFirstWindowArrivalCode (queueParameters rate)
            (firstWindowArrivalCodeOfRound rate round)).rate i) =
        (firstWindowArrivalCodeOfRound rate round).2.2 i :=
          decodeFirstWindowArrivalCode_floor (queueParameters rate)
            (firstWindowArrivalCodeOfRound rate round) i
      _ = Nat.floor ((queueParameters rate).n * round.reward i / round.rate i) := by
        simp [firstWindowArrivalCodeOfRound, roundReadout, firstWindowArrivalCode,
          hmarker]
        rfl
  · simp [hmarker]

private theorem acceptedRecord_eq_decoded (rate : RateInput p)
    (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K) (i : Fin p.K) :
    RecordedQueueRun.acceptedRecord (queueParameters rate) state
      (decodeFirstWindowArrivalCode (queueParameters rate)
        (firstWindowArrivalCodeOfRound rate round)) i =
      RecordedQueueRun.acceptedRecord (queueParameters rate) state round i := by
  have henabled : (decodeFirstWindowArrivalCode (queueParameters rate)
      (firstWindowArrivalCodeOfRound rate round)).enabled = round.enabled := by
    rfl
  cases hoverflow : state.overflow
  · cases hround : round.enabled
    · simp [RecordedQueueRun.acceptedRecord, hoverflow, hround, henabled]
    · simpa [RecordedQueueRun.acceptedRecord, hoverflow, hround, henabled] using
        congrArg (fun n => (true, n)) (quantizedArrival_eq_decoded rate round i)
  · simp [RecordedQueueRun.acceptedRecord, hoverflow]

private theorem step_eq_decoded (rate : RateInput p)
    (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K) :
    RecordedQueueRun.step (queueParameters rate) state
        (decodeFirstWindowArrivalCode (queueParameters rate)
          (firstWindowArrivalCodeOfRound rate round)) =
      RecordedQueueRun.step (queueParameters rate) state round := by
  cases state with
  | mk registers overflow records =>
    have hrecords :
        (fun i => RecordedQueueRun.acceptedRecord (queueParameters rate)
          ⟨registers, overflow, records⟩
          (decodeFirstWindowArrivalCode (queueParameters rate)
            (firstWindowArrivalCodeOfRound rate round)) i) =
        fun i => RecordedQueueRun.acceptedRecord (queueParameters rate)
          ⟨registers, overflow, records⟩ round i := by
      funext i
      exact acceptedRecord_eq_decoded rate ⟨registers, overflow, records⟩ round i
    simp [RecordedQueueRun.step, hrecords]

private theorem execute_eq_decoded (rate : RateInput p)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (state : RecordedQueueRun.RunState p.K) :
    RecordedQueueRun.execute (queueParameters rate) rounds state =
      RecordedQueueRun.execute (queueParameters rate)
        (rounds.map (fun round => decodeFirstWindowArrivalCode (queueParameters rate)
          (firstWindowArrivalCodeOfRound rate round))) state := by
  induction rounds generalizing state with
  | nil => rfl
  | cons round rounds ih =>
    change RecordedQueueRun.execute (queueParameters rate) rounds
        (RecordedQueueRun.step (queueParameters rate) state round) =
      RecordedQueueRun.execute (queueParameters rate)
        (rounds.map (fun round => decodeFirstWindowArrivalCode (queueParameters rate)
          (firstWindowArrivalCodeOfRound rate round)))
        (RecordedQueueRun.step (queueParameters rate) state
          (decodeFirstWindowArrivalCode (queueParameters rate)
            (firstWindowArrivalCodeOfRound rate round)))
    rw [step_eq_decoded rate state round]
    exact ih _

private theorem run_eq_decoded (rate : RateInput p)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) :
    RecordedQueueRun.run (queueParameters rate) rounds =
      RecordedQueueRun.run (queueParameters rate)
        (rounds.map (fun round => decodeFirstWindowArrivalCode (queueParameters rate)
          (firstWindowArrivalCodeOfRound rate round))) := by
  exact execute_eq_decoded rate rounds (RecordedQueueRun.initialState p.K)

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
  let _ : MeasurableSingletonClass (Unit ⊕ α) := inferInstance
  rw [heq]
  exact (measurableSet_singleton _).preimage
    ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates

private instance arrivalCodeListMeasurableSingleton :
    MeasurableSingletonClass (List (ArrivalCode p)) :=
  measurableSingleton_listObservation

private theorem measurable_from_countable_domain {X Y : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] (f : X → Y) : Measurable f := by
  intro u hu
  have heq : f ⁻¹' u = ⋃ x : X, ⋃ _hx : f x ∈ u, ({x} : Set X) := by
    ext x
    simp
  rw [heq]
  exact MeasurableSet.iUnion fun x =>
    MeasurableSet.iUnion fun _hx => measurableSet_singleton x

private def codedRunRegisters (q : RecordedQueueRun.Parameters)
    (codes : List (ArrivalCode p)) : Fin p.K → ℕ × ℕ :=
  (RecordedQueueRun.run q (codes.map (decodeFirstWindowArrivalCode q))).registers

private theorem measurable_codedRunRegisters (q : RecordedQueueRun.Parameters) :
    Measurable (codedRunRegisters (p := p) q) :=
  measurable_from_countable_domain (codedRunRegisters (p := p) q)

private theorem run_prefix_registers_eq_coded (rate : RateInput p)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (n : ℕ) :
    (RecordedQueueRun.run (queueParameters rate) (rounds.take n)).registers =
      codedRunRegisters (queueParameters rate)
        ((rounds.map (firstWindowArrivalCodeOfRound rate)).take n) := by
  rw [run_eq_decoded rate (rounds.take n)]
  simp [codedRunRegisters, List.map_take, List.map_map, Function.comp_def]

private theorem measurable_list_take_of_measurable {X α : Type*}
    [MeasurableSpace X] [MeasurableSpace α]
    (records : X → List α) (hrecords : Measurable records)
    (n : X → ℕ) (hn : Measurable n) :
    Measurable (fun x => (records x).take (n x)) := by
  classical
  have hc := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp hrecords
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
    by_cases hj : j < n x <;> simp [hj]
  apply measurable_comap_iff.mpr
  convert hlen.prodMk ht using 1
  funext x
  exact Prod.ext List.length_take rfl

private def firstWindowRegisters (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (v : ℕ) (omega : SourceInput p) : Fin p.K → ℕ × ℕ :=
  (RecordedQueueRun.run (queueParameters rate)
    ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).take
      (v - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h))).registers

private theorem measurable_on_generated_fibers {Y : Type*} [MeasurableSpace Y]
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (f : SourceInput p → Y) (empty : Y)
    (hno : ∀ source, (ReferenceCompletePhysicalHistory.generatedBoundary
      rate source rewards C_star C_h).crossing = none → f source = empty)
    (hf : ∀ s : Fin (p.T + 1), Measurable
      (fun x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s.val =>
        f x.val)) : Measurable f := by
  let cover (tag : Option (Fin (p.T + 1))) : Set (SourceInput p) :=
    match tag with
    | none => {source | (ReferenceCompletePhysicalHistory.generatedBoundary
        rate source rewards C_star C_h).crossing = none}
    | some s => ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
        (rate := rate) rewards C_star C_h s.val
  have hm (tag) : MeasurableSet (cover tag) := by
    cases tag with
    | none =>
        exact ReferenceCorrectedLaunchMeasurability.measurableSet_generated_no_crossing
          rate rewards C_star C_h
    | some s =>
        exact ReferenceGeneratedDownAmbiguityMeasurability.measurableSet_generatedLaunchFiberSet
          (rate := rate) rewards C_star C_h s.val
  have hc (source) : ∃ tag, source ∈ cover tag := by
    cases h : (ReferenceCompletePhysicalHistory.generatedBoundary
        rate source rewards C_star C_h).crossing with
    | none => exact ⟨none, h⟩
    | some crossing =>
        exact ⟨some ⟨ReferenceCompletePhysicalHistory.physicalStart
            rate source rewards C_star C_h,
          Nat.lt_succ_of_le (ReferenceCompletePhysicalHistory.physicalStart_le_T
            rate source rewards C_star C_h)⟩,
          by simp only [cover,
            ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet,
            h, Option.isSome_some, true_and, Set.mem_ofPred_eq]⟩
  have hr (tag) : Measurable (fun x : cover tag => f x.val) := by
    cases tag with
    | none =>
        exact measurable_const' (fun x y => (hno x.val x.property).trans
          (hno y.val y.property).symm)
    | some s => exact hf s
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

private theorem measurable_firstWindowRegisters_on_fiber
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ) (v : ℕ)
    (s : Fin (p.T + 1)) : Measurable
      (fun x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s.val =>
        firstWindowRegisters rate rewards C_star C_h v x.val) := by
  let count := p.T - s.val
  have hread := (ReferenceFirstLiveOverflowReadout.measurable_wholeFirstLiveCellReadout
    rate rewards C_star C_h).comp
      (measurable_subtype_coe : Measurable
        (Subtype.val : ReferenceFirstLiveOverflowReadout.LaunchFiber
          rate rewards C_star C_h s.val → SourceInput p))
  have hcodes := ReferenceActiveHorizonMeasurability.measurable_list_map _ hread
    (firstWindowArrivalCode rate) (measurable_firstWindowArrivalCode rate)
  have hprefix := measurable_list_take_of_measurable _ hcodes
    (fun _ : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s.val =>
      v - s.val) measurable_const
  have hcoded := (measurable_codedRunRegisters (p := p) (queueParameters rate)).comp hprefix
  have heq : (fun x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s.val =>
      firstWindowRegisters rate rewards C_star C_h v x.val) =
    fun x => codedRunRegisters (queueParameters rate)
      (((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCellReadout rate rewards C_star C_h
        x.val).map
          (firstWindowArrivalCode rate)).take (v - s.val)) := by
    funext x
    have hcells := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
      rate rewards C_star C_h s x
    have hreadouts := ReferenceFirstLiveOverflowReadout.wholeFirstLive_readouts_on_fiber
      rate rewards C_star C_h s x
    have helapsed := ReferenceFirstLiveOverflowReadout.launch_elapsed
      rate rewards C_star C_h s.val x
    have hstart : ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h = s.val := by
      simpa [ReferenceCompletePhysicalHistory.physicalStart,
        ReferenceCompletePhysicalHistory.generatedBoundary,
        ReferenceCompletePhysicalHistory.generatedInput] using helapsed
    rw [firstWindowRegisters, hcells.2, hstart, hreadouts.2.1]
    have hcode :
        (ReferenceFirstLiveOverflowReadout.firstLiveCellReadout rate rewards C_star C_h
          s.val count (ReferenceFirstLiveOverflowReadout.maximal_span s) x).map
          (firstWindowArrivalCode rate) =
        (ReferenceFirstLiveOverflowReadout.firstLiveCells rate rewards C_star C_h
          s.val count (ReferenceFirstLiveOverflowReadout.maximal_span s) x).map
          (firstWindowArrivalCodeOfRound rate) := by
      simp [ReferenceFirstLiveOverflowReadout.firstLiveCellReadout,
        ReferenceFirstLiveOverflowReadout.firstLiveCells,
        firstWindowArrivalCodeOfRound, roundReadout]
    rw [hcode]
    exact run_prefix_registers_eq_coded rate
      (ReferenceFirstLiveOverflowReadout.firstLiveCells rate rewards C_star C_h
        s.val count (ReferenceFirstLiveOverflowReadout.maximal_span s) x) (v - s.val)
  rw [heq]
  exact hcoded

private theorem measurable_firstWindowRegisters (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (v : ℕ) :
    Measurable (firstWindowRegisters rate rewards C_star C_h v) := by
  apply measurable_on_generated_fibers rate rewards C_star C_h _ (fun _ : Fin p.K => (0, 0))
  · intro source hno
    have hcells := ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
      rate rewards C_star C_h source hno
    simp [firstWindowRegisters, hcells.2.1, RecordedQueueRun.run,
      RecordedQueueRun.execute, RecordedQueueRun.initialState, queueParameters]
  · intro s
    exact measurable_firstWindowRegisters_on_fiber rate rewards C_star C_h v s

private theorem actualLiveSourceCells_rate_lower_bound
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T) :
    ∀ round ∈ ReferenceFirstWindowNumericalStream.actualLiveSourceCells
        rate source rewards C_star C_h hc count hspan,
      ∀ j : Fin p.K, 32 * rate.eta.val ≤ round.rate j := by
  intro round hround j
  have hcellsLength := ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
    rate source rewards C_star C_h hc count hspan
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hround
  have hkWindow : k < (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length := by
    rw [← hcellsLength]
    exact hk
  let kFin : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length := ⟨k, hkWindow⟩
  let sourceCell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hc count hspan kFin
  have hgetInput :
      (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
        rate source rewards C_star C_h hc count hspan)[k]'hk = sourceCell.input := by
    simpa [kFin, sourceCell] using
      ReferenceFirstWindowNumericalStream.actualLiveSourceCells_get
        rate source rewards C_star C_h hc count hspan kFin
  have hinput : round = sourceCell.input := hget.symm.trans hgetInput
  rw [hinput]
  change 32 * rate.eta.val ≤ sourceCell.input.rate j
  have hfacts := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt_facts
    rate source rewards C_star C_h hc count hspan kFin
  dsimp only at hfacts
  rcases hfacts with ⟨_, _, _, _, _, _, hrate, _, _⟩
  rw [hrate, sourceCell.selected.view.payload.rate_eq_canonical]
  exact CanonicalRecordingRates.thirtyTwo_mul_eta_le_xi p rate.eta.property
    sourceCell.selected.view.payload.anchor j

private theorem wholeFirstLiveCells_rate_lower_bound
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p) :
    ∀ round ∈ ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
        rate rewards C_star C_h source,
      ∀ j : Fin p.K, 32 * rate.eta.val ≤ round.rate j := by
  intro round hround j
  let boundary := ReferenceCompletePhysicalHistory.generatedBoundary
    rate source rewards C_star C_h
  cases hcross : boundary.crossing with
  | none =>
      have hno := ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
        rate rewards C_star C_h source hcross
      rw [hno.2.1] at hround
      simp at hround
  | some crossing =>
      have hc : (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true := by
        simpa [boundary, ReferenceCompletePhysicalHistory.generatedBoundary,
          ReferenceCompletePhysicalHistory.generatedInput] using
            (show boundary.crossing.isSome = true by simp [hcross])
      let start := ReferenceInitializationRun.elapsed p boundary.completed
      have hstart : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = start := by
        rfl
      have hstartLe : start ≤ p.T := by
        rw [← hstart]
        exact ReferenceCompletePhysicalHistory.physicalStart_le_T rate source rewards C_star C_h
      let s : Fin (p.T + 1) := ⟨start, Nat.lt_succ_of_le hstartLe⟩
      let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h start :=
        ⟨source, ⟨hc, rfl⟩⟩
      have hwhole := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
        rate rewards C_star C_h s x
      have hspan : ReferenceInitializationRun.elapsed p boundary.completed + (p.T - start) ≤ p.T := by
        dsimp [start]
        omega
      have hcells :
          ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h source =
            ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate source rewards C_star C_h
              hc (p.T - start) hspan := by
        simpa only [ReferenceFirstLiveOverflowReadout.firstLiveCells,
          ReferenceFirstLiveOverflowReadout.launch_crossing,
          ReferenceFirstLiveOverflowReadout.launch_span, s] using hwhole.2
      rw [hcells] at hround
      exact actualLiveSourceCells_rate_lower_bound rate source rewards C_star C_h hc
        (p.T - start) hspan round hround j

private def potentialFromRegisters (q : RecordedQueueRun.Parameters)
    (registers : Fin p.K → ℕ × ℕ) : ℝ :=
  ∑ i : Fin p.K, ProductSetLaw.theta p.m
    (fun j => ScoreWeights.scoreWeight (1 + 1 / (q.D : ℝ)) (registers j).1) i *
      (((registers i).2 : ℝ) / (q.n : ℝ)) ^ 2

private def weightedBacklogFromRegisters (q : RecordedQueueRun.Parameters)
    (registers : Fin p.K → ℕ × ℕ) : ℝ :=
  ∑ i : Fin p.K, ProductSetLaw.theta p.m
    (fun j => ScoreWeights.scoreWeight (1 + 1 / (q.D : ℝ)) (registers j).1) i *
      (((registers i).2 : ℝ) / (q.n : ℝ))

private def backlogFromRegisters (q : RecordedQueueRun.Parameters)
    (registers : Fin p.K → ℕ × ℕ) (j : Fin p.K) : ℝ :=
  (((registers j).2 : ℝ) / (q.n : ℝ))

private theorem firstWindowPotentialAt_eq_registers
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (v : ℕ) (omega : SourceInput p) :
    firstWindowPotentialAt rate rewards C_star C_h v omega =
      potentialFromRegisters (queueParameters rate)
        (firstWindowRegisters rate rewards C_star C_h v omega) := by
  rfl

private theorem firstWindowWeightedBacklogAt_eq_registers
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (v : ℕ) (omega : SourceInput p) :
    firstWindowWeightedBacklogAt rate rewards C_star C_h v omega =
      weightedBacklogFromRegisters (queueParameters rate)
        (firstWindowRegisters rate rewards C_star C_h v omega) := by
  rfl

private theorem firstWindowBacklogAt_eq_registers
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (j : Fin p.K) (v : ℕ) (omega : SourceInput p) :
    firstWindowBacklogAt rate rewards C_star C_h j v omega =
      backlogFromRegisters (queueParameters rate)
        (firstWindowRegisters rate rewards C_star C_h v omega) j := by
  rfl

/-- The actual prefix potential is ambient Borel on the complete source. -/
theorem measurable_firstWindowPotentialAt (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (v : ℕ) :
    Measurable (firstWindowPotentialAt rate rewards C_star C_h v) := by
  convert (measurable_from_countable_domain
    (potentialFromRegisters (queueParameters rate))).comp
      (measurable_firstWindowRegisters rate rewards C_star C_h v) using 1
  funext omega
  exact firstWindowPotentialAt_eq_registers rate rewards C_star C_h v omega

/-- The weighted backlog of the same actual prefix is ambient Borel. -/
theorem measurable_firstWindowWeightedBacklogAt (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (v : ℕ) :
    Measurable (firstWindowWeightedBacklogAt rate rewards C_star C_h v) := by
  convert (measurable_from_countable_domain
    (weightedBacklogFromRegisters (queueParameters rate))).comp
      (measurable_firstWindowRegisters rate rewards C_star C_h v) using 1
  funext omega
  exact firstWindowWeightedBacklogAt_eq_registers rate rewards C_star C_h v omega

/-- Each arm's normalized backlog in the same actual prefix is ambient Borel. -/
theorem measurable_firstWindowBacklogAt (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (j : Fin p.K) (v : ℕ) :
    Measurable (firstWindowBacklogAt rate rewards C_star C_h j v) := by
  convert (measurable_from_countable_domain
    (fun registers => backlogFromRegisters (queueParameters rate) registers j)).comp
      (measurable_firstWindowRegisters rate rewards C_star C_h v) using 1
  funext omega
  exact firstWindowBacklogAt_eq_registers rate rewards C_star C_h j v omega

/-- The exponential of beta times the actual arm backlog is ambient Borel. -/
theorem measurable_firstWindowExpBacklogAt (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (j : Fin p.K) (v : ℕ) :
    Measurable (fun omega => Real.exp
      (ReferenceFirstLiveSourceSavedMoments.beta rate *
        firstWindowBacklogAt rate rewards C_star C_h j v omega)) := by
  exact Real.measurable_exp.comp
    ((measurable_const.mul (measurable_firstWindowBacklogAt rate rewards C_star C_h j v)))

private theorem firstWindowBacklogAt_bounds (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (j : Fin p.K) (v : ℕ)
    (omega : SourceInput p) :
    0 ≤ firstWindowBacklogAt rate rewards C_star C_h j v omega ∧
      firstWindowBacklogAt rate rewards C_star C_h j v omega ≤
        2 * (1 / (32 * rate.eta.val)) := by
  constructor
  · unfold firstWindowBacklogAt StoppedQueueBound.normalizedBacklog
    positivity
  · have hrate := wholeFirstLiveCells_rate_lower_bound rate rewards C_star C_h omega
    have hcap := StoppedQueueBound.run_prefix_normalized_backlog_le_twice_threshold
      (queueParameters rate)
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega)
      hrate
      (v - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h) j
    have hcap' : firstWindowBacklogAt rate rewards C_star C_h j v omega ≤
        2 * ((queueParameters rate).eta⁻¹ * (32 : ℝ)⁻¹) := by
      simpa [firstWindowBacklogAt] using hcap
    calc
      firstWindowBacklogAt rate rewards C_star C_h j v omega ≤
          2 * ((queueParameters rate).eta⁻¹ * (32 : ℝ)⁻¹) := hcap'
      _ = 2 * (1 / (32 * rate.eta.val)) := by
        simp [queueParameters, one_div, mul_inv_rev]
        rfl

private theorem firstWindowPotentialAt_bounds (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (v : ℕ) (omega : SourceInput p) :
    0 ≤ firstWindowPotentialAt rate rewards C_star C_h v omega ∧
      firstWindowPotentialAt rate rewards C_star C_h v omega ≤
        (p.m : ℝ) * (2 * (1 / (32 * rate.eta.val))) ^ 2 := by
  let q := queueParameters rate
  let state := RecordedQueueRun.run q
    ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).take
      (v - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h))
  have hsum := RecordedMarginalGrowth.state_sum_theta_eq_m q state
    (ConstructorDimensions.m_pos p) p.m_lt_K
  have htheta (i : Fin p.K) :
      0 < ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight q state) i :=
    RecordedMarginalGrowth.state_theta_pos q state i
      (ConstructorDimensions.m_pos p) p.m_lt_K
  have hback (i : Fin p.K) :
      0 ≤ StoppedQueueBound.normalizedBacklog q state i ∧
        StoppedQueueBound.normalizedBacklog q state i ≤
          2 * (1 / (32 * rate.eta.val)) := by
    have hb := firstWindowBacklogAt_bounds rate rewards C_star C_h i v omega
    simpa [firstWindowBacklogAt, state, q, queueParameters] using hb
  have hcap0 : 0 ≤ 2 * (1 / (32 * rate.eta.val)) := by positivity [rate.eta.property]
  change 0 ≤ RecordedWeightedDrift.weightedSquarePotential p.m q state ∧
    RecordedWeightedDrift.weightedSquarePotential p.m q state ≤
      (p.m : ℝ) * (2 * (1 / (32 * rate.eta.val))) ^ 2
  unfold RecordedWeightedDrift.weightedSquarePotential
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (le_of_lt (htheta i)) (sq_nonneg _)
  · calc
      _ ≤ ∑ i : Fin p.K,
          ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight q state) i *
            (2 * (1 / (32 * rate.eta.val))) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (htheta i))
        have hb := hback i
        have hsq : (StoppedQueueBound.normalizedBacklog q state i) ^ 2 ≤
            (2 * (1 / (32 * rate.eta.val))) ^ 2 := by
          have hprod := mul_nonneg (sub_nonneg.mpr hb.2)
            (add_nonneg hcap0 hb.1)
          nlinarith
        exact hsq
      _ = (p.m : ℝ) * (2 * (1 / (32 * rate.eta.val))) ^ 2 := by
        rw [← Finset.sum_mul, hsum]

private theorem firstWindowWeightedBacklogAt_bounds (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (v : ℕ) (omega : SourceInput p) :
    0 ≤ firstWindowWeightedBacklogAt rate rewards C_star C_h v omega ∧
      firstWindowWeightedBacklogAt rate rewards C_star C_h v omega ≤
        (p.m : ℝ) * (2 * (1 / (32 * rate.eta.val))) := by
  let q := queueParameters rate
  let state := RecordedQueueRun.run q
    ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).take
      (v - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h))
  have hsum := RecordedMarginalGrowth.state_sum_theta_eq_m q state
    (ConstructorDimensions.m_pos p) p.m_lt_K
  have htheta (i : Fin p.K) :
      0 < ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight q state) i :=
    RecordedMarginalGrowth.state_theta_pos q state i
      (ConstructorDimensions.m_pos p) p.m_lt_K
  have hback (i : Fin p.K) :
      0 ≤ StoppedQueueBound.normalizedBacklog q state i ∧
        StoppedQueueBound.normalizedBacklog q state i ≤
          2 * (1 / (32 * rate.eta.val)) := by
    have hb := firstWindowBacklogAt_bounds rate rewards C_star C_h i v omega
    simpa [firstWindowBacklogAt, state, q, queueParameters] using hb
  change 0 ≤ RecordedWeightedDrift.weightedBacklog p.m q state ∧
    RecordedWeightedDrift.weightedBacklog p.m q state ≤
      (p.m : ℝ) * (2 * (1 / (32 * rate.eta.val)))
  unfold RecordedWeightedDrift.weightedBacklog
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (le_of_lt (htheta i)) (hback i).1
  · calc
      _ ≤ ∑ i : Fin p.K,
          ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight q state) i *
            (2 * (1 / (32 * rate.eta.val))) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hback i).2 (le_of_lt (htheta i))
      _ = (p.m : ℝ) * (2 * (1 / (32 * rate.eta.val))) := by
        rw [← Finset.sum_mul, hsum]

private theorem integrable_of_norm_le_uniform_source {f : SourceInput p → ℝ}
    {C : ℝ} (hf : Measurable f) (_hC : 0 ≤ C)
    (hbound : ∀ omega, ‖f omega‖ ≤ C) :
    Integrable f (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  let _ : IsProbabilityMeasure (BootstrapPrivateRoundStreams.sourceInputLaw p) :=
    BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  refine (integrable_const C).mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with omega
  simpa only [Real.norm_eq_abs, abs_of_nonneg _hC] using hbound omega

/-- The actual whole-source potential is integrable under the original source law. -/
theorem integrable_firstWindowPotentialAt (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (v : ℕ) :
    Integrable (firstWindowPotentialAt rate rewards C_star C_h v)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  apply integrable_of_norm_le_uniform_source
    (C := (p.m : ℝ) * (2 * (1 / (32 * rate.eta.val))) ^ 2)
    (measurable_firstWindowPotentialAt rate rewards C_star C_h v)
    (by positivity [rate.eta.property])
  intro omega
  rw [Real.norm_eq_abs, abs_of_nonneg
    (firstWindowPotentialAt_bounds rate rewards C_star C_h v omega).1]
  exact (firstWindowPotentialAt_bounds rate rewards C_star C_h v omega).2

/-- The actual whole-source weighted backlog is integrable under the original law. -/
theorem integrable_firstWindowWeightedBacklogAt (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (v : ℕ) :
    Integrable (firstWindowWeightedBacklogAt rate rewards C_star C_h v)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  apply integrable_of_norm_le_uniform_source
    (C := (p.m : ℝ) * (2 * (1 / (32 * rate.eta.val))))
    (measurable_firstWindowWeightedBacklogAt rate rewards C_star C_h v)
    (by positivity [rate.eta.property])
  intro omega
  rw [Real.norm_eq_abs, abs_of_nonneg
    (firstWindowWeightedBacklogAt_bounds rate rewards C_star C_h v omega).1]
  exact (firstWindowWeightedBacklogAt_bounds rate rewards C_star C_h v omega).2

/-- Every arm's actual whole-source normalized backlog is integrable under the original law. -/
theorem integrable_firstWindowBacklogAt (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (j : Fin p.K) (v : ℕ) :
    Integrable (firstWindowBacklogAt rate rewards C_star C_h j v)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  apply integrable_of_norm_le_uniform_source
    (C := 2 * (1 / (32 * rate.eta.val)))
    (measurable_firstWindowBacklogAt rate rewards C_star C_h j v)
    (by positivity [rate.eta.property])
  intro omega
  rw [Real.norm_eq_abs, abs_of_nonneg
    (firstWindowBacklogAt_bounds rate rewards C_star C_h j v omega).1]
  exact (firstWindowBacklogAt_bounds rate rewards C_star C_h j v omega).2

/-- The actual exponential backlog moment is integrable under the original law. -/
theorem integrable_firstWindowExpBacklogAt (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (j : Fin p.K) (v : ℕ) :
    Integrable (fun omega => Real.exp
      (ReferenceFirstLiveSourceSavedMoments.beta rate *
        firstWindowBacklogAt rate rewards C_star C_h j v omega))
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  let beta := ReferenceFirstLiveSourceSavedMoments.beta rate
  let cap := 2 * (1 / (32 * rate.eta.val))
  have hbeta : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hcap : 0 ≤ cap := by positivity [rate.eta.property]
  apply integrable_of_norm_le_uniform_source (C := Real.exp (beta * cap))
    (measurable_firstWindowExpBacklogAt rate rewards C_star C_h j v)
    (Real.exp_nonneg _)
  intro omega
  have hback := firstWindowBacklogAt_bounds rate rewards C_star C_h j v omega
  have hexp : Real.exp (beta * firstWindowBacklogAt rate rewards C_star C_h j v omega) ≤
      Real.exp (beta * cap) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hback.2 (le_of_lt hbeta)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), beta, cap] using hexp

/-- Before the launch boundary the actual queue has its zero potential. -/
theorem firstWindowPotentialAt_zero (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (omega : SourceInput p) :
    firstWindowPotentialAt rate rewards C_star C_h 0 omega = 0 := by
  simp [firstWindowPotentialAt, queueParameters, RecordedWeightedDrift.weightedSquarePotential,
    RecordedQueueRun.run, RecordedQueueRun.execute, RecordedQueueRun.initialState,
    StoppedQueueBound.normalizedBacklog]

/-- The terminal actual queue potential is nonnegative on every original source. -/
theorem firstWindowPotentialAt_horizon_nonneg (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (omega : SourceInput p) :
    0 ≤ firstWindowPotentialAt rate rewards C_star C_h p.T omega := by
  change 0 ≤ RecordedWeightedDrift.weightedSquarePotential p.m (queueParameters rate)
    (RecordedQueueRun.run (queueParameters rate)
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).take
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h)))
  unfold RecordedWeightedDrift.weightedSquarePotential
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg
    (le_of_lt (RecordedMarginalGrowth.state_theta_pos (queueParameters rate)
      (RecordedQueueRun.run (queueParameters rate)
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).take
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h)))
      i (ConstructorDimensions.m_pos p) p.m_lt_K))
    (sq_nonneg _)

private def sourceStratumIndex {p : Parameters} (q : Fin (ConstructorDimensions.M p))
    (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val) :=
  ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs

private theorem actualLiveSourceCells_zero
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed ≤ p.T) :
    ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate source rewards C_star C_h hc 0 hspan = [] := by
  have hwindow : ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate source rewards C_star C_h
      hc 0 hspan = [] := by
    simp [ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
      ReferenceActivePhysicalHorizon.run_zero_records]
  apply List.eq_nil_of_length_eq_zero
  rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length, hwindow]
  rfl

private theorem actualLiveSourceCells_length_le_count
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T) :
    (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate source rewards C_star C_h hc count hspan).length ≤ count := by
  rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length]
  calc
    (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate source rewards C_star C_h hc count hspan).length ≤
        (ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate source rewards C_star C_h hc count hspan).records.length :=
      (List.takeWhile_prefix _).length_le
    _ = count := by
      simp [ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
        ReferenceActivePhysicalHorizon.run_record_count]

/-- Actual first-live numerical cells are nested for every valid prefix length.
The only inputs are the original crossing, order, and span data. -/
theorem actualLiveSourceCells_take_of_le
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (a b : ℕ) (hab : a ≤ b)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + b ≤ p.T) :
    (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate source rewards C_star C_h hc b hspan).take a =
      ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate source rewards C_star C_h hc a
        (by omega) := by
  classical
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      rw [actualLiveSourceCells_zero rate source rewards C_star C_h hc hspan]
      simp
  | succ b ih =>
      cases a with
      | zero =>
          have hspan0 : ReferenceInitializationRun.elapsed p
              (ReferenceInitializationRun.output
                (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed ≤ p.T := by
            omega
          rw [actualLiveSourceCells_zero rate source rewards C_star C_h hc hspan0]
          simp
      | succ a =>
          have hab' : a ≤ b := by omega
          have hspanB : ReferenceInitializationRun.elapsed p
              (ReferenceInitializationRun.output
                (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + b ≤ p.T := by
            omega
          let t : Fin p.T := ⟨
            ReferenceInitializationRun.elapsed p
              (ReferenceInitializationRun.output
                (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + b,
            by omega⟩
          have hs : ReferenceInitializationRun.elapsed p
              (ReferenceInitializationRun.output
                (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed ≤ t.val := by
            simp [t]
          let q := ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source
          let start := ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
          have hmember : source ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
              (sourceStratumIndex q t start hs) := by
            change source ∈ ReferenceRetainedSourceCoupling.retainedSourceEvent rate rewards C_star C_h q start
            exact ⟨rfl, hc, rfl⟩
          let z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
              (sourceStratumIndex q t start hs) :=
            ⟨source, hmember⟩
          let control0 : ContinuousLearningRows.TimeControl p := Classical.choice inferInstance
          have hstep := ReferenceFirstLiveNumericalPrefixTemporal.actualNumericalCells_take_successor
            rate rewards C_star C_h q t start hs control0 z
          have htn : t.val - start = b := by simp [t, start]
          have hstep' :
              (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate source rewards C_star C_h hc
                (b + 1) hspan).take b =
              ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate source rewards C_star C_h hc b hspanB := by
            simpa only [Subtype.coe_mk, htn] using hstep
          by_cases heq : a = b
          · have hlen := actualLiveSourceCells_length_le_count rate source rewards C_star C_h hc (b + 1) hspan
            simpa only [heq] using (List.take_of_length_le hlen)
          · have haB : a + 1 ≤ b := by omega
            calc
              (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate source rewards C_star C_h hc
                (b + 1) hspan).take (a + 1) =
                  ((ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate source rewards C_star C_h hc
                    (b + 1) hspan).take b).take (a + 1) := by
                      symm
                      rw [List.take_take, Nat.min_eq_left haB]
              _ = (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate source rewards C_star C_h hc
                  b hspanB).take (a + 1) := by rw [hstep']
              _ = ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate source rewards C_star C_h hc
                  (a + 1) (by omega) := ih (a + 1) (by omega) hspanB

variable (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
  (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) (s : ℕ)
  (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p)

local notation "Zplus" => ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
  rate rewards C_star C_h q t s hs control0
local notation "n" => t.val - s

/-- The whole-source physical suffix, cut at the original current record,
is exactly the current source-stratum cell list. -/
theorem wholeFirstLiveCells_take_current (z : Zplus) :
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val.val).take (n + 1) =
      ReferenceFirstLiveSourceCellReadout.cells rate rewards C_star C_h q t s hs control0 z := by
  let source := z.val.val
  have hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true :=
    z.val.property.2.1
  have helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s := by
    simpa only [ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] using z.val.property.2.2
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = s := by
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using helapsed
  let sFin : Fin (p.T + 1) := ⟨s, by omega⟩
  let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s := ⟨source, ⟨hcross, by
    exact helapsed⟩⟩
  have hwhole := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber rate rewards C_star C_h sFin x
  have hfullSpan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
        (p.T - s) ≤ p.T := by
    rw [helapsed]
    simpa only [sFin] using ReferenceFirstLiveOverflowReadout.maximal_span sFin
  have hwholeCells : ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h source =
      ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate source rewards C_star C_h hcross
        (p.T - s) hfullSpan := by
    simpa only [ReferenceFirstLiveOverflowReadout.firstLiveCells,
      ReferenceFirstLiveOverflowReadout.launch_crossing,
      ReferenceFirstLiveOverflowReadout.launch_span, sFin] using hwhole.2
  have hprefix := actualLiveSourceCells_take_of_le rate source rewards C_star C_h hcross
    (t.val - s + 1) (p.T - s) (by omega) hfullSpan
  have hspanCurrent : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
        (t.val - s + 1) ≤ p.T := by
    rw [helapsed]
    omega
  have hcells : ReferenceFirstLiveSourceCellReadout.cells rate rewards C_star C_h q t s hs control0 z =
      ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate source rewards C_star C_h hcross
        (t.val - s + 1) hspanCurrent := by
    simp only [ReferenceFirstLiveSourceCellReadout.cells,
      ReferenceFirstLiveSourceCellReadout.sourceCurrentCount]
    rfl
  calc
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val.val).take (n + 1) =
        (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate source rewards C_star C_h hcross
          (p.T - s) hfullSpan).take (n + 1) := by
          rw [hwholeCells]
    _ = ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate source rewards C_star C_h hcross
          (n + 1) hspanCurrent := by
          exact hprefix
    _ = ReferenceFirstLiveSourceCellReadout.cells rate rewards C_star C_h q t s hs control0 z := hcells.symm

private theorem wholeFirstLiveCells_take_strict_current (z : Zplus) :
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val.val).take n =
      (ReferenceFirstLiveSourceCellReadout.cells rate rewards C_star C_h q t s hs control0 z).take n := by
  have h := wholeFirstLiveCells_take_current rate rewards C_star C_h q t s hs control0 z
  calc
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val.val).take n =
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val.val).take
          (n + 1)).take n := by
          symm
          rw [List.take_take, Nat.min_eq_left (by omega : n ≤ n + 1)]
    _ = (ReferenceFirstLiveSourceCellReadout.cells rate rewards C_star C_h q t s hs control0 z).take n := by rw [h]

/-- The public strict-prefix energy readout is E's before-potential. -/
theorem firstWindowPotentialAt_before (z : Zplus) :
    firstWindowPotentialAt rate rewards C_star C_h t.val z.val.val =
      ReferenceFirstLiveQueueEnergyEnvelope.potentialBefore rate rewards C_star C_h q t s hs control0 z := by
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val.val rewards C_star C_h = s := by
    have helapsed : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z.val.val rewards C_star C_h rate)).completed = s := by
      simpa only [ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] using z.val.property.2.2
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using helapsed
  rw [firstWindowPotentialAt, ReferenceFirstLiveQueueEnergyEnvelope.potentialBefore, hstart]
  simp only [queueParameters]
  rw [wholeFirstLiveCells_take_strict_current rate rewards C_star C_h q t s hs control0 z]

/-- The current cell is included in the after-potential readout. -/
theorem firstWindowPotentialAt_after (z : Zplus) :
    firstWindowPotentialAt rate rewards C_star C_h (t.val + 1) z.val.val =
      ReferenceFirstLiveQueueEnergyEnvelope.potentialAfter rate rewards C_star C_h q t s hs control0 z := by
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val.val rewards C_star C_h = s := by
    have helapsed : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z.val.val rewards C_star C_h rate)).completed = s := by
      simpa only [ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] using z.val.property.2.2
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using helapsed
  have hnext : t.val + 1 - s = n + 1 := by omega
  rw [firstWindowPotentialAt, ReferenceFirstLiveQueueEnergyEnvelope.potentialAfter, hstart]
  simp only [queueParameters]
  rw [hnext]
  rw [wholeFirstLiveCells_take_current rate rewards C_star C_h q t s hs control0 z]
  have hlen : (ReferenceFirstLiveSourceCellReadout.cells rate rewards C_star C_h q t s hs control0 z).length =
      n + 1 := by
    simpa only [ReferenceFirstLiveSourceCellReadout.sourceCurrentCount] using
      ReferenceFirstLiveSourceCellReadout.cells_length rate rewards C_star C_h q t s hs control0 z
  rw [List.take_of_length_le (by rw [hlen])]

/-- The weighted strict-prefix backlog readout is E's before-readout. -/
theorem firstWindowWeightedBacklogAt_before (z : Zplus) :
    firstWindowWeightedBacklogAt rate rewards C_star C_h t.val z.val.val =
      ReferenceFirstLiveQueueEnergyEnvelope.weightedBacklogBefore rate rewards C_star C_h q t s hs control0 z := by
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val.val rewards C_star C_h = s := by
    have helapsed : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z.val.val rewards C_star C_h rate)).completed = s := by
      simpa only [ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] using z.val.property.2.2
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using helapsed
  rw [firstWindowWeightedBacklogAt, ReferenceFirstLiveQueueEnergyEnvelope.weightedBacklogBefore, hstart]
  simp only [queueParameters]
  rw [wholeFirstLiveCells_take_strict_current rate rewards C_star C_h q t s hs control0 z]

/-- The normalized strict-prefix queue register is M's before-backlog. -/
theorem firstWindowBacklogAt_before (z : Zplus) (j : Fin p.K) :
    firstWindowBacklogAt rate rewards C_star C_h j t.val z.val.val =
      ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
        rate rewards C_star C_h q t s hs control0 j z := by
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val.val rewards C_star C_h = s := by
    have helapsed : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z.val.val rewards C_star C_h rate)).completed = s := by
      simpa only [ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] using z.val.property.2.2
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using helapsed
  rw [firstWindowBacklogAt,
    ReferenceFirstLiveQueueEnergyEnvelope.backlogBefore_eq_normalized rate rewards C_star C_h q t s hs control0 j z,
    hstart]
  simp only [queueParameters]
  rw [wholeFirstLiveCells_take_strict_current rate rewards C_star C_h q t s hs control0 z]

/-- The inclusive current cell produces M's after-backlog, including an
overflow-detecting update. -/
theorem firstWindowBacklogAt_after (z : Zplus) (j : Fin p.K) :
    firstWindowBacklogAt rate rewards C_star C_h j (t.val + 1) z.val.val =
      ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter
        rate rewards C_star C_h q t s hs control0 j z := by
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val.val rewards C_star C_h = s := by
    have helapsed : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z.val.val rewards C_star C_h rate)).completed = s := by
      simpa only [ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] using z.val.property.2.2
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using helapsed
  have hnext : t.val + 1 - s = n + 1 := by omega
  rw [firstWindowBacklogAt,
    ReferenceFirstLiveQueueEnergyEnvelope.backlogAfter_eq_normalized rate rewards C_star C_h q t s hs control0 j z,
    hstart]
  simp only [queueParameters]
  rw [hnext]
  rw [wholeFirstLiveCells_take_current rate rewards C_star C_h q t s hs control0 z]
  have hlen : (ReferenceFirstLiveSourceCellReadout.cells rate rewards C_star C_h q t s hs control0 z).length =
      n + 1 := by
    simpa only [ReferenceFirstLiveSourceCellReadout.sourceCurrentCount] using
      ReferenceFirstLiveSourceCellReadout.cells_length rate rewards C_star C_h q t s hs control0 z
  rw [List.take_of_length_le (by rw [hlen])]

local notation "BirthZ" => ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
  (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)

/-- On the actual first-launch source stratum, the whole-source stream has
the accepted first cell as its first numerical input. -/
theorem firstWindowBirthCells_take_one (z : BirthZ) :
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val).take 1 =
      [ReferenceFirstLaunchCommonUpdateSource.firstCell rate rewards C_star C_h q t control0 z] := by
  have hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).crossing.isSome = true :=
    z.property.2.1
  have helapsed := ReferenceFirstLaunchCommonUpdateSource.source_elapsed_eq
    rate rewards C_star C_h q t z
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = t.val := by
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using helapsed
  let sFin : Fin (p.T + 1) := ⟨t.val, Nat.lt_succ_of_le t.isLt.le⟩
  let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h t.val :=
    ⟨z.val, ⟨hcross, helapsed⟩⟩
  have hwhole := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber rate rewards C_star C_h sFin x
  have hfullSpan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed +
        (p.T - t.val) ≤ p.T := by
    rw [helapsed]
    simpa only [sFin] using ReferenceFirstLiveOverflowReadout.maximal_span sFin
  have hwholeCells : ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val =
      ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h hcross
        (p.T - t.val) hfullSpan := by
    simpa only [ReferenceFirstLiveOverflowReadout.firstLiveCells,
      ReferenceFirstLiveOverflowReadout.launch_crossing,
      ReferenceFirstLiveOverflowReadout.launch_span, sFin] using hwhole.2
  have hprefix := actualLiveSourceCells_take_of_le rate z.val rewards C_star C_h hcross
    1 (p.T - t.val) (by omega) hfullSpan
  have hcells := ReferenceFirstLaunchCommonUpdateSource.source_first_cell_chronological
    rate rewards C_star C_h q t control0 z
  calc
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val).take 1 =
        (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h hcross
          (p.T - t.val) hfullSpan).take 1 := by rw [hwholeCells]
    _ = ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h hcross
          1 (ReferenceFirstLaunchCommonUpdateSource.source_first_span rate rewards C_star C_h q t z) := hprefix
    _ = [ReferenceFirstLaunchCommonUpdateSource.firstCell rate rewards C_star C_h q t control0 z] := hcells.2.1

private theorem firstWindowBirthRun_eq_firstUpdate (z : BirthZ) :
    RecordedQueueRun.run (queueParameters rate)
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val).take 1) =
      ReferenceFirstLaunchCommonUpdateSource.firstUpdate rate rewards C_star C_h q t control0 z := by
  have hcells := firstWindowBirthCells_take_one rate rewards C_star C_h q t control0 z
  have hchron := ReferenceFirstLaunchCommonUpdateSource.source_first_chronological_execute
    rate rewards C_star C_h q t control0 z
  have hactual := ReferenceFirstLaunchCommonUpdateSource.source_first_cell_chronological
    rate rewards C_star C_h q t control0 z
  rw [hactual.2.1] at hchron
  rw [hcells]
  simpa [RecordedQueueRun.run, queueParameters] using hchron

/-- The birth potential before its first physical update is zero. -/
theorem firstWindowPotentialAt_birth_before (z : BirthZ) :
    firstWindowPotentialAt rate rewards C_star C_h t.val z.val = 0 := by
  have helapsed := ReferenceFirstLaunchCommonUpdateSource.source_elapsed_eq
    rate rewards C_star C_h q t z
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = t.val := by
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using helapsed
  rw [firstWindowPotentialAt, hstart]
  simp [queueParameters, RecordedWeightedDrift.weightedSquarePotential,
    RecordedQueueRun.run, RecordedQueueRun.execute, RecordedQueueRun.initialState,
    StoppedQueueBound.normalizedBacklog]

/-- The birth after-potential is exactly the energy of F's actual first update. -/
theorem firstWindowPotentialAt_birth_after (z : BirthZ) :
    firstWindowPotentialAt rate rewards C_star C_h (t.val + 1) z.val =
      RecordedWeightedDrift.weightedSquarePotential p.m (queueParameters rate)
        (ReferenceFirstLaunchCommonUpdateSource.firstUpdate rate rewards C_star C_h q t control0 z) := by
  have helapsed := ReferenceFirstLaunchCommonUpdateSource.source_elapsed_eq
    rate rewards C_star C_h q t z
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = t.val := by
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using helapsed
  have hnext : t.val + 1 - t.val = 1 := by omega
  rw [firstWindowPotentialAt, hstart, hnext,
    firstWindowBirthRun_eq_firstUpdate rate rewards C_star C_h q t control0 z]

/-- The birth backlog is zero before the first physical update. -/
theorem firstWindowBacklogAt_birth_before (z : BirthZ) (j : Fin p.K) :
    firstWindowBacklogAt rate rewards C_star C_h j t.val z.val = 0 := by
  have helapsed := ReferenceFirstLaunchCommonUpdateSource.source_elapsed_eq
    rate rewards C_star C_h q t z
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = t.val := by
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using helapsed
  rw [firstWindowBacklogAt, hstart]
  simp [queueParameters, RecordedQueueRun.run, RecordedQueueRun.execute,
    RecordedQueueRun.initialState, StoppedQueueBound.normalizedBacklog]

/-- The birth after-backlog is the exact normalized register in F's actual
inclusive first update. -/
theorem firstWindowBacklogAt_birth_after (z : BirthZ) (j : Fin p.K) :
    firstWindowBacklogAt rate rewards C_star C_h j (t.val + 1) z.val =
      StoppedQueueBound.normalizedBacklog (queueParameters rate)
        (ReferenceFirstLaunchCommonUpdateSource.firstUpdate rate rewards C_star C_h q t control0 z) j := by
  have helapsed := ReferenceFirstLaunchCommonUpdateSource.source_elapsed_eq
    rate rewards C_star C_h q t z
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = t.val := by
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using helapsed
  have hnext : t.val + 1 - t.val = 1 := by omega
  rw [firstWindowBacklogAt, hstart, hnext,
    firstWindowBirthRun_eq_firstUpdate rate rewards C_star C_h q t control0 z]

end Bandits.Support.ReferenceFirstLiveCalendarPrefixReadout

end
