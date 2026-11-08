/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveNumericalPrefixBorel

import Lean.Elab.Tactic.Omega
import Mathlib.MeasureTheory.Function.Floor

/-!
# Borel readout of the actual first-live numerical queue run

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,256-264`,
`sources/zip4/manuscript/06_interruptions.tex:391-397,425-426`, and
`sources/zip4/manuscript/07_public_setup.tex:127-164`.

The public output is the complete run of the existing recorded queue machine
on the actual first-live numerical cells. Its Borel proof factors through the
faithful tagged finite observation of the admitted numerical-prefix producer.
This is an ambient measurability result; it does not assert temporal adaptation,
a conditional law, or a regret conclusion.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceFirstWindowNumericalStream

namespace Bandits.Support.ReferenceFirstLiveNumericalQueueBorel

private abbrev RateInput := ReferenceActivePhysicalStep.RateInput
private abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
private abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : ConstructorDimensions.Parameters}

private abbrev SourceZ (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (q : Fin (M p)) (s : ℕ) (hs : s ≤ t.val) :=
  ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
    (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)

private theorem sourceElapsed
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (t : Fin p.T) (q : Fin (M p)) (s : ℕ) (hs : s ≤ t.val)
    (z : SourceZ rate rewards C_star C_h t q s hs) :
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed = s := by
  simpa only [ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] using z.property.2.2

private theorem sourceCountSpan
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (t : Fin p.T) (q : Fin (M p)) (s : ℕ) (hs : s ≤ t.val)
    (z : SourceZ rate rewards C_star C_h t q s hs) :
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed +
        (t.val - s) ≤ p.T := by
  rw [sourceElapsed rate rewards C_star C_h t q s hs z]
  omega

private abbrev ArrivalCode (K : ℕ) := Bool × (Fin K → ℕ)

private abbrev RunOutput (K : ℕ) :=
  (Fin K → ℕ × ℕ) × (Bool × (Fin K → List (Bool × ℕ)))

private def numericalArrivalCode (q : RecordedQueueRun.Parameters)
    (cell : ReferenceFirstLiveNumericalPrefixBorel.NumericalCellReadout p) :
    ArrivalCode p.K :=
  (cell.1, fun i =>
    if cell.2.1 = some i then
      Nat.floor ((q.n : ℝ) * cell.2.2.1 i / cell.2.2.2 i)
    else 0)

private theorem measurable_numericalArrivalCode (q : RecordedQueueRun.Parameters) :
    Measurable (numericalArrivalCode (p := p) q) := by
  apply measurable_fst.prodMk
  apply measurable_pi_iff.mpr
  intro i
  have hmarker : Measurable (fun cell :
      ReferenceFirstLiveNumericalPrefixBorel.NumericalCellReadout p => cell.2.1) :=
    measurable_fst.comp measurable_snd
  have hreward : Measurable (fun cell :
      ReferenceFirstLiveNumericalPrefixBorel.NumericalCellReadout p => cell.2.2.1 i) :=
    (measurable_pi_apply i).comp
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hrate : Measurable (fun cell :
      ReferenceFirstLiveNumericalPrefixBorel.NumericalCellReadout p => cell.2.2.2 i) :=
    (measurable_pi_apply i).comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hratio : Measurable (fun cell :
      ReferenceFirstLiveNumericalPrefixBorel.NumericalCellReadout p =>
      (q.n : ℝ) * cell.2.2.1 i / cell.2.2.2 i) := by
    exact measurable_div.comp ((measurable_const.mul hreward).prodMk hrate)
  have hfloor := Nat.measurable_floor.comp hratio
  have hresult : Measurable (fun cell :
      ReferenceFirstLiveNumericalPrefixBorel.NumericalCellReadout p =>
      if cell.2.1 = some i then Nat.floor ((q.n : ℝ) * cell.2.2.1 i / cell.2.2.2 i)
      else 0) :=
    Measurable.ite (MeasurableSet.preimage (measurableSet_singleton (some i)) hmarker)
      hfloor measurable_const
  simpa only [numericalArrivalCode, Function.comp_def] using hresult

private def numericalArrivalTag (q : RecordedQueueRun.Parameters) :
    Unit ⊕ ReferenceFirstLiveNumericalPrefixBorel.NumericalCellReadout p →
      Unit ⊕ ArrivalCode p.K
  | .inl _ => .inl ()
  | .inr cell => .inr (numericalArrivalCode q cell)

private theorem measurable_numericalArrivalTag (q : RecordedQueueRun.Parameters) :
    Measurable (numericalArrivalTag (p := p) q) :=
  Measurable.sumElim measurable_const
    (measurable_inr.comp (measurable_numericalArrivalCode (p := p) q))

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
  let : MeasurableSingletonClass (Unit ⊕ α) := inferInstance
  rw [heq]
  exact (measurableSet_singleton _).preimage
    ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates

private instance arrivalCodeListMeasurableSingletonClass :
    MeasurableSingletonClass
      (List (Unit ⊕ ArrivalCode p.K)) :=
  measurableSingleton_listObservation

private theorem measurable_list_ofFn {X α : Type*} [MeasurableSpace X]
    [MeasurableSpace α] (n : ℕ) (f : X → Fin n → α) (hf : Measurable f) :
    Measurable (fun x => List.ofFn (f x)) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun x =>
    ((List.ofFn (f x)).length,
      fun j => ReferenceActiveHorizonMeasurability.listObservationAt
        (List.ofFn (f x)) j))
  simp only [List.length_ofFn]
  apply measurable_const.prodMk
  apply measurable_pi_iff.mpr
  intro j
  by_cases hj : j < n
  · let i : Fin n := ⟨j, hj⟩
    have heq : (fun x => ReferenceActiveHorizonMeasurability.listObservationAt
        (List.ofFn (f x)) j) = fun x => Sum.inr (f x i) := by
      funext x
      simp [ReferenceActiveHorizonMeasurability.listObservationAt, i, hj]
    rw [heq]
    exact measurable_inr.comp ((measurable_pi_apply i).comp hf)
  · have heq : (fun x => ReferenceActiveHorizonMeasurability.listObservationAt
        (List.ofFn (f x)) j) = fun _ => (Sum.inl () : Unit ⊕ α) := by
      funext x
      simp [ReferenceActiveHorizonMeasurability.listObservationAt, hj]
    rw [heq]
    exact measurable_const

private def arrivalCodeOfRound {K : ℕ} (q : RecordedQueueRun.Parameters)
    (round : RecordedQueueRun.RoundInput K) : ArrivalCode K :=
  (round.enabled, fun i => RecordedQueueRun.quantizedArrival q round i)

private def acceptedArrivalCode {K : ℕ} (state : RecordedQueueRun.RunState K)
    (code : ArrivalCode K) (i : Fin K) : Bool × ℕ :=
  if state.overflow then (false, 0)
  else if code.1 then (true, code.2 i)
  else (false, 0)

private def stepArrivalCode {K : ℕ} (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (code : ArrivalCode K) :
    RecordedQueueRun.RunState K := by
  classical
  let record := fun i => acceptedArrivalCode state code i
  exact ⟨
    fun i => QueueReplay.transition (4 * q.n) (state.registers i) (record i),
    state.overflow || decide (∃ i, 32 *
      (QueueReplay.transition (4 * q.n) (state.registers i) (record i)).2 > q.D),
    fun i => state.records i ++ [record i]⟩

private theorem stepArrivalCode_eq_step {K : ℕ} (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (round : RecordedQueueRun.RoundInput K) :
    stepArrivalCode q state (arrivalCodeOfRound q round) =
      RecordedQueueRun.step q state round := by
  cases state
  simp [stepArrivalCode, acceptedArrivalCode, arrivalCodeOfRound,
    RecordedQueueRun.step, RecordedQueueRun.acceptedRecord,
    RecordedQueueRun.quantizedArrival]
  constructor
  · rfl
  constructor
  · rfl
  · rfl

private def processArrivalTags {K : ℕ} (q : RecordedQueueRun.Parameters) :
    List (Unit ⊕ ArrivalCode K) → RecordedQueueRun.RunState K →
      RecordedQueueRun.RunState K
  | [], state => state
  | .inl _ :: tags, state => processArrivalTags q tags state
  | .inr code :: tags, state =>
      processArrivalTags q tags (stepArrivalCode q state code)

private def runArrivalTags {K : ℕ} (q : RecordedQueueRun.Parameters)
    (tags : List (Unit ⊕ ArrivalCode K)) : RunOutput K :=
  let state := processArrivalTags q tags (RecordedQueueRun.initialState K)
  (state.registers, (state.overflow, state.records))

private theorem processArrivalTags_map_rounds {K : ℕ}
    (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput K))
    (state : RecordedQueueRun.RunState K) :
    processArrivalTags q
        (rounds.map fun round => Sum.inr (arrivalCodeOfRound q round)) state =
      RecordedQueueRun.execute q rounds state := by
  induction rounds generalizing state with
  | nil => rfl
  | cons round rounds ih =>
      change processArrivalTags q
          (rounds.map fun round => Sum.inr (arrivalCodeOfRound q round))
          (stepArrivalCode q state (arrivalCodeOfRound q round)) =
        RecordedQueueRun.execute q rounds (RecordedQueueRun.step q state round)
      rw [ih, stepArrivalCode_eq_step]

private theorem processArrivalTags_absent {K : ℕ}
    (q : RecordedQueueRun.Parameters) (padding : ℕ)
    (state : RecordedQueueRun.RunState K) :
    processArrivalTags q (List.replicate padding (Sum.inl ())) state = state := by
  induction padding with
  | zero => rfl
  | succ padding ih =>
      simp [List.replicate_succ, processArrivalTags, ih]

private theorem processArrivalTags_append_absent {K : ℕ}
    (q : RecordedQueueRun.Parameters) (tags : List (Unit ⊕ ArrivalCode K))
    (state : RecordedQueueRun.RunState K) (padding : ℕ) :
    processArrivalTags q
        (tags ++ List.replicate padding (Sum.inl ())) state =
      processArrivalTags q tags state := by
  induction tags generalizing state with
  | nil => exact processArrivalTags_absent q padding state
  | cons tag tags ih =>
      cases tag with
      | inl value =>
          simpa only [List.cons_append, processArrivalTags] using ih state
      | inr code =>
          simpa only [List.cons_append, processArrivalTags] using
            ih (stepArrivalCode q state code)

private def taggedGetElem? {α β : Type*} (values : List α) (f : α → β)
    (index : ℕ) : Unit ⊕ β :=
  (values[index]?).elim (Sum.inl ()) (fun value => Sum.inr (f value))

private theorem ofFn_taggedGetElem? {α β : Type*} (values : List α)
    (n : ℕ) (hvalues : values.length ≤ n) (f : α → β) :
    List.ofFn (fun k : Fin n => taggedGetElem? values f k.val) =
      values.map (fun value => Sum.inr (f value)) ++
        List.replicate (n - values.length) (Sum.inl ()) := by
  induction n generalizing values with
  | zero =>
      have hnil : values = [] := List.eq_nil_iff_length_eq_zero.mpr (by omega)
      subst values
      simp
  | succ n ih =>
      cases values with
      | nil => simp [taggedGetElem?, List.replicate_succ]
      | cons value values =>
          have htail : values.length ≤ n := by simp only [List.length_cons] at hvalues; omega
          have htailFun :
              (fun k : Fin n => taggedGetElem? (value :: values) f k.succ.val) =
                fun k => taggedGetElem? values f k.val := by
            funext k
            simp [taggedGetElem?]
          have htailLists := congrArg List.ofFn htailFun
          have hfirst :
              List.ofFn (fun k : Fin (n + 1) =>
                taggedGetElem? (value :: values) f k.val) =
              Sum.inr (f value) :: List.ofFn (fun k : Fin n =>
                taggedGetElem? values f k.val) := by
            rw [List.ofFn_succ]
            simp only [List.cons.injEq]
            constructor
            · simp [taggedGetElem?]
            · exact htailLists
          rw [hfirst, ih values htail]
          simp [Nat.succ_sub_succ_eq_sub]

private theorem runArrivalTags_of_readout {K : ℕ}
    (q : RecordedQueueRun.Parameters)
    (values : List (RecordedQueueRun.RoundInput K)) (n : ℕ)
    (hvalues : values.length ≤ n) :
    runArrivalTags q
        (List.ofFn fun k : Fin n =>
          taggedGetElem? values (arrivalCodeOfRound q) k.val) =
      ((RecordedQueueRun.run q values).registers,
        ((RecordedQueueRun.run q values).overflow,
          (RecordedQueueRun.run q values).records)) := by
  have hcodes := ofFn_taggedGetElem?
    (α := RecordedQueueRun.RoundInput K)
    (β := ArrivalCode K) values n hvalues (arrivalCodeOfRound q)
  have htagRun : runArrivalTags (K := K) q
        (List.ofFn fun k : Fin n =>
          taggedGetElem? values (arrivalCodeOfRound q) k.val) =
      runArrivalTags (K := K) q
        (List.map (fun value => Sum.inr (arrivalCodeOfRound q value)) values ++
          List.replicate (n - values.length) (Sum.inl ())) :=
    congrArg
      (fun tags : List (Unit ⊕ ArrivalCode K) =>
        runArrivalTags (K := K) q tags)
      hcodes
  have hpadded : runArrivalTags q
        (List.map (fun value => Sum.inr (arrivalCodeOfRound q value)) values ++
          List.replicate (n - values.length) (Sum.inl ())) =
      ((RecordedQueueRun.run q values).registers,
        ((RecordedQueueRun.run q values).overflow,
          (RecordedQueueRun.run q values).records)) := by
    simp only [runArrivalTags, RecordedQueueRun.run]
    rw [processArrivalTags_append_absent]
    rw [processArrivalTags_map_rounds]
  exact htagRun.trans hpadded

private def outputNumericalCellTag (q : RecordedQueueRun.Parameters) :
    Unit ⊕ ReferenceFirstLiveNumericalPrefixBorel.NumericalCellReadout p →
      Unit ⊕ ArrivalCode p.K :=
  numericalArrivalTag q

/-- The complete register, overflow flag, and accepted-record output of the
actual finite first-live queue run. The source stratum and all constants are
the common original-source telescope; `control0` is retained as in the
numerical-prefix producer. -/
def numericalCountRunReadout
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)) :
    (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))) :=
  let _control0 := control0
  let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards
    C_star C_h z.property.2.1 (t.val - s)
    (by
      have he : ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed = s :=
        by simpa only [ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] using z.property.2.2
      rw [he]
      omega)
  let V := RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) cells
  (V.registers, (V.overflow, V.records))

private theorem numericalCountRunReadout_eq_arrivalTags
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (z : SourceZ rate rewards C_star C_h t q s hs) :
    numericalCountRunReadout rate rewards C_star C_h q t s hs control0 z =
      runArrivalTags (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (List.ofFn fun k : Fin (t.val - s) =>
          outputNumericalCellTag (p := p)
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (ReferenceFirstLiveNumericalPrefixBorel.numericalCountPastReadout
              rate rewards C_star C_h q t s hs control0 z k)) := by
  let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards
    C_star C_h z.property.2.1 (t.val - s)
    (sourceCountSpan rate rewards C_star C_h t q s hs z)
  have hlen : cells.length ≤ t.val - s := by
    dsimp [cells]
    exact ReferenceFirstLiveNumericalPrefixBorel.numericalCountPast_length_le
      rate rewards C_star C_h q t s hs control0 z
  have hread (k : Fin (t.val - s)) :
      ReferenceFirstLiveNumericalPrefixBorel.numericalCountPastReadout
          rate rewards C_star C_h q t s hs control0 z k =
        match cells[k.val]? with
        | none => (Sum.inl () : Unit ⊕
            ReferenceFirstLiveNumericalPrefixBorel.NumericalCellReadout p)
        | some cell => Sum.inr
            (cell.enabled, (cell.recordedArm, (cell.reward, cell.rate))) := by
    rfl
  have hcodes :
      (List.ofFn (fun k : Fin (t.val - s) =>
        outputNumericalCellTag (p := p)
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (ReferenceFirstLiveNumericalPrefixBorel.numericalCountPastReadout
            rate rewards C_star C_h q t s hs control0 z k)) :
          List (Unit ⊕ ArrivalCode p.K)) =
        (List.ofFn (fun k : Fin (t.val - s) =>
          taggedGetElem? cells
            (arrivalCodeOfRound
              (ReferenceFirstLaunchNumericalCell.queueParameters rate)) k.val) :
            List (Unit ⊕ ArrivalCode p.K)) := by
    apply congrArg List.ofFn
    funext k
    rw [hread k]
    cases hcell : cells[k.val]? with
    | none => simp [taggedGetElem?, hcell, outputNumericalCellTag,
        numericalArrivalTag]
    | some cell =>
        simp only [taggedGetElem?, hcell]
        change Sum.inr (numericalArrivalCode
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (cell.enabled, (cell.recordedArm, (cell.reward, cell.rate)))) =
          Sum.inr (arrivalCodeOfRound
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell)
        apply congrArg Sum.inr
        apply Prod.ext
        · rfl
        ·
          funext i
          simp [numericalArrivalCode, arrivalCodeOfRound,
            RecordedQueueRun.quantizedArrival]
  have hrun := runArrivalTags_of_readout
    (ReferenceFirstLaunchNumericalCell.queueParameters rate) cells (t.val - s) hlen
  change ((RecordedQueueRun.run
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) cells).registers,
    ((RecordedQueueRun.run
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) cells).overflow,
      (RecordedQueueRun.run
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cells).records)) =
      runArrivalTags (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (List.ofFn fun k : Fin (t.val - s) =>
          outputNumericalCellTag (p := p)
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (ReferenceFirstLiveNumericalPrefixBorel.numericalCountPastReadout
              rate rewards C_star C_h q t s hs control0 z k))
  have htagRun := congrArg
    (fun tags : List (Unit ⊕ ArrivalCode p.K) =>
      runArrivalTags (K := p.K)
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) tags)
    hcodes
  simpa only [ArrivalCode] using (htagRun.trans hrun).symm

/-- The complete first-live numerical queue output is Borel on the inherited
ambient source stratum. -/
theorem measurable_numericalCountRunReadout
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (numericalCountRunReadout rate rewards C_star C_h q t s hs control0) := by
  let qpar := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let observation := ReferenceFirstLiveNumericalPrefixBorel.numericalCountPastReadout
    rate rewards C_star C_h q t s hs control0
  have hObservation : Measurable observation :=
    ReferenceFirstLiveNumericalPrefixBorel.measurable_numericalCountPastReadout
      rate rewards C_star C_h q t s hs control0
  have htags : Measurable (fun z : SourceZ rate rewards C_star C_h t q s hs =>
      fun k : Fin (t.val - s) =>
        outputNumericalCellTag (p := p) qpar (observation z k)) := by
    apply measurable_pi_iff.mpr
    intro k
    exact (measurable_numericalArrivalTag (p := p) qpar).comp
      ((measurable_pi_apply k).comp hObservation)
  let codeList (z : SourceZ rate rewards C_star C_h t q s hs) :=
    List.ofFn (fun k : Fin (t.val - s) =>
      outputNumericalCellTag (p := p) qpar (observation z k))
  have hcodeList : Measurable codeList := measurable_list_ofFn
    (t.val - s) (fun z k => outputNumericalCellTag (p := p) qpar (observation z k)) htags
  have hrunCodes : Measurable (runArrivalTags (K := p.K) qpar) :=
    measurable_of_countable _
  have hresult : Measurable (fun z : SourceZ rate rewards C_star C_h t q s hs =>
      runArrivalTags qpar (codeList z)) := hrunCodes.comp hcodeList
  have heq :
      numericalCountRunReadout rate rewards C_star C_h q t s hs control0 =
        fun z => runArrivalTags qpar (codeList z) := by
    funext z
    exact numericalCountRunReadout_eq_arrivalTags
      rate rewards C_star C_h q t s hs control0 z
  rw [heq]
  exact hresult

/-- The event that the actual complete numerical queue run has not overflowed
is Borel on the original source stratum. -/
theorem measurableSet_numericalCountRunOverflowFalse
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSet {z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) |
      (numericalCountRunReadout rate rewards C_star C_h q t s hs control0 z).2.1 = false} := by
  exact (measurableSet_singleton false).preimage
    (measurable_fst.comp
      (measurable_snd.comp
        (measurable_numericalCountRunReadout
          rate rewards C_star C_h q t s hs control0)))

/-- Each arm's complete final score/backlog pair is Borel. -/
theorem measurable_numericalCountRunRegister
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin p.K) :
    Measurable (fun z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) =>
      (numericalCountRunReadout rate rewards C_star C_h q t s hs control0 z).1 i) :=
  (measurable_pi_apply i).comp
    (measurable_fst.comp
      (measurable_numericalCountRunReadout
        rate rewards C_star C_h q t s hs control0))

/-- Each arm's complete chronological accepted/no-op record list is Borel in
the existing length-and-index list observation space. -/
theorem measurable_numericalCountRunRecords
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin p.K) :
    Measurable (fun z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) =>
      (numericalCountRunReadout rate rewards C_star C_h q t s hs control0 z).2.2 i) :=
  (measurable_pi_apply i).comp
    (measurable_snd.comp
      (measurable_snd.comp
        (measurable_numericalCountRunReadout
          rate rewards C_star C_h q t s hs control0)))

end Bandits.Support.ReferenceFirstLiveNumericalQueueBorel

end
