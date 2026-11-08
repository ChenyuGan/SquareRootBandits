/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCorrectedSliceNumericalPrefix

import Mathlib.Tactic

/-!
# Corrected stopped energy on the original source

The observations in this module retain the initialized queue from launch.
The endpoint code reads the complete original horizon. It makes no claim of
strict-prefix predictability or invariance under replacement of a control row.

Sources: `04_slow_fast_learner.tex:140-188,245-315`,
`05_binary_transport.tex:354-431`, `06_interruptions.tex:355-426`.
These are internal components for the original-source overflow assembly.
-/

@[expose] public section
noncomputable section

open Bandits.Support ConstructorDimensions MeasureTheory
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ReferenceSourcePrefixHistoryFiltration (actualRecord actualLaunchBy)
open ReferenceFirstCollectionRenewalIncomingQueueMeasurability (stateReadout)
open scoped Classical BigOperators

open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
  (correctedCell sourceRecords sourceStart prefixInputs prefixReadout endDate)
open ReferenceLaterCollectionSourceReadoutMeasurability
  (arrivalCoordinates numericalCoordinates arrivalsFromNumerical)
open ReferenceFirstCollectionCurrentQueueReadout
  (optionalReadoutUpdate readoutUpdate)
open ReferenceCompleteNumericalBranchObservation
  (branchArrivalProjection arrivalBranchReadout branchReadout leftProjection rightProjection)


namespace Bandits.Support.ReferenceFirstCollectionCorrectedStoppedEnergyTelescope


variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

local notation "X" => SourceInput p
local instance sourceInputMeasurableSpace : MeasurableSpace X := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "Input" => RecordedQueueRun.RoundInput p.K
local notation "Readout" => ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K
local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

/-- Continuing bits of the complete horizon observation, with absence false. -/
def horizonContinuing (j : Fin p.T) (x : X) : Bool :=
  (ReferenceInspectedPastRoundObservations.pastRoundObservations
    rate rewards C_star C_h p.T le_rfl x j).elim false (ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingCode rate)

/-- A literal chosen-cutoff tag test. Other outcomes remain false. -/
def chosenCutoffTag : Option (ReferenceFirstCollectionRenewalNextRecordingPriorView.LiveTag p) → Bool
  | some (.inr (.inr (.inr (_, true)))) => true
  | _ => false

/-- Current cutoff bits use the original continuous actual inputs. -/
def horizonCutoff (j : Fin p.T) (x : X) : Bool :=
  chosenCutoffTag ((ReferenceFirstCollectionCorrectedNextPhysicalReadout.actualInput?
    rate rewards C_star C_h j x).bind ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag)

/-- The finite continuing segment starts at the inherited AFTER boundary. -/
def continuingSegment (t : Fin p.T) (x : X) : List Bool :=
  List.ofFn fun i : Fin (p.T - (t.val + 1)) =>
    horizonContinuing rate rewards C_star C_h
      ⟨t.val + 1 + i.val, by have := i.isLt; omega⟩ x

/-- Length of the initial continuing segment in the complete horizon code. -/
def continuingLength (t : Fin p.T) (x : X) : ℕ :=
  ((continuingSegment rate rewards C_star C_h t x).takeWhile id).length

/-- Finite full-history endpoint code; the first chosen cutoff update is included. -/
def endpointCode (t : Fin p.T) (x : X) : ℕ :=
  let j := t.val + 1 + continuingLength rate rewards C_star C_h t x
  j + if hj : j < p.T then
    if horizonCutoff rate rewards C_star C_h ⟨j, hj⟩ x then 1 else 0
  else 0

private theorem measurable_optionElim {A D : Type*}
    [MeasurableSpace A] [MeasurableSpace D] (f : A → D)
    (hf : Measurable f) (d : D) :
    Measurable (fun o : Option A => o.elim d f) := by
  have h := (hf.sumElim (measurable_const (a := d) :
    Measurable (fun _ : PUnit => d))).comp
    (comap_measurable (Equiv.optionEquivSumPUnit A))
  convert h using 1
  funext o
  cases o <;> rfl

/-- Ambient Borelness uses the accepted full record-code observation. -/
theorem measurable_horizonContinuing (j : Fin p.T) :
    Measurable (horizonContinuing rate rewards C_star C_h j) := by
  exact (measurable_optionElim _ (ReferenceFirstCollectionRenewalFutureFirstReplacementView.measurable_continuingCode rate) false).comp
    ((measurable_pi_apply j).comp
      (ReferenceInspectedPastRoundObservations.measurable_pastRoundObservations
        rate rewards C_star C_h p.T le_rfl))

private theorem measurable_optionBind {A D : Type*}
    [MeasurableSpace A] [MeasurableSpace (Option D)]
    (g : A → Option D) (hg : Measurable g) :
    Measurable (fun o : Option A => o.bind g) := by
  convert measurable_optionElim g hg none using 1
  funext o
  cases o <;> rfl

/-- Ambient Borelness preserves the continuous actual-input carrier. -/
theorem measurable_horizonCutoff (j : Fin p.T) :
    Measurable (horizonCutoff rate rewards C_star C_h j) := by
  exact (measurable_of_countable chosenCutoffTag).comp
    ((measurable_optionBind ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag ReferenceFirstCollectionRenewalNextRecordingPriorView.measurable_dispatchTag).comp
      (ReferenceFirstCollectionCorrectedNextPhysicalReadout.measurable_actualInput?
        rate rewards C_star C_h j))

/-- Only the resulting finite Boolean observation is treated as countable. -/
theorem measurable_continuingLength (t : Fin p.T) :
    Measurable (continuingLength rate rewards C_star C_h t) := by
  have hflags : Measurable (fun x : X => fun i : Fin (p.T - (t.val + 1)) =>
      horizonContinuing rate rewards C_star C_h
        ⟨t.val + 1 + i.val, by have := i.isLt; omega⟩ x) :=
    Measurable.of_eval (fun _ => measurable_horizonContinuing rate rewards C_star C_h _)
  exact (measurable_of_countable (fun flags : Fin (p.T - (t.val + 1)) → Bool =>
    ((List.ofFn flags).takeWhile id).length)).comp hflags

/-- The endpoint code is a Borel function of the full original history. -/
theorem measurable_endpointCode (t : Fin p.T) :
    Measurable (endpointCode rate rewards C_star C_h t) := by
  have hc : Measurable (fun x : X => fun j : Fin p.T =>
      horizonCutoff rate rewards C_star C_h j x) :=
    Measurable.of_eval (fun j => measurable_horizonCutoff rate rewards C_star C_h j)
  exact (measurable_of_countable (fun z : ℕ × (Fin p.T → Bool) =>
    let j := t.val + 1 + z.1
    j + if hj : j < p.T then if z.2 ⟨j, hj⟩ then 1 else 0 else 0)).comp
      ((measurable_continuingLength rate rewards C_star C_h t).prodMk hc)

private theorem horizonContinuing_actual (j : Fin p.T) (x : X) :
    horizonContinuing rate rewards C_star C_h j x =
      (actualRecord rate rewards C_star C_h j x).any
        ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen := by
  unfold horizonContinuing ReferenceInspectedPastRoundObservations.pastRoundObservations
  simp only [Fin.castLE_refl]
  cases hr : actualRecord rate rewards C_star C_h j x with
  | none => rfl
  | some r =>
    simpa only [Option.map_some, Option.elim_some, Option.any_some] using
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingCode_actual rate r

private theorem horizonCutoff_actual (j : Fin p.T) (x : X) :
    horizonCutoff rate rewards C_star C_h j x =
      (actualRecord rate rewards C_star C_h j x).any (fun r =>
        match r.output.preparation.coordinator with
        | .live _ _ _ (.cutoffChosen ..) => true
        | _ => false) := by
  unfold horizonCutoff ReferenceFirstCollectionCorrectedNextPhysicalReadout.actualInput?
  cases hr : actualRecord rate rewards C_star C_h j x with
  | none => rfl
  | some r =>
    simp only [Option.map_some, Option.bind_some, Option.any_some]
    have hd : ReferenceActivePhysicalStep.dispatch r.input = r.output.preparation.coordinator := by
      rw [r.output_eq]
      rfl
    unfold ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag
    rw [hd]
    cases r.output.preparation.coordinator <;> try rfl
    rename_i registers owned base out
    cases out <;> rfl

/-- The complete horizon bits reproduce exactly the actual post-birth suffix. -/
theorem continuingSegment_actual (u t : Fin p.T) (x : X)
    (hx : x ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u t) :
    continuingSegment rate rewards C_star C_h t x =
      ((ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h x).drop
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h x + 1)).map
          ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen := by
  have ht := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time rate rewards C_star C_h u t x hx
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate x rewards C_star C_h
  change (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h x).length =
    p.T - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h x at hlen
  apply List.ext_getElem
  · simp only [continuingSegment, List.length_ofFn, List.length_map, List.length_drop]
    omega
  · intro i hi hi'
    have hiT : i < p.T - (t.val + 1) := by simpa [continuingSegment] using hi
    let j : Fin p.T := ⟨t.val + 1 + i, by omega⟩
    have hs : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h x ≤ j.val := by dsimp [j]; omega
    have hidx : j.val - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h x =
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h x + 1 + i := by dsimp [j]; omega
    have hr : actualRecord rate rewards C_star C_h j x =
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h x)[ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h x + 1 + i]? := by
      unfold actualRecord
      change (if ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h x ≤ j.val then
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h x)[j.val - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h x]? else none) = _
      rw [ite_eq_left hs]
      rw [hidx]
    have hlookup : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h x + 1 + i <
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h x).length := by
      simp only [List.length_map, List.length_drop] at hi'
      omega
    simp only [continuingSegment, List.getElem_ofFn, List.getElem_map, List.getElem_drop]
    change horizonContinuing rate rewards C_star C_h j x =
      ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h x)[
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h x + 1 + i]
    rw [horizonContinuing_actual, hr, List.getElem?_eq_getElem hlookup]
    rfl

/-- The observed length is the original continuing-tail length, including an empty tail. -/
theorem continuingLength_actual (u t : Fin p.T) (x : X)
    (hx : x ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u t) :
    continuingLength rate rewards C_star C_h t x =
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length := by
  rw [continuingLength, continuingSegment_actual rate rewards C_star C_h u t x hx,
    List.takeWhile_map, List.length_map]
  rfl

/-- The finite Borel endpoint code equals the original endpoint on the corrected cell. -/
theorem endpointCode_actual (u t : Fin p.T) (x : X)
    (hx : x ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u t) :
    endpointCode rate rewards C_star C_h t x = ReferenceFirstCollectionCorrectedSliceNumericalPrefix.endDate rate rewards C_star C_h t x := by
  have ht := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time rate rewards C_star C_h u t x hx
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate x rewards C_star C_h
  change (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h x).length =
    p.T - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h x at hlen
  unfold endpointCode
  rw [continuingLength_actual rate rewards C_star C_h u t x hx]
  dsimp only
  unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.endDate
  congr 1
  by_cases hj : t.val + 1 + (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length < p.T
  · rw [dite_eq_left hj, horizonCutoff_actual]
    have hs : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h x ≤
        t.val + 1 + (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length := by omega
    have hidx : t.val + 1 + (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length -
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h x =
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h x + 1 + (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length := by omega
    unfold actualRecord
    change (if (if ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h x ≤
      t.val + 1 + (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length then
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h x)[
        t.val + 1 + (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length -
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h x]? else none).any _ then 1 else 0) = _
    rw [ite_eq_left hs]
    rw [hidx]
    unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.cutoffDelta
    cases (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h x)[ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h x +
        1 + (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length]? with
    | none => rfl
    | some r =>
      simp only [Option.any_some]
      split <;> split <;> simp_all
  · rw [dite_eq_right hj]
    unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.cutoffDelta
    rw [List.getElem?_eq_none (by omega)]

local instance branchArrivalOptionMeasurableSpace :
    MeasurableSpace (Option ((Bool × (Fin p.K → ℕ)) ⊕ (Bool × (Fin p.K → ℕ)))) :=
  ReferenceCompleteNumericalBranchObservation.branchArrivalOptionMeasurableSpace (p := p)

private instance sumMeasurableSingleton {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) where
  measurableSet_singleton x := by
    cases x with
    | inl a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inl_image
    | inr b => simpa only [Set.image_singleton] using (MeasurableSet.singleton b).inr_image

private instance optionMeasurableSingleton {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Option α) where
  measurableSet_singleton x := by
    have h := (comap_measurable (Equiv.optionEquivSumPUnit α))
      (MeasurableSet.singleton (Equiv.optionEquivSumPUnit α x))
    convert h using 1
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage,
      (Equiv.optionEquivSumPUnit α).injective.eq_iff]

private instance listMeasurableSingleton {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (List α) where
  measurableSet_singleton L := by
    have hinj : Function.Injective
        (ReferenceActiveHorizonMeasurability.listObservationCoordinates (α := α)) := by
      intro A B h
      have hlen : A.length = B.length := congrArg Prod.fst h
      apply List.ext_getElem hlen
      intro k hk hk'
      have he := congrFun (congrArg Prod.snd h) k
      simpa only [ReferenceActiveHorizonMeasurability.listObservationCoordinates,
        ReferenceActiveHorizonMeasurability.listObservationAt,
        List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk', Sum.inr.injEq] using he
    have hh := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
      (MeasurableSet.singleton
        (ReferenceActiveHorizonMeasurability.listObservationCoordinates L))
    convert hh using 1
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, hinj.eq_iff]

private theorem cell0_coordinates (r : Record) :
    (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r).map numericalCoordinates =
      (branchReadout rate 0 r).map (Sum.elim id id) := by
  have hp := ReferenceCompleteNumericalBranchObservation.branch_readout_projections rate 0 r
  rw [ReferenceFirstCollectionCurrentRetainedGate.cell0, Option.map_or]
  have hl := congrArg Prod.fst hp
  have hr := congrArg Prod.snd hp
  change leftProjection _ =
    (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).map numericalCoordinates at hl
  change rightProjection _ =
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).map numericalCoordinates at hr
  rw [← hl, ← hr]
  cases branchReadout rate 0 r with
  | none => rfl
  | some value => cases value <;> rfl

/-- The projection keeps each actual cell, including its absence and quantized floor. -/
theorem cell0_arrival_coordinates (r : Record) :
    (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r).map
        (arrivalCoordinates rate) =
      (arrivalBranchReadout rate 0 r).map (Sum.elim id id) := by
  have h := congrArg (Option.map (arrivalsFromNumerical rate)) (cell0_coordinates rate r)
  simp only [Option.map_map] at h
  have hf : (fun c : Input => arrivalsFromNumerical rate (numericalCoordinates c)) =
      arrivalCoordinates rate := by
    funext c
    exact ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical_numericalCoordinates rate c
  rw [show arrivalsFromNumerical rate ∘ numericalCoordinates = arrivalCoordinates rate from hf] at h
  rw [h]
  unfold arrivalBranchReadout
  simp only [Option.map_map]
  congr 1
  funext value
  cases value <;> rfl

/-- The countable readout update agrees with the existing queue transition. -/
theorem readoutUpdate_step (s : RecordedQueueRun.RunState p.K) (c : Input) :
    readoutUpdate rate (stateReadout s) (arrivalCoordinates rate c) =
      stateReadout (RecordedQueueRun.step Q s c) := by
  cases s
  rfl

private theorem optional_fold_none (cells : List (Option Input)) :
    cells.foldl (fun old c => optionalReadoutUpdate rate old
      (c.map (arrivalCoordinates rate))) none = none := by
  induction cells with
  | nil => rfl
  | cons c cells ih =>
    simpa only [List.foldl_cons, optionalReadoutUpdate, Option.bind_none] using ih

private theorem optional_fold_execute (cells : List (Option Input))
    (s : RecordedQueueRun.RunState p.K) :
    cells.foldl (fun old c => optionalReadoutUpdate rate old
      (c.map (arrivalCoordinates rate))) (some (stateReadout s)) =
      (cells.mapM id).map (fun cs => stateReadout (RecordedQueueRun.execute Q cs s)) := by
  induction cells generalizing s with
  | nil => rfl
  | cons cell cells ih =>
    cases cell with
    | none =>
      simp only [List.foldl_cons, Option.map_none, optionalReadoutUpdate,
        Option.bind_some, List.mapM_cons, id_eq, Option.map_none]
      exact optional_fold_none rate cells
    | some c =>
      rw [List.foldl_cons]
      change cells.foldl (fun old c => optionalReadoutUpdate rate old
        (c.map (arrivalCoordinates rate)))
          (some (readoutUpdate rate (stateReadout s) (arrivalCoordinates rate c))) = _
      rw [readoutUpdate_step, ih]
      cases htail : cells.mapM id <;>
        simp [List.mapM_cons, htail, RecordedQueueRun.execute]

/-- The exact optional arrival fold, preserving dates and optional L/R tags in its input. -/
def arrivalFold (n : ℕ) (x : X) : Option Readout :=
  if actualLaunchBy rate rewards C_star C_h n x then
    (((branchArrivalProjection rate rewards C_star C_h 0 x).take
      (n - sourceStart rate rewards C_star C_h x)).map
        (fun entry => entry.2.map (Sum.elim id id))).foldl
          (optionalReadoutUpdate rate)
          (some (stateReadout (RecordedQueueRun.initialState p.K)))
  else none

/-- Original prefix-to-arrival-fold identity, valid also at the terminal boundary. -/
theorem prefixReadout_eq_arrivalFold (n : ℕ) (x : X) :
    prefixReadout rate rewards C_star C_h n x =
      arrivalFold rate rewards C_star C_h n x := by
  unfold prefixReadout prefixInputs arrivalFold
  by_cases hl : actualLaunchBy rate rewards C_star C_h n x
  · rw [ite_eq_left hl, ite_eq_left hl]
    unfold branchArrivalProjection ReferenceCompleteNumericalBranchObservation.branchCalendar
    simp only [List.map_take, List.map_map, Function.comp_def]
    have hm :
        ((sourceRecords rate rewards C_star C_h x).take
          (n - sourceStart rate rewards C_star C_h x)).map (fun r =>
            (arrivalBranchReadout rate 0 r).map (Sum.elim id id)) =
        (((sourceRecords rate rewards C_star C_h x).take
          (n - sourceStart rate rewards C_star C_h x)).map
            (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).map
              (Option.map (arrivalCoordinates rate)) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro r _
      exact (cell0_arrival_coordinates rate r).symm
    simp only [← List.map_take]
    change _ = (((sourceRecords rate rewards C_star C_h x).take
      (n - sourceStart rate rewards C_star C_h x)).map (fun r =>
        (arrivalBranchReadout rate 0 r).map (Sum.elim id id))).foldl _ _
    rw [hm, List.foldl_map]
    exact (optional_fold_execute rate _ (RecordedQueueRun.initialState p.K)).symm
  · simp only [ite_eq_right hl, Option.map_none]

/-- Launch is a finite union of actual generated launch fibers, including the horizon. -/
theorem measurableSet_actualLaunchBy (n : ℕ) :
    MeasurableSet {x : X | actualLaunchBy rate rewards C_star C_h n x} := by
  have he : {x : X | actualLaunchBy rate rewards C_star C_h n x} =
      ⋃ s : Fin (n + 1),
        ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
          (rate := rate) rewards C_star C_h s.val := by
    ext x
    constructor
    · rintro ⟨hc, hs⟩
      exact Set.mem_iUnion.mpr ⟨⟨ReferenceCompletePhysicalHistory.physicalStart
        rate x rewards C_star C_h, by omega⟩, hc, rfl⟩
    · intro hx
      obtain ⟨s, hc, hs⟩ := Set.mem_iUnion.mp hx
      exact ⟨hc, hs ▸ Nat.le_of_lt_succ s.isLt⟩
  rw [he]
  exact MeasurableSet.iUnion (fun s =>
    ReferenceGeneratedDownAmbiguityMeasurability.measurableSet_generatedLaunchFiberSet
      (rate := rate) rewards C_star C_h s.val)

private theorem measurable_arrivalProjection_zero :
    Measurable (fun x : X => branchArrivalProjection rate rewards C_star C_h 0 x) := by
  have hzero : Measurable (fun x : X => ((0 : ℕ), x)) :=
    measurable_const.prodMk measurable_id
  have hm := (ReferenceCompleteNumericalBranchObservation.measurable_branchArrivalProjection
    rate rewards C_star C_h).comp hzero
  simpa only [Function.comp_def] using hm

private theorem measurable_foldFromCode (n : ℕ) :
    Measurable (fun z :
        List (ReferenceCompleteNumericalBranchObservation.BranchArrivalEntry rate) × ℕ =>
      ((z.1.take (n - z.2)).map (fun entry => entry.2.map (Sum.elim id id))).foldl
        (optionalReadoutUpdate rate)
        (some (stateReadout (RecordedQueueRun.initialState p.K)))) := by
  exact measurable_of_countable _

private theorem measurable_arrivalFold (n : ℕ) :
    Measurable (arrivalFold rate rewards C_star C_h n) := by
  have hfold := (measurable_foldFromCode rate n).comp
    ((measurable_arrivalProjection_zero rate rewards C_star C_h).prodMk
      (ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
        rate rewards C_star C_h))
  exact hfold.ite (measurableSet_actualLaunchBy rate rewards C_star C_h n)
    (measurable_const (a := none))

/-- Ambient readout Borelness, without assigning a discrete structure to raw inputs. -/
theorem measurable_prefixReadout (n : ℕ) :
    Measurable (prefixReadout rate rewards C_star C_h n) := by
  have he : prefixReadout rate rewards C_star C_h n =
      arrivalFold rate rewards C_star C_h n :=
    funext (prefixReadout_eq_arrivalFold rate rewards C_star C_h n)
  rw [he]
  exact measurable_arrivalFold rate rewards C_star C_h n

local instance optionNatMeasurableSpace : MeasurableSpace (Option ℕ) :=
  ReferenceFirstCollectionRenewalAuxiliaryLaw.optionNatMeasurableSpace

/-- Borelness of the actual localization event; no normalization is introduced. -/
theorem measurableSet_correctedCell (u t : Fin p.T) :
    MeasurableSet (correctedCell rate rewards C_star C_h u t) := by
  have hfirst : MeasurableSet
      (ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t) := by
    exact ReferenceFirstCollectionSamplerCall.measurableSet_firstCollectionCall_cell
      rate rewards C_star C_h u t
  have hfreeze : MeasurableSet {x : X | ∃ g,
      ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt? rate rewards C_star C_h t x = some g ∧
        t.val + 1 < g} := by
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro g
    by_cases hg : t.val + 1 < g
    · simpa only [hg, and_true] using
        (measurableSet_eq_fun
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurable_oldFreezeAt?
            rate rewards C_star C_h t) (measurable_const (a := some g)))
    · simp only [hg, and_false, Set.ofPred_false]
      exact MeasurableSet.empty
  exact hfirst.inter hfreeze

/-- Clamping observes the same run; it does not change physical play. -/
def clampedIndex (t : Fin p.T) (n : ℕ) (x : X) : ℕ :=
  min (max (t.val + 1) n) (endDate rate rewards C_star C_h t x)

theorem clampedIndex_bounds (u t : Fin p.T) (n : ℕ) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t) :
    t.val + 1 ≤ clampedIndex rate rewards C_star C_h t n x ∧
      clampedIndex rate rewards C_star C_h t n x ≤ endDate rate rewards C_star C_h t x := by
  have he := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.endDate_bounds
    rate rewards C_star C_h u t x hx
  exact ⟨le_min (le_max_left _ _) he.1, min_le_right _ _⟩

/-- Presence comes from the actual initialized full prefix at the clamped date. -/
theorem clampedReadout_present (u t : Fin p.T) (n : ℕ) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t) :
    (prefixReadout rate rewards C_star C_h
      (clampedIndex rate rewards C_star C_h t n x) x).isSome := by
  have hb := clampedIndex_bounds rate rewards C_star C_h u t n x hx
  obtain ⟨L, _hL, _hlen, hread⟩ :=
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_prefix_inputs
      rate rewards C_star C_h u t x hx _ hb.1 hb.2
  rw [hread]
  rfl

/-- The unique actual optional readout, accessed only on its proved presence domain. -/
def clampedReadout (u t : Fin p.T) (n : ℕ)
    (x : correctedCell rate rewards C_star C_h u t) : Readout :=
  (prefixReadout rate rewards C_star C_h
    (clampedIndex rate rewards C_star C_h t n x.val) x.val).get
      (clampedReadout_present rate rewards C_star C_h u t n x.val x.property)

/-- Literal localized exponential energy with inherited AFTER energy at birth. -/
def stoppedEnergy (u t : Fin p.T) (a : Fin p.K) (n : ℕ) (x : X) : ℝ :=
  if hx : x ∈ correctedCell rate rewards C_star C_h u t then
    Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
      (((clampedReadout rate rewards C_star C_h u t n ⟨x, hx⟩).1 a).2 : ℝ) / ((Q).n : ℝ))
  else 0

/-- Actual one-date difference, including the first overflow update. -/
def energyIncrement (u t : Fin p.T) (a : Fin p.K) (q : Fin p.T) (x : X) : ℝ :=
  stoppedEnergy rate rewards C_star C_h u t a (q.val + 1) x -
    stoppedEnergy rate rewards C_star C_h u t a q.val x

theorem stoppedEnergy_off_cell (u t : Fin p.T) (a : Fin p.K) (n : ℕ) (x : X)
    (hx : x ∉ correctedCell rate rewards C_star C_h u t) :
    stoppedEnergy rate rewards C_star C_h u t a n x = 0 := by
  exact dite_eq_right hx

/-- At every genuine in-slice date, the observation reads exactly the actual option. -/
theorem stoppedEnergy_eq_readout (u t : Fin p.T) (a : Fin p.K) (n : ℕ) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t)
    (hn : t.val + 1 ≤ n) (hne : n ≤ endDate rate rewards C_star C_h t x)
    (o : Readout) (ho : prefixReadout rate rewards C_star C_h n x = some o) :
    stoppedEnergy rate rewards C_star C_h u t a n x =
      Real.exp (CanonicalRecordingRates.beta p rate.eta.val * ((o.1 a).2 : ℝ) / ((Q).n : ℝ)) := by
  have hi : clampedIndex rate rewards C_star C_h t n x = n := by
    simp only [clampedIndex, max_eq_right hn, min_eq_left hne]
  have hr : clampedReadout rate rewards C_star C_h u t n ⟨x, hx⟩ = o := by
    unfold clampedReadout
    apply Option.get_of_eq_some
    simpa only [hi] using ho
  simp only [stoppedEnergy, dite_eq_left hx, hr]

/-- Clamping makes all observations before the birth boundary equal. -/
theorem stoppedEnergy_before_birth (u t : Fin p.T) (a : Fin p.K) (n : ℕ) (x : X)
    (hn : n ≤ t.val + 1) :
    stoppedEnergy rate rewards C_star C_h u t a n x =
      stoppedEnergy rate rewards C_star C_h u t a (t.val + 1) x := by
  by_cases hx : x ∈ correctedCell rate rewards C_star C_h u t
  · have hi : clampedIndex rate rewards C_star C_h t n x =
        clampedIndex rate rewards C_star C_h t (t.val + 1) x := by
      simp only [clampedIndex, max_eq_left hn, max_self]
    simp only [stoppedEnergy, dite_eq_left hx, clampedReadout, hi]
  · simp only [stoppedEnergy_off_cell rate rewards C_star C_h u t a _ x hx]

/-- After the endpoint only the analytical observation is frozen. -/
theorem stoppedEnergy_after_endpoint (u t : Fin p.T) (a : Fin p.K) (n : ℕ) (x : X)
    (hn : endDate rate rewards C_star C_h t x ≤ n) :
    stoppedEnergy rate rewards C_star C_h u t a n x =
      stoppedEnergy rate rewards C_star C_h u t a (endDate rate rewards C_star C_h t x) x := by
  by_cases hx : x ∈ correctedCell rate rewards C_star C_h u t
  · have hb := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.endDate_bounds
      rate rewards C_star C_h u t x hx
    have hi : clampedIndex rate rewards C_star C_h t n x =
        clampedIndex rate rewards C_star C_h t (endDate rate rewards C_star C_h t x) x := by
      simp only [clampedIndex, max_eq_right (hb.1.trans hn), min_eq_right hn,
        max_eq_right hb.1, min_self]
    simp only [stoppedEnergy, dite_eq_left hx, clampedReadout, hi]
  · simp only [stoppedEnergy_off_cell rate rewards C_star C_h u t a _ x hx]

/-- Off the actual open slice the scalar increment vanishes. -/
theorem energyIncrement_eq_zero (u t : Fin p.T) (a : Fin p.K) (q : Fin p.T) (x : X)
    (hq : q.val < t.val + 1 ∨ endDate rate rewards C_star C_h t x ≤ q.val) :
    energyIncrement rate rewards C_star C_h u t a q x = 0 := by
  unfold energyIncrement
  rcases hq with hq | hq
  · rw [stoppedEnergy_before_birth rate rewards C_star C_h u t a (q.val + 1) x (by omega),
      stoppedEnergy_before_birth rate rewards C_star C_h u t a q.val x (by omega), sub_self]
  · rw [stoppedEnergy_after_endpoint rate rewards C_star C_h u t a (q.val + 1) x (by omega),
      stoppedEnergy_after_endpoint rate rewards C_star C_h u t a q.val x hq, sub_self]

/-- Exact actual initialized-run difference; no conditional moment is an input. -/
theorem energyIncrement_actual_step (u t : Fin p.T) (a : Fin p.K) (q : Fin p.T) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t)
    (hq : t.val + 1 ≤ q.val) (hqe : q.val < endDate rate rewards C_star C_h t x) :
    ∃ (L : List Input) (r : Record) (c : Input),
      prefixInputs rate rewards C_star C_h q.val x = some L ∧
      (sourceRecords rate rewards C_star C_h x)[q.val - sourceStart rate rewards C_star C_h x]? = some r ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧
      prefixInputs rate rewards C_star C_h (q.val + 1) x = some (L ++ [c]) ∧
      energyIncrement rate rewards C_star C_h u t a q x =
        Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
          (((RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c).registers a).2 : ℝ) / ((Q).n : ℝ)) -
        Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
          (((RecordedQueueRun.run Q L).registers a).2 : ℝ) / ((Q).n : ℝ)) := by
  obtain ⟨L, r, c, hL, hr, hc, hnext, hread⟩ :=
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_step_inputs
      rate rewards C_star C_h u t x hx q.val hq hqe
  have hbefore : prefixReadout rate rewards C_star C_h q.val x =
      some (stateReadout (RecordedQueueRun.run Q L)) := by
    simp only [prefixReadout, hL, Option.map_some]
  refine ⟨L, r, c, hL, hr, hc, hnext, ?_⟩
  unfold energyIncrement
  rw [stoppedEnergy_eq_readout rate rewards C_star C_h u t a _ x hx (by omega) (by omega) _ hread,
    stoppedEnergy_eq_readout rate rewards C_star C_h u t a _ x hx hq hqe.le _ hbefore]
  rfl

/-- The index on the corrected cell has the finite full-history Borel code above. -/
theorem measurable_clampedIndex (u t : Fin p.T) (n : ℕ) :
    Measurable (fun x : correctedCell rate rewards C_star C_h u t =>
      clampedIndex rate rewards C_star C_h t n x.val) := by
  have hm : Measurable (fun x : correctedCell rate rewards C_star C_h u t =>
      min (max (t.val + 1) n) (endpointCode rate rewards C_star C_h t x.val)) :=
    (measurable_of_countable (fun e : ℕ => min (max (t.val + 1) n) e)).comp
    ((measurable_endpointCode rate rewards C_star C_h t).comp measurable_subtype_coe)
  have he : (fun x : correctedCell rate rewards C_star C_h u t =>
      clampedIndex rate rewards C_star C_h t n x.val) =
      (fun x => min (max (t.val + 1) n) (endpointCode rate rewards C_star C_h t x.val)) := by
    funext x
    rw [endpointCode_actual rate rewards C_star C_h u t x.val x.property]
    rfl
  rw [he]
  exact hm

/-- Readout Borelness on its proved presence domain, using no default readout. -/
theorem measurable_clampedReadout (u t : Fin p.T) (n : ℕ) :
    Measurable (clampedReadout rate rewards C_star C_h u t n) := by
  have hjoint : Measurable (fun z : ℕ × X => prefixReadout rate rewards C_star C_h z.1 z.2) :=
    measurable_from_prod_countable_right (fun k => measurable_prefixReadout rate rewards C_star C_h k)
  have hobs := hjoint.comp
    ((measurable_clampedIndex rate rewards C_star C_h u t n).prodMk measurable_subtype_coe)
  let present : correctedCell rate rewards C_star C_h u t →
      {o : Option Readout // o.isSome} := fun x =>
    ⟨prefixReadout rate rewards C_star C_h
      (clampedIndex rate rewards C_star C_h t n x.val) x.val,
        clampedReadout_present rate rewards C_star C_h u t n x.val x.property⟩
  have hpresent : Measurable present := hobs.subtype_mk
  exact (measurable_of_countable (fun o : {o : Option Readout // o.isSome} =>
    o.val.get o.property)).comp hpresent

/-- Ambient Borel energy on the original continuous source, at every clamped date. -/
theorem measurable_stoppedEnergy (u t : Fin p.T) (a : Fin p.K) (n : ℕ) :
    Measurable (stoppedEnergy rate rewards C_star C_h u t a n) := by
  have hm : Measurable (fun x : correctedCell rate rewards C_star C_h u t =>
      Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
        (((clampedReadout rate rewards C_star C_h u t n x).1 a).2 : ℝ) / ((Q).n : ℝ))) :=
    (measurable_of_countable (fun o : Readout =>
      Real.exp (CanonicalRecordingRates.beta p rate.eta.val * ((o.1 a).2 : ℝ) / ((Q).n : ℝ)))).comp
        (measurable_clampedReadout rate rewards C_star C_h u t n)
  exact hm.dite measurable_const (measurableSet_correctedCell rate rewards C_star C_h u t)

theorem measurable_energyIncrement (u t : Fin p.T) (a : Fin p.K) (q : Fin p.T) :
    Measurable (energyIncrement rate rewards C_star C_h u t a q) :=
  (measurable_stoppedEnergy rate rewards C_star C_h u t a (q.val + 1)).sub
    (measurable_stoppedEnergy rate rewards C_star C_h u t a q.val)

private theorem mem_of_mapM_id_some {α : Type*} (cells : List (Option α))
    (inputs : List α) (hmap : cells.mapM id = some inputs) (c : α)
    (hc : c ∈ inputs) : ∃ o, o ∈ cells ∧ o = some c := by
  induction cells generalizing inputs with
  | nil =>
    have hnil : inputs = [] := Option.some.inj (by simpa using hmap)
    subst inputs
    simp at hc
  | cons cell cells ih =>
    cases cell with
    | none => simp [List.mapM_cons] at hmap
    | some d =>
      simp only [List.mapM_cons] at hmap
      cases htail : cells.mapM id with
      | none => simp [htail] at hmap
      | some tail =>
        simp [htail] at hmap
        have hmem : c = d ∨ c ∈ tail := List.mem_cons.mp (by simpa [hmap] using hc)
        rcases hmem with hcd | hctail
        · subst c
          exact ⟨some d, by simp, rfl⟩
        · obtain ⟨o, ho, hsome⟩ := ih tail htail hctail
          exact ⟨o, by simp [ho], hsome⟩

/-- The lower rate bound is produced from actual record provenance in the full prefix. -/
theorem prefixInputs_rate_bounds (n : ℕ) (x : X) (L : List Input)
    (hL : prefixInputs rate rewards C_star C_h n x = some L) :
    ∀ c ∈ L, ∀ a, 32 * rate.eta.val ≤ c.rate a := by
  have hl := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
    rate rewards C_star C_h n x L hL
  simp only [prefixInputs, ite_eq_left hl] at hL
  intro c hc
  obtain ⟨o, ho, hsome⟩ := mem_of_mapM_id_some _ L hL c hc
  obtain ⟨r, _hr, hcell⟩ := List.mem_map.mp ho
  have hactual : ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate r = some c := by
    exact hcell.trans hsome
  exact (ReferenceFirstCollectionRenewalFutureQueueReadout.calendarCell_present_rate_bounds
    rate r c hactual).2

/-- Reachable optional readouts satisfy the twice-threshold queue bound internally. -/
theorem prefixReadout_backlog_bounds (n : ℕ) (x : X) (o : Readout)
    (ho : prefixReadout rate rewards C_star C_h n x = some o) (a : Fin p.K) :
    0 ≤ ((o.1 a).2 : ℝ) / ((Q).n : ℝ) ∧
      ((o.1 a).2 : ℝ) / ((Q).n : ℝ) ≤ 2 * (1 / (32 * rate.eta.val)) := by
  unfold prefixReadout at ho
  cases hL : prefixInputs rate rewards C_star C_h n x with
  | none => simp only [hL, Option.map_none, reduceCtorEq] at ho
  | some L =>
    have he : stateReadout (RecordedQueueRun.run Q L) = o :=
      Option.some.inj (by simpa only [hL, Option.map_some] using ho)
    rw [← he]
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · have hbound := StoppedQueueBound.run_prefix_normalized_backlog_le_twice_threshold
        Q L (prefixInputs_rate_bounds rate rewards C_star C_h n x L hL) L.length a
      simpa only [List.take_length, StoppedQueueBound.normalizedBacklog, stateReadout,
        ReferenceFirstLaunchNumericalCell.queueParameters] using hbound

/-- Exact uniform envelope from the source threshold and canonical beta. -/
def energyCeiling : ℝ :=
  Real.exp (CanonicalRecordingRates.beta p rate.eta.val * (2 * (1 / (32 * rate.eta.val))))

/-- Uniform energy domination on the entire original source, including outside the cell. -/
theorem stoppedEnergy_bounds (u t : Fin p.T) (a : Fin p.K) (n : ℕ) (x : X) :
    0 ≤ stoppedEnergy rate rewards C_star C_h u t a n x ∧
      stoppedEnergy rate rewards C_star C_h u t a n x ≤ energyCeiling rate := by
  by_cases hx : x ∈ correctedCell rate rewards C_star C_h u t
  · have hb := clampedIndex_bounds rate rewards C_star C_h u t n x hx
    obtain ⟨L, _hL, _hlen, hread⟩ :=
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_prefix_inputs
        rate rewards C_star C_h u t x hx _ hb.1 hb.2
    have hget : clampedReadout rate rewards C_star C_h u t n ⟨x, hx⟩ =
        stateReadout (RecordedQueueRun.run Q L) :=
      Option.get_of_eq_some _ hread
    have hbound := prefixReadout_backlog_bounds rate rewards C_star C_h _ x _ hread a
    simp only [stoppedEnergy, dite_eq_left hx, hget]
    constructor
    · exact (Real.exp_pos _).le
    · apply Real.exp_le_exp.mpr
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hbound.2
        (CanonicalRecordingRates.beta_pos p rate.eta.property).le
  · rw [stoppedEnergy_off_cell rate rewards C_star C_h u t a n x hx]
    exact ⟨le_rfl, (Real.exp_pos _).le⟩

/-- The two actual adjacent energies give an integrable uniform increment envelope. -/
theorem energyIncrement_abs_le (u t : Fin p.T) (a : Fin p.K) (q : Fin p.T) (x : X) :
    |energyIncrement rate rewards C_star C_h u t a q x| ≤ 2 * energyCeiling rate := by
  have hnext := stoppedEnergy_bounds rate rewards C_star C_h u t a (q.val + 1) x
  have hprior := stoppedEnergy_bounds rate rewards C_star C_h u t a q.val x
  calc
    |energyIncrement rate rewards C_star C_h u t a q x| ≤
        |stoppedEnergy rate rewards C_star C_h u t a (q.val + 1) x| +
          |stoppedEnergy rate rewards C_star C_h u t a q.val x| := abs_sub _ _
    _ ≤ energyCeiling rate + energyCeiling rate := by
      rw [abs_of_nonneg hnext.1, abs_of_nonneg hprior.1]
      exact add_le_add hnext.2 hprior.2
    _ = 2 * energyCeiling rate := by ring

/-- Original-source integrability follows from Borelness and deterministic domination. -/
theorem integrable_stoppedEnergy (u t : Fin p.T) (a : Fin p.K) (n : ℕ) :
    Integrable (stoppedEnergy rate rewards C_star C_h u t a n) (sourceInputLaw p) := by
  have hconst : Integrable (fun _ : X => energyCeiling rate) (sourceInputLaw p) :=
    integrable_const _
  refine hconst.mono' (measurable_stoppedEnergy rate rewards C_star C_h u t a n).aestronglyMeasurable ?_
  filter_upwards [] with x
  have hb := stoppedEnergy_bounds rate rewards C_star C_h u t a n x
  simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

theorem integrable_energyIncrement (u t : Fin p.T) (a : Fin p.K) (q : Fin p.T) :
    Integrable (energyIncrement rate rewards C_star C_h u t a q) (sourceInputLaw p) :=
  (integrable_stoppedEnergy rate rewards C_star C_h u t a (q.val + 1)).sub
    (integrable_stoppedEnergy rate rewards C_star C_h u t a q.val)

/-- Actual endpoint telescope. The inherited birth energy is never replaced by one. -/
theorem stoppedEnergy_telescope (u t : Fin p.T) (a : Fin p.K) (x : X) :
    stoppedEnergy rate rewards C_star C_h u t a p.T x =
      stoppedEnergy rate rewards C_star C_h u t a (t.val + 1) x +
        ∑ q : Fin p.T, energyIncrement rate rewards C_star C_h u t a q x := by
  have hsum : (∑ q : Fin p.T, energyIncrement rate rewards C_star C_h u t a q x) =
      stoppedEnergy rate rewards C_star C_h u t a p.T x -
        stoppedEnergy rate rewards C_star C_h u t a 0 x := by
    unfold energyIncrement
    rw [Fin.sum_univ_eq_sum_range (fun k =>
      stoppedEnergy rate rewards C_star C_h u t a (k + 1) x -
        stoppedEnergy rate rewards C_star C_h u t a k x) p.T]
    exact Finset.sum_range_sub (fun k => stoppedEnergy rate rewards C_star C_h u t a k x) p.T
  rw [hsum, stoppedEnergy_before_birth rate rewards C_star C_h u t a 0 x (by omega)]
  ring

/-- Unnormalized expectation telescope under the same original private-source law.
The next consumer integrates these same increments after proving future moments. -/
theorem integral_stoppedEnergy_telescope (u t : Fin p.T) (a : Fin p.K) :
    (∫ x, stoppedEnergy rate rewards C_star C_h u t a p.T x ∂sourceInputLaw p) =
      (∫ x, stoppedEnergy rate rewards C_star C_h u t a (t.val + 1) x ∂sourceInputLaw p) +
        ∑ q : Fin p.T, ∫ x, energyIncrement rate rewards C_star C_h u t a q x ∂sourceInputLaw p := by
  have hsum : Integrable (fun x : X =>
      ∑ q : Fin p.T, energyIncrement rate rewards C_star C_h u t a q x) (sourceInputLaw p) :=
    integrable_finsetSum Finset.univ (fun q _ =>
      integrable_energyIncrement rate rewards C_star C_h u t a q)
  calc
    _ = ∫ x, stoppedEnergy rate rewards C_star C_h u t a (t.val + 1) x +
        ∑ q : Fin p.T, energyIncrement rate rewards C_star C_h u t a q x ∂sourceInputLaw p := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (stoppedEnergy_telescope rate rewards C_star C_h u t a)
    _ = (∫ x, stoppedEnergy rate rewards C_star C_h u t a (t.val + 1) x ∂sourceInputLaw p) +
        ∫ x, ∑ q : Fin p.T, energyIncrement rate rewards C_star C_h u t a q x ∂sourceInputLaw p :=
      integral_add (integrable_stoppedEnergy rate rewards C_star C_h u t a (t.val + 1)) hsum
    _ = _ := by
      rw [integral_finsetSum Finset.univ (fun q _ =>
        integrable_energyIncrement rate rewards C_star C_h u t a q)]

/-- The birth observation is inherited from the actual AFTER queue at the first call. -/
theorem stoppedEnergy_birth_actual (u t : Fin p.T) (a : Fin p.K) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t) :
    ∃ (L : List Input) (c : Input),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t x = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell rate rewards C_star C_h t x = some c ∧
      prefixInputs rate rewards C_star C_h (t.val + 1) x = some (L ++ [c]) ∧
      stoppedEnergy rate rewards C_star C_h u t a (t.val + 1) x =
        Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
          (((RecordedQueueRun.run Q (L ++ [c])).registers a).2 : ℝ) / ((Q).n : ℝ)) := by
  obtain ⟨L, c, hL, hc, hinputs, _hlen⟩ :=
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_initial_inputs
      rate rewards C_star C_h u t x hx
  have hread : prefixReadout rate rewards C_star C_h (t.val + 1) x =
      some (stateReadout (RecordedQueueRun.run Q (L ++ [c]))) := by
    simp only [prefixReadout, hinputs, Option.map_some]
  refine ⟨L, c, hL, hc, hinputs, ?_⟩
  exact stoppedEnergy_eq_readout rate rewards C_star C_h u t a _ x hx le_rfl
    (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.endDate_bounds
      rate rewards C_star C_h u t x hx).1 _ hread

/-- The terminal observation is the same actual initialized full-prefix endpoint. -/
theorem stoppedEnergy_terminal_actual (u t : Fin p.T) (a : Fin p.K) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t) :
    ∃ L : List Input,
      prefixInputs rate rewards C_star C_h (endDate rate rewards C_star C_h t x) x = some L ∧
      prefixReadout rate rewards C_star C_h (endDate rate rewards C_star C_h t x) x =
        some (stateReadout (RecordedQueueRun.run Q L)) ∧
      stoppedEnergy rate rewards C_star C_h u t a p.T x =
        Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
          (((RecordedQueueRun.run Q L).registers a).2 : ℝ) / ((Q).n : ℝ)) := by
  have hb := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.endDate_bounds
    rate rewards C_star C_h u t x hx
  obtain ⟨L, hL, _hlen, hread⟩ :=
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_prefix_inputs
      rate rewards C_star C_h u t x hx _ hb.1 le_rfl
  refine ⟨L, hL, hread, ?_⟩
  rw [stoppedEnergy_after_endpoint rate rewards C_star C_h u t a p.T x hb.2]
  exact stoppedEnergy_eq_readout rate rewards C_star C_h u t a _ x hx hb.1 le_rfl _ hread

/-- A last-round birth has no fabricated successor action and no energy increments. -/
theorem terminal_birth_increments_zero (u t : Fin p.T) (a : Fin p.K) (x : X)
    (ht : t.val + 1 = p.T) (q : Fin p.T) :
    energyIncrement rate rewards C_star C_h u t a q x = 0 := by
  exact energyIncrement_eq_zero rate rewards C_star C_h u t a q x (Or.inl (by omega))

/-- No localized increment is assigned outside the corrected cell. -/
theorem energyIncrement_off_cell (u t : Fin p.T) (a : Fin p.K) (q : Fin p.T) (x : X)
    (hx : x ∉ correctedCell rate rewards C_star C_h u t) :
    energyIncrement rate rewards C_star C_h u t a q x = 0 := by
  simp only [energyIncrement, stoppedEnergy_off_cell rate rewards C_star C_h u t a _ x hx, sub_self]

end Bandits.Support.ReferenceFirstCollectionCorrectedStoppedEnergyTelescope
end
