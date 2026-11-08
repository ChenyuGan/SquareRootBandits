/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView

/-!
# Actual optional recording at the first next renewal date

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:391-426`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The outer option records numerical presence at the actual first next date.
The inner option records the physical arm or bottom, including zero arrivals.
All measures are the original, unnormalized renewal restrictions.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open scoped Classical MeasureTheory

namespace Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingLaw


open ReferenceActivePhysicalStep
open ReferenceFirstCollectionRenewalIncomingQueuePrefix
open ReferenceCompleteFirstPhaseObservationRecovery
open ReferenceCompleteNumericalBranchObservation
open ReferenceActiveHorizonMeasurability
open ReferenceSourcePrefixHistoryFiltration

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

local notation "Z" => ReferenceFirstCollectionRenewalNextControlLaw.Source rate rewards C_star C_h u t
local notation "ν" => ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
  rate rewards C_star C_h u t
local notation "κ" => ContinuousLearningRows.timeControlLaw p
local notation "Code" => NumericalCoordinates p

/-- Literal optional marker of the actual first next numerical readout. -/
def nextMarker (z : Z) (hq : t.val + 1 < p.T) : Option (Option (Fin p.K)) :=
  (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell rate rewards C_star C_h u t z hq).map (fun c => c.recordedArm)

/-- Scalar indicator-test coefficient; absence supplies no numerical cell. -/
def coefficientOfParameters (o : Option (Option (Fin p.K)))
    (parameters : Option (Bool × (Fin p.K → ℝ))) : ℝ :=
  match o, parameters with
  | none, none => 1
  | none, some _ => 0
  | some none, none => 0
  | some none, some (false, _) => 1
  | some none, some (true, xi) => 1 - ∑ j, xi j
  | some (some _), none => 0
  | some (some _), some (false, _) => 0
  | some (some j), some (true, xi) => xi j

/-- The coefficient uses precisely the actual optional enabled/rate readout. -/
def nextCoefficient (o : Option (Option (Fin p.K))) (z : Z)
    (hq : t.val + 1 < p.T) : ℝ :=
  coefficientOfParameters o (ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters rate rewards C_star C_h u t z hq)

/-- The bounded real indicator of an actual optional marker fiber. -/
def nextTest (o : Option (Option (Fin p.K))) (z : Z)
    (hq : t.val + 1 < p.T) : ℝ :=
  if nextMarker rate rewards C_star C_h u t z hq = o then 1 else 0

private theorem measurable_variable_observation {X B : Type*}
    [MeasurableSpace X] [MeasurableSpace B]
    (f : X → List B) (hf : Measurable f) (j : X → ℕ) (hj : Measurable j) :
    Measurable (fun x => listObservationAt (f x) (j x)) := by
  have ho := measurable_snd.comp (measurable_listObservationCoordinates.comp hf)
  have he : Measurable (fun v : (ℕ → Unit ⊕ B) × ℕ => v.1 v.2) :=
    measurable_from_prod_countable_left (fun n => measurable_pi_apply n)
  exact he.comp (ho.prodMk hj)

private theorem measurable_marker_readout {X : Type*} [MeasurableSpace X]
    (f : X → List (Fin p.T × Option Code)) (hf : Measurable f)
    (j : X → ℕ) (hj : Measurable j)
    (cells : X → Option (RecordedQueueRun.RoundInput p.K))
    (q : Fin p.T) (h : ∀ x, (f x)[j x]? = some (q, (cells x).map encodeNumerical)) :
    Measurable (fun x => (cells x).map (fun c => c.recordedArm)) := by
  let read : Unit ⊕ (Fin p.T × Option Code) → Option (Option (Fin p.K)) :=
    Sum.elim (fun _ => none) (fun e => e.2.map (fun c => c.2.1))
  have hcode : Measurable (fun e : Fin p.T × Option Code =>
      Equiv.optionEquivSumPUnit Code e.2) := (comap_measurable _).comp measurable_snd
  have hread : Measurable (fun e : Code ⊕ PUnit =>
      Sum.elim (fun c : Code => some c.2.1) (fun _ => none) e) :=
    ((measurable_of_countable (fun a : Option (Fin p.K) => some a)).comp
      (measurable_fst.comp measurable_snd)).sumElim measurable_const
  have hm : Measurable (fun e : Fin p.T × Option Code => e.2.map (fun c => c.2.1)) := by
    convert hread.comp hcode using 1
    funext e
    rcases e with ⟨_, c⟩
    cases c <;> rfl
  have hr : Measurable read := measurable_const.sumElim hm
  convert hr.comp (measurable_variable_observation f hf j hj) using 1
  funext x
  simp only [Function.comp_def, listObservationAt, h, read, Sum.elim_inr,
    Option.map_map]
  rfl

/-- Borelness on the original source, without a success or presence premise. -/
theorem measurable_nextMarker (hq : t.val + 1 < p.T) :
    Measurable (fun z : Z => nextMarker rate rewards C_star C_h u t z hq) := by
  have hc : Measurable (ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation rate rewards C_star C_h u t) :=
    (measurable_completeBranchObservation rate rewards C_star C_h).comp measurable_subtype_coe
  have hs : Measurable (start rate rewards C_star C_h u t) :=
    (ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
      rate rewards C_star C_h).comp measurable_subtype_coe
  have hj : Measurable (fun z : Z => t.val - start rate rewards C_star C_h u t z + 1) :=
    (measurable_of_countable (fun s : ℕ => t.val - s + 1)).comp hs
  have hl := measurable_marker_readout
    (fun z : Z => rawLiveNumericalDecoder rate (ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation rate rewards C_star C_h u t z))
    ((measurable_rawLiveNumericalDecoder rate).comp hc) _ hj
    (fun z => ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextLive rate rewards C_star C_h u t z hq) ⟨t.val + 1, hq⟩
    (fun z => ReferenceFirstCollectionRenewalNextPhysicalPrefix.rawLive_next_lookup rate rewards C_star C_h u t z hq)
  have hr := measurable_marker_readout
    (fun z : Z => rawCollectionNumericalDecoder rate (ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation rate rewards C_star C_h u t z))
    ((measurable_rawCollectionNumericalDecoder rate).comp hc) _ hj
    (fun z => ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCollection rate rewards C_star C_h u t z hq) ⟨t.val + 1, hq⟩
    (fun z => ReferenceFirstCollectionRenewalNextPhysicalPrefix.rawCollection_next_lookup rate rewards C_star C_h u t z hq)
  have hm := (measurable_of_countable
    (fun v : Option (Option (Fin p.K)) × Option (Option (Fin p.K)) => v.1.or v.2)).comp
      (hl.prodMk hr)
  simpa only [Function.comp_def, nextMarker,
    ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell, Option.map_or] using hm

/-- Joint Borelness retains the entire control, including unused coordinates. -/
theorem measurable_nextMarker_joint (hq : t.val + 1 < p.T) :
    Measurable (fun v : Z × ContinuousLearningRows.TimeControl p =>
      nextMarker rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalNextRecordingPriorView.withNextControl rate rewards C_star C_h u t v.1 hq v.2) hq) := by
  have hm : Measurable (fun v : Z × ContinuousLearningRows.TimeControl p =>
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p ⟨t.val + 1, hq⟩
        v.1.val v.2) := (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl
    p ⟨t.val + 1, hq⟩).comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  exact (measurable_nextMarker rate rewards C_star C_h u t hq).comp hm.subtype_mk

/-- Equality of the successor strict prefix identifies the actual optional
cell, even when future controls differ and either readout is absent. -/
theorem nextMarker_congr (control0 : ContinuousLearningRows.TimeControl p)
    (z z' : Z) (hq : t.val + 1 < p.T)
    (hp : sourcePrefix control0 (t.val + 2) z.val =
      sourcePrefix control0 (t.val + 2) z'.val) :
    nextMarker rate rewards C_star C_h u t z hq =
      nextMarker rate rewards C_star C_h u t z' hq := by
  have he : ReferenceFirstCollectionRenewalNextPhysicalPrefix.rawJoinedPrefix rate rewards C_star C_h u t z (t.val + 2) =
      ReferenceFirstCollectionRenewalNextPhysicalPrefix.rawJoinedPrefix rate rewards C_star C_h u t z' (t.val + 2) := by
    rw [ReferenceFirstCollectionRenewalNextPhysicalPrefix.rawJoinedPrefix_factor rate rewards C_star C_h u t control0 z _ (by omega),
      ReferenceFirstCollectionRenewalNextPhysicalPrefix.rawJoinedPrefix_factor rate rewards C_star C_h u t control0 z' _ (by omega), hp]
  rw [ReferenceFirstCollectionRenewalNextPhysicalPrefix.rawJoinedPrefix_next, ReferenceFirstCollectionRenewalNextPhysicalPrefix.rawJoinedPrefix_next] at he
  have hlast := congrArg List.getLast? he
  simp only [List.getLast?_append_cons, List.getLast?_singleton, Option.some.injEq] at hlast
  have hm := congrArg (Option.map (fun c : Code => c.2.1)) hlast
  simpa only [Option.map_map, Function.comp_def, encodeNumerical,
    ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates, nextMarker] using hm

/-- Restore just the next control in the prior observer. Later controls
remain reset; the actual optional marker is nevertheless reconstructed. -/
theorem nextMarker_reconstruct (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (hq : t.val + 1 < p.T) :
    nextMarker rate rewards C_star C_h u t
      (ReferenceFirstCollectionRenewalNextRecordingPriorView.withNextControl rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver rate rewards C_star C_h u t control0 z) hq
        (ReferenceFirstCollectionRenewalNextControlLaw.nextControl rate rewards C_star C_h u t hq z)) hq =
      nextMarker rate rewards C_star C_h u t z hq := by
  apply nextMarker_congr rate rewards C_star C_h u t control0
  have hr := prefix_successor_restore control0 (⟨t.val + 1, hq⟩ : Fin p.T) z.val
  change sourcePrefix control0 (t.val + 2)
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p ⟨t.val + 1, hq⟩
      (ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver
        rate rewards C_star C_h u t control0 z).val
      (ReferenceFirstCollectionRenewalNextControlLaw.nextControl rate rewards C_star C_h u t hq z)) = _
  rw [ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver_val]
  change sourcePrefix control0 (t.val + 2)
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p ⟨t.val + 1, hq⟩
      (sourcePrefix control0 (t.val + 1) z.val)
      ((z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val)).2 ⟨t.val + 1, hq⟩)) = _
  rw [← hr, sourcePrefix_sourcePrefix control0 _ _ le_rfl]

/-- Each present numerical readout is the literal snapshot map with actual
choice inputs. The optional snapshot distinguishes collection from live play.
All branch and preparation facts are produced on this same source. -/
theorem nextMarker_physical_kernel (z : Z) (hq : t.val + 1 < p.T) :
    match ReferenceFirstCollectionRenewalNextRecordingPriorView.nextRecordingView
      rate rewards C_star C_h u t z hq with
    | none => nextMarker rate rewards C_star C_h u t z hq = none
    | some (parameters, view, code) =>
      ∃ (enabled : Bool)
        (snapshot : Option (ActiveRoundActions.Snapshot view.payload.assignment))
        (valid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff
          (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
            rate rewards C_star C_h u t z hq).input.time view.complementWeights),
        parameters = some (enabled, view.payload.rate) ∧
        code = snapshot.map (fun s => (s.missing, fun i => some
          (FollowerDownMeasurability.followerStatusCode (s.status i)))) ∧
        nextMarker rate rewards C_star C_h u t z hq = some
          (SnapshotRecordingKernel.recordingMap p
            (snapshot.elim .collection (fun s => .live view.payload.assignment s)) enabled
            rate.eta.val rate.eta.property rate.sourceCap view.payload.anchor
            (ReferenceFirstWindowNumericalStream.sourceWeights view.payload view.complementWeights)
            view.payload.anchor_pos
            (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid)
            (ContinuousLearningRows.sliceAt
              (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
                rate rewards C_star C_h u t z hq).input.time
              (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
                rate rewards C_star C_h u t z hq).input.row.2)) := by
  have hr := ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextDate_readouts
    rate rewards C_star C_h u t z hq
  have hl := ReferenceFirstCollectionRenewalNextPhysicalPrefix.next_continuing_physical
    rate rewards C_star C_h u t z hq
  have hc := ReferenceFirstCollectionRenewalNextPhysicalPrefix.next_cutoff_physical
    rate rewards C_star C_h u t z hq
  have hs := ReferenceFirstCollectionRenewalNextRecordingPriorView.next_continuing_snapshot
    rate rewards C_star C_h u t z hq
  dsimp only at hr hl hc hs
  cases hd : (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
      rate rewards C_star C_h u t z hq).output.preparation.coordinator
    <;> simp only [hd] at hr hl hc hs
  all_goals try
    obtain ⟨hL, _, hC, _⟩ := hr
    have hn : ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
        rate rewards C_star C_h u t z hq = none := by
      simp only [ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell, hL, hC,
        Option.none_or]
    have hv := ReferenceFirstCollectionRenewalNextRecordingPriorView.nextRecordingView_presence
      rate rewards C_star C_h u t z hq
    rw [hn] at hv
    cases he : ReferenceFirstCollectionRenewalNextRecordingPriorView.nextRecordingView
        rate rewards C_star C_h u t z hq with
    | none => simp only [nextMarker, hn, Option.map_none]
    | some v => rw [he] at hv; cases hv
  rename_i registers owned base out
  cases out <;> simp only at hr hl hc hs
  all_goals try
    obtain ⟨hL, _, hC, _⟩ := hr
    have hn : ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
        rate rewards C_star C_h u t z hq = none := by
      simp only [ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell, hL, hC,
        Option.none_or]
    have hv := ReferenceFirstCollectionRenewalNextRecordingPriorView.nextRecordingView_presence
      rate rewards C_star C_h u t z hq
    rw [hn] at hv
    cases he : ReferenceFirstCollectionRenewalNextRecordingPriorView.nextRecordingView
        rate rewards C_star C_h u t z hq with
    | none => simp only [nextMarker, hn, Option.map_none]
    | some v => rw [he] at hv; cases hv
  · rename_i dispatched hstart ledger hinit hledger hdomain hclock hpending hnone selected
    obtain ⟨c, payload, ledger', started, weights, recording, hC, hL, hcall,
      henabled, hrate, _⟩ := hc
    have hdom := (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain
      (start rate rewards C_star C_h u t z)
      (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord rate rewards C_star C_h u t z hq)).mp
      (by change (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCollection
        rate rewards C_star C_h u t z hq).isSome = true; rw [hC]; rfl)
    have hsig : start rate rewards C_star C_h u t z < registers.payload.sigma.val := by
      simpa only [hd] using hdom.2
    have hread : c = ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput
        (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord rate rewards C_star C_h u t z hq)
        registers owned base dispatched selected := by
      unfold ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCollection at hC
      simp only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
        dite_eq_left hdom.1, hd, dite_eq_left hsig, Option.some.injEq] at hC
      exact hC.symm
    let view : ReferenceDownReception.ChoiceTimeView p rate.eta := {
      payload := registers.payload
      pendingAtChoice := dispatched.startResult.pending
      cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u
      complementWeights := (liveRegistersAt registers
        (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
          rate rewards C_star C_h u t z hq).input.time).complementWeights }
    have hv : ReferenceFirstCollectionRenewalNextRecordingPriorView.nextDownView
        rate rewards C_star C_h u t z hq = some view := by
      simp only [ReferenceFirstCollectionRenewalNextRecordingPriorView.nextDownView, hd,
        DispatchCut.downView, DispatchCut.selection, selectionAt, dite_true, Option.map_some]
      rfl
    have ht : ReferenceFirstCollectionRenewalNextRecordingPriorView.isCutoffTag
        (ReferenceFirstCollectionRenewalNextRecordingPriorView.nextTag
          rate rewards C_star C_h u t z hq) = true := by
      rw [ReferenceFirstCollectionRenewalNextRecordingPriorView.nextTag_eq, hd]
      rfl
    have hn : ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
        rate rewards C_star C_h u t z hq = some c := by
      simp only [ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell, hL, hC, Option.none_or]
    have hcanonical := ReferenceFirstCollectionRenewalNextRecordingPriorView.nextCell_rate_canonical
      rate rewards C_star C_h u t z hq
    rw [hn] at hcanonical
    obtain ⟨view', hv', hrate', _⟩ := hcanonical
    have hactualRate : c.rate = view.payload.rate := hrate'.trans
      (congrArg (fun v : ReferenceDownReception.ChoiceTimeView p rate.eta => v.payload.rate)
        (Option.some.inj (hv'.symm.trans hv)))
    rw [ReferenceFirstCollectionRenewalNextRecordingPriorView.nextRecordingView, hv,
      Option.map_some, ht]
    dsimp only [Bool.true_eq, ite_true]
    refine ⟨c.enabled, none, selected.choiceInputsValid, ?_, rfl, ?_⟩
    · simp only [ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters,
        hn, Option.map_some, hactualRate]
    · simp only [nextMarker, hn, Option.map_some]
      rw [hread]
      rfl
  · obtain ⟨cell0, hL0, hC, _⟩ := hl
    obtain ⟨cell, hL, hv, hmissing, hstatus, hrate⟩ := hs
    have hinput : cell0.input = cell.input := Option.some.inj (hL0.symm.trans hL)
    have hn : ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
        rate rewards C_star C_h u t z hq = some cell.input := by
      rw [ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell, hL0, Option.some_or, hinput]
    have hcanonical := ReferenceFirstCollectionRenewalNextRecordingPriorView.nextCell_rate_canonical
      rate rewards C_star C_h u t z hq
    rw [hn] at hcanonical
    obtain ⟨view', hv', hrate', _⟩ := hcanonical
    have hactualRate : cell.input.rate = cell.selected.view.payload.rate := hrate'.trans
      (congrArg (fun v : ReferenceDownReception.ChoiceTimeView p rate.eta => v.payload.rate)
        (Option.some.inj (hv'.symm.trans hv)))
    have ht : ReferenceFirstCollectionRenewalNextRecordingPriorView.isCutoffTag
        (ReferenceFirstCollectionRenewalNextRecordingPriorView.nextTag
          rate rewards C_star C_h u t z hq) = false := by
      rw [ReferenceFirstCollectionRenewalNextRecordingPriorView.nextTag_eq, hd]
      rfl
    rw [ReferenceFirstCollectionRenewalNextRecordingPriorView.nextRecordingView, hv,
      Option.map_some, ht]
    dsimp only [Bool.false_eq_true, ite_false]
    refine ⟨true, some (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states),
      cell.choiceInputsValid, ?_, ?_, ?_⟩
    · simp only [ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters,
        hn, Option.map_some, cell.enabled, hactualRate]
    · simp only [Option.map_some, hmissing]
      exact congrArg some (congrArg (Prod.mk _) (funext hstatus))
    · simp only [nextMarker, hn, Option.map_some]
      rw [cell.recordedArm_eq]
      unfold ReferenceFirstWindowNumericalStream.sourceArm
      rw [cell.selected.pending_eq]
      rfl

private theorem snapshot_code_injective (assignment : ActiveRoundActions.Assignment p.m p.K) :
    Function.Injective (fun snapshot : Option (ActiveRoundActions.Snapshot assignment) =>
      snapshot.map (fun s => (s.missing, fun i => some
        (FollowerDownMeasurability.followerStatusCode (s.status i))))) := by
  intro a b h
  cases a with
  | none => cases b with
    | none => rfl
    | some b => cases h
  | some a =>
    cases b with
    | none => cases h
    | some b =>
      have he := Option.some.inj h
      have hm := congrArg Prod.fst he
      have hs : a.status = b.status := by
        funext i
        have hi := Option.some.inj (congrFun (congrArg Prod.snd he) i)
        have hd := congrArg FollowerDownMeasurability.followerStatusOfCode hi
        simpa only [FollowerDownMeasurability.followerStatusOfCode_code] using hd
      cases a
      cases b
      cases hm
      cases hs
      rfl

/-- The current slice of each genuinely replaced source is exactly the
slice of its whole replacement control. All other coordinates are retained. -/
theorem next_slice_replaceControl (z : Z) (hq : t.val + 1 < p.T)
    (control : ContinuousLearningRows.TimeControl p) :
    ContinuousLearningRows.sliceAt
      (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalNextRecordingPriorView.withNextControl
          rate rewards C_star C_h u t z hq control) hq).input.time
      (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalNextRecordingPriorView.withNextControl
          rate rewards C_star C_h u t z hq control) hq).input.row.2 = control.1 := by
  have hf := ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord_fields
    rate rewards C_star C_h u t
      (ReferenceFirstCollectionRenewalNextRecordingPriorView.withNextControl
        rate rewards C_star C_h u t z hq control) hq
  simp only [ContinuousLearningRows.sliceAt, RoundInput.row, hf.1, hf.2.1, hf.2.2.1]
  simp only [
    ReferenceFirstCollectionRenewalNextRecordingPriorView.withNextControl,
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ActualInitializationPhysicalStep.selectedRowIndex,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
    Function.update_self]

/-- Fix the actual prior view, then apply the physical producer anew at every
whole-control replacement. Both arm and bottom fibers are identified exactly. -/
theorem nextMarker_control_kernel (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (hq : t.val + 1 < p.T) :
    match ReferenceFirstCollectionRenewalNextRecordingPriorView.nextRecordingView
      rate rewards C_star C_h u t z hq with
    | none => ∀ control, nextMarker rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalNextRecordingPriorView.withNextControl
          rate rewards C_star C_h u t z hq control) hq = none
    | some (parameters, view, _) =>
      ∃ (enabled : Bool)
        (snapshot : Option (ActiveRoundActions.Snapshot view.payload.assignment))
        (valid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff
          (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
            rate rewards C_star C_h u t z hq).input.time view.complementWeights),
        parameters = some (enabled, view.payload.rate) ∧
        ∀ control, nextMarker rate rewards C_star C_h u t
          (ReferenceFirstCollectionRenewalNextRecordingPriorView.withNextControl
            rate rewards C_star C_h u t z hq control) hq = some
          (SnapshotRecordingKernel.recordingMap p
            (snapshot.elim .collection (fun s => .live view.payload.assignment s)) enabled
            rate.eta.val rate.eta.property rate.sourceCap view.payload.anchor
            (ReferenceFirstWindowNumericalStream.sourceWeights view.payload view.complementWeights)
            view.payload.anchor_pos
            (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid) control.1) := by
  have hactual := nextMarker_physical_kernel rate rewards C_star C_h u t z hq
  cases hv : ReferenceFirstCollectionRenewalNextRecordingPriorView.nextRecordingView
      rate rewards C_star C_h u t z hq with
  | none =>
    intro control
    have h := nextMarker_physical_kernel rate rewards C_star C_h u t
      (ReferenceFirstCollectionRenewalNextRecordingPriorView.withNextControl
        rate rewards C_star C_h u t z hq control) hq
    rw [← ReferenceFirstCollectionRenewalNextRecordingPriorView.nextRecordingView_replaceControl
      rate rewards C_star C_h u t control0 z hq control, hv] at h
    exact h
  | some v =>
    rcases v with ⟨parameters, view, code⟩
    rw [hv] at hactual
    obtain ⟨enabled, snapshot, valid, hp, hs, _⟩ := hactual
    refine ⟨enabled, snapshot, valid, hp, ?_⟩
    intro control
    have h := nextMarker_physical_kernel rate rewards C_star C_h u t
      (ReferenceFirstCollectionRenewalNextRecordingPriorView.withNextControl
        rate rewards C_star C_h u t z hq control) hq
    rw [← ReferenceFirstCollectionRenewalNextRecordingPriorView.nextRecordingView_replaceControl
      rate rewards C_star C_h u t control0 z hq control, hv] at h
    obtain ⟨enabled', snapshot', valid', hp', hs', hy⟩ := h
    have he : enabled' = enabled := congrArg Prod.fst (Option.some.inj (hp'.symm.trans hp))
    have hsn : snapshot' = snapshot := snapshot_code_injective _ (hs'.symm.trans hs)
    subst enabled'
    subst snapshot'
    rw [next_slice_replaceControl] at hy
    exact hy

private theorem recording_control_mass
    (regime : SnapshotRecordingKernel.Regime p) (enabled : Bool)
    (anchor weights : Fin p.K → ℝ) (ha : ∀ j, 0 < anchor j)
    (hw : ∀ j, 0 < weights j) (hal : ∀ j, anchor j ≤ weights j)
    (hau : ∀ j, weights j ≤ 2 * anchor j) (o : Option (Option (Fin p.K))) :
    κ {c | some (SnapshotRecordingKernel.recordingMap p regime enabled
        rate.eta.val rate.eta.property rate.sourceCap anchor weights ha hw hal hau c.1) = o} =
      ENNReal.ofReal (coefficientOfParameters o
        (some (enabled, CanonicalRecordingRates.xi p rate.eta.val anchor))) := by
  let f := SnapshotRecordingKernel.recordingMap p regime enabled
    rate.eta.val rate.eta.property rate.sourceCap anchor weights ha hw hal hau
  have hf : Measurable f := SnapshotRecordingKernel.measurable_recordingMap
    p regime rate.eta.val rate.eta.property rate.sourceCap anchor weights ha hw hal hau enabled
  have hm (a : Option (Fin p.K)) : κ {c | f c.1 = a} =
      (ContinuousControlSlice.sliceLaw p.m p.K) {x | f x = a} := by
    rw [← ContinuousLearningRows.map_slice p,
      Measure.map_apply measurable_fst
        (show MeasurableSet {x | f x = a} from (measurableSet_singleton a).preimage hf)]
    rfl
  cases o with
  | none => simp only [reduceCtorEq, Set.ofPred_false, measure_empty,
      coefficientOfParameters, ENNReal.ofReal_zero]
  | some a =>
    simp only [Option.some.injEq]
    rw [show {c : ContinuousLearningRows.TimeControl p | _ = a} = {c | f c.1 = a} from rfl, hm]
    cases enabled with
    | false =>
      cases a <;> simp only [f, SnapshotRecordingKernel.recordingMap_disabled,
        coefficientOfParameters, Set.ofPred_true, measure_univ, ENNReal.ofReal_one,
        reduceCtorEq, Set.ofPred_false, measure_empty, ENNReal.ofReal_zero]
    | true =>
      cases a with
      | none =>
        exact SnapshotRecordingKernel.recordingMap_none_mass
          p regime rate.eta.val rate.eta.property rate.sourceCap anchor weights ha hw hal hau
      | some j =>
        exact SnapshotRecordingKernel.recordingMap_atom_mass
          p regime rate.eta.val rate.eta.property rate.sourceCap anchor weights ha hw hal hau j

private theorem recordingView_parameters (z : Z) (hq : t.val + 1 < p.T)
    (parameters : Option (Bool × (Fin p.K → ℝ)))
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (code : Option (Finset (Fin (p.m - 1)) × (Fin (p.m - 1) → Option (Fin 3))))
    (hv : ReferenceFirstCollectionRenewalNextRecordingPriorView.nextRecordingView
      rate rewards C_star C_h u t z hq = some (parameters, view, code)) :
    ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
      rate rewards C_star C_h u t z hq = parameters := by
  unfold ReferenceFirstCollectionRenewalNextRecordingPriorView.nextRecordingView at hv
  cases hh : ReferenceFirstCollectionRenewalNextRecordingPriorView.nextDownView
      rate rewards C_star C_h u t z hq with
  | none => simp only [hh, Option.map_none, reduceCtorEq] at hv
  | some v =>
    simp only [hh, Option.map_some, Option.some.injEq] at hv
    exact congrArg Prod.fst hv

/-- Complete pointwise whole-control law of the actual optional next marker.
No source mass, physical success, or ordinary-for-all-controls premise occurs. -/
theorem nextMarker_control_mass (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (hq : t.val + 1 < p.T) (o : Option (Option (Fin p.K))) :
    κ {control | nextMarker rate rewards C_star C_h u t
      (ReferenceFirstCollectionRenewalNextRecordingPriorView.withNextControl
        rate rewards C_star C_h u t z hq control) hq = o} =
      ENNReal.ofReal (nextCoefficient rate rewards C_star C_h u t o z hq) := by
  have hk := nextMarker_control_kernel rate rewards C_star C_h u t control0 z hq
  cases hv : ReferenceFirstCollectionRenewalNextRecordingPriorView.nextRecordingView
      rate rewards C_star C_h u t z hq with
  | none =>
    rw [hv] at hk
    have hp := ReferenceFirstCollectionRenewalNextRecordingPriorView.nextRecordingView_presence
      rate rewards C_star C_h u t z hq
    rw [hv] at hp
    have hn : ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
        rate rewards C_star C_h u t z hq = none := by
      cases hh : ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
          rate rewards C_star C_h u t z hq with
      | none => rfl
      | some c => rw [hh] at hp; cases hp
    simp only [hk, nextCoefficient,
      ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters, hn, Option.map_none]
    rcases o with _ | (_ | j) <;> simp only [coefficientOfParameters, Set.ofPred_true, measure_univ,
      ENNReal.ofReal_one, reduceCtorEq, Set.ofPred_false, measure_empty, ENNReal.ofReal_zero]
  | some v =>
    rcases v with ⟨parameters, view, code⟩
    rw [hv] at hk
    obtain ⟨enabled, snapshot, valid, hp, hy⟩ := hk
    have hpar := recordingView_parameters rate rewards C_star C_h u t z hq
      parameters view code hv
    have hcanonical : view.payload.rate = CanonicalRecordingRates.xi p rate.eta.val
        view.payload.anchor := funext view.payload.rate_eq_canonical
    simp only [hy, nextCoefficient, hpar, hp, hcanonical]
    exact recording_control_mass rate _ enabled _ _ view.payload.anchor_pos
      (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
      (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
      (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid) o

/-- Every actual present rate vector has the canonical total-mass bound.
The payload and canonical rates come from the actual numerical producer. -/
theorem nextParameters_bounds (z : Z) (hq : t.val + 1 < p.T)
    (enabled : Bool) (xi : Fin p.K → ℝ)
    (hp : ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
      rate rewards C_star C_h u t z hq = some (enabled, xi)) :
    (∀ j, 0 ≤ xi j) ∧ (∑ j, xi j) ≤ 1 := by
  have hcanonical := ReferenceFirstCollectionRenewalNextRecordingPriorView.nextCell_rate_canonical
    rate rewards C_star C_h u t z hq
  unfold ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters at hp
  cases hc : ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq with
  | none => simp only [hc, Option.map_none, reduceCtorEq] at hp
  | some cell =>
    simp only [hc, Option.map_some, Option.some.injEq] at hp
    rw [hc] at hcanonical
    obtain ⟨view, _, hr, _⟩ := hcanonical
    have hxi : cell.rate = xi := congrArg Prod.snd hp
    constructor
    · intro j
      rw [← hxi]
      exact (cell.rate_pos j).le
    · rw [← hxi, hr]
      have hrate : view.payload.rate = CanonicalRecordingRates.xi p rate.eta.val
          view.payload.anchor := funext view.payload.rate_eq_canonical
      rw [hrate]
      exact CanonicalRecordingRates.sum_xi_le_one p rate.eta.property rate.sourceCap
        view.payload.anchor view.payload.anchor_pos

/-- Every scalar test coefficient lies in the probability interval. -/
theorem nextCoefficient_bounds (o : Option (Option (Fin p.K))) (z : Z)
    (hq : t.val + 1 < p.T) :
    0 ≤ nextCoefficient rate rewards C_star C_h u t o z hq ∧
      nextCoefficient rate rewards C_star C_h u t o z hq ≤ 1 := by
  cases hp : ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
      rate rewards C_star C_h u t z hq with
  | none =>
    rcases o with _ | (_ | j) <;>
      simp only [nextCoefficient, hp, coefficientOfParameters, le_refl, zero_le_one, and_self]
  | some parameters =>
    rcases parameters with ⟨enabled, xi⟩
    obtain ⟨hpos, hsum⟩ := nextParameters_bounds rate rewards C_star C_h u t z hq enabled xi hp
    have hn : 0 ≤ ∑ j, xi j := Finset.sum_nonneg (fun j _ => hpos j)
    have hu (j : Fin p.K) : xi j ≤ 1 :=
      (Finset.single_le_sum (fun a _ => hpos a) (Finset.mem_univ j)).trans hsum
    rcases o with _ | (_ | j) <;> cases enabled <;>
      simp only [nextCoefficient, hp, coefficientOfParameters]
    all_goals first
      | exact ⟨zero_le_one, le_refl 1⟩
      | exact ⟨le_refl 0, zero_le_one⟩
      | exact ⟨sub_nonneg.mpr hsum, sub_le_self 1 hn⟩
      | exact ⟨hpos j, hu j⟩

/-- The coefficient formula is Borel on its literal optional parameter space. -/
theorem measurable_coefficientOfParameters (o : Option (Option (Fin p.K))) :
    Measurable (coefficientOfParameters (p := p) o) := by
  have hs : Measurable (fun v : Bool × (Fin p.K → ℝ) =>
      coefficientOfParameters o (some v)) := by
    apply measurable_from_prod_countable_right
    intro enabled
    rcases o with _ | (_ | j) <;> cases enabled
    all_goals first
      | exact measurable_const
      | exact measurable_pi_apply j
      | exact measurable_const.sub
          (Finset.measurable_fun_sum Finset.univ (fun j _ => measurable_pi_apply j))
  have hm : Measurable (Sum.elim
      (fun v : Bool × (Fin p.K → ℝ) => coefficientOfParameters o (some v))
      (fun _ : PUnit => coefficientOfParameters o none)) := hs.sumElim measurable_const
  have he : Measurable (Equiv.optionEquivSumPUnit (Bool × (Fin p.K → ℝ))) :=
    comap_measurable _
  convert hm.comp he using 1
  funext parameters
  cases parameters <;> rfl

/-- Predictability uses the admitted parameter factorization, at the next
prior field itself. -/
theorem measurable_nextCoefficient (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) (o : Option (Option (Fin p.K))) :
    Measurable[ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
      rate rewards C_star C_h u t control0]
      (fun z : Z => nextCoefficient rate rewards C_star C_h u t o z hq) :=
  (measurable_coefficientOfParameters o).comp
    (ReferenceFirstCollectionRenewalNextRecordingPriorView.measurable_nextParameters
      rate rewards C_star C_h u t control0 hq)

theorem nextCoefficient_factor (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (hq : t.val + 1 < p.T) (o : Option (Option (Fin p.K))) :
    nextCoefficient rate rewards C_star C_h u t o z hq =
      nextCoefficient rate rewards C_star C_h u t o
        (ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver
          rate rewards C_star C_h u t control0 z) hq := by
  unfold nextCoefficient
  rw [ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters_factor
    rate rewards C_star C_h u t control0 z hq]

private theorem integrable_of_measurable_norm_le_one {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (f : X → ℝ) (hf : Measurable f)
    (hb : ∀ x, ‖f x‖ ≤ 1) : Integrable f μ :=
  (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hb)

theorem measurable_nextTest (hq : t.val + 1 < p.T) (o : Option (Option (Fin p.K))) :
    Measurable (fun z : Z => nextTest rate rewards C_star C_h u t o z hq) := by
  exact (measurable_of_countable (fun a : Option (Option (Fin p.K)) =>
    if a = o then (1 : ℝ) else 0)).comp
      (measurable_nextMarker rate rewards C_star C_h u t hq)

theorem integrable_nextTest (hq : t.val + 1 < p.T) (o : Option (Option (Fin p.K))) :
    Integrable (fun z : Z => nextTest rate rewards C_star C_h u t o z hq) ν := by
  apply integrable_of_measurable_norm_le_one _
    (measurable_nextTest rate rewards C_star C_h u t hq o)
  intro z
  unfold nextTest
  split <;> norm_num

theorem integrable_nextCoefficient (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) (o : Option (Option (Fin p.K))) :
    Integrable (fun z : Z => nextCoefficient rate rewards C_star C_h u t o z hq) ν := by
  apply integrable_of_measurable_norm_le_one _
    ((measurable_nextCoefficient rate rewards C_star C_h u t control0 hq o).mono
      (ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
        rate rewards C_star C_h u t control0) le_rfl)
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (nextCoefficient_bounds rate rewards C_star C_h u t o z hq).1]
  exact (nextCoefficient_bounds rate rewards C_star C_h u t o z hq).2

/-- The real indicator integral of every replaced physical fiber is exactly
its scalar coefficient. The entire next control law is integrated. -/
theorem nextTest_control_integral (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (hq : t.val + 1 < p.T) (o : Option (Option (Fin p.K))) :
    (∫ control, nextTest rate rewards C_star C_h u t o
      (ReferenceFirstCollectionRenewalNextRecordingPriorView.withNextControl
        rate rewards C_star C_h u t z hq control) hq ∂κ) =
      nextCoefficient rate rewards C_star C_h u t o z hq := by
  have hpair : Measurable (fun control : ContinuousLearningRows.TimeControl p => (z, control)) :=
    measurable_const.prodMk measurable_id
  have hm := (measurable_nextMarker_joint rate rewards C_star C_h u t hq).comp hpair
  dsimp only [Function.comp_def] at hm
  let S := {control | nextMarker rate rewards C_star C_h u t
    (ReferenceFirstCollectionRenewalNextRecordingPriorView.withNextControl
      rate rewards C_star C_h u t z hq control) hq = o}
  have hs : MeasurableSet S := (measurableSet_singleton o).preimage hm
  have heq : (fun control => nextTest rate rewards C_star C_h u t o
      (ReferenceFirstCollectionRenewalNextRecordingPriorView.withNextControl
        rate rewards C_star C_h u t z hq control) hq) = S.indicator (fun _ => (1 : ℝ)) := by
    funext control
    simp only [nextTest, S, Set.indicator_apply, Set.mem_ofPred_eq]
  rw [heq]
  rw [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one, measureReal_def,
    nextMarker_control_mass rate rewards C_star C_h u t control0 z hq o,
    ENNReal.toReal_ofReal (nextCoefficient_bounds rate rewards C_star C_h u t o z hq).1]

/-- The literal Borel fiber test on the original source times whole control. -/
def nextMarkerTestSet (hq : t.val + 1 < p.T) (o : Option (Option (Fin p.K))) :
    Set (Z × ContinuousLearningRows.TimeControl p) :=
  {v | nextMarker rate rewards C_star C_h u t
    (ReferenceFirstCollectionRenewalNextRecordingPriorView.withNextControl
      rate rewards C_star C_h u t v.1 hq v.2) hq = o}

theorem measurableSet_nextMarkerTestSet (hq : t.val + 1 < p.T)
    (o : Option (Option (Fin p.K))) :
    MeasurableSet (nextMarkerTestSet rate rewards C_star C_h u t hq o) :=
  (measurableSet_singleton o).preimage
    (measurable_nextMarker_joint rate rewards C_star C_h u t hq)

private theorem nextControlTest_eq (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) (o : Option (Option (Fin p.K))) (z : Z) :
    ReferenceFirstCollectionRenewalNextControlLaw.nextControlTest
      rate rewards C_star C_h u t control0 hq
      (nextMarkerTestSet rate rewards C_star C_h u t hq o) z =
      nextTest rate rewards C_star C_h u t o z hq := by
  simp only [ReferenceFirstCollectionRenewalNextControlLaw.nextControlTest,
    nextMarkerTestSet, Set.indicator_apply, Set.mem_ofPred_eq,
    nextMarker_reconstruct, nextTest]

private theorem nextControlSectionIntegral_eq (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) (o : Option (Option (Fin p.K))) (z : Z) :
    ReferenceFirstCollectionRenewalNextControlLaw.nextControlSectionIntegral
      rate rewards C_star C_h u t (nextMarkerTestSet rate rewards C_star C_h u t hq o)
      (ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver
        rate rewards C_star C_h u t control0 z) =
      nextCoefficient rate rewards C_star C_h u t o z hq := by
  simp only [ReferenceFirstCollectionRenewalNextControlLaw.nextControlSectionIntegral,
    nextMarkerTestSet, Set.indicator_apply, Set.mem_ofPred_eq]
  change (∫ control, nextTest rate rewards C_star C_h u t o
    (ReferenceFirstCollectionRenewalNextRecordingPriorView.withNextControl
      rate rewards C_star C_h u t
      (ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver
        rate rewards C_star C_h u t control0 z) hq control) hq ∂κ) = _
  rw [nextTest_control_integral rate rewards C_star C_h u t control0,
    ← nextCoefficient_factor rate rewards C_star C_h u t control0 z hq o]

/-- The actual physical indicator has the stated integral on EVERY event of
the exact next-prior field, under the same finite unnormalized renewal law. -/
theorem nextMarker_test_setIntegral (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) (o : Option (Option (Fin p.K))) (G : Set Z)
    (hG : MeasurableSet[ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
      rate rewards C_star C_h u t control0] G) :
    (∫ z in G, nextTest rate rewards C_star C_h u t o z hq ∂ν) =
      ∫ z in G, nextCoefficient rate rewards C_star C_h u t o z hq ∂ν := by
  have h := ReferenceFirstCollectionRenewalNextControlLaw.nextControl_test_setIntegral
    rate rewards C_star C_h u t control0 hq
    (nextMarkerTestSet rate rewards C_star C_h u t hq o)
    (measurableSet_nextMarkerTestSet rate rewards C_star C_h u t hq o) G hG
  simpa only [nextControlTest_eq, nextControlSectionIntegral_eq] using h

/-- Complete conditional distribution of the actual optional next marker.
This reintegrates the whole control at the next date; it uses no earlier-field
tower, normalization, positive event mass, or no-failure assumption. -/
theorem nextMarker_condExp (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) (o : Option (Option (Fin p.K))) :
    (ν)[(fun z => nextTest rate rewards C_star C_h u t o z hq) |
      ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
        rate rewards C_star C_h u t control0] =ᵐ[ν]
      fun z => nextCoefficient rate rewards C_star C_h u t o z hq := by
  have hf := integrable_nextTest rate rewards C_star C_h u t hq o
  have hg := integrable_nextCoefficient rate rewards C_star C_h u t control0 hq o
  have hm := measurable_nextCoefficient rate rewards C_star C_h u t control0 hq o
  exact (ae_eq_condExp_of_forall_setIntegral_eq
    (ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
      rate rewards C_star C_h u t control0) hf
    (fun _ _ _ => hg.integrableOn)
    (fun G hG _ => (nextMarker_test_setIntegral
      rate rewards C_star C_h u t control0 hq o G hG).symm)
    hm.stronglyMeasurable.aestronglyMeasurable).symm

/-- Numerical presence agrees exactly with the actual parameter observation. -/
theorem nextMarker_none_iff (z : Z) (hq : t.val + 1 < p.T) :
    nextMarker rate rewards C_star C_h u t z hq = none ↔
      ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
        rate rewards C_star C_h u t z hq = none := by
  unfold nextMarker ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
  cases ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
    rate rewards C_star C_h u t z hq <;> simp only [Option.map_none, Option.map_some,
      reduceCtorEq]

/-- Exact actual tag cases: initializer/local failures and dagger are absent;
chosen branches are present, including disabled cutoff. The clock-failure
constructor is excluded by the admitted actual-run clock result. -/
theorem nextMarker_tag_cases (z : Z) (hq : t.val + 1 < p.T) :
    match ReferenceFirstCollectionRenewalNextRecordingPriorView.nextTag
      rate rewards C_star C_h u t z hq with
    | some (.inl _) => False
    | some (.inr (.inr (.inr _))) =>
      (nextMarker rate rewards C_star C_h u t z hq).isSome = true
    | _ => nextMarker rate rewards C_star C_h u t z hq = none := by
  have hc := ReferenceFirstCollectionRenewalNextRecordingPriorView.nextTag_no_clockFailure
    rate rewards C_star C_h u t z hq
  have hr := ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextDate_readouts
    rate rewards C_star C_h u t z hq
  rw [ReferenceFirstCollectionRenewalNextRecordingPriorView.nextTag_eq] at hc ⊢
  dsimp only at hr
  cases hd : (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
      rate rewards C_star C_h u t z hq).output.preparation.coordinator
    <;> simp only [hd] at hc hr ⊢
  all_goals try
    obtain ⟨hL, _, hC, _⟩ := hr
    simp only [nextMarker, ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell,
      hL, hC, Option.none_or, Option.map_none]
  rename_i registers owned base out
  cases out <;> simp only [ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm,
    ReferenceLiveDispatchOutputMeasurability.outcomeData] at hc hr ⊢
  case initializerFailure =>
    obtain ⟨hL, _, hC, _⟩ := hr
    simp only [nextMarker, ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell,
      hL, hC, Option.none_or, Option.map_none]
  case localFailure =>
    obtain ⟨hL, _, hC, _⟩ := hr
    simp only [nextMarker, ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell,
      hL, hC, Option.none_or, Option.map_none]
  case cutoffChosen =>
    obtain ⟨c, hC, _, hL, _⟩ := hr
    simp only [nextMarker, ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell,
      hL, hC, Option.none_or, Option.map_some, Option.isSome_some]
  case continuingChosen =>
    obtain ⟨c, hL, _, hC, _⟩ := hr
    simp only [nextMarker, ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell,
      hL, Option.some_or, Option.map_some, Option.isSome_some]

/-- A present arm marker is tied to an actual physical owner action and that
owner's actual grid reward observation, including when the reward is zero. -/
theorem nextMarker_owner_observation (z : Z) (hq : t.val + 1 < p.T) (a : Fin p.K) :
    nextMarker rate rewards C_star C_h u t z hq = some (some a) →
      ∃ owner : Fin p.m,
        (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
          rate rewards C_star C_h u t z hq).actions owner = a ∧
        (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
          rate rewards C_star C_h u t z hq).gridFeedback owner = rewards ⟨t.val + 1, hq⟩ a ∧
        (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
          rate rewards C_star C_h u t z hq).ownEntries owner =
            (a, ActualInitializationPhysicalStep.observationOfGrid p (rewards ⟨t.val + 1, hq⟩ a)) := by
  intro hmarker
  have hr := ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextDate_readouts
    rate rewards C_star C_h u t z hq
  have hl := ReferenceFirstCollectionRenewalNextPhysicalPrefix.next_continuing_physical
    rate rewards C_star C_h u t z hq
  have hc := ReferenceFirstCollectionRenewalNextPhysicalPrefix.next_cutoff_physical
    rate rewards C_star C_h u t z hq
  have hf := ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord_fields
    rate rewards C_star C_h u t z hq
  have finish (owner : Fin p.m)
      (ha : (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
        rate rewards C_star C_h u t z hq).actions owner = a)
      (hy : (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
        rate rewards C_star C_h u t z hq).gridFeedback owner = rewards ⟨t.val + 1, hq⟩ a) :
      (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
        rate rewards C_star C_h u t z hq).ownEntries owner =
          (a, ActualInitializationPhysicalStep.observationOfGrid p (rewards ⟨t.val + 1, hq⟩ a)) := by
    rw [ReferenceActivePhysicalHorizon.RoundRecord.ownEntries_formula,
      ← ReferenceActivePhysicalHorizon.RoundRecord.gridFeedback_formula, ha, hy]
  dsimp only at hr hl hc
  cases hd : (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
      rate rewards C_star C_h u t z hq).output.preparation.coordinator
    <;> simp only [hd] at hr hl hc
  all_goals try
    obtain ⟨hL, _, hC, _⟩ := hr
    simp only [nextMarker, ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell,
      hL, hC, Option.none_or, Option.map_none, reduceCtorEq] at hmarker
  rename_i registers owned base out
  cases out <;> simp only at hr hl hc
  all_goals try
    obtain ⟨hL, _, hC, _⟩ := hr
    simp only [nextMarker, ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell,
      hL, hC, Option.none_or, Option.map_none, reduceCtorEq] at hmarker
  · obtain ⟨c, payload, ledger, started, weights, recording, hC, hL, _hcall,
      _henabled, _hrate, _hreward, _hrun, _hdiag, _hgate, _harrivals, _hunique, howners⟩ := hc
    have ha : c.recordedArm = some a := by
      simpa only [nextMarker, ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell,
        hL, hC, Option.none_or, Option.map_some, Option.some.injEq] using hmarker
    obtain ⟨valid, _hslot, _hsource, _hfreeze, _howns, haction, _hmask, _hthin,
      hfeedback, _harrival⟩ := howners a ha
    rw [hf.1] at hfeedback
    exact ⟨ActiveRoundActions.coordinator p.two_le_m, haction, hfeedback,
      finish _ haction hfeedback⟩
  · obtain ⟨cell, hL, _hC, _henabled, _hreward, _hrate, _hphysical, howners, _⟩ := hl
    have ha : cell.input.recordedArm = some a := by
      simpa only [nextMarker, ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell,
        hL, Option.some_or, Option.map_some, Option.some.injEq] using hmarker
    obtain ⟨owner, _howns, _hunique, haction, hfeedback, _hobs⟩ := howners a ha
    rw [hf.1] at hfeedback
    exact ⟨owner, haction, hfeedback, finish owner haction hfeedback⟩

end Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingLaw

end
