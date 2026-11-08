/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalFutureFirstReplacementView
public import Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Optional recording law on the future first-replacement slice

This module composes the actual first-replacement physical recording section
with whole-control freshness on the same original renewal source. The marker
keeps outer absence distinct from a present bottom record.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open scoped Classical MeasureTheory

namespace Bandits.Support.ReferenceFirstCollectionRenewalFutureRecordingLaw

open ReferenceFirstCollectionRenewalFutureFirstReplacementView
open ReferenceFirstCollectionRenewalFutureControlLaw
open ReferenceFirstCollectionRenewalNextRecordingLaw
open ReferenceFirstCollectionRenewalAuxiliaryLaw
open ReferenceFirstCollectionRenewalSourceCurrentPrefix
open ReferenceCompleteFirstPhaseObservationRecovery
open ReferenceCompleteNumericalBranchObservation
open ReferenceFirstCollectionRenewalIncomingQueuePrefix
open ReferenceFirstCollectionRenewalNextControlLaw
open ReferenceFirstCollectionRenewalNextRecordingPriorView
open ReferenceActiveHorizonMeasurability
open ReferenceSourcePrefixHistoryFiltration

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

local notation "Z" => ReferenceFirstCollectionRenewalFutureControlLaw.Source
  rate rewards C_star C_h u t
local notation "ν" => renewalSourceLaw rate rewards C_star C_h u t
local notation "κ" => ContinuousLearningRows.timeControlLaw p

private theorem measurable_option_bind {X A B : Type*}
    (mX : MeasurableSpace X) [MeasurableSpace A] [MeasurableSpace B]
    (g : X → Option A) (hg : @Measurable X (Option A) mX inferInstance g)
    (f : A → Option B) (hf : Measurable f) :
    @Measurable X (Option B) mX inferInstance (fun x => (g x).bind f) := by
  let eA := Equiv.optionEquivSumPUnit A
  let eB := Equiv.optionEquivSumPUnit B
  have hg' : @Measurable X (Sum A PUnit) mX inferInstance (fun x => eA (g x)) :=
    (comap_measurable eA).comp hg
  have hf' : Measurable (fun a => eB (f a)) :=
    (comap_measurable eB).comp hf
  have hs : Measurable (Sum.elim (fun a => eB (f a))
      (fun _ : PUnit => Sum.inr PUnit.unit)) := hf'.sumElim measurable_const
  have heq : (fun x => eB ((g x).bind f)) =
      fun x => Sum.elim (fun a => eB (f a))
        (fun _ : PUnit => Sum.inr PUnit.unit) (eA (g x)) := by
    funext x
    cases g x <;> rfl
  have hsum : @Measurable X (Sum B PUnit) mX inferInstance
      (fun x => eB ((g x).bind f)) := by
    rw [heq]
    exact hs.comp hg'
  exact (measurable_comap_iff (mα := mX)
    (mγ := (inferInstance : MeasurableSpace (Sum B PUnit)))
    (f := fun x => (g x).bind f) (g := eB)).mpr hsum

/-- The literal optional parameter projection of the accepted future view. -/
def futureParameters (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Option (Bool × (Fin p.K → ℝ)) :=
  (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
    rate rewards C_star C_h u t z q hfuture).bind fun view => view.1

/-- The source-derived coefficient of one literal optional marker fiber. -/
def futureCoefficient (o : Option (Option (Fin p.K))) (z : Z)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) : ℝ :=
  ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters o
    (futureParameters rate rewards C_star C_h u t z q hfuture)

/-- The real indicator of the actual optional future marker fiber. -/
def futureTest (o : Option (Option (Fin p.K))) (z : Z)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) : ℝ :=
  if ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker
      rate rewards C_star C_h u t z q hfuture = o then 1 else 0

/-- Literal Borel marker fiber on the original source and whole future control. -/
def futureMarkerTestSet (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) : Set (Z × ContinuousLearningRows.TimeControl p) :=
  {v | ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker
    rate rewards C_star C_h u t
      (ReferenceFirstCollectionRenewalFutureFirstReplacementView.withFutureControl
        rate rewards C_star C_h u t v.1 q hfuture v.2) q hfuture = o}

/-- The two APIs name the same original-source strict-prefix field. -/
theorem futurePriorField_eq_priorField (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) :
    ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q =
    ReferenceFirstCollectionRenewalFutureFirstReplacementView.priorField
      rate rewards C_star C_h u t control0 q.val := rfl

/-- Their observers agree by the two literal source-prefix value equations. -/
theorem futurePriorObserver_eq_priorObserver
    (control0 : ContinuousLearningRows.TimeControl p) (z : Z)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorObserver
        rate rewards C_star C_h u t control0 q (by omega) z =
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.priorObserver
        rate rewards C_star C_h u t control0 z q hfuture := by
  apply Subtype.ext
  rw [ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorObserver_val,
    ReferenceFirstCollectionRenewalFutureFirstReplacementView.priorObserver_val]

/-- The parameters are exactly measurable in the future prefix field. -/
theorem measurable_futureParameters
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q]
      (fun z : Z => futureParameters rate rewards C_star C_h u t z q hfuture) := by
  rw [futurePriorField_eq_priorField rate rewards C_star C_h u t control0 q]
  have hview := ReferenceFirstCollectionRenewalFutureFirstReplacementView.measurable_futureRecordingView
    rate rewards C_star C_h u t control0 q hfuture
  have hparams : Measurable (fun view : ViewData rate => view.1) := measurable_fst
  exact measurable_option_bind
    (ReferenceFirstCollectionRenewalFutureFirstReplacementView.priorField
      rate rewards C_star C_h u t control0 q.val)
    _ hview _ hparams

/-- The parameter projection factors through the actual prior observer. -/
theorem futureParameters_factor
    (control0 : ContinuousLearningRows.TimeControl p) (z : Z)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    futureParameters rate rewards C_star C_h u t z q hfuture =
      futureParameters rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalFutureFirstReplacementView.priorObserver
          rate rewards C_star C_h u t control0 z q hfuture) q hfuture := by
  simp only [futureParameters]
  rw [ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_view_factor]

/-- The coefficient is measurable in precisely the accepted future field. -/
theorem measurable_futureCoefficient
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) :
    Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q]
      (fun z : Z => futureCoefficient rate rewards C_star C_h u t o z q hfuture) :=
  (ReferenceFirstCollectionRenewalNextRecordingLaw.measurable_coefficientOfParameters
    (p := p) o).comp
      (measurable_futureParameters rate rewards C_star C_h u t control0 q hfuture)

/-- The coefficient has the same observer factorization as its parameters. -/
theorem futureCoefficient_factor
    (control0 : ContinuousLearningRows.TimeControl p) (z : Z)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) :
    futureCoefficient rate rewards C_star C_h u t o z q hfuture =
      futureCoefficient rate rewards C_star C_h u t o
        (ReferenceFirstCollectionRenewalFutureFirstReplacementView.priorObserver
          rate rewards C_star C_h u t control0 z q hfuture) q hfuture := by
  simp only [futureCoefficient]
  rw [futureParameters_factor rate rewards C_star C_h u t control0 z q hfuture]

private theorem measurable_variable_observation {X B : Type*}
    [MeasurableSpace X] [MeasurableSpace B]
    (f : X → List B) (hf : Measurable f) (j : X → ℕ) (hj : Measurable j) :
    Measurable (fun x => listObservationAt (f x) (j x)) := by
  have ho := measurable_snd.comp (measurable_listObservationCoordinates.comp hf)
  have he : Measurable (fun v : (ℕ → Unit ⊕ B) × ℕ => v.1 v.2) :=
    measurable_from_prod_countable_left (fun n => measurable_pi_apply n)
  exact he.comp (ho.prodMk hj)

private theorem measurable_marker_readout {X : Type*} [MeasurableSpace X]
    (f : X → List (Fin p.T × Option (NumericalCoordinates p))) (hf : Measurable f)
    (j : X → ℕ) (hj : Measurable j)
    (cells : X → Option (RecordedQueueRun.RoundInput p.K))
    (q : Fin p.T)
    (h : ∀ x, (f x)[j x]? = some
      (q, (cells x).map ReferenceCompleteNumericalBranchObservation.encodeNumerical)) :
    Measurable (fun x => (cells x).map (fun c => c.recordedArm)) := by
  let read : Unit ⊕ (Fin p.T × Option (NumericalCoordinates p)) →
      Option (Option (Fin p.K)) :=
    Sum.elim (fun _ => none) (fun e => e.2.map (fun c => c.2.1))
  have hcode : Measurable (fun e : Fin p.T × Option (NumericalCoordinates p) =>
      Equiv.optionEquivSumPUnit (NumericalCoordinates p) e.2) :=
    (comap_measurable _).comp measurable_snd
  have hread : Measurable (fun e : NumericalCoordinates p ⊕ PUnit =>
      Sum.elim (fun c : NumericalCoordinates p => some c.2.1) (fun _ => none) e) :=
    ((measurable_of_countable (fun a : Option (Fin p.K) => some a)).comp
      (measurable_fst.comp measurable_snd)).sumElim measurable_const
  have hm : Measurable (fun e : Fin p.T × Option (NumericalCoordinates p) =>
      e.2.map (fun c => c.2.1)) := by
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

/-- The actual optional marker is Borel on the original source, without a
success or presence premise. The decoder reads the original complete suffix. -/
theorem measurable_futureMarker
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Measurable (fun z : Z =>
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker
        rate rewards C_star C_h u t z q hfuture) := by
  let obs := fun z : Z => completeObservation rate rewards C_star C_h u t z
  have hobs : Measurable obs := by
    exact (measurable_completeBranchObservation rate rewards C_star C_h).comp
      measurable_subtype_coe
  have hs : Measurable (fun z : Z => start rate rewards C_star C_h u t z) :=
    (ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
      rate rewards C_star C_h).comp measurable_subtype_coe
  have hj : Measurable (fun z : Z => q.val - start rate rewards C_star C_h u t z) :=
    (measurable_of_countable (fun s : ℕ => q.val - s)).comp hs
  have hlive := measurable_marker_readout
    (fun z : Z => rawLiveNumericalDecoder rate (obs z))
    ((measurable_rawLiveNumericalDecoder rate).comp hobs) _ hj
    (fun z => ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
      (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
        rate rewards C_star C_h u t z q hfuture)) q
    (by
      intro z
      unfold obs
      unfold ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation
      rw [rawLiveNumericalDecoder_completeSuffixRecords, List.getElem?_map]
      have hr := ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord_lookup
        rate rewards C_star C_h u t z q hfuture
      dsimp only [ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords] at hr
      rw [hr]
      change some ((ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
          rate rewards C_star C_h u t z q hfuture).input.time,
        (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
          (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
            rate rewards C_star C_h u t z q hfuture)).map
          ReferenceCompleteNumericalBranchObservation.encodeNumerical) = _
      rw [(ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord_fields
        rate rewards C_star C_h u t z q hfuture).1])
  have hcollection := measurable_marker_readout
    (fun z : Z => rawCollectionNumericalDecoder rate (obs z))
    ((measurable_rawCollectionNumericalDecoder rate).comp hobs) _ hj
    (fun z => ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
      (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
        rate rewards C_star C_h u t z q hfuture)) q
    (by
      intro z
      unfold obs
      unfold ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation
      rw [rawCollectionNumericalDecoder_completeSuffixRecords, List.getElem?_map]
      have hr := ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord_lookup
        rate rewards C_star C_h u t z q hfuture
      dsimp only [ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords] at hr
      rw [hr]
      change some ((ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
          rate rewards C_star C_h u t z q hfuture).input.time,
        (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
          (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
            rate rewards C_star C_h u t z q hfuture)).map
          ReferenceCompleteNumericalBranchObservation.encodeNumerical) = _
      rw [(ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord_fields
        rate rewards C_star C_h u t z q hfuture).1])
  have hle : ReferenceFirstCollectionRenewalFutureFirstReplacementView.priorField
      rate rewards C_star C_h u t control0 q.val ≤ (inferInstance : MeasurableSpace Z) :=
    MeasurableSpace.comap_mono ((sourcePrefixFiltration control0).le' (q.val + 1))
  have hp := (ReferenceFirstCollectionRenewalFutureFirstReplacementView.measurable_priorSlice
    rate rewards C_star C_h u t control0 q).mono hle le_rfl
  have ht : Measurable (fun z : Z =>
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureTag
        rate rewards C_star C_h u t z q hfuture) :=
    (ReferenceFirstCollectionRenewalNextRecordingPriorView.measurable_dispatchTag.comp
      (ReferenceFirstCollectionRenewalFutureFirstReplacementView.measurable_futureInput
        rate rewards C_star C_h u t q hfuture))
  have hcode : Measurable (fun v : Bool ×
      Option (ReferenceFirstCollectionRenewalNextRecordingPriorView.LiveTag p) =>
      if v.1 then match v.2 with
        | some (.inr (.inr (.inr (_, cutoff)))) => some cutoff
        | _ => none
      else none) := measurable_of_countable _
  have hbranch : Measurable (fun z : Z =>
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch
        rate rewards C_star C_h u t z q hfuture) := by
    convert hcode.comp (hp.prodMk ht) using 1
    funext z
    simp only [ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch,
      Function.comp_def,
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.priorSlice_eq
        rate rewards C_star C_h u t z q hfuture,
      Bool.decide_iff]
    rfl
  have hm := (measurable_of_countable
      (fun v : Option Bool ×
        (Option (Option (Fin p.K)) × Option (Option (Fin p.K))) =>
        v.1.elim none (fun _ => v.2.1.or v.2.2))).comp
      (hbranch.prodMk (hlive.prodMk hcollection))
  have hformula : (fun z : Z =>
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker
        rate rewards C_star C_h u t z q hfuture) =
      fun z => (ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch
        rate rewards C_star C_h u t z q hfuture).elim none (fun _ =>
          ((ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
            (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
              rate rewards C_star C_h u t z q hfuture)).map (fun c => c.recordedArm)).or
          ((ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
            (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
              rate rewards C_star C_h u t z q hfuture)).map (fun c => c.recordedArm))) := by
    funext z
    cases hb : ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch
        rate rewards C_star C_h u t z q hfuture <;>
      simp [ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker,
        ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell, hb,
        Option.map_or]
  rw [hformula]
  exact hm

/-- The joint actual marker is Borel while retaining every whole-control
coordinate, including all K+1 assignment coordinates. -/
theorem measurable_futureMarker_joint
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Measurable (fun v : Z × ContinuousLearningRows.TimeControl p =>
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker
        rate rewards C_star C_h u t
          (ReferenceFirstCollectionRenewalFutureFirstReplacementView.withFutureControl
            rate rewards C_star C_h u t v.1 q hfuture v.2) q hfuture) := by
  have hreplace : Measurable (fun v : Z × ContinuousLearningRows.TimeControl p =>
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q v.1.val v.2) :=
    (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p q).comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  have hsource : Measurable (fun v : Z × ContinuousLearningRows.TimeControl p =>
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.withFutureControl
        rate rewards C_star C_h u t v.1 q hfuture v.2) := by
    have hlift : Measurable (fun v : Z × ContinuousLearningRows.TimeControl p =>
        (⟨ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q v.1.val v.2,
          (ReferenceFirstCollectionRenewalFutureControlLaw.renewalCallEvent_iff_replaceFutureControl
            rate rewards C_star C_h u t q (by omega) v.1.val v.2).mp v.1.property⟩ : Z)) :=
      hreplace.subtype_mk
    have heq : (fun v : Z × ContinuousLearningRows.TimeControl p =>
        ReferenceFirstCollectionRenewalFutureFirstReplacementView.withFutureControl
          rate rewards C_star C_h u t v.1 q hfuture v.2) =
        (fun v => (⟨ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q v.1.val v.2,
          (ReferenceFirstCollectionRenewalFutureControlLaw.renewalCallEvent_iff_replaceFutureControl
            rate rewards C_star C_h u t q (by omega) v.1.val v.2).mp v.1.property⟩ : Z)) := by
      funext v
      apply Subtype.ext
      exact ReferenceFirstCollectionRenewalFutureFirstReplacementView.withFutureControl_val
        rate rewards C_star C_h u t v.1 q hfuture v.2
    rw [heq]
    exact hlift
  exact (measurable_futureMarker rate rewards C_star C_h u t control0 q hfuture).comp hsource

/-- Every literal marker fiber in the whole-control product is Borel. -/
theorem measurableSet_futureMarkerTestSet
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) :
    MeasurableSet (futureMarkerTestSet rate rewards C_star C_h u t q hfuture o) :=
  (measurableSet_singleton o).preimage
    (measurable_futureMarker_joint rate rewards C_star C_h u t control0 q hfuture)

/-- Actual marker absence is exactly outer absence of the physical slice view;
present bottom remains `some none`. -/
theorem futureMarker_outer_absence_iff
    (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker
        rate rewards C_star C_h u t z q hfuture = none ↔
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
        rate rewards C_star C_h u t z q hfuture = none := by
  cases hv : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture with
  | none =>
      have hread := ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_readout
        rate rewards C_star C_h u t z q hfuture
      rw [hv] at hread
      obtain ⟨_, hcell⟩ := hread
      simp [ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker, hcell]
  | some v =>
      obtain ⟨parameters, view, code⟩ := v
      have hread := ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_readout
        rate rewards C_star C_h u t z q hfuture
      rw [hv] at hread
      obtain ⟨cell, _, _, hcell, _, _, _, _, _⟩ := hread
      simp [ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker, hcell]

/-- The coefficient cases distinguish outer absence, a disabled present cell,
and the enabled arm and bottom fibers. -/
theorem futureCoefficient_cases
    (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    (futureParameters rate rewards C_star C_h u t z q hfuture = none ∧
      futureCoefficient rate rewards C_star C_h u t none z q hfuture = 1 ∧
      futureCoefficient rate rewards C_star C_h u t (some none) z q hfuture = 0 ∧
      ∀ a, futureCoefficient rate rewards C_star C_h u t (some (some a)) z q hfuture = 0) ∨
    (∃ xi, futureParameters rate rewards C_star C_h u t z q hfuture = some (false, xi) ∧
      futureCoefficient rate rewards C_star C_h u t none z q hfuture = 0 ∧
      futureCoefficient rate rewards C_star C_h u t (some none) z q hfuture = 1 ∧
      ∀ a, futureCoefficient rate rewards C_star C_h u t (some (some a)) z q hfuture = 0) ∨
    (∃ xi, futureParameters rate rewards C_star C_h u t z q hfuture = some (true, xi) ∧
      futureCoefficient rate rewards C_star C_h u t none z q hfuture = 0 ∧
      futureCoefficient rate rewards C_star C_h u t (some none) z q hfuture =
        1 - ∑ a, xi a ∧
      ∀ a, futureCoefficient rate rewards C_star C_h u t (some (some a)) z q hfuture = xi a) := by
  cases hv : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture with
  | none =>
      left
      simp [futureParameters, futureCoefficient, hv,
        ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
  | some v =>
      rcases v with ⟨parameters, view, code⟩
      have hread := ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_readout
        rate rewards C_star C_h u t z q hfuture
      rw [hv] at hread
      obtain ⟨cell, snapshot, valid, hcell, hparameters, hrate, _, _, _⟩ := hread
      have hparams : futureParameters rate rewards C_star C_h u t z q hfuture =
          some (cell.enabled, cell.rate) := by
        simp [futureParameters, hv, hparameters]
      cases henabled : cell.enabled with
      | false =>
          right
          left
          refine ⟨cell.rate, ?_, ?_, ?_, ?_⟩
          · simpa [henabled] using hparams
          · simp [futureCoefficient, hparams,
              henabled,
              ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
          · simp [futureCoefficient, hparams,
              henabled,
              ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
          · intro a
            simp [futureCoefficient, hparams,
              henabled,
              ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
      | true =>
          right
          right
          refine ⟨cell.rate, ?_, ?_, ?_, ?_⟩
          · simpa [henabled] using hparams
          · simp [futureCoefficient, hparams,
              henabled,
              ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
          · simp [futureCoefficient, hparams,
              henabled,
              ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
          · simp [futureCoefficient, hparams,
              henabled,
              ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]

/-- The actual payload's canonical rates bound every future coefficient. -/
theorem futureCoefficient_bounds
    (o : Option (Option (Fin p.K))) (z : Z)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    0 ≤ futureCoefficient rate rewards C_star C_h u t o z q hfuture ∧
      futureCoefficient rate rewards C_star C_h u t o z q hfuture ≤ 1 := by
  cases hv : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture with
  | none =>
      simp only [futureCoefficient, futureParameters, hv,
        ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
      rcases o with _ | (_ | a) <;> simp
  | some v =>
      rcases v with ⟨parameters, view, code⟩
      have hread := ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_readout
        rate rewards C_star C_h u t z q hfuture
      rw [hv] at hread
      obtain ⟨cell, snapshot, valid, hcell, hparameters, hrate, _, _, _⟩ := hread
      have hcanonical : view.payload.rate =
          CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor := by
        funext a
        exact view.payload.rate_eq_canonical a
      have hparams : futureParameters rate rewards C_star C_h u t z q hfuture =
          some (cell.enabled, CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor) := by
        simp [futureParameters, hv, hparameters, hrate, hcanonical]
      have hpos : ∀ a : Fin p.K,
          0 < CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor a :=
        fun a => CanonicalRecordingRates.xi_pos p rate.eta.property
          view.payload.anchor a
      have hsum : (∑ a : Fin p.K,
          CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor a) ≤ 1 :=
        CanonicalRecordingRates.sum_xi_le_one p rate.eta.property rate.sourceCap
          view.payload.anchor view.payload.anchor_pos
      have hsum_nonneg : 0 ≤ ∑ a : Fin p.K,
          CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor a :=
        Finset.sum_nonneg (fun a _ => (hpos a).le)
      have hxi_le (a : Fin p.K) :
          CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor a ≤ 1 := by
        exact (Finset.single_le_sum (fun j _ => (hpos j).le)
          (Finset.mem_univ a)).trans hsum
      simp only [futureCoefficient, hparams,
        ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
      cases o with
      | none => exact ⟨le_refl 0, zero_le_one⟩
      | some marker =>
          cases marker with
          | none =>
              cases e : cell.enabled with
              | false => exact ⟨zero_le_one, le_refl 1⟩
              | true => exact ⟨sub_nonneg.mpr hsum, sub_le_self 1 hsum_nonneg⟩
          | some a =>
              cases e : cell.enabled with
              | false => exact ⟨le_refl 0, zero_le_one⟩
              | true => exact ⟨(hpos a).le, hxi_le a⟩

private theorem integrable_of_measurable_norm_le_one
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (hb : ∀ x, ‖f x‖ ≤ 1) : Integrable f μ :=
  (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)

/-- The actual real marker indicator is integrable even when the original
renewal restriction has zero mass. -/
theorem integrable_futureTest
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) :
    Integrable (fun z : Z => futureTest rate rewards C_star C_h u t o z q hfuture) ν := by
  apply integrable_of_measurable_norm_le_one _
  · simpa only [futureTest, Function.comp_def] using
      ((measurable_of_countable (fun a : Option (Option (Fin p.K)) =>
        if a = o then (1 : ℝ) else 0)).comp
        (measurable_futureMarker rate rewards C_star C_h u t control0 q hfuture))
  · intro z
    simp only [futureTest]
    split <;> norm_num

/-- The future coefficient is integrable under the same finite, possibly zero
renewal-source measure. -/
theorem integrable_futureCoefficient
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) :
    Integrable (fun z : Z => futureCoefficient rate rewards C_star C_h u t o z q hfuture) ν := by
  have hle : ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q ≤ (inferInstance : MeasurableSpace Z) :=
    ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
      rate rewards C_star C_h u t control0 q (by omega)
  apply integrable_of_measurable_norm_le_one _
    ((measurable_futureCoefficient rate rewards C_star C_h u t control0 q hfuture o).mono
      hle le_rfl)
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (futureCoefficient_bounds rate rewards C_star C_h u t o z q hfuture).1]
  exact (futureCoefficient_bounds rate rewards C_star C_h u t o z q hfuture).2

/-- The actual disabled cutoff endpoint has a present cell with bottom marker. -/
theorem futureMarker_disabled
    (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (parameters : Option (Bool × (Fin p.K → ℝ)))
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (hview : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture = some (parameters, view, none))
    (hdisabled : parameters = some (false, view.payload.rate)) :
    ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker
      rate rewards C_star C_h u t z q hfuture = some none :=
  ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker_disabled
    rate rewards C_star C_h u t z q hfuture parameters view hview hdisabled

/-- Snapshot codes retain the full finite live snapshot, including each
unoccupied/pending/released status. -/
private theorem snapshot_code_injective
    (assignment : ActiveRoundActions.Assignment p.m p.K) :
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

/-- SnapshotRecordingKernel's existing mass law integrates the complete
time-control measure through its original slice projection. -/
private theorem snapshotRecording_control_mass
    (regime : SnapshotRecordingKernel.Regime p) (enabled : Bool)
    (anchor weights : Fin p.K → ℝ) (ha : ∀ j, 0 < anchor j)
    (hw : ∀ j, 0 < weights j) (hal : ∀ j, anchor j ≤ weights j)
    (hau : ∀ j, weights j ≤ 2 * anchor j)
    (o : Option (Option (Fin p.K))) :
    κ {control | some (SnapshotRecordingKernel.recordingMap p regime enabled
        rate.eta.val rate.eta.property rate.sourceCap anchor weights ha hw hal hau
        control.1) = o} =
      ENNReal.ofReal (ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters o
        (some (enabled, CanonicalRecordingRates.xi p rate.eta.val anchor))) := by
  let f := SnapshotRecordingKernel.recordingMap p regime enabled
    rate.eta.val rate.eta.property rate.sourceCap anchor weights ha hw hal hau
  have hf : Measurable f := SnapshotRecordingKernel.measurable_recordingMap
    p regime rate.eta.val rate.eta.property rate.sourceCap anchor weights ha hw hal hau enabled
  have hm (a : Option (Fin p.K)) : κ {control | f control.1 = a} =
      (ContinuousControlSlice.sliceLaw p.m p.K) {x | f x = a} := by
    rw [← ContinuousLearningRows.map_slice p,
      Measure.map_apply measurable_fst
        (show MeasurableSet {x | f x = a} from
          (measurableSet_singleton a).preimage hf)]
    rfl
  cases o with
  | none =>
      simp only [reduceCtorEq, Set.ofPred_false, measure_empty,
        ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters,
        ENNReal.ofReal_zero]
  | some a =>
      simp only [Option.some.injEq]
      rw [show {control : ContinuousLearningRows.TimeControl p | _ = a} =
        {control | f control.1 = a} from rfl, hm]
      cases enabled with
      | false =>
          cases a <;> simp only [f, SnapshotRecordingKernel.recordingMap_disabled,
            ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters,
            Set.ofPred_true, measure_univ, ENNReal.ofReal_one,
            reduceCtorEq, Set.ofPred_false, measure_empty,
            ENNReal.ofReal_zero]
      | true =>
          cases a with
          | none =>
              exact SnapshotRecordingKernel.recordingMap_none_mass
                p regime rate.eta.val rate.eta.property rate.sourceCap
                anchor weights ha hw hal hau
          | some j =>
              exact SnapshotRecordingKernel.recordingMap_atom_mass
                p regime rate.eta.val rate.eta.property rate.sourceCap
                anchor weights ha hw hal hau j

/-- Reconstruct the actual marker from the prior observer and its whole
current control, using the original prefix and physical section. -/
theorem futureMarker_reconstruct
    (control0 : ContinuousLearningRows.TimeControl p) (z : Z)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker
        rate rewards C_star C_h u t
          (ReferenceFirstCollectionRenewalFutureFirstReplacementView.withFutureControl
            rate rewards C_star C_h u t
              (ReferenceFirstCollectionRenewalFutureFirstReplacementView.priorObserver
                rate rewards C_star C_h u t control0 z q hfuture)
              q hfuture
              (ReferenceFirstCollectionRenewalFutureControlLaw.futureControl
                rate rewards C_star C_h u t q z)) q hfuture =
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker
        rate rewards C_star C_h u t z q hfuture := by
  let control := ReferenceFirstCollectionRenewalFutureControlLaw.futureControl
    rate rewards C_star C_h u t q z
  have hself : ReferenceFirstCollectionRenewalFutureFirstReplacementView.withFutureControl
      rate rewards C_star C_h u t z q hfuture control = z := by
    apply Subtype.ext
    rw [ReferenceFirstCollectionRenewalFutureFirstReplacementView.withFutureControl_val]
    change ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z.val
      (ReferenceSourceCurrentControlFreshness.u_t p q z.val) = z.val
    exact ReferenceFixedTimeSourceControlCoupling.replaceSourceControl_original p q z.val
  have hview : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalFutureFirstReplacementView.priorObserver
          rate rewards C_star C_h u t control0 z q hfuture) q hfuture =
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
        rate rewards C_star C_h u t z q hfuture := by
    exact (ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_view_factor
      rate rewards C_star C_h u t control0 z q hfuture).symm
  conv_rhs => rw [← hself]
  have hleft := ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_marker_section
    rate rewards C_star C_h u t control0
      (ReferenceFirstCollectionRenewalFutureFirstReplacementView.priorObserver
        rate rewards C_star C_h u t control0 z q hfuture) q hfuture
  have hright := ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_marker_section
    rate rewards C_star C_h u t control0 z q hfuture
  rw [hview] at hleft
  cases hv : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture with
  | none =>
      simp only [hv] at hleft hright
      simpa [control] using (hleft control).trans (hright control).symm
  | some v =>
      rcases v with ⟨parameters, view, code⟩
      simp only [hv] at hleft hright
      obtain ⟨enabledL, snapshotL, validL, hparamsL, hcodeL, hsectionL⟩ := hleft
      obtain ⟨enabledR, snapshotR, validR, hparamsR, hcodeR, hsectionR⟩ := hright
      have henabled : enabledL = enabledR := by
        have hpair : some (enabledL, view.payload.rate) =
            some (enabledR, view.payload.rate) := hparamsL.symm.trans hparamsR
        exact congrArg Prod.fst (Option.some.inj hpair)
      have hsnapshot : snapshotL = snapshotR :=
        snapshot_code_injective (p := p) view.payload.assignment
          (hcodeL.symm.trans hcodeR)
      subst enabledR
      subst snapshotR
      have hmarkerL := hsectionL control
      have hmarkerR := hsectionR control
      have hkernel :
          SnapshotRecordingKernel.recordingMap p
            (snapshotL.elim .collection (fun s => .live view.payload.assignment s)) enabledL
            rate.eta.val rate.eta.property rate.sourceCap view.payload.anchor
            (ReferenceFirstWindowNumericalStream.sourceWeights view.payload view.complementWeights)
            view.payload.anchor_pos
            (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ validL)
            (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ validL)
            (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ validL) control.1 =
          SnapshotRecordingKernel.recordingMap p
            (snapshotL.elim .collection (fun s => .live view.payload.assignment s)) enabledL
            rate.eta.val rate.eta.property rate.sourceCap view.payload.anchor
            (ReferenceFirstWindowNumericalStream.sourceWeights view.payload view.complementWeights)
            view.payload.anchor_pos
            (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ validR)
            (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ validR)
            (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ validR) control.1 := by
        rfl
      exact hmarkerL.trans ((congrArg some hkernel).trans hmarkerR.symm)

/-- The complete whole-control physical fiber law, including collection,
live occupied/unoccupied statuses, disabled rounds and all unused controls. -/
theorem futureMarker_control_mass
    (control0 : ContinuousLearningRows.TimeControl p) (z : Z)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) :
    κ {control | ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker
      rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalFutureFirstReplacementView.withFutureControl
          rate rewards C_star C_h u t z q hfuture control) q hfuture = o} =
      ENNReal.ofReal (futureCoefficient rate rewards C_star C_h u t o z q hfuture) := by
  have hk := ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_marker_section
    rate rewards C_star C_h u t control0 z q hfuture
  cases hv : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture with
  | none =>
      simp only [hv] at hk
      cases o with
      | none =>
          have hset : {control : ContinuousLearningRows.TimeControl p |
              ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker
                rate rewards C_star C_h u t
                  (ReferenceFirstCollectionRenewalFutureFirstReplacementView.withFutureControl
                    rate rewards C_star C_h u t z q hfuture control) q hfuture = none} =
              Set.univ := by
            ext control
            simp [hk control]
          rw [hset]
          simp [futureCoefficient, futureParameters, hv,
            ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
      | some a =>
          have hset : {control : ContinuousLearningRows.TimeControl p |
              ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker
                rate rewards C_star C_h u t
                  (ReferenceFirstCollectionRenewalFutureFirstReplacementView.withFutureControl
                    rate rewards C_star C_h u t z q hfuture control) q hfuture = some a} =
              ∅ := by
            ext control
            simp [hk control]
          rw [hset]
          cases a with
          | none => simp [futureCoefficient, futureParameters, hv,
              ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
          | some j => simp [futureCoefficient, futureParameters, hv,
              ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
  | some v =>
      rcases v with ⟨parameters, view, code⟩
      rw [hv] at hk
      obtain ⟨enabled, snapshot, valid, hparams, hcode, hsection⟩ := hk
      have hcanonical : view.payload.rate =
          CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor := by
        funext a
        exact view.payload.rate_eq_canonical a
      have hparameters : futureParameters rate rewards C_star C_h u t z q hfuture =
          some (enabled, CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor) := by
        simp [futureParameters, hv, hparams, hcanonical]
      let regime : SnapshotRecordingKernel.Regime p :=
        snapshot.elim .collection (fun s => .live view.payload.assignment s)
      let recordMap : ContinuousLearningRows.TimeControl p → Option (Fin p.K) := fun control =>
        SnapshotRecordingKernel.recordingMap p regime enabled rate.eta.val
          rate.eta.property rate.sourceCap view.payload.anchor
          (ReferenceFirstWindowNumericalStream.sourceWeights view.payload view.complementWeights)
          view.payload.anchor_pos
          (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid) control.1
      have hset :
          {control : ContinuousLearningRows.TimeControl p |
            ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker
              rate rewards C_star C_h u t
                (ReferenceFirstCollectionRenewalFutureFirstReplacementView.withFutureControl
                  rate rewards C_star C_h u t z q hfuture control) q hfuture = o} =
          {control | some (recordMap control) = o} := by
        ext control
        change ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker
            rate rewards C_star C_h u t
              (ReferenceFirstCollectionRenewalFutureFirstReplacementView.withFutureControl
                rate rewards C_star C_h u t z q hfuture control) q hfuture = o ↔
          some (recordMap control) = o
        rw [hsection control]
      rw [hset, futureCoefficient, hparameters]
      exact snapshotRecording_control_mass rate regime enabled view.payload.anchor
        (ReferenceFirstWindowNumericalStream.sourceWeights view.payload view.complementWeights)
        view.payload.anchor_pos
        (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid) o

/-- The real indicator integral of every replaced physical marker fiber is
the same source-derived coefficient. -/
theorem futureTest_control_integral
    (control0 : ContinuousLearningRows.TimeControl p) (z : Z)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) :
    (∫ control, futureTest rate rewards C_star C_h u t o
      (ReferenceFirstCollectionRenewalFutureFirstReplacementView.withFutureControl
        rate rewards C_star C_h u t z q hfuture control) q hfuture ∂κ) =
      futureCoefficient rate rewards C_star C_h u t o z q hfuture := by
  have hpair : Measurable (fun control : ContinuousLearningRows.TimeControl p => (z, control)) :=
    measurable_const.prodMk measurable_id
  have hm := (measurable_futureMarker_joint rate rewards C_star C_h u t
    control0 q hfuture).comp hpair
  dsimp only [Function.comp_def] at hm
  let S := {control : ContinuousLearningRows.TimeControl p |
    ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker
      rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalFutureFirstReplacementView.withFutureControl
          rate rewards C_star C_h u t z q hfuture control) q hfuture = o}
  have hs : MeasurableSet S := (measurableSet_singleton o).preimage hm
  have heq : (fun control => futureTest rate rewards C_star C_h u t o
      (ReferenceFirstCollectionRenewalFutureFirstReplacementView.withFutureControl
        rate rewards C_star C_h u t z q hfuture control) q hfuture) =
      S.indicator (fun _ => (1 : ℝ)) := by
    funext control
    simp only [futureTest, S, Set.indicator_apply, Set.mem_ofPred_eq]
  rw [heq]
  rw [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one, measureReal_def,
    futureMarker_control_mass rate rewards C_star C_h u t control0 z q hfuture o,
    ENNReal.toReal_ofReal (futureCoefficient_bounds rate rewards C_star C_h u t
      o z q hfuture).1]

/-- The indicator of the literal Borel marker fiber, evaluated using the
actual strict-prefix observer and the actual complete current control. -/
theorem futureControlTest_eq
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) (z : Z) :
    ReferenceFirstCollectionRenewalFutureControlLaw.futureControlTest
      rate rewards C_star C_h u t control0 q (by omega)
      (futureMarkerTestSet rate rewards C_star C_h u t q hfuture o) z =
    futureTest rate rewards C_star C_h u t o z q hfuture := by
  simp only [ReferenceFirstCollectionRenewalFutureControlLaw.futureControlTest,
    futureMarkerTestSet, Set.indicator_apply, Set.mem_ofPred_eq]
  rw [futurePriorObserver_eq_priorObserver rate rewards C_star C_h u t control0 z q hfuture]
  simpa only [futureTest] using congrArg
    (fun marker : Option (Option (Fin p.K)) => if marker = o then (1 : ℝ) else 0)
    (futureMarker_reconstruct rate rewards C_star C_h u t control0 z q hfuture)

/-- The Borel section integral is precisely the future coefficient after
factoring the actual view through its prior observer. -/
theorem futureControlSectionIntegral_eq
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) (z : Z) :
    ReferenceFirstCollectionRenewalFutureControlLaw.futureControlSectionIntegral
      rate rewards C_star C_h u t
      (futureMarkerTestSet rate rewards C_star C_h u t q hfuture o)
      (ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorObserver
        rate rewards C_star C_h u t control0 q (by omega) z) =
    futureCoefficient rate rewards C_star C_h u t o z q hfuture := by
  change (∫ control,
      (futureMarkerTestSet rate rewards C_star C_h u t q hfuture o).indicator
        (fun _ => (1 : ℝ))
        (ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorObserver
          rate rewards C_star C_h u t control0 q (by omega) z, control) ∂κ) = _
  have hsection : (fun control : ContinuousLearningRows.TimeControl p =>
      (futureMarkerTestSet rate rewards C_star C_h u t q hfuture o).indicator
        (fun _ => (1 : ℝ))
        (ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorObserver
          rate rewards C_star C_h u t control0 q (by omega) z, control)) =
      fun control => futureTest rate rewards C_star C_h u t o
        (ReferenceFirstCollectionRenewalFutureFirstReplacementView.withFutureControl
          rate rewards C_star C_h u t
            (ReferenceFirstCollectionRenewalFutureFirstReplacementView.priorObserver
              rate rewards C_star C_h u t control0 z q hfuture)
            q hfuture control) q hfuture := by
    funext control
    rw [futurePriorObserver_eq_priorObserver rate rewards C_star C_h u t
      control0 z q hfuture]
    simp only [futureMarkerTestSet, Set.indicator_apply, Set.mem_ofPred_eq,
      futureTest]
  rw [hsection, futureTest_control_integral rate rewards C_star C_h u t
    control0 (ReferenceFirstCollectionRenewalFutureFirstReplacementView.priorObserver
      rate rewards C_star C_h u t control0 z q hfuture) q hfuture o]
  exact (futureCoefficient_factor rate rewards C_star C_h u t control0 z q hfuture o).symm

/-- Every event in the exact future prior field has the same marker-indicator
and coefficient integrals under the original unnormalized renewal law. -/
theorem futureMarker_test_setIntegral
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) (G : Set Z)
    (hG : MeasurableSet[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q] G) :
    (∫ z in G, futureTest rate rewards C_star C_h u t o z q hfuture ∂ν) =
      ∫ z in G, futureCoefficient rate rewards C_star C_h u t o z q hfuture ∂ν := by
  have h := ReferenceFirstCollectionRenewalFutureControlLaw.futureControl_test_setIntegral
    rate rewards C_star C_h u t control0 q (by omega)
    (futureMarkerTestSet rate rewards C_star C_h u t q hfuture o)
    (measurableSet_futureMarkerTestSet rate rewards C_star C_h u t
      control0 q hfuture o) G hG
  simpa only [futureControlTest_eq rate rewards C_star C_h u t control0 q hfuture o,
    futureControlSectionIntegral_eq rate rewards C_star C_h u t control0 q hfuture o]
    using h

/-- Conditional expectation of the actual future marker-fiber indicator is
the same-source predictable coefficient, including on zero-mass restrictions. -/
theorem futureMarker_condExp
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) :
    (ν)[(fun z => futureTest rate rewards C_star C_h u t o z q hfuture) |
      ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q] =ᵐ[ν]
      fun z => futureCoefficient rate rewards C_star C_h u t o z q hfuture := by
  have h := ReferenceFirstCollectionRenewalFutureControlLaw.futureControl_test_condExp
    rate rewards C_star C_h u t control0 q (by omega)
    (futureMarkerTestSet rate rewards C_star C_h u t q hfuture o)
    (measurableSet_futureMarkerTestSet rate rewards C_star C_h u t
      control0 q hfuture o)
  have htest : (fun z => ReferenceFirstCollectionRenewalFutureControlLaw.futureControlTest
      rate rewards C_star C_h u t control0 q (by omega)
      (futureMarkerTestSet rate rewards C_star C_h u t q hfuture o) z) =
      fun z => futureTest rate rewards C_star C_h u t o z q hfuture := by
    funext z
    exact futureControlTest_eq rate rewards C_star C_h u t control0 q hfuture o z
  change (ν)[(fun z => ReferenceFirstCollectionRenewalFutureControlLaw.futureControlTest
      rate rewards C_star C_h u t control0 q (by omega)
      (futureMarkerTestSet rate rewards C_star C_h u t q hfuture o) z) |
      ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q] =ᵐ[ν]
      (fun z => ∫ control,
        (futureMarkerTestSet rate rewards C_star C_h u t q hfuture o).indicator
        (fun _ => (1 : ℝ))
        (ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorObserver
          rate rewards C_star C_h u t control0 q (by omega) z, control) ∂κ) at h
  rw [htest] at h
  filter_upwards [h] with z hz
  have hsection := futureControlSectionIntegral_eq
    rate rewards C_star C_h u t control0 q hfuture o z
  simpa only [ReferenceFirstCollectionRenewalFutureControlLaw.futureControlSectionIntegral]
    using hz.trans hsection

end Bandits.Support.ReferenceFirstCollectionRenewalFutureRecordingLaw
