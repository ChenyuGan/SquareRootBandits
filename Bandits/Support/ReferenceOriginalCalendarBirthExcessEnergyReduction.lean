/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalCalendarFirstBranchIncrementTransport
public import Bandits.Support.ReferenceOriginalCalendarLiveCollectionIncrementTransport

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# Original-calendar renewed-birth excess and carried-energy telescope

This module assembles the actual same-date FIRST, renewed-birth, continuing
LIVE, and collection/cutoff branches under the unchanged original source law.
The renewed-birth increment remains a signed term in the conclusion.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions (Parameters)
open ReferenceActivePhysicalStep (RateInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceOriginalCalendarBirthExcessEnergyReduction

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (control0 : TimeControl p) (a : Fin p.K)

local notation "X" => SourceInput p
local notation "mu" => sourceInputLaw p
local notation "CE" => ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
  rate rewards C_star C_h

/-- The literal active renewed-birth observation at original date `q`. -/
public def activeBirthEvent (q : Fin p.T) : Set X :=
  {z | (ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector
      rate rewards C_star C_h q z).isSome = true ∧
    ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
      rate rewards C_star C_h q z}

/-- The actual carried-energy increment restricted to that same observed
active renewed-birth event. -/
public def activeBirthIncrement (q : Fin p.T) : X → ℝ :=
  (activeBirthEvent rate rewards C_star C_h q).indicator
    (fun z => CE (q.val + 1) a z - CE q.val a z)

/-- Ambient Borelness of the literal observed birth restriction. -/
public theorem measurableSet_activeBirthEvent (q : Fin p.T) :
    MeasurableSet (activeBirthEvent rate rewards C_star C_h q) := by
  -- The actual selector retains its observed record; on that branch the
  -- numerical cell is enabled. Thus active birth is the selector event
  -- intersected with the present, non-overflowed original prefix.
  classical
  -- The prefix part is a finite optional readout, and the selector's Bool
  -- tag is determined by the accepted complete-record observer.
  have hprefix : Measurable (fun z : X =>
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h q.val z) := by
    have hp := ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_prefixReadout
      rate rewards C_star C_h q.val
    simpa [ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.sourceInputMeasurableSpace,
      ReferenceInitializationMeasurability.optionCountableMeasurableSpace,
      LaterAssignmentStartMeasurability.optionMeasurableSpace] using hp
  have hbirth : MeasurableSet {z : X |
      (ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector
        rate rewards C_star C_h q z).isSome = true} := by
    -- The actual later-choice bit is a discrete projection of the full
    -- collection observation; the live numerical readout keeps its option.
    let : MeasurableSpace (Option Unit) :=
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.optionMeasurableSpace
    let : MeasurableSingletonClass (Option Unit) := by
      constructor
      intro o
      let e := Equiv.optionEquivSumPUnit Unit
      have hset : e ⁻¹' {e o} = {o} := by
        ext x
        exact e.injective.eq_iff
      rw [← hset]
      apply comap_measurable e
      cases he : e o with
      | inl u =>
          simpa only [Set.image_singleton] using
            (MeasurableSet.singleton u).inl_image (β := PUnit)
      | inr u =>
          simpa only [Set.image_singleton] using
            (MeasurableSet.singleton u).inr_image (α := Unit)
    let tag : ReferenceActivePhysicalStep.RoundInput p rate → Bool := fun x =>
      match ReferenceCollectionOutcomeMeasurability.canonicalCollectionFullObservation x with
      | none => false
      | some (.inl _) => false
      | some (.inr observation) => decide (observation.2.2.1 = .laterChosen)
    have htag : Measurable tag := by
      let instClock : MeasurableSpace
          (ReferenceCollectionDispatchMeasurability.ClockObservation p) :=
        ReferenceCollectionOutcomeMeasurability.instMeasurableSpaceClockObservation
      let : MeasurableSpace
          (ReferenceCollectionDispatchMeasurability.ClockObservation p) := instClock
      let instOptionNat : MeasurableSpace (Option ℕ) :=
        LaterAssignmentStartMeasurability.optionMeasurableSpace
      let : MeasurableSpace (Option ℕ) := instOptionNat
      let instOptionTriple : MeasurableSpace (Option (ℕ × ℕ × ℕ)) :=
        LaterAssignmentStartMeasurability.optionMeasurableSpace
      let : MeasurableSpace (Option (ℕ × ℕ × ℕ)) := instOptionTriple
      let instOptionPair : MeasurableSpace (Option (ℕ × ℕ)) :=
        LaterAssignmentStartMeasurability.optionMeasurableSpace
      let : MeasurableSpace (Option (ℕ × ℕ)) := instOptionPair
      let boundaryTag (o : Unit ⊕ ReferenceCollectionOutcomeMeasurability.FullObservation p rate) : Bool :=
        Sum.elim (fun _ : Unit => false)
          (fun observation => decide (observation.2.2.1 = .laterChosen)) o
      have htagProjection : Measurable (fun observation :
          ReferenceCollectionOutcomeMeasurability.FullObservation p rate =>
          observation.2.2.1) :=
        measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_id))
      have htagRight : Measurable (fun observation :
          ReferenceCollectionOutcomeMeasurability.FullObservation p rate =>
          decide (observation.2.2.1 =
            ReferenceCollectionOutcomeMeasurability.CollectionTag.laterChosen)) := by
        have htagTag : Measurable (fun t : ReferenceCollectionOutcomeMeasurability.CollectionTag p =>
            decide (t = ReferenceCollectionOutcomeMeasurability.CollectionTag.laterChosen)) :=
          measurable_of_countable _
        exact htagTag.comp htagProjection
      have hleft : Measurable (boundaryTag ∘ Sum.inl) := by
        change Measurable (fun _ : Unit => false)
        exact measurable_const
      have hright : Measurable (boundaryTag ∘ Sum.inr) := by
        change Measurable (fun observation :
          ReferenceCollectionOutcomeMeasurability.FullObservation p rate =>
          decide (observation.2.2.1 =
            ReferenceCollectionOutcomeMeasurability.CollectionTag.laterChosen))
        exact htagRight
      have hboundary : @Measurable
          (Unit ⊕ ReferenceCollectionOutcomeMeasurability.FullObservation p rate)
          Bool Sum.instMeasurableSpace Bool.instMeasurableSpace boundaryTag :=
        measurable_fun_sum hleft hright
      have hoptional := ReferenceCollectionOutcomeMeasurability.measurable_optionalElim
        false boundaryTag hboundary
      have hcanonical :=
        ReferenceCollectionOutcomeMeasurability.measurable_canonicalCollectionFullObservation
          (p := p) (rate := rate)
      have htagFunction' : tag = fun x =>
          ReferenceCollectionOutcomeMeasurability.optionalElim false boundaryTag
            (ReferenceCollectionOutcomeMeasurability.canonicalCollectionFullObservation x) := by
        funext x
        unfold tag
        cases hobs : ReferenceCollectionOutcomeMeasurability.canonicalCollectionFullObservation x with
        | none => rfl
        | some observation => cases observation <;> rfl
      rw [htagFunction']
      exact hoptional.comp hcanonical
    -- This factorization uses only the record code and its actual optional
    -- live readout, so absence remains absence.
    let f (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) : Option Unit :=
      if tag r.input = true ∧
          (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).isSome = true
        then some () else none
    have hf (k : ℕ) : Measurable (fun x :
        ReferenceCompleteSuffixInputMeasurability.IndexedSource rate rewards C_star C_h k =>
        f ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate x.val rewards C_star C_h
          |>.get ⟨k, x.property⟩))) := by
      have hinput := ReferenceCompleteSuffixInputMeasurability.measurable_actualRoundInputAt
        rate rewards C_star C_h k
      have htagk : Measurable (fun x :
          ReferenceCompleteSuffixInputMeasurability.IndexedSource rate rewards C_star C_h k =>
          tag (ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt
            rate rewards C_star C_h k x)) := by
        exact htag.comp hinput
      have hlive : MeasurableSet {x :
          ReferenceCompleteSuffixInputMeasurability.IndexedSource rate rewards C_star C_h k |
          (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
            (ReferenceCompletePhysicalHistory.completeSuffixRecords rate x.val rewards C_star C_h
              |>.get ⟨k, x.property⟩)).isSome = true} :=
        ReferenceLaterLiveReadoutDomain.measurableSet_indexedReadoutDomain_fixed
          rate rewards C_star C_h 0 k
      have hcond : MeasurableSet {x :
          ReferenceCompleteSuffixInputMeasurability.IndexedSource rate rewards C_star C_h k |
          tag (ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt
              rate rewards C_star C_h k x) = true ∧
            (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
              (ReferenceCompletePhysicalHistory.completeSuffixRecords rate x.val rewards C_star C_h
                |>.get ⟨k, x.property⟩)).isSome = true} :=
        (measurableSet_eq_fun htagk measurable_const).inter hlive
      have hfEq : (fun x :
          ReferenceCompleteSuffixInputMeasurability.IndexedSource rate rewards C_star C_h k =>
          f ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate x.val rewards C_star C_h
            |>.get ⟨k, x.property⟩))) = fun x =>
          if tag (ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt
              rate rewards C_star C_h k x) = true ∧
            (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
              (ReferenceCompletePhysicalHistory.completeSuffixRecords rate x.val rewards C_star C_h
                |>.get ⟨k, x.property⟩)).isSome = true then some () else none := by
        funext x
        simp only [f, ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt]
        rfl
      rw [hfEq]
      exact Measurable.ite hcond measurable_const measurable_const
    have hm := ReferenceOriginalCalendarContinuingLiveRecorderLaw.measurable_actualReadout
      rate rewards C_star C_h f hf q
    have heq : {z : X |
        (ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector
          rate rewards C_star C_h q z).isSome = true} =
        {z | (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
          rate rewards C_star C_h q z).bind f = some ()} := by
      ext z
      cases hr : ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
          rate rewards C_star C_h q z with
      | none =>
          have hrec : ReferenceSourcePrefixHistoryFiltration.actualRecord
              rate rewards C_star C_h q z = none := hr
          simp [ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector,
            ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt, hrec, f]
      | some r =>
        have hrec : ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h q z = some r := hr
        have htag_eq : tag r.input =
            ReferenceCollectionPhaseHistory.laterChosen r.input := by
          cases hs : r.input.state.coordinator with
          | collection payload ledger proposal =>
              let b : ReferenceCollectionDispatchMeasurability.BoundaryInput p rate :=
                ((payload, r.input.row), ledger, proposal, r.input.state.upDecoderBank, r.input.time)
              by_cases hc : ReferenceCollectionDispatchMeasurability.cutoffValid b
              · let z := ReferenceCollectionDispatchMeasurability.boundaryLocal ⟨b, hc⟩
                have hobs := ReferenceCollectionOutcomeMeasurability.canonicalCollectionFullObservation_collection
                  r.input payload ledger proposal hs
                have hdispatch := ReferenceCollectionDispatchMeasurability.dispatch_collection
                  r.input payload ledger proposal hs hc
                have htagActual := ReferenceCollectionOutcomeMeasurability.collectionTag_eq_actual z
                have hc' : ReferenceCollectionDispatchMeasurability.cutoffValid
                    ((payload, r.input.row), ledger, proposal,
                      r.input.state.upDecoderBank, r.input.time) := hc
                have hobs' : ReferenceCollectionOutcomeMeasurability.canonicalCollectionFullObservation
                    r.input = some (.inr
                      (ReferenceCollectionOutcomeMeasurability.collectionFullObservation z)) := by
                  rw [hobs]
                  apply congrArg some
                  unfold ReferenceCollectionOutcomeMeasurability.boundaryFullObservation
                  rw [dite_eq_left hc']
                have hleft : tag r.input = decide
                    (ReferenceCollectionOutcomeMeasurability.collectionTag z = .laterChosen) := by
                  unfold tag
                  rw [hobs']
                  simp [ReferenceCollectionOutcomeMeasurability.collectionFullObservation]
                  rfl
                have hright : decide (ReferenceCollectionOutcomeMeasurability.outcomeTag
                    (CoordinatorRoundDispatch.dispatchCollection
                      (ReferenceCollectionDispatchMeasurability.assemble z)) = .laterChosen) =
                    ReferenceCollectionPhaseHistory.laterChosen r.input := by
                  simp only [ReferenceCollectionPhaseHistory.laterChosen,
                    ReferenceActivePhysicalStep.prepare, hdispatch]
                  cases hout : CoordinatorRoundDispatch.dispatchCollection
                      (ReferenceCollectionDispatchMeasurability.assemble z) <;>
                    simp [ReferenceCollectionOutcomeMeasurability.outcomeTag]
                calc
                  tag r.input = decide
                      (ReferenceCollectionOutcomeMeasurability.collectionTag z = .laterChosen) := hleft
                  _ = decide (ReferenceCollectionOutcomeMeasurability.outcomeTag
                        (CoordinatorRoundDispatch.dispatchCollection
                          (ReferenceCollectionDispatchMeasurability.assemble z)) = .laterChosen) := by
                    rw [htagActual]
                  _ = ReferenceCollectionPhaseHistory.laterChosen r.input := hright
              · have hobs := ReferenceCollectionOutcomeMeasurability.canonicalCollectionFullObservation_invalid
                  r.input payload ledger proposal hs hc
                have hdispatch := (ReferenceCollectionDispatchMeasurability.dispatch_collection_invalid
                  r.input payload ledger proposal hs hc).1
                have hleft : tag r.input = false := by
                  unfold tag
                  rw [hobs.1]
                have hright : ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
                  simp only [ReferenceCollectionPhaseHistory.laterChosen,
                    ReferenceActivePhysicalStep.prepare, hdispatch]
                exact hleft.trans hright.symm
            | first =>
                have hphase : ReferenceCollectionDispatchMeasurability.collectionCoordinates?
                    (ReferenceActivePhysicalStepMeasurability.encodeCoordinator
                      r.input.state.coordinator) = none := by
                  simp [ReferenceCollectionDispatchMeasurability.collectionCoordinates?,
                    ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hs]
                have hobs := ReferenceCollectionOutcomeMeasurability.canonicalCollectionFullObservation_absent
                  r.input hphase
                have hdispatch := ReferenceActivePhysicalStep.dispatch_first r.input hs
                have hleft : tag r.input = false := by
                  unfold tag
                  rw [hobs.1]
                have hright : ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
                  simp only [ReferenceCollectionPhaseHistory.laterChosen,
                    ReferenceActivePhysicalStep.prepare, hdispatch]
                exact hleft.trans hright.symm
            | live regs owned base =>
                have hphase : ReferenceCollectionDispatchMeasurability.collectionCoordinates?
                    (ReferenceActivePhysicalStepMeasurability.encodeCoordinator
                      r.input.state.coordinator) = none := by
                  simp [ReferenceCollectionDispatchMeasurability.collectionCoordinates?,
                    ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hs]
                have hobs := ReferenceCollectionOutcomeMeasurability.canonicalCollectionFullObservation_absent
                  r.input hphase
                have hdispatch : ReferenceActivePhysicalStep.dispatch r.input =
                    .live regs owned base (CoordinatorRoundDispatch.dispatchLive
                      (ReferenceActivePhysicalStep.liveInput r.input regs owned base)) := by
                  simp only [ReferenceActivePhysicalStep.dispatch, hs,
                    CoordinatorRoundDispatch.dispatch]
                  rfl
                have hleft : tag r.input = false := by
                  unfold tag
                  rw [hobs.1]
                have hright : ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
                  simp only [ReferenceCollectionPhaseHistory.laterChosen,
                    ReferenceActivePhysicalStep.prepare, hdispatch]
                exact hleft.trans hright.symm
            | dagger =>
                have hphase : ReferenceCollectionDispatchMeasurability.collectionCoordinates?
                    (ReferenceActivePhysicalStepMeasurability.encodeCoordinator
                      r.input.state.coordinator) = none := by
                  simp [ReferenceCollectionDispatchMeasurability.collectionCoordinates?,
                    ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hs]
                have hobs := ReferenceCollectionOutcomeMeasurability.canonicalCollectionFullObservation_absent
                  r.input hphase
                have hdispatch := ReferenceActivePhysicalStep.dispatch_dagger r.input hs
                have hleft : tag r.input = false := by
                  unfold tag
                  rw [hobs.1]
                have hright : ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
                  simp only [ReferenceCollectionPhaseHistory.laterChosen,
                    ReferenceActivePhysicalStep.prepare, hdispatch]
                exact hleft.trans hright.symm
        change (((ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h q z).bind (fun r0 =>
              (ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthRecordSelector
                rate r0).map (fun cp =>
                  (⟨r0, cp⟩ : ReferenceOriginalCalendarRetainedBranchPartition.ActualBranchData rate)))).isSome = true) ↔
          (ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h q z).bind f = some ()
        rw [hrec]
        simp only [Option.bind_some]
        cases hread : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r with
        | none => simp [ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthRecordSelector,
            hread, f]
        | some c =>
            cases hdispatch : ReferenceActivePhysicalStep.dispatch r.input with
            | first outcome => cases outcome <;>
                simp [ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthRecordSelector,
                  hread, hdispatch, f, htag_eq, ReferenceCollectionPhaseHistory.laterChosen,
                  ReferenceActivePhysicalStep.prepare]
            | live regs owned base outcome => cases outcome <;>
                simp [ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthRecordSelector,
                  hread, hdispatch, f, htag_eq, ReferenceCollectionPhaseHistory.laterChosen,
                  ReferenceActivePhysicalStep.prepare]
            | collection payload ledger clock cutoff outcome => cases outcome <;>
                simp [ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthRecordSelector,
                  hread, hdispatch, f, htag_eq, ReferenceCollectionPhaseHistory.laterChosen,
                  ReferenceActivePhysicalStep.prepare]
            | invalidCollectionCutoff =>
                simp [ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthRecordSelector,
                  hread, hdispatch, f, htag_eq, ReferenceCollectionPhaseHistory.laterChosen,
                  ReferenceActivePhysicalStep.prepare]
            | dagger =>
                simp [ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthRecordSelector,
                  hread, hdispatch, f, htag_eq, ReferenceCollectionPhaseHistory.laterChosen,
                  ReferenceActivePhysicalStep.prepare]
    rw [heq]
    exact (MeasurableSet.singleton (some ())).preimage hm
  -- Active update is the conjunction of a present, non-overflowed carried
  -- prefix and its enabled current observed cell.
  have hclean : MeasurableSet {z : X | ∃ o :
      ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h q.val z = some o ∧ o.2.1 = false} := by
    let : MeasurableSpace
        (Option (ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K)) :=
      ReferenceInitializationMeasurability.optionCountableMeasurableSpace _
    let : MeasurableSingletonClass
        (Option (ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K)) :=
      ReferenceInitializationMeasurability.optionCountableMeasurableSingletonClass _
    have hm : Measurable (fun z : X =>
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
          rate rewards C_star C_h q.val z).elim false (fun o => decide (o.2.1 = false))) := by
      have hobs : Measurable (fun o :
          Option (ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K) =>
          o.elim false (fun o => decide (o.2.1 = false))) := measurable_of_countable _
      exact hobs.comp hprefix
    have heq : {z : X | ∃ o : ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K,
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
          rate rewards C_star C_h q.val z = some o ∧ o.2.1 = false} =
        {z | (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
          rate rewards C_star C_h q.val z).elim false (fun o => decide (o.2.1 = false)) = true} := by
      ext z
      cases hp : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
          rate rewards C_star C_h q.val z with
      | none => simp [hp]
      | some o =>
          simp only [Set.mem_ofPred_eq, hp, Option.elim_some, decide_eq_true_eq,
            Option.some.injEq]
          constructor
          · rintro ⟨o', rfl, hclear⟩
            exact hclear
          · intro hclear
            exact ⟨o, rfl, hclear⟩
    rw [heq]
    exact (measurableSet_singleton true).preimage hm
  have hactiveBirthEq : activeBirthEvent rate rewards C_star C_h q =
      {z | (ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector
          rate rewards C_star C_h q z).isSome = true ∧
        z ∈ {z : X | ∃ o : ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K,
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
            rate rewards C_star C_h q.val z = some o ∧ o.2.1 = false}} := by
    ext z
    constructor
    · rintro ⟨hbirth', hactive'⟩
      obtain ⟨o, c, hP, hcell, hclear, henabled⟩ := hactive'
      exact ⟨hbirth', ⟨o, hP, hclear⟩⟩
    · rintro ⟨hbirth', o, hP, hclear⟩
      have hdata := Option.isSome_iff_exists.mp hbirth'
      rcases hdata with ⟨⟨r, ⟨c, payload⟩⟩, hselector⟩
      have hcell := ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector_actualCell
        rate rewards C_star C_h q z r c payload hselector
      have hread := ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthRecordSelector_cell
        rate r c payload (by
          unfold ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector at hselector
          rcases Option.bind_eq_some_iff.mp hselector with ⟨r', hr, hm⟩
          rcases Option.map_eq_some_iff.mp hm with ⟨cp, hcp, heq⟩
          cases heq
          exact hcp)
      have henabled := (ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical
        0 r c hread).1
      exact ⟨hbirth', ⟨o, c, hP, hcell, hclear, henabled⟩⟩
  rw [hactiveBirthEq]
  simpa only [Set.inter_def, Set.mem_ofPred_eq] using hbirth.inter hclean

public theorem integrable_activeBirthIncrement (q : Fin p.T) :
    Integrable (activeBirthIncrement rate rewards C_star C_h a q) (sourceInputLaw p) := by
  unfold activeBirthIncrement
  have hnext := ReferenceOriginalCalendarCarriedStoppedEnergy.integrable_carriedStoppedEnergy
    rate rewards C_star C_h (q.val + 1) (by omega) a
  have hcurrent := ReferenceOriginalCalendarCarriedStoppedEnergy.integrable_carriedStoppedEnergy
    rate rewards C_star C_h q.val q.isLt.le a
  exact (hnext.sub hcurrent).indicator (measurableSet_activeBirthEvent
    rate rewards C_star C_h q)

open ReferenceOriginalCalendarRetainedBranchPartition
open ReferenceOriginalCalendarFirstBranchIncrementTransport
open ReferenceOriginalCalendarLiveCollectionIncrementTransport

/-- Constructor separation makes the actual FIRST and active renewed-birth
observations disjoint. -/
public theorem firstSelectorEvent_disjoint_activeBirthEvent (q : Fin p.T) :
    Disjoint (firstSelectorEvent rate rewards C_star C_h q)
      (activeBirthEvent rate rewards C_star C_h q) := by
  apply Set.disjoint_left.mpr
  intro z hfirst hbirth
  exact (branchSelectors_disjoint rate rewards C_star C_h q z).2.1
    ⟨hfirst, hbirth.1⟩

/-- Same-date branch reduction. FIRST and active birth retain their exact
increments; only the complement receives a unit allowance. -/
public theorem carriedStoppedEnergy_increment_le_branch_reduction
    (q : Fin p.T) (z : X) :
    CE (q.val + 1) a z - CE q.val a z ≤
      firstSelectorIncrement rate rewards C_star C_h q a z +
      activeBirthIncrement rate rewards C_star C_h a q z +
      (firstSelectorEvent rate rewards C_star C_h q ∪
        activeBirthEvent rate rewards C_star C_h q)ᶜ.indicator (fun _ => (1 : ℝ)) z +
      (branchContribution rate rewards C_star C_h q a z
        (continuingLiveSelector rate rewards C_star C_h q z) +
       branchContribution rate rewards C_star C_h q a z
        (collectionOrCutoffSelector rate rewards C_star C_h q z)) := by
  have hd := branchSelectors_disjoint rate rewards C_star C_h q z
  by_cases hfirst : z ∈ firstSelectorEvent rate rewards C_star C_h q
  · have hf : (firstChosenSelector rate rewards C_star C_h q z).isSome = true := hfirst
    have hl : continuingLiveSelector rate rewards C_star C_h q z = none :=
      Option.not_isSome_iff_eq_none.mp (fun h => hd.1 ⟨hf, h⟩)
    have hc : collectionOrCutoffSelector rate rewards C_star C_h q z = none :=
      Option.not_isSome_iff_eq_none.mp (fun h => hd.2.2.1 ⟨hf, h⟩)
    have hb : z ∉ activeBirthEvent rate rewards C_star C_h q :=
      fun h => hd.2.1 ⟨hf, h.1⟩
    simp [firstSelectorIncrement, activeBirthIncrement, hfirst, hb,
      branchContribution, hl, hc]
  · by_cases hbirth : z ∈ activeBirthEvent rate rewards C_star C_h q
    · have hl : continuingLiveSelector rate rewards C_star C_h q z = none :=
        Option.not_isSome_iff_eq_none.mp (fun h => hd.2.2.2.1 ⟨h, hbirth.1⟩)
      have hc : collectionOrCutoffSelector rate rewards C_star C_h q z = none :=
        Option.not_isSome_iff_eq_none.mp (fun h => hd.2.2.2.2.2 ⟨hbirth.1, h⟩)
      simp [firstSelectorIncrement, activeBirthIncrement, hfirst, hbirth,
        branchContribution, hl, hc]
    · have hf : firstChosenSelector rate rewards C_star C_h q z = none :=
        Option.not_isSome_iff_eq_none.mp hfirst
      by_cases hactive : ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
          rate rewards C_star C_h q z
      · have hb : renewedBirthSelector rate rewards C_star C_h q z = none :=
          Option.not_isSome_iff_eq_none.mp (fun h => hbirth ⟨h, hactive⟩)
        have hu := carriedStoppedEnergy_update_by_branches rate rewards C_star C_h q a z
        have hp := branchPenalty_sum_le_one rate rewards C_star C_h q z
        simp only [hf, hb, branchPenalty, branchContribution, zero_add, add_zero] at hu hp
        simp only [firstSelectorIncrement, activeBirthIncrement,
          Set.indicator_of_notMem hfirst, Set.indicator_of_notMem hbirth,
          Set.mem_compl_iff, Set.mem_union, not_or, hfirst, hbirth,
          not_false_eq_true, and_self, Set.indicator_of_mem, zero_add]
        dsimp only [branchContribution]
        linarith only [hu, hp]
      · have hu := ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy_update_bound
          rate rewards C_star C_h q a z
        simp only [ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt,
          hactive, ite_false, mul_zero, Real.exp_zero, sub_self, add_zero] at hu
        have hl : branchContribution rate rewards C_star C_h q a z
            (continuingLiveSelector rate rewards C_star C_h q z) = 0 := by
          cases continuingLiveSelector rate rewards C_star C_h q z <;>
            simp [branchContribution, hactive]
        have hc : branchContribution rate rewards C_star C_h q a z
            (collectionOrCutoffSelector rate rewards C_star C_h q z) = 0 := by
          cases collectionOrCutoffSelector rate rewards C_star C_h q z <;>
            simp [branchContribution, hactive]
        simp only [firstSelectorIncrement, activeBirthIncrement,
          Set.indicator_of_notMem hfirst, Set.indicator_of_notMem hbirth,
          Set.mem_compl_iff, Set.mem_union, not_or, hfirst, hbirth,
          not_false_eq_true, and_self, Set.indicator_of_mem, hl, hc, zero_add, add_zero]
        linarith only [hu]

include control0 in
/-- The original joint source-law datewise estimate, with the literal signed
active renewed-birth excess left in the conclusion. -/
public theorem integral_carriedStoppedEnergy_increment_le_birth_excess (q : Fin p.T) :
    (∫ z : X, (CE (q.val + 1) a z - CE q.val a z) ∂mu) ≤
      1 + (∫ z : X, activeBirthIncrement rate rewards C_star C_h a q z ∂mu) -
        (sourceInputLaw p).real (activeBirthEvent rate rewards C_star C_h q) := by
  let A := firstSelectorEvent rate rewards C_star C_h q
  let B := activeBirthEvent rate rewards C_star C_h q
  have hA : MeasurableSet A := measurableSet_firstSelectorEvent
    rate rewards C_star C_h control0 q a
  have hB : MeasurableSet B := measurableSet_activeBirthEvent rate rewards C_star C_h q
  have hiF := integrable_firstSelectorIncrement rate rewards C_star C_h control0 q a
  have hiB := integrable_activeBirthIncrement rate rewards C_star C_h a q
  have hiC : Integrable ((A ∪ B)ᶜ.indicator (fun _ : X => (1 : ℝ))) mu :=
    (integrable_const 1).indicator (hA.union hB).compl
  have hiL := continuingLive_collectionOrCutoff_branchContribution_sum_integrable
      rate rewards C_star C_h control0 q a
  have hiD := (ReferenceOriginalCalendarCarriedStoppedEnergy.integrable_carriedStoppedEnergy
    rate rewards C_star C_h (q.val + 1) (by omega) a).sub
      (ReferenceOriginalCalendarCarriedStoppedEnergy.integrable_carriedStoppedEnergy
        rate rewards C_star C_h q.val q.isLt.le a)
  have hle := integral_mono hiD (((hiF.add hiB).add hiC).add hiL)
    (carriedStoppedEnergy_increment_le_branch_reduction rate rewards C_star C_h a q)
  simp only [Pi.add_apply, Pi.sub_apply] at hle
  have hsplitL := integral_add ((hiF.add hiB).add hiC) hiL
  have hsplitC := integral_add (hiF.add hiB) hiC
  have hsplitB := integral_add hiF hiB
  simp only [Pi.add_apply] at hsplitL hsplitC hsplitB
  rw [hsplitL, hsplitC, hsplitB,
    integral_indicator_const (1 : ℝ) (hA.union hB).compl] at hle
  simp only [smul_eq_mul, mul_one] at hle
  have hfirst := integral_firstSelectorIncrement_le_event_mass
    rate rewards C_star C_h control0 q a
  have hlive := continuingLive_collectionOrCutoff_branchContribution_sum_integral_nonpos
      rate rewards C_star C_h control0 q a
  have hmass := measureReal_add_measureReal_compl (μ := mu) (hA.union hB)
  rw [measureReal_union
    (firstSelectorEvent_disjoint_activeBirthEvent rate rewards C_star C_h q) hB,
    probReal_univ] at hmass
  dsimp only [A, B] at hle hmass
  linarith only [hle, hfirst, hlive, hmass]

include control0 in
/-- Finite-prefix telescope of the actual carried stopped energy. No sign
claim is made for any renewed-birth excess. -/
public theorem integral_carriedStoppedEnergy_prefix_le_birth_excess
    (n : ℕ) (hn : n ≤ p.T) :
    (∫ z : X, CE n a z ∂mu) ≤ (n : ℝ) + 1 +
      ∑ q ∈ Finset.univ.filter (fun q : Fin p.T => q.val < n),
        ((∫ z : X, activeBirthIncrement rate rewards C_star C_h a q z ∂mu) -
          (sourceInputLaw p).real (activeBirthEvent rate rewards C_star C_h q)) := by
  induction n with
  | zero =>
      simp only [ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy_zero,
        integral_const, probReal_univ, smul_eq_mul, one_mul, Nat.cast_zero,
        zero_add, Nat.not_lt_zero, Finset.filter_false, Finset.sum_empty, add_zero]
      exact le_rfl
  | succ n ih =>
      have hlt : n < p.T := by omega
      let q : Fin p.T := ⟨n, hlt⟩
      have hstep := integral_carriedStoppedEnergy_increment_le_birth_excess
        rate rewards C_star C_h control0 a q
      rw [integral_sub
        (ReferenceOriginalCalendarCarriedStoppedEnergy.integrable_carriedStoppedEnergy
          rate rewards C_star C_h (q.val + 1) hn a)
        (ReferenceOriginalCalendarCarriedStoppedEnergy.integrable_carriedStoppedEnergy
          rate rewards C_star C_h q.val hlt.le a)] at hstep
      have hprev := ih (by omega)
      have hfilter : Finset.univ.filter (fun r : Fin p.T => r.val < n + 1) =
          insert q (Finset.univ.filter (fun r : Fin p.T => r.val < n)) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Fin.ext_iff]
        dsimp only [q]
        omega
      have hnot : q ∉ Finset.univ.filter (fun r : Fin p.T => r.val < n) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, q, lt_self_iff_false,
          not_false_eq_true]
      rw [hfilter, Finset.sum_insert hnot, Nat.cast_succ]
      dsimp only [q] at hstep ⊢
      linarith only [hstep, hprev]

end Bandits.Support.ReferenceOriginalCalendarBirthExcessEnergyReduction

end
