/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteInstallationCollectionPrefixNumericalTruth

import Mathlib.Tactic

/-!
# Selected-row locality of the complete original numerical prefix

The statements compare the existing optional zero-origin numerical prefix on
the whole source carrier.  They preserve the original complete suffix, private
coordinates, selected row, rewards, and stopped run.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open BootstrapPrivateRoundStreams
open ReferenceActivePhysicalHorizon
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
open ReferenceLaterCollectionSourceReadoutMeasurability
open ReferenceActiveHorizonMeasurability

namespace Bandits.Support.ReferenceCompletePrefixReadoutRowLocality

variable {p : ConstructorDimensions.Parameters}

private theorem prepared_configuration_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (left right : RoundRecord (p := p) (rate := rate))
    (hstate : left.input.state = right.input.state)
    (htime : left.input.time = right.input.time)
    (hrow : left.input.row = right.input.row) (i : Fin (p.m - 1)) :
    (left.output.preparation.followers.followers i).configuration =
      (right.output.preparation.followers.followers i).configuration := by
  rw [left.output_eq, right.output_eq]
  change (DeclaredFollowerLocalRound.prepare rate i left.input.row
    (left.input.state.activations i) left.input.time (left.input.active i)
    (left.input.state.followers i)).configuration =
      (DeclaredFollowerLocalRound.prepare rate i right.input.row
        (right.input.state.activations i) right.input.time (right.input.active i)
        (right.input.state.followers i)).configuration
  simp only [hstate, htime, hrow]

private theorem collection_guard_iff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (x y : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : x.state = y.state) (htime : x.time = y.time)
    (hrow : x.row = y.row) :
    ReferenceLaterCollectionReadoutDomain.observableReadoutGuard rate 0 x ↔
      ReferenceLaterCollectionReadoutDomain.observableReadoutGuard rate 0 y := by
  have hlive : ReferenceLaterCollectionReadoutDomain.actualLiveOutcomeData rate x =
      ReferenceLaterCollectionReadoutDomain.actualLiveOutcomeData rate y := by
    unfold ReferenceLaterCollectionReadoutDomain.actualLiveOutcomeData
    rw [hstate]
    exact congrArg (fun z : Fin p.T × CompletePublicTable.CompleteRow p =>
      match ReferenceActivePhysicalStepMeasurability.encodeCoordinator y.state.coordinator with
      | .inl _ => none
      | .inr (.inl (payload, live)) =>
          some (ReferenceLiveDispatchOutputMeasurability.outcomeData
            (CoordinatorRoundDispatch.dispatchLive
              (ReferenceLiveDispatchMeasurability.liveInputOfCoordinates
                (payload, (live, z)))), payload.sigma)
      | .inr (.inr _) => none)
      (show (x.time, x.row) = (y.time, y.row) from Prod.ext htime hrow)
  simp only [ReferenceLaterCollectionReadoutDomain.observableReadoutGuard,
    ReferenceLaterCollectionReadoutDomain.preparedFollowerTag,
    ReferenceActivePhysicalStepMeasurability.preparedFollowerCode,
    ReferenceLaterCollectionReadoutDomain.canonicalCollectionTag,
    ReferenceCollectionOutcomeMeasurability.canonicalCollectionFullObservation,
    hlive, hstate, htime, hrow]

private theorem sourceCell_eq_of_view
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (left right : RoundRecord (p := p) (rate := rate))
    (lv rv : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (hv : lv = rv)
    (ls rs : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (hstates : ls = rs)
    (lc : CoordinatorLocalArmChoice.ChoiceInputsValid lv.payload lv.cutoff
      left.input.time lv.complementWeights)
    (rc : CoordinatorLocalArmChoice.ChoiceInputsValid rv.payload rv.cutoff
      right.input.time rv.complementWeights)
    (htime : left.input.time = right.input.time)
    (hrow : left.input.row = right.input.row)
    (hrewards : left.input.rewards = right.input.rewards) :
    ReferenceFirstWindowNumericalStream.sourceCell left lv.payload lv.pendingAtChoice
        ls lv.complementWeights lv.cutoff lc =
      ReferenceFirstWindowNumericalStream.sourceCell right rv.payload rv.pendingAtChoice
        rs rv.complementWeights rv.cutoff rc := by
  cases hv
  cases hstates
  simp only [ReferenceFirstWindowNumericalStream.sourceCell,
    ReferenceFirstWindowNumericalStream.sourceArm, htime, hrow, hrewards]

private theorem live_readout_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (left right : RoundRecord (p := p) (rate := rate))
    (hstate : left.input.state = right.input.state)
    (htime : left.input.time = right.input.time)
    (hrow : left.input.row = right.input.row)
    (hrewards : left.input.rewards = right.input.rewards)
    (hcode : roundRecordCode left = roundRecordCode right) :
    ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 left =
      ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 right := by
  have hview : left.output.preparation.coordinator.downView =
      right.output.preparation.coordinator.downView := by
    rw [left.output.preparation.coordinator_eq, right.output.preparation.coordinator_eq]
    rw [← (roundRecordCode_front left).2.1, ← (roundRecordCode_front right).2.1, hcode]
  have hprepared := prepared_configuration_eq rate left right hstate htime hrow
  have ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary left ↔
      ReferenceLaterLiveNumericalReadout.preparedOrdinary right := by
    simp only [ReferenceLaterLiveNumericalReadout.preparedOrdinary, hprepared]
  unfold ReferenceActivePhysicalStep.DispatchCut.downView at hview
  unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
  cases hl : left.output.preparation.coordinator.selection with
  | none =>
      cases hr : right.output.preparation.coordinator.selection with
      | none => rfl
      | some selected => simp only [hl, hr, Option.map_none, Option.map_some,
          reduceCtorEq] at hview
  | some l =>
      cases hr : right.output.preparation.coordinator.selection with
      | none => simp only [hl, hr, Option.map_none, Option.map_some,
          reduceCtorEq] at hview
      | some r =>
          have hv : l.view = r.view := by
            simpa only [hl, hr, Option.map_some, Option.some.injEq] using hview
          have hc : (0 < l.view.payload.sigma.val ∧
              CoordinatorLocalArmChoice.assignmentIsLive l.view.payload
                l.view.cutoff left.input.time) ↔
              (0 < r.view.payload.sigma.val ∧
              CoordinatorLocalArmChoice.assignmentIsLive r.view.payload
                r.view.cutoff right.input.time) := by rw [hv, htime]
          dsimp only
          by_cases hcl : 0 < l.view.payload.sigma.val ∧
              CoordinatorLocalArmChoice.assignmentIsLive l.view.payload l.view.cutoff left.input.time
          · have hcr := hc.mp hcl
            simp only [ite_eq_left hcl, ite_eq_left hcr]
            by_cases hol : ReferenceLaterLiveNumericalReadout.preparedOrdinary left
            · have hor := ho.mp hol
              simp only [dite_eq_left hol, dite_eq_left hor]
              congr 1
              apply sourceCell_eq_of_view rate left right l.view r.view hv
                _ _ _ _ _ htime hrow hrewards
              funext i
              have hordinary :=
                (ReferenceLaterLiveNumericalReadout.prepared_configuration left hol i).symm.trans
                  ((hprepared i).trans
                    (ReferenceLaterLiveNumericalReadout.prepared_configuration right hor i))
              exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hordinary).1
            · have hor : ¬ ReferenceLaterLiveNumericalReadout.preparedOrdinary right :=
                fun h => hol (ho.mpr h)
              simp only [dite_eq_right hol, dite_eq_right hor]
          · have hcr : ¬ (0 < r.view.payload.sigma.val ∧
                CoordinatorLocalArmChoice.assignmentIsLive r.view.payload r.view.cutoff right.input.time) :=
              fun h => hcl (hc.mpr h)
            simp only [ite_eq_right hcl, ite_eq_right hcr]

private theorem numericalCoordinates_injective :
    Function.Injective
      (ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates
        (p := p)) := by
  intro a b h
  rcases a with ⟨ae, aa, aw, ar, _, _, _⟩
  rcases b with ⟨be, ba, bw, br, _, _, _⟩
  simp only [ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates,
    Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩
  rfl

private theorem collection_readout_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (left right : RoundRecord (p := p) (rate := rate))
    (hstate : left.input.state = right.input.state)
    (htime : left.input.time = right.input.time)
    (hrow : left.input.row = right.input.row)
    (hrewards : left.input.rewards = right.input.rewards)
    (hcode : roundRecordCode left = roundRecordCode right) :
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 left =
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 right := by
  have hg : (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 left).isSome = true ↔
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 right).isSome = true := by
    rw [ReferenceLaterCollectionReadoutDomain.readout_isSome_iff,
      ReferenceLaterCollectionReadoutDomain.readout_isSome_iff]
    exact collection_guard_iff rate left.input right.input hstate htime hrow
  apply Option.map_injective numericalCoordinates_injective
  rw [ReferenceLaterCollectionSourceReadoutMeasurability.readout_numerical_factorization
      (s := 0) (record := left),
    ReferenceLaterCollectionSourceReadoutMeasurability.readout_numerical_factorization
      (s := 0) (record := right),
    hcode, hrewards, htime]
  exact if_congr hg rfl rfl

private theorem cell0_eq_of_record_code
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (left right : RoundRecord (p := p) (rate := rate))
    (hstate : left.input.state = right.input.state)
    (htime : left.input.time = right.input.time)
    (hrow : left.input.row = right.input.row)
    (hrewards : left.input.rewards = right.input.rewards)
    (hcode : roundRecordCode left = roundRecordCode right) :
    ReferenceFirstCollectionCurrentRetainedGate.cell0 rate left =
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate right := by
  unfold ReferenceFirstCollectionCurrentRetainedGate.cell0
  rw [live_readout_eq rate left right hstate htime hrow hrewards hcode,
    collection_readout_eq rate left right hstate htime hrow hrewards hcode]

private theorem selectedRowIndex_eq_right
    (z z' : SourceInput p) (j : Fin (M p))
    (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j) :
    ActualInitializationPhysicalStep.selectedRowIndex p z' = j := by
  have hscalar : z.2.1.2 = z'.2.1.2 := congrArg (fun e => e.1.2) hprivate
  change PrivateSourceStreams.coordinatorIndex p z'.2.1.2 = j
  rw [← hscalar]
  exact hJ

/-- The actual option-valued prefix inputs are invariant when the complete
selected row, public IDs, and all original private data are fixed. -/
public theorem prefixInputs_eq_of_source_data
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ)
    (z z' : SourceInput p) (j : Fin (M p))
    (hids : z.1.1 = z'.1.1) (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j)
    (hrow : z.1.2 j = z'.1.2 j) :
    prefixInputs rate rewards C_star C_h n z =
      prefixInputs rate rewards C_star C_h n z' := by
  classical
  obtain ⟨_hinput, hboundary, _hlaunch⟩ :=
    ReferenceCompletePhysicalHistory.generatedInput_and_launch_eq_of_source_data
      rate z z' rewards C_star C_h j hids hprivate hJ hrow
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h =
      ReferenceCompletePhysicalHistory.physicalStart rate z' rewards C_star C_h := by
    exact congrArg (fun boundary : ReferenceInitializationRun.Boundary p =>
      ReferenceInitializationRun.elapsed p boundary.completed) hboundary
  have hlaunchBy :
      ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h n z ↔
        ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h n z' := by
    unfold ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
    rw [hboundary, hstart]
  have hcodes := ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode_eq_of_source_data
    (rate := rate) rewards C_star C_h z z' j hids hprivate hJ hrow
  have hlen : (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z' rewards C_star C_h).length := by
    have hc := congrArg List.length hcodes
    simpa only [ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode,
      List.length_map] using hc
  by_cases hl : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h n z
  · have hl' := hlaunchBy.mp hl
    let count := n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let leftRecords := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h
    let rightRecords := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z' rewards C_star C_h
    have hslots : (leftRecords.take count).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) =
        (rightRecords.take count).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) := by
      have hslotsLen : ((leftRecords.take count).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).length =
          ((rightRecords.take count).map
            (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).length := by
        simp only [List.length_map, List.length_take, leftRecords, rightRecords]
        rw [hlen]
      apply List.ext_getElem hslotsLen
      intro k hkL hkR
      have hkLeft : k < leftRecords.length := by
        have h := hkL
        simp only [List.length_map, List.length_take] at h
        omega
      have hkRight : k < rightRecords.length := by
        have h := hkR
        simp only [List.length_map, List.length_take] at h
        omega
      have hkCodeL : k < (ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
          (rate := rate) rewards C_star C_h z).length := by
        simpa only [ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode,
          List.length_map] using hkLeft
      have hkCodeR : k < (ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
          (rate := rate) rewards C_star C_h z').length := by
        simpa only [ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode,
          List.length_map] using hkRight
      let leftRecord := leftRecords.get ⟨k, hkLeft⟩
      let rightRecord := rightRecords.get ⟨k, hkRight⟩
      have hcode : roundRecordCode leftRecord = roundRecordCode rightRecord := by
        have h := congrArg (fun codes => codes[k]?) hcodes
        have hL : (ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
            (rate := rate) rewards C_star C_h z)[k]? = some (roundRecordCode leftRecord) := by
          rw [List.getElem?_eq_getElem hkCodeL]
          simp [ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode,
            List.getElem_map, List.get_eq_getElem, leftRecord, leftRecords]
        have hR : (ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
            (rate := rate) rewards C_star C_h z')[k]? = some (roundRecordCode rightRecord) := by
          rw [List.getElem?_eq_getElem hkCodeR]
          simp [ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode,
            List.getElem_map, List.get_eq_getElem, rightRecord, rightRecords]
        rw [hL, hR] at h
        exact Option.some.inj h
      have hfieldsL := ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt_fields
        rate rewards C_star C_h k ⟨z, hkLeft⟩
      have hfieldsR := ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt_fields
        rate rewards C_star C_h k ⟨z', hkRight⟩
      have hencoded : ReferenceActivePhysicalStepMeasurability.encodeState
          leftRecord.input.state =
          ReferenceActivePhysicalStepMeasurability.encodeState rightRecord.input.state := by
        have hL : ReferenceActivePhysicalStepMeasurability.encodeState leftRecord.input.state =
            (roundRecordCode leftRecord).2.1 := by
          simp only [leftRecord, leftRecords,
            ReferenceCompletePhysicalHistory.completeSuffixRecords,
            ReferenceActiveHorizonMeasurability.roundRecordCode]
        have hR : ReferenceActivePhysicalStepMeasurability.encodeState rightRecord.input.state =
            (roundRecordCode rightRecord).2.1 := by
          simp only [rightRecord, rightRecords,
            ReferenceCompletePhysicalHistory.completeSuffixRecords,
            ReferenceActiveHorizonMeasurability.roundRecordCode]
        rw [hL, hR, hcode]
      have hstate := ReferenceActivePhysicalStepMeasurability.encodeState_injective hencoded
      have htime : leftRecord.input.time = rightRecord.input.time := by
        apply Fin.ext
        have hL : leftRecord.input.time.val = (roundRecordCode leftRecord).1 := by
          simp only [leftRecord, leftRecords,
            ReferenceCompletePhysicalHistory.completeSuffixRecords,
            ReferenceActiveHorizonMeasurability.roundRecordCode]
        have hR : rightRecord.input.time.val = (roundRecordCode rightRecord).1 := by
          simp only [rightRecord, rightRecords,
            ReferenceCompletePhysicalHistory.completeSuffixRecords,
            ReferenceActiveHorizonMeasurability.roundRecordCode]
        rw [hL, hR, hcode]
      have hJ' := selectedRowIndex_eq_right z z' j hprivate hJ
      have hrowsL : leftRecord.input.rows = z.1.2 := by
        simpa only [ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt,
          leftRecord, leftRecords, List.get_eq_getElem] using hfieldsL.1
      have hselectedL : leftRecord.input.selected = j := by
        simpa only [ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt,
          leftRecord, leftRecords, List.get_eq_getElem] using hfieldsL.2.1.trans hJ
      have hrowsR : rightRecord.input.rows = z'.1.2 := by
        simpa only [ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt,
          rightRecord, rightRecords, List.get_eq_getElem] using hfieldsR.1
      have hselectedR : rightRecord.input.selected = j := by
        simpa only [ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt,
          rightRecord, rightRecords, List.get_eq_getElem] using hfieldsR.2.1.trans hJ'
      have hrowRecords : leftRecord.input.row = rightRecord.input.row := by
        change leftRecord.input.rows leftRecord.input.selected =
          rightRecord.input.rows rightRecord.input.selected
        rw [hrowsL, hselectedL, hrowsR, hselectedR]
        exact hrow
      have hrewards : leftRecord.input.rewards = rightRecord.input.rewards := by
        exact hfieldsL.2.2.1.trans hfieldsR.2.2.1.symm
      have hcell := cell0_eq_of_record_code rate leftRecord rightRecord
        hstate htime hrowRecords hrewards hcode
      simpa [leftRecords, rightRecords, leftRecord, rightRecord] using hcell
    unfold prefixInputs
    rw [ite_eq_left hl, ite_eq_left hl']
    simp only [sourceStart, hstart.symm]
    change List.mapM id ((leftRecords.take count).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)) =
      List.mapM id ((rightRecords.take count).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate))
    rw [hslots]
  · have hl' : ¬ ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h n z' := fun h => hl (hlaunchBy.mpr h)
    simp [prefixInputs, hl, hl']

public theorem prefixReadout_eq_of_source_data
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ)
    (z z' : SourceInput p) (j : Fin (M p))
    (hids : z.1.1 = z'.1.1) (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j)
    (hrow : z.1.2 j = z'.1.2 j) :
    prefixReadout rate rewards C_star C_h n z =
      prefixReadout rate rewards C_star C_h n z' := by
  unfold prefixReadout
  rw [prefixInputs_eq_of_source_data rate rewards C_star C_h n z z' j
    hids hprivate hJ hrow]

public theorem prefixReadout_eq_on_selectedRow_update
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ)
    (ids : CompletePublicTable.IDArray p)
    (rows otherRows : CompletePublicTable.CompleteRows p)
    (j : Fin (M p)) (rho : CompletePublicTable.CompleteRow p)
    (e : ExtendedPrivateCoordinates p)
    (hJ : PrivateSourceStreams.coordinatorIndex p e.1.2 = j) :
    prefixReadout rate rewards C_star C_h n ((ids, Function.update rows j rho), e) =
      prefixReadout rate rewards C_star C_h n
        ((ids, Function.update otherRows j rho), e) := by
  apply prefixReadout_eq_of_source_data rate rewards C_star C_h n
    ((ids, Function.update rows j rho), e)
    ((ids, Function.update otherRows j rho), e) j
  · rfl
  · rfl
  · exact hJ
  · simp

local notation "Readout" =>
  ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K

local instance sourceInputMeasurableSpace : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionReadoutMeasurableSpace : MeasurableSpace (Option Readout) :=
  ReferenceInitializationMeasurability.optionCountableMeasurableSpace Readout

local instance optionReadoutMeasurableSingleton :
    MeasurableSingletonClass (Option Readout) :=
  ReferenceInitializationMeasurability.optionCountableMeasurableSingletonClass Readout

/-- The first numerical overflow transition is the actual consecutive pair of
optional readouts.  Its post observation is at `t + 1`, after that update. -/
public theorem measurableSet_prefixReadout_firstFlagTransition
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :
    MeasurableSet {z : SourceInput p |
      ∃ pre post : Readout,
        prefixReadout rate rewards C_star C_h t.val z = some pre ∧
        pre.2.1 = false ∧
        prefixReadout rate rewards C_star C_h (t.val + 1) z = some post ∧
        post.2.1 = true} := by
  have hpre : Measurable (prefixReadout rate rewards C_star C_h t.val) :=
    ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_prefixReadout
      rate rewards C_star C_h t.val
  have hpost : Measurable (prefixReadout rate rewards C_star C_h (t.val + 1)) :=
    ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_prefixReadout
      rate rewards C_star C_h (t.val + 1)
  have hrepr :
      {z : SourceInput p | ∃ pre post : Readout,
        prefixReadout rate rewards C_star C_h t.val z = some pre ∧
        pre.2.1 = false ∧
        prefixReadout rate rewards C_star C_h (t.val + 1) z = some post ∧
        post.2.1 = true} =
      ⋃ pre : Readout, ⋃ post : Readout,
        if pre.2.1 = false ∧ post.2.1 = true then
          {z : SourceInput p | prefixReadout rate rewards C_star C_h t.val z = some pre} ∩
            {z : SourceInput p | prefixReadout rate rewards C_star C_h (t.val + 1) z = some post}
        else ∅ := by
    ext z
    constructor
    · rintro ⟨pre, post, hprez, hpref, hpostz, hpostf⟩
      simp only [Set.mem_iUnion]
      refine ⟨pre, post, ?_⟩
      simp [hpref, hpostf, hprez, hpostz]
    · intro hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨pre, post, hz⟩ := hz
      by_cases hflags : pre.2.1 = false ∧ post.2.1 = true
      · simp only [ite_eq_left hflags, Set.mem_inter_iff] at hz
        exact ⟨pre, post, hz.1, hflags.1, hz.2, hflags.2⟩
      · simp only [ite_eq_right hflags, Set.mem_empty_iff_false] at hz
  rw [hrepr]
  apply MeasurableSet.iUnion
  intro pre
  apply MeasurableSet.iUnion
  intro post
  by_cases hflags : pre.2.1 = false ∧ post.2.1 = true
  · simp only [ite_eq_left hflags]
    exact (hpre (MeasurableSet.singleton (some pre))).inter
      (hpost (MeasurableSet.singleton (some post)))
  · simp only [ite_eq_right hflags]
    exact MeasurableSet.empty

end Bandits.Support.ReferenceCompletePrefixReadoutRowLocality

end
