/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveSourceSavedMoments
public import Bandits.Support.ReferenceSourcePhysicalFlagConditionalLaw

import Lean.Elab.Tactic.Omega

/-!
# Actual strict-past numerical prefix consistency

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,256-264`,
`sources/zip4/manuscript/06_interruptions.tex:391-397,425-426`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

This module compares the numerical inputs actually produced by the first-live
physical records on an original source and on its literal strict control
prefix. It retains the variable first-cutoff convention and compares only
computed numerical inputs when complete source rows differ. It does not make
a conditional-law claim or identify an authentic history.
-/

@[expose] public section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.RecordedQueueRun
open scoped Classical
open Bandits.Support.ReferenceFirstLiveRecordingSourceCylinder
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open Bandits.Support.CoordinatorLocalArmChoice

namespace Bandits.Support.ReferenceFirstLiveNumericalPrefixTemporal

private theorem sourceArm_congr
    {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}
    {record : ReferenceFirstWindowNumericalStream.RoundRecord (p := p) (rate := rate)}
    (left right : ReferenceActivePhysicalStep.Selection record.input)
    (hselected : left = right)
    (statesLeft statesRight : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (hstates : statesLeft = statesRight)
    (hvalidLeft : CoordinatorLocalArmChoice.ChoiceInputsValid left.view.payload left.view.cutoff
      record.input.time left.view.complementWeights)
    (hvalidRight : CoordinatorLocalArmChoice.ChoiceInputsValid right.view.payload right.view.cutoff
      record.input.time right.view.complementWeights) :
    ReferenceFirstWindowNumericalStream.sourceArm record left.view.payload
      left.view.pendingAtChoice statesLeft left.view.complementWeights left.view.cutoff hvalidLeft =
    ReferenceFirstWindowNumericalStream.sourceArm record right.view.payload
      right.view.pendingAtChoice statesRight right.view.complementWeights right.view.cutoff hvalidRight := by
  cases hselected
  cases hstates
  rfl

private theorem roundInput_ext {K : ℕ} (left right : RecordedQueueRun.RoundInput K)
    (henabled : left.enabled = right.enabled)
    (harm : left.recordedArm = right.recordedArm)
    (hreward : left.reward = right.reward)
    (hrate : left.rate = right.rate) :
    left = right := by
  cases left
  cases right
  simp_all

/-- The numerical input is independent of the witness chosen for the same actual record. -/
theorem actualLiveSourceCell_input_unique
    {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}
    {record : ReferenceFirstWindowNumericalStream.RoundRecord (p := p) (rate := rate)}
    (a b : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record) :
    a.input = b.input := by
  have hselected : a.selected = b.selected :=
    Option.some.inj (a.selection_actual.symm.trans b.selection_actual)
  have hstates : a.states = b.states := by
    funext i
    have hconfig := (a.ordinary i).symm.trans (b.ordinary i)
    have hstate : a.states i = b.states i := by
      injection hconfig with hstate _
    exact hstate
  have harm := sourceArm_congr a.selected b.selected hselected a.states b.states hstates
    a.choiceInputsValid b.choiceInputsValid
  have hrate : a.selected.view.payload.rate = b.selected.view.payload.rate :=
    congrArg (fun selected => selected.view.payload.rate) hselected
  calc
    a.input = ReferenceFirstWindowNumericalStream.sourceCell record a.selected.view.payload
        a.selected.view.pendingAtChoice a.states a.selected.view.complementWeights
        a.selected.view.cutoff a.choiceInputsValid := a.input_eq
    _ = ReferenceFirstWindowNumericalStream.sourceCell record b.selected.view.payload
        b.selected.view.pendingAtChoice b.states b.selected.view.complementWeights
        b.selected.view.cutoff b.choiceInputsValid := by
          unfold ReferenceFirstWindowNumericalStream.sourceCell
          apply roundInput_ext
          · rfl
          · exact harm
          · rfl
          · exact hrate
    _ = b.input := b.input_eq.symm

private theorem actualCellInput_eq_of_record_eq
    {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}
    {leftRecord rightRecord : ReferenceFirstWindowNumericalStream.RoundRecord
      (p := p) (rate := rate)}
    (hrecord : leftRecord = rightRecord)
    (left : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell leftRecord)
    (right : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell rightRecord) :
    left.input = right.input := by
  cases hrecord
  exact actualLiveSourceCell_input_unique left right

private theorem run_records_take_successor
    {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      (count + 1) hspan hmode).records.take count =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        (by omega) hmode).records := by
  rw [ReferenceActivePhysicalHorizon.run_successor_step]
  simp only [ReferenceActivePhysicalHorizon.foldRound]
  have hlen := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
    rewards start count (by omega) hmode
  have hle : count ≤ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      count (by omega) hmode).records.length := by
    exact le_of_eq hlen.symm
  rw [List.take_append_of_le_length hle]
  exact List.take_of_length_le (le_of_eq hlen)

private theorem firstLiveWindow_record_eq_actualRunRecordAt
    {p : ConstructorDimensions.Parameters} (rate : ReferenceActivePhysicalStep.RateInput p)
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (k : ℕ) (hkcount : k < count)
    (hkwindow : k < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records).length) :
    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records)[k] =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selected rewards start k
        (by omega) hmode := by
  let E := ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  have hwindowPrefix : W.IsPrefix E.records := List.takeWhile_prefix _
  have hkE : k < E.records.length := lt_of_lt_of_le hkwindow hwindowPrefix.length_le
  have hwindowElem : W[k] = E.records[k] := hwindowPrefix.getElem hkwindow
  have htimeMap := ReferenceActivePhysicalHorizon.run_time_values
    initial rows selected rewards start count hspan hmode
  have hkMap : k < (E.records.map (fun record => record.input.time.val)).length := by
    simpa [E] using hkE
  have htimeElem :
      (E.records.map (fun record => record.input.time.val))[k] = W[k].input.time.val := by
    calc
      (E.records.map (fun record => record.input.time.val))[k] = E.records[k].input.time.val := by
        simp
      _ = W[k].input.time.val := by rw [← hwindowElem]
  have htimeMap' : E.records.map (fun record => record.input.time.val) =
      ReferenceActivePhysicalHorizon.calendar start count := by
    simpa [E] using htimeMap
  have hkcalendar : k < (ReferenceActivePhysicalHorizon.calendar start count).length := by
    simpa [ReferenceActivePhysicalHorizon.calendar] using hkcount
  have hcalendar :
      (ReferenceActivePhysicalHorizon.calendar start count)[k]'hkcalendar = start + k := by
    simp [ReferenceActivePhysicalHorizon.calendar]
  have hwindowTime : W[k].input.time.val = start + k := by
    calc
      W[k].input.time.val = (E.records.map (fun record => record.input.time.val))[k] := htimeElem.symm
      _ = (ReferenceActivePhysicalHorizon.calendar start count)[k] := by
        exact List.getElem_of_eq htimeMap' hkMap
      _ = start + k := hcalendar
  let next := ReferenceActivePhysicalHorizon.run initial rows selected rewards start
    (k + 1) (by omega) hmode
  let actual := ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selected
    rewards start k (by omega) hmode
  have hnextPrefix : ∃ suffix, E.records = next.records ++ suffix := by
    obtain ⟨suffix, hrecords⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
      initial rows selected rewards start (k + 1) (count - (k + 1)) (by omega) hmode
    refine ⟨suffix, ?_⟩
    simpa [E, next, Nat.add_sub_of_le (show k + 1 ≤ count by omega)] using hrecords
  obtain ⟨suffix, hrecords⟩ := hnextPrefix
  have hsuccessor := ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
    initial rows selected rewards start k (by omega) hmode
  have hactualMemNext : actual ∈ next.records := by
    change actual ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      (k + 1) (by omega) hmode).records
    rw [hsuccessor]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hactualMemE : actual ∈ E.records := by
    rw [hrecords]
    exact List.mem_append_left _ hactualMemNext
  have hwindowMemE : W[k] ∈ E.records := by
    rw [hwindowElem]
    exact List.getElem_mem hkE
  have hactualTime : actual.input.time.val = start + k := rfl
  exact ReferenceAssignmentPayloadChronology.run_records_time_injective
    initial rows selected rewards start count hspan hmode hwindowMemE hactualMemE
    (hwindowTime.trans hactualTime.symm)

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p))
  (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
  (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)
local notation "n" => t.val - s

private def liveCutoffTag
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (row : CompletePublicTable.CompleteRow p)
    (out : CoordinatorRoundDispatch.LiveOutcome
      { eta := rate.eta, registers := r, ownedRegisters := owned,
        followerBaseScore := base, row := row }) : Bool :=
  match out with
  | .cutoffChosen _ _ _ _ _ _ _ _ _ _ => true
  | _ => false

private theorem liveCutoffTag_eq_projection
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (row : CompletePublicTable.CompleteRow p)
    (out : CoordinatorRoundDispatch.LiveOutcome
      { eta := rate.eta, registers := r, ownedRegisters := owned,
        followerBaseScore := base, row := row }) :
    liveCutoffTag rate r owned base row out =
      (match (ReferenceActiveDispatchTemporal.liveOutcomeData r owned base row out).2.2 with
      | .inr (.inr (.inr _)) => true
      | _ => false) := by
  cases out <;> rfl

private theorem cutoffChosen_live
    (input : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hphase : input.state.coordinator = .live r owned base) :
    ReferenceCollectionPhaseHistory.cutoffChosen input =
      liveCutoffTag rate (ReferenceActivePhysicalStep.liveRegistersAt r input.time)
        (ReferenceActivePhysicalStep.liveOwnedAt r owned input.time) base input.row
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput input r owned base)) := by
  dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen,
    ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
  simp only [hphase, CoordinatorRoundDispatch.dispatch]
  cases CoordinatorRoundDispatch.dispatchLive
    (ReferenceActivePhysicalStep.liveInput input r owned base) <;> rfl

private theorem cutoffChosen_eq_of_current
    (state : ReferenceActivePhysicalStep.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p)
    (selected otherSelected : Fin (M p)) (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards otherRewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (hcurrent : (rows selected).2 time = (otherRows otherSelected).2 time) :
    ReferenceCollectionPhaseHistory.cutoffChosen
        ⟨state, rows, selected, time, active, rewards⟩ =
      ReferenceCollectionPhaseHistory.cutoffChosen
        ⟨state, otherRows, otherSelected, time, active, otherRewards⟩ := by
  classical
  cases hphase : state.coordinator with
  | first =>
      dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen,
        ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
      simp only [hphase, CoordinatorRoundDispatch.dispatch]
      rfl
  | live r owned base =>
      have hdata := ReferenceActiveDispatchTemporal.liveOutcomeData_eq_of_current
        (ReferenceActivePhysicalStep.liveRegistersAt r time)
        (ReferenceActivePhysicalStep.liveOwnedAt r owned time) base
        (rows selected) (otherRows otherSelected) hcurrent
      have htag := congrArg (fun data =>
        match data.2.2 with
        | .inr (.inr (.inr _)) => true
        | _ => false) hdata
      rw [← liveCutoffTag_eq_projection rate, ← liveCutoffTag_eq_projection rate] at htag
      rw [cutoffChosen_live rate _ r owned base hphase,
        cutoffChosen_live rate _ r owned base hphase]
      simpa only [ReferenceActivePhysicalStep.liveInput,
        ReferenceActivePhysicalStep.RoundInput.row, liveCutoffTag] using htag
  | collection payload ledger proposal =>
      dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen,
        ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
      simp only [hphase]
      by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [dite_eq_left hc, CoordinatorRoundDispatch.dispatch]
        rfl
      · simp only [dite_eq_right hc]
  | dagger =>
      dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen,
        ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
      simp only [hphase]

private theorem cutoffChosen_congr (left right : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : left.state = right.state) (htime : left.time = right.time)
    (hcurrent : left.row.2 left.time = right.row.2 right.time) :
    ReferenceCollectionPhaseHistory.cutoffChosen left =
      ReferenceCollectionPhaseHistory.cutoffChosen right := by
  cases left
  cases right
  dsimp only at hstate htime hcurrent
  cases hstate
  cases htime
  exact cutoffChosen_eq_of_current rate _ _ _ _ _ _ _ _ _ hcurrent

private theorem dispatch_downView_eq_of_current
    (state : ReferenceActivePhysicalStep.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (time : Fin p.T) (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards otherRewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (hcurrent : (rows selected).2 time = (otherRows selected).2 time) :
    let x : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, rows, selected, time, active, rewards⟩
    let y : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, otherRows, selected, time, active, otherRewards⟩
    (ReferenceActivePhysicalStep.dispatch x).downView =
      (ReferenceActivePhysicalStep.dispatch y).downView := by
  let x : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, rows, selected, time, active, rewards⟩
  let y : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, otherRows, selected, time, active, otherRewards⟩
  change (ReferenceActivePhysicalStep.dispatch x).downView =
    (ReferenceActivePhysicalStep.dispatch y).downView
  cases hphase : state.coordinator with
  | first =>
      have hpair := ReferenceActiveTemporalCausality.first_dispatch_projections_eq_of_current
        state rows otherRows selected active rewards otherRewards hphase hcurrent
      exact congrArg Prod.snd hpair
  | live r owned base =>
      have hdata := ReferenceActiveDispatchTemporal.live_dispatch_data_eq_of_current
        state rows otherRows selected time active rewards otherRewards r owned base hphase hcurrent
      exact congrArg (fun data => data.2.1) hdata
  | collection payload ledger proposal =>
      have hdata := ReferenceActiveDispatchTemporal.collection_dispatch_data_eq_of_current
        state rows otherRows selected time active rewards otherRewards payload ledger proposal
        hphase hcurrent
      exact congrArg (fun data => data.2.1) hdata
  | dagger =>
      rw [ReferenceActivePhysicalStep.dispatch_dagger x hphase,
        ReferenceActivePhysicalStep.dispatch_dagger y hphase]
      rfl

private theorem dispatch_downView_eq_of_roundInputs
    (left right : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : left.state = right.state) (hselected : left.selected = right.selected)
    (htime : left.time = right.time)
    (hcurrent : left.row.2 left.time = right.row.2 right.time) :
    (ReferenceActivePhysicalStep.dispatch left).downView =
      (ReferenceActivePhysicalStep.dispatch right).downView := by
  cases left with
  | mk leftState leftRows leftSelected leftTime leftActive leftRewards =>
    cases right with
    | mk rightState rightRows rightSelected rightTime rightActive rightRewards =>
      dsimp only at hstate hselected htime hcurrent
      cases hstate
      cases hselected
      cases htime
      exact dispatch_downView_eq_of_current rate leftState leftRows rightRows
        leftSelected leftTime leftActive leftRewards rightRewards hcurrent

private theorem prepare_configuration_eq_of_roundInputs
    (left right : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : left.state = right.state) (hselected : left.selected = right.selected)
    (htime : left.time = right.time)
    (hcurrent : left.row.2 left.time = right.row.2 right.time)
    (i : Fin (p.m - 1)) :
    ((ReferenceActivePhysicalStep.prepare left).followers.followers i).configuration =
      ((ReferenceActivePhysicalStep.prepare right).followers.followers i).configuration := by
  cases left with
  | mk leftState leftRows leftSelected leftTime leftActive leftRewards =>
    cases right with
    | mk rightState rightRows rightSelected rightTime rightActive rightRewards =>
      dsimp only at hstate hselected htime hcurrent
      cases hstate
      cases hselected
      cases htime
      have hproj := ReferenceActiveTemporalCausality.prepare_projections_eq_of_current
        (row := leftRows leftSelected) (otherRow := rightRows leftSelected) (t := leftTime)
        i (leftState.activations i) (leftActive i) (leftState.followers i) hcurrent
      exact congrArg Prod.snd hproj

private theorem sourceArm_eq_of_view_eq
    {recordLeft recordRight : ReferenceFirstWindowNumericalStream.RoundRecord
      (p := p) (rate := rate)}
    (leftView rightView : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (hview : leftView = rightView)
    (leftStates rightStates : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (hstates : leftStates = rightStates)
    (leftValid : CoordinatorLocalArmChoice.ChoiceInputsValid leftView.payload leftView.cutoff
      recordLeft.input.time leftView.complementWeights)
    (rightValid : CoordinatorLocalArmChoice.ChoiceInputsValid rightView.payload rightView.cutoff
      recordRight.input.time rightView.complementWeights)
    (hcurrent : (recordLeft.input.row.2 recordLeft.input.time) =
      (recordRight.input.row.2 recordRight.input.time)) :
    ReferenceFirstWindowNumericalStream.sourceArm recordLeft leftView.payload
      leftView.pendingAtChoice leftStates leftView.complementWeights leftView.cutoff leftValid =
    ReferenceFirstWindowNumericalStream.sourceArm recordRight rightView.payload
      rightView.pendingAtChoice rightStates rightView.complementWeights rightView.cutoff rightValid := by
  have hrow : (recordLeft.input.row.2 recordLeft.input.time).1 =
      (recordRight.input.row.2 recordRight.input.time).1 := congrArg Prod.fst hcurrent
  cases hstates
  have hassignment : leftView.payload.assignment = rightView.payload.assignment :=
    congrArg (fun view => view.payload.assignment) hview
  have hpending : leftView.pendingAtChoice = rightView.pendingAtChoice :=
    congrArg (fun view => view.pendingAtChoice) hview
  have hanchor : leftView.payload.anchor = rightView.payload.anchor :=
    congrArg (fun view => view.payload.anchor) hview
  have hweights :
      ReferenceFirstWindowNumericalStream.sourceWeights leftView.payload leftView.complementWeights =
        ReferenceFirstWindowNumericalStream.sourceWeights rightView.payload rightView.complementWeights :=
    congrArg (fun view => ReferenceFirstWindowNumericalStream.sourceWeights
      view.payload view.complementWeights) hview
  have hregime : SnapshotRecordingKernel.Regime.live leftView.payload.assignment
      { missing := leftView.pendingAtChoice, status := fun i => (leftStates i).status } =
    SnapshotRecordingKernel.Regime.live rightView.payload.assignment
      { missing := rightView.pendingAtChoice, status := fun i => (leftStates i).status } := by
    rw [hassignment, hpending]
  unfold ReferenceFirstWindowNumericalStream.sourceArm
  simp [hregime, hanchor, hweights, hrow]

private theorem actualCell_input_eq_of_current
    {recordLeft recordRight : ReferenceFirstWindowNumericalStream.RoundRecord
      (p := p) (rate := rate)}
    (left : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell recordLeft)
    (right : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell recordRight)
    (hstate : recordLeft.input.state = recordRight.input.state)
    (hselected : recordLeft.input.selected = recordRight.input.selected)
    (htime : recordLeft.input.time = recordRight.input.time)
    (hrewards : recordLeft.input.rewards = recordRight.input.rewards)
    (hcurrent : recordLeft.input.row.2 recordLeft.input.time =
      recordRight.input.row.2 recordRight.input.time) :
    left.input = right.input := by
  have hdispatch :
      (ReferenceActivePhysicalStep.dispatch recordLeft.input).downView =
        (ReferenceActivePhysicalStep.dispatch recordRight.input).downView := by
    exact dispatch_downView_eq_of_roundInputs rate recordLeft.input recordRight.input
      hstate hselected htime hcurrent
  have hdown : recordLeft.output.preparation.coordinator.downView =
      recordRight.output.preparation.coordinator.downView := by
    rw [recordLeft.output_eq, recordRight.output_eq]
    exact hdispatch
  have hleftView : recordLeft.output.preparation.coordinator.downView =
      some left.selected.view := by
    simp [ReferenceActivePhysicalStep.DispatchCut.downView, left.selection_actual]
  have hrightView : recordRight.output.preparation.coordinator.downView =
      some right.selected.view := by
    simp [ReferenceActivePhysicalStep.DispatchCut.downView, right.selection_actual]
  have hview : left.selected.view = right.selected.view :=
    Option.some.inj (hleftView.symm.trans (hdown.trans hrightView))
  have hstates : left.states = right.states := by
    funext i
    have hconfiguration := prepare_configuration_eq_of_roundInputs rate recordLeft.input
      recordRight.input hstate hselected htime hcurrent i
    have hconfiguration :
        (recordLeft.output.preparation.followers.followers i).configuration =
          (recordRight.output.preparation.followers.followers i).configuration := by
      rw [recordLeft.output_eq, recordRight.output_eq]
      exact hconfiguration
    have hordinary := (left.ordinary i).symm.trans
      (hconfiguration.trans (right.ordinary i))
    exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hordinary).1
  have harm := sourceArm_eq_of_view_eq rate left.selected.view right.selected.view hview
    left.states right.states hstates left.choiceInputsValid right.choiceInputsValid hcurrent
  have hrate : left.selected.view.payload.rate = right.selected.view.payload.rate :=
    congrArg (fun view => view.payload.rate) hview
  calc
    left.input = ReferenceFirstWindowNumericalStream.sourceCell recordLeft
        left.selected.view.payload left.selected.view.pendingAtChoice left.states
        left.selected.view.complementWeights left.selected.view.cutoff left.choiceInputsValid := left.input_eq
    _ = ReferenceFirstWindowNumericalStream.sourceCell recordRight
        right.selected.view.payload right.selected.view.pendingAtChoice right.states
        right.selected.view.complementWeights right.selected.view.cutoff right.choiceInputsValid := by
          unfold ReferenceFirstWindowNumericalStream.sourceCell
          apply roundInput_ext
          · rfl
          · exact harm
          · funext arm
            have hrewardAt : recordLeft.input.rewards recordLeft.input.time arm =
                recordRight.input.rewards recordRight.input.time arm := by
              calc
                _ = recordRight.input.rewards recordLeft.input.time arm :=
                  congrArg (fun table => table recordLeft.input.time arm) hrewards
                _ = recordRight.input.rewards recordRight.input.time arm := by
                  rw [← htime]
            change (((recordLeft.input.rewards recordLeft.input.time arm).val : ℝ) / (D p : ℝ)) =
              (((recordRight.input.rewards recordRight.input.time arm).val : ℝ) / (D p : ℝ))
            exact congrArg (fun reward => ((reward.val : ℝ) / (D p : ℝ))) hrewardAt
          · exact hrate
    _ = right.input := right.input_eq.symm

private theorem run_cutoffTags_eq
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hcontrols : ∀ j : Fin p.T, start ≤ j.val → j.val < start + count →
      (rows selected).2 j = (otherRows selected).2 j)
    (hbefore : ∀ j : Fin p.T, j.val < start →
      ((rows selected).2 j).1 ContinuousControlSlice.Label.prop =
        ((otherRows selected).2 j).1 ContinuousControlSlice.Label.prop) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.map
        (fun record => ReferenceCollectionPhaseHistory.cutoffChosen record.input) =
      (ReferenceActivePhysicalHorizon.run initial otherRows selected rewards start count hspan hmode).records.map
        (fun record => ReferenceCollectionPhaseHistory.cutoffChosen record.input) := by
  induction count with
  | zero =>
      rw [ReferenceActivePhysicalHorizon.run_zero_records,
        ReferenceActivePhysicalHorizon.run_zero_records]
  | succ count ih =>
      have hprefix : start + count ≤ p.T := by omega
      have hcontrolsPrefix : ∀ j : Fin p.T, start ≤ j.val → j.val < start + count →
          (rows selected).2 j = (otherRows selected).2 j := by
        intro j hj hk
        exact hcontrols j hj (by omega)
      have htags := ih hprefix hcontrolsPrefix
      have hstate := (ReferenceActiveTemporalAssembly.run_eq_of_temporal_reads initial
        rows otherRows selected rewards rewards start count hprefix hmode
        hcontrolsPrefix (fun _ _ _ => rfl) (fun _ => hbefore)).1
      rw [ReferenceActivePhysicalHorizon.run_successor_step,
        ReferenceActivePhysicalHorizon.run_successor_step]
      simp only [ReferenceActivePhysicalHorizon.foldRound, List.map_append,
        List.map_singleton]
      rw [htags]
      congr 1
      apply congrArg List.singleton
      apply cutoffChosen_congr
      · exact hstate
      · rfl
      · exact hcontrols ⟨start + count, by omega⟩ (by dsimp; omega) (by dsimp; omega)

private theorem run_cutoffTags_eq_of_initial_eq
    (initialLeft initialRight : ReferenceActivePhysicalHorizon.State p rate)
    (hinitial : initialLeft = initialRight)
    (rows otherRows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmodeLeft : ReferenceActivePhysicalHorizon.allActiveAtStart initialLeft start)
    (hmodeRight : ReferenceActivePhysicalHorizon.allActiveAtStart initialRight start)
    (hcontrols : ∀ j : Fin p.T, start ≤ j.val → j.val < start + count →
      (rows selected).2 j = (otherRows selected).2 j)
    (hbefore : ∀ j : Fin p.T, j.val < start →
      ((rows selected).2 j).1 ContinuousControlSlice.Label.prop =
        ((otherRows selected).2 j).1 ContinuousControlSlice.Label.prop) :
    (ReferenceActivePhysicalHorizon.run initialLeft rows selected rewards start count hspan hmodeLeft).records.map
        (fun record => ReferenceCollectionPhaseHistory.cutoffChosen record.input) =
      (ReferenceActivePhysicalHorizon.run initialRight otherRows selected rewards start count hspan hmodeRight).records.map
        (fun record => ReferenceCollectionPhaseHistory.cutoffChosen record.input) := by
  cases hinitial
  exact run_cutoffTags_eq rate initialLeft rows otherRows selected rewards start count
    hspan hmodeLeft hcontrols hbefore

theorem sourceStratum_facts (z : Z) :
    ActualInitializationPhysicalStep.selectedRowIndex p z.val = q ∧
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).crossing.isSome = true ∧
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed = s := by
  have hproperty := z.property
  change z.val ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
    (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) at hproperty
  change ReferenceRetainedSourceCoupling.retainedSourceEvent rate rewards C_star C_h q s z.val at hproperty
  rcases hproperty with ⟨hindex, hcross, hstart⟩
  exact ⟨(ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
    p z.val).symm.trans hindex, hcross, hstart⟩

/-- The literal strict control prefix of every original source point stays in
the same selected-row, crossing, and elapsed-start stratum. -/
theorem actualSourcePrefix_mem (z : Z) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val ∈
      ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
        (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) := by
  have hz := sourceStratum_facts rate rewards C_star C_h q t s hs z
  have hlaunch := (ReferenceSourcePrefixHistoryFiltration.actualLaunchStratum_factor rate rewards C_star C_h control0 t.val
    (by omega) s hs z.val).mp ⟨hz.2.1, hz.2.2⟩
  change ReferenceRetainedSourceCoupling.retainedSourceEvent rate rewards C_star C_h q s
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val)
  refine ⟨?_, hlaunch.1, hlaunch.2⟩
  rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected]
  exact hz.1

/-- The pointwise strict prefix is itself represented in the original source
stratum. The witness has this literal value; no alternate source map is used. -/
theorem actualSourcePrefix_in_sourceStratum (z : Z) :
    ∃ w : Z,
      w.val = ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val := by
  exact ⟨⟨_, actualSourcePrefix_mem rate rewards C_star C_h q t s hs control0 z⟩, rfl⟩

/-- The source prefix retains the actual corrected launch option and hence
the full corrected state, including all carried follower and private data. -/
theorem actualSourcePrefix_preservesLaunch (z : Z) :
    ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h =
        ReferenceCompletePhysicalHistory.physicalStart rate
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val) rewards C_star C_h ∧
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate z.val rewards C_star C_h =
        ReferenceCorrectedInitializationLaunch.correctedLaunch rate
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val) rewards C_star C_h := by
  have hz := sourceStratum_facts rate rewards C_star C_h q t s hs z
  have hby : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h t.val z.val := by
    refine ⟨hz.2.1, ?_⟩
    change ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed ≤ t.val
    rw [hz.2.2]
    exact hs
  exact ReferenceSourcePrefixHistoryFiltration.sourcePrefix_preserves_actual_launch rate rewards C_star C_h control0 t.val
    (by omega) z.val hby

private theorem sourcePrefix_controls_eq_on_window (z w : Z)
    (hw : w.val = ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val) :
    ∀ j : Fin p.T, s ≤ j.val → j.val < s + n →
      (z.val.1.2 q).2 j = (w.val.1.2 q).2 j := by
  intro j hstart hstop
  have hz := sourceStratum_facts rate rewards C_star C_h q t s hs z
  have hjt : j.val < t.val := by omega
  have hprefix := ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control
    control0 t.val z.val j
  rw [hz.1] at hprefix
  have hpref :
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val).1.2 q).2 j =
        (z.val.1.2 q).2 j := by
    simpa only [ite_eq_left hjt] using hprefix
  rw [hw]
  exact hpref.symm

private theorem sourcePrefix_pastProp_eq (z w : Z)
    (hw : w.val = ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val) :
    ∀ j : Fin p.T, j.val < s →
      ((z.val.1.2 q).2 j).1 ContinuousControlSlice.Label.prop =
        ((w.val.1.2 q).2 j).1 ContinuousControlSlice.Label.prop := by
  intro j hj
  have hz := sourceStratum_facts rate rewards C_star C_h q t s hs z
  have hjt : j.val < t.val := by omega
  have hprefix := ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control
    control0 t.val z.val j
  rw [hz.1] at hprefix
  have hpref :
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val).1.2 q).2 j =
        (z.val.1.2 q).2 j := by
    simpa only [ite_eq_left hjt] using hprefix
  rw [hw]
  exact congrArg (fun slice => slice.1 ContinuousControlSlice.Label.prop) hpref.symm

/-- The actual first-live cutoff tags on the strict past are unchanged by the
literal source prefix. Every control comparison is confined to rounds before
`t`; the current boundary record is retained separately by the n+1 window. -/
theorem actualSourcePrefix_cutoffTags_eq (z w : Z)
    (hw : w.val = ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val) :
    (actualFirstLiveRun rate z.val rewards C_star C_h
      (sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1 n
      (by rw [(sourceStratum_facts rate rewards C_star C_h q t s hs z).2.2]
          omega)).records.map
        (fun record => ReferenceCollectionPhaseHistory.cutoffChosen record.input) =
    (actualFirstLiveRun rate w.val rewards C_star C_h
      (sourceStratum_facts rate rewards C_star C_h q t s hs w).2.1 n
      (by rw [(sourceStratum_facts rate rewards C_star C_h q t s hs w).2.2]
          omega)).records.map
        (fun record => ReferenceCollectionPhaseHistory.cutoffChosen record.input) := by
  have hz := sourceStratum_facts rate rewards C_star C_h q t s hs z
  have hwfacts := sourceStratum_facts rate rewards C_star C_h q t s hs w
  have hprefixCross :
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val)
          rewards C_star C_h rate)).crossing.isSome = true := by
    simpa [hw] using hwfacts.2.1
  have hprefixElapsed :
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val)
            rewards C_star C_h rate)).completed = s := by
    simpa [hw] using hwfacts.2.2
  have hcorrected := (actualSourcePrefix_preservesLaunch
    rate rewards C_star C_h q t s hs control0 z).2
  have hlaunchZ := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate z.val rewards C_star C_h hz.2.1
  have hlaunchPrefix := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val)
    rewards C_star C_h hprefixCross
  have hinitialPrefix :
      ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hz.2.1 =
        ReferenceFirstLaunchNumericalCell.launchState rate
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val)
          rewards C_star C_h hprefixCross := by
    have hlaunchEq := hcorrected
    rw [hlaunchZ, hlaunchPrefix] at hlaunchEq
    exact Option.some.inj hlaunchEq
  have hinitial :
      ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hz.2.1 =
        ReferenceFirstLaunchNumericalCell.launchState rate w.val rewards C_star C_h hwfacts.2.1 := by
    simpa [hw] using hinitialPrefix
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hz.2.1) s := by
    simpa [hz.2.2] using
      (actualFirstLiveSeed rate z.val rewards C_star C_h hz.2.1).activeAtStart
  have hcontrols := sourcePrefix_controls_eq_on_window rate rewards C_star C_h q t s hs
    control0 z w hw
  have hbefore := sourcePrefix_pastProp_eq rate rewards C_star C_h q t s hs control0 z w hw
  have hmodeW : ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceFirstLaunchNumericalCell.launchState rate w.val rewards C_star C_h hwfacts.2.1) s := by
    simpa [hwfacts.2.2] using
      (actualFirstLiveSeed rate w.val rewards C_star C_h hwfacts.2.1).activeAtStart
  have htags := run_cutoffTags_eq_of_initial_eq rate
    (ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hz.2.1)
    (ReferenceFirstLaunchNumericalCell.launchState rate w.val rewards C_star C_h hwfacts.2.1)
    hinitial z.val.1.2 w.val.1.2 q rewards s n
    (by omega)
    hmode hmodeW hcontrols hbefore
  simpa only [actualFirstLiveRun, hz.1, hwfacts.1, hz.2.2, hwfacts.2.2] using htags

private theorem takeWhile_length_eq_of_map_tag {α : Type*} (tag : α → Bool)
    (values : List α) :
    (values.takeWhile (fun value => !(tag value))).length =
      ((values.map tag).takeWhile (fun flag => !flag)).length := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      cases htag : tag value <;> simp [htag, ih]

private theorem firstLiveWindow_length_eq_of_cutoffTags
    (left right : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hmap : left.map (fun record => ReferenceCollectionPhaseHistory.cutoffChosen record.input) =
      right.map (fun record => ReferenceCollectionPhaseHistory.cutoffChosen record.input)) :
    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow left).length =
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow right).length := by
  have hflags := congrArg (fun flags : List Bool =>
    (flags.takeWhile (fun flag => !flag)).length) hmap
  calc
    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow left).length =
        ((left.map fun record => ReferenceCollectionPhaseHistory.cutoffChosen record.input).takeWhile
          (fun flag => !flag)).length := by
            exact takeWhile_length_eq_of_map_tag
              (fun record => ReferenceCollectionPhaseHistory.cutoffChosen record.input) left
    _ = ((right.map fun record => ReferenceCollectionPhaseHistory.cutoffChosen record.input).takeWhile
          (fun flag => !flag)).length := hflags
    _ = (ReferenceFirstLiveConfirmationHistory.firstLiveWindow right).length := by
            symm
            exact takeWhile_length_eq_of_map_tag
              (fun record => ReferenceCollectionPhaseHistory.cutoffChosen record.input) right

private theorem run_finalState_eq_of_initial_eq
    (initialLeft initialRight : ReferenceActivePhysicalHorizon.State p rate)
    (hinitial : initialLeft = initialRight)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmodeLeft : ReferenceActivePhysicalHorizon.allActiveAtStart initialLeft start)
    (hmodeRight : ReferenceActivePhysicalHorizon.allActiveAtStart initialRight start) :
    (ReferenceActivePhysicalHorizon.run initialLeft rows selected rewards start count hspan hmodeLeft).finalState =
      (ReferenceActivePhysicalHorizon.run initialRight rows selected rewards start count hspan hmodeRight).finalState := by
  cases hinitial
  rfl

/-- The actual numerical cells on the first `n` rounds agree on the original
source and its literal strict source prefix. This compares the computed
first-live records at the same calendar positions; whole rows remain distinct. -/
theorem actualNumericalCells_eq_of_sourcePrefix (z w : Z)
    (hw : w.val = ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val) :
    actualLiveSourceCells rate z.val rewards C_star C_h
      (sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1 n
      (by rw [(sourceStratum_facts rate rewards C_star C_h q t s hs z).2.2]
          omega) =
    actualLiveSourceCells rate w.val rewards C_star C_h
      (sourceStratum_facts rate rewards C_star C_h q t s hs w).2.1 n
      (by rw [(sourceStratum_facts rate rewards C_star C_h q t s hs w).2.2]
          omega) := by
  have hz := sourceStratum_facts rate rewards C_star C_h q t s hs z
  have hwfacts := sourceStratum_facts rate rewards C_star C_h q t s hs w
  have hprefixCross :
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val)
          rewards C_star C_h rate)).crossing.isSome = true := by
    simpa [hw] using hwfacts.2.1
  have hcorrected := (actualSourcePrefix_preservesLaunch
    rate rewards C_star C_h q t s hs control0 z).2
  have hlaunchZ := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate z.val rewards C_star C_h hz.2.1
  have hlaunchPrefix := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val)
    rewards C_star C_h hprefixCross
  have hinitialPrefix :
      ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hz.2.1 =
        ReferenceFirstLaunchNumericalCell.launchState rate
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val)
          rewards C_star C_h hprefixCross := by
    have hlaunchEq := hcorrected
    rw [hlaunchZ, hlaunchPrefix] at hlaunchEq
    exact Option.some.inj hlaunchEq
  have hinitial :
      ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hz.2.1 =
        ReferenceFirstLaunchNumericalCell.launchState rate w.val rewards C_star C_h hwfacts.2.1 := by
    simpa [hw] using hinitialPrefix
  have hmodeZ : ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hz.2.1) s := by
    simpa [hz.2.2] using
      (actualFirstLiveSeed rate z.val rewards C_star C_h hz.2.1).activeAtStart
  have hmodeW : ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceFirstLaunchNumericalCell.launchState rate w.val rewards C_star C_h hwfacts.2.1) s := by
    simpa [hwfacts.2.2] using
      (actualFirstLiveSeed rate w.val rewards C_star C_h hwfacts.2.1).activeAtStart
  have hcontrols := sourcePrefix_controls_eq_on_window rate rewards C_star C_h q t s hs
    control0 z w hw
  have hbefore := sourcePrefix_pastProp_eq rate rewards C_star C_h q t s hs control0 z w hw
  have hspanZ : s + n ≤ p.T := by omega
  have hspanW : s + n ≤ p.T := hspanZ
  have hactualSpanZ :
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed + n ≤ p.T := by
    rw [hz.2.2]
    exact hspanZ
  have hactualSpanW :
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput w.val rewards C_star C_h rate)).completed + n ≤ p.T := by
    rw [hwfacts.2.2]
    exact hspanW
  have htags := actualSourcePrefix_cutoffTags_eq rate rewards C_star C_h q t s hs control0 z w hw
  have hwindowLen :
      (actualFirstLiveWindow rate z.val rewards C_star C_h hz.2.1 n hactualSpanZ).length =
        (actualFirstLiveWindow rate w.val rewards C_star C_h hwfacts.2.1 n hactualSpanW).length := by
    change (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (actualFirstLiveRun rate z.val rewards C_star C_h hz.2.1 n hactualSpanZ).records).length =
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (actualFirstLiveRun rate w.val rewards C_star C_h hwfacts.2.1 n hactualSpanW).records).length
    apply firstLiveWindow_length_eq_of_cutoffTags
    simpa only [actualFirstLiveRun, hz.2.2, hwfacts.2.2] using htags
  have hcountZ : (actualFirstLiveWindow rate z.val rewards C_star C_h hz.2.1 n hactualSpanZ).length ≤ n := by
    have hprefix : (actualFirstLiveWindow rate z.val rewards C_star C_h hz.2.1 n hactualSpanZ).IsPrefix
        (actualFirstLiveRun rate z.val rewards C_star C_h hz.2.1 n hactualSpanZ).records :=
      List.takeWhile_prefix _
    have hlen := hprefix.length_le
    rw [actualFirstLiveRun, ReferenceActivePhysicalHorizon.run_record_count] at hlen
    exact hlen
  have hcountW : (actualFirstLiveWindow rate w.val rewards C_star C_h hwfacts.2.1 n hactualSpanW).length ≤ n := by
    have hprefix : (actualFirstLiveWindow rate w.val rewards C_star C_h hwfacts.2.1 n hactualSpanW).IsPrefix
        (actualFirstLiveRun rate w.val rewards C_star C_h hwfacts.2.1 n hactualSpanW).records :=
      List.takeWhile_prefix _
    have hlen := hprefix.length_le
    rw [actualFirstLiveRun, ReferenceActivePhysicalHorizon.run_record_count] at hlen
    exact hlen
  apply List.ext_getElem
  · simpa only [actualLiveSourceCells_length] using hwindowLen
  · intro i hia hib
    have hiZ : i < (actualFirstLiveWindow rate z.val rewards C_star C_h hz.2.1 n hactualSpanZ).length := by
      simpa only [actualLiveSourceCells_length] using hia
    have hiW : i < (actualFirstLiveWindow rate w.val rewards C_star C_h hwfacts.2.1 n hactualSpanW).length := by
      simpa only [actualLiveSourceCells_length] using hib
    have hkcountZ : i < n := lt_of_lt_of_le hiZ hcountZ
    have hkcountW : i < n := lt_of_lt_of_le hiW hcountW
    let kZ : Fin (actualFirstLiveWindow rate z.val rewards C_star C_h hz.2.1 n hactualSpanZ).length :=
      ⟨i, hiZ⟩
    let kW : Fin (actualFirstLiveWindow rate w.val rewards C_star C_h hwfacts.2.1 n hactualSpanW).length :=
      ⟨i, hiW⟩
    let actualZ := ReferenceAssignmentPayloadChronology.actualRunRecordAt
      (ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hz.2.1)
      z.val.1.2 q rewards s i (by omega) hmodeZ
    let actualW := ReferenceAssignmentPayloadChronology.actualRunRecordAt
      (ReferenceFirstLaunchNumericalCell.launchState rate w.val rewards C_star C_h hwfacts.2.1)
      w.val.1.2 q rewards s i (by omega) hmodeW
    have hiZbase : i < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceActivePhysicalHorizon.run
          (ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hz.2.1)
          z.val.1.2 q rewards s n hspanZ hmodeZ).records).length := by
      simpa [actualFirstLiveWindow, actualFirstLiveRun, hz.2.2, hz.1] using hiZ
    have hiWbase : i < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceActivePhysicalHorizon.run
          (ReferenceFirstLaunchNumericalCell.launchState rate w.val rewards C_star C_h hwfacts.2.1)
          w.val.1.2 q rewards s n hspanW hmodeW).records).length := by
      simpa [actualFirstLiveWindow, actualFirstLiveRun, hwfacts.2.2, hwfacts.1] using hiW
    have hrecordZ := firstLiveWindow_record_eq_actualRunRecordAt
      (rate := rate)
      (initial := ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hz.2.1)
      (rows := z.val.1.2) (selected := q) (rewards := rewards) (start := s) (count := n)
      (hspan := hspanZ) (hmode := hmodeZ) (k := i) (hkcount := hkcountZ) (hkwindow := hiZbase)
    have hrecordW := firstLiveWindow_record_eq_actualRunRecordAt
      (rate := rate)
      (initial := ReferenceFirstLaunchNumericalCell.launchState rate w.val rewards C_star C_h hwfacts.2.1)
      (rows := w.val.1.2) (selected := q) (rewards := rewards) (start := s) (count := n)
      (hspan := hspanW) (hmode := hmodeW) (k := i) (hkcount := hkcountW) (hkwindow := hiWbase)
    have hrecordZ' :
        (actualFirstLiveWindow rate z.val rewards C_star C_h hz.2.1 n hactualSpanZ)[i] = actualZ := by
      simpa [actualFirstLiveWindow, actualFirstLiveRun, hz.2.2, hz.1, actualZ] using hrecordZ
    have hrecordW' :
        (actualFirstLiveWindow rate w.val rewards C_star C_h hwfacts.2.1 n hactualSpanW)[i] = actualW := by
      simpa [actualFirstLiveWindow, actualFirstLiveRun, hwfacts.2.2, hwfacts.1, actualW] using hrecordW
    have hcontrolsPrefix : ∀ j : Fin p.T, s ≤ j.val → j.val < s + i →
        (z.val.1.2 q).2 j = (w.val.1.2 q).2 j := by
      intro j hjStart hjEnd
      exact hcontrols j hjStart (by omega)
    have hrunState := (ReferenceActiveTemporalAssembly.run_eq_of_temporal_reads
      (ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hz.2.1)
      z.val.1.2 w.val.1.2 q rewards rewards s i (by omega) hmodeZ
      hcontrolsPrefix (fun _ _ _ => rfl) (fun _ => hbefore)).1
    have hsameInitialRun :
        (ReferenceActivePhysicalHorizon.run
          (ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hz.2.1)
          w.val.1.2 q rewards s i (by omega) hmodeZ).finalState =
          (ReferenceActivePhysicalHorizon.run
            (ReferenceFirstLaunchNumericalCell.launchState rate w.val rewards C_star C_h hwfacts.2.1)
            w.val.1.2 q rewards s i (by omega) hmodeW).finalState := by
      exact run_finalState_eq_of_initial_eq rate
        (initialLeft := ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hz.2.1)
        (initialRight := ReferenceFirstLaunchNumericalCell.launchState rate w.val rewards C_star C_h hwfacts.2.1)
        hinitial (rows := w.val.1.2) (selected := q) (rewards := rewards)
        (start := s) (count := i) (hspan := by omega) hmodeZ hmodeW
    have hstate :
        (actualFirstLiveWindow rate z.val rewards C_star C_h hz.2.1 n hactualSpanZ)[i].input.state =
          (actualFirstLiveWindow rate w.val rewards C_star C_h hwfacts.2.1 n hactualSpanW)[i].input.state := by
      calc
        _ = actualZ.input.state := congrArg (fun record => record.input.state) hrecordZ'
        _ = (ReferenceActivePhysicalHorizon.run
              (ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hz.2.1)
              z.val.1.2 q rewards s i (by omega) hmodeZ).finalState := rfl
        _ = (ReferenceActivePhysicalHorizon.run
              (ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hz.2.1)
              w.val.1.2 q rewards s i (by omega) hmodeZ).finalState := hrunState
        _ = (ReferenceActivePhysicalHorizon.run
              (ReferenceFirstLaunchNumericalCell.launchState rate w.val rewards C_star C_h hwfacts.2.1)
              w.val.1.2 q rewards s i (by omega) hmodeW).finalState := hsameInitialRun
        _ = actualW.input.state := rfl
        _ = (actualFirstLiveWindow rate w.val rewards C_star C_h hwfacts.2.1 n hactualSpanW)[i].input.state :=
          congrArg (fun record => record.input.state) hrecordW'.symm
    have htime :
        (actualFirstLiveWindow rate z.val rewards C_star C_h hz.2.1 n hactualSpanZ)[i].input.time =
        (actualFirstLiveWindow rate w.val rewards C_star C_h hwfacts.2.1 n hactualSpanW)[i].input.time := by
      calc
        _ = actualZ.input.time := congrArg (fun record => record.input.time) hrecordZ'
        _ = actualW.input.time := rfl
        _ = _ := congrArg (fun record => record.input.time) hrecordW'.symm
    have hselected :
        (actualFirstLiveWindow rate z.val rewards C_star C_h hz.2.1 n hactualSpanZ)[i].input.selected =
          (actualFirstLiveWindow rate w.val rewards C_star C_h hwfacts.2.1 n hactualSpanW)[i].input.selected := by
      calc
        _ = actualZ.input.selected := congrArg (fun record => record.input.selected) hrecordZ'
        _ = actualW.input.selected := rfl
        _ = _ := congrArg (fun record => record.input.selected) hrecordW'.symm
    have hrewards :
        (actualFirstLiveWindow rate z.val rewards C_star C_h hz.2.1 n hactualSpanZ)[i].input.rewards =
          (actualFirstLiveWindow rate w.val rewards C_star C_h hwfacts.2.1 n hactualSpanW)[i].input.rewards := by
      calc
        _ = actualZ.input.rewards := congrArg (fun record => record.input.rewards) hrecordZ'
        _ = actualW.input.rewards := rfl
        _ = _ := congrArg (fun record => record.input.rewards) hrecordW'.symm
    have hcurrentAt : actualZ.input.row.2 actualZ.input.time =
        actualW.input.row.2 actualW.input.time := by
      change (z.val.1.2 q).2 actualZ.input.time =
        (w.val.1.2 q).2 actualW.input.time
      have htimeZ : actualZ.input.time = ⟨s + i, by omega⟩ := rfl
      have htimeW : actualW.input.time = ⟨s + i, by omega⟩ := rfl
      rw [htimeZ, htimeW]
      exact hcontrols ⟨s + i, by omega⟩ (by change s ≤ s + i; omega)
        (by change s + i < s + n; omega)
    have hcurrent :
        (actualFirstLiveWindow rate z.val rewards C_star C_h hz.2.1 n hactualSpanZ)[i].input.row.2
          (actualFirstLiveWindow rate z.val rewards C_star C_h hz.2.1 n hactualSpanZ)[i].input.time =
        (actualFirstLiveWindow rate w.val rewards C_star C_h hwfacts.2.1 n hactualSpanW)[i].input.row.2
          (actualFirstLiveWindow rate w.val rewards C_star C_h hwfacts.2.1 n hactualSpanW)[i].input.time := by
      rw [hrecordZ', hrecordW']
      exact hcurrentAt
    have hinput := actualCell_input_eq_of_current rate
      (actualLiveSourceCellAt rate z.val rewards C_star C_h hz.2.1 n hactualSpanZ kZ)
      (actualLiveSourceCellAt rate w.val rewards C_star C_h hwfacts.2.1 n hactualSpanW kW)
      hstate hselected htime hrewards hcurrent
    have hgetZ := actualLiveSourceCells_get rate z.val rewards C_star C_h hz.2.1 n hactualSpanZ kZ
    have hgetW := actualLiveSourceCells_get rate w.val rewards C_star C_h hwfacts.2.1 n hactualSpanW kW
    calc
      (actualLiveSourceCells rate z.val rewards C_star C_h hz.2.1 n hactualSpanZ)[i] =
          (actualLiveSourceCellAt rate z.val rewards C_star C_h hz.2.1 n hactualSpanZ kZ).input := by
            simpa [kZ] using hgetZ
      _ = (actualLiveSourceCellAt rate w.val rewards C_star C_h hwfacts.2.1 n hactualSpanW kW).input := hinput
      _ = (actualLiveSourceCells rate w.val rewards C_star C_h hwfacts.2.1 n hactualSpanW)[i] := by
            symm
            simpa [kW] using hgetW

private theorem run_records_take_successor_for_source (z : Z) :
    (actualFirstLiveRun rate z.val rewards C_star C_h (sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1
      (n + 1) (by have hz := sourceStratum_facts rate rewards C_star C_h q t s hs z; omega)).records.take n =
    (actualFirstLiveRun rate z.val rewards C_star C_h (sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1
      n (by have hz := sourceStratum_facts rate rewards C_star C_h q t s hs z; omega)).records := by
  have hz := sourceStratum_facts rate rewards C_star C_h q t s hs z
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hz.2.1) s := by
    simpa [hz.2.2] using
      (actualFirstLiveSeed rate z.val rewards C_star C_h hz.2.1).activeAtStart
  have hsuccessor := run_records_take_successor
    (ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hz.2.1)
    z.val.1.2 q rewards s n (by omega)
    hmode
  simpa [actualFirstLiveRun, hz.2.2, hz.1] using hsuccessor

private theorem actual_windows_take_successor (z : Z) :
    (actualFirstLiveWindow rate z.val rewards C_star C_h
      (sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1
      (n + 1) (by have hz := sourceStratum_facts rate rewards C_star C_h q t s hs z; omega)).take n =
     actualFirstLiveWindow rate z.val rewards C_star C_h
      (sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1
      n (by have hz := sourceStratum_facts rate rewards C_star C_h q t s hs z; omega) := by
  have hrecords := run_records_take_successor_for_source rate rewards C_star C_h q t s hs z
  change (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (actualFirstLiveRun rate z.val rewards C_star C_h _ (n + 1) _).records).take n = _
  calc
    _ = ((actualFirstLiveRun rate z.val rewards C_star C_h _ (n + 1) _).records.take n).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.cutoffChosen r.input) := by
          exact List.take_takeWhile
    _ = ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (actualFirstLiveRun rate z.val rewards C_star C_h _ n _).records := by
          rw [hrecords]
          rfl

private theorem actual_cells_take_of_window_take_eq
    (source : ReferenceFirstWindowNumericalStream.SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (countA countB takeCount : ℕ)
    (hspanA : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + countA ≤ p.T)
    (hspanB : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + countB ≤ p.T)
    (hwindow : (actualFirstLiveWindow rate source rewards C_star C_h hc countA hspanA).take takeCount =
      actualFirstLiveWindow rate source rewards C_star C_h hc countB hspanB) :
    (actualLiveSourceCells rate source rewards C_star C_h hc countA hspanA).take takeCount =
      actualLiveSourceCells rate source rewards C_star C_h hc countB hspanB := by
  apply List.ext_getElem
  · have hlen := congrArg List.length hwindow
    simpa [List.length_take, actualLiveSourceCells_length] using hlen
  · intro j hja hjb
    have hbound : j < min takeCount
          (actualLiveSourceCells rate source rewards C_star C_h hc countA hspanA).length := by
      simpa [List.length_take, actualLiveSourceCells_length] using hja
    have hjtake : j < takeCount := lt_of_lt_of_le hbound (Nat.min_le_left _ _)
    have hjA : j < (actualFirstLiveWindow rate source rewards C_star C_h hc countA hspanA).length :=
      lt_of_lt_of_le hbound ((Nat.min_le_right _ _).trans
        (le_of_eq (actualLiveSourceCells_length rate source rewards C_star C_h hc countA hspanA)))
    have hjB : j < (actualFirstLiveWindow rate source rewards C_star C_h hc countB hspanB).length := by
      simpa [actualLiveSourceCells_length] using hjb
    have hget := congrArg (fun values : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p)
        (rate := rate)) => values[j]?) hwindow
    have hrecord :
        (actualFirstLiveWindow rate source rewards C_star C_h hc countA hspanA)[j]'hjA =
        (actualFirstLiveWindow rate source rewards C_star C_h hc countB hspanB)[j]'hjB := by
      rw [List.getElem?_take_of_lt hjtake, List.getElem?_eq_getElem hjA,
        List.getElem?_eq_getElem hjB] at hget
      exact Option.some.inj hget
    have hinput := actualCellInput_eq_of_record_eq hrecord
      (actualLiveSourceCellAt rate source rewards C_star C_h hc countA hspanA ⟨j, hjA⟩)
      (actualLiveSourceCellAt rate source rewards C_star C_h hc countB hspanB ⟨j, hjB⟩)
    simpa only [actualLiveSourceCells, List.getElem_take, List.getElem_ofFn] using hinput

/-- On the original source, the first `n` actual numerical cells are exactly
the strict prefix of the same variable first-live window with `n+1` records. -/
theorem actualNumericalCells_take_successor (_control0 : ContinuousLearningRows.TimeControl p) (z : Z) :
    (actualLiveSourceCells rate z.val rewards C_star C_h
      (sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1
      (n + 1) (by have hz := sourceStratum_facts rate rewards C_star C_h q t s hs z; omega)).take n =
     actualLiveSourceCells rate z.val rewards C_star C_h
      (sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1
      n (by have hz := sourceStratum_facts rate rewards C_star C_h q t s hs z; omega) := by
  have hwindow := actual_windows_take_successor rate rewards C_star C_h q t s hs z
  exact actual_cells_take_of_window_take_eq rate rewards C_star C_h
    z.val (sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1
    (n + 1) n n _ _ hwindow

/-- The strict past of the actual `n+1` window is unchanged by replacing
only the current and future selected-row controls by the literal prefix. -/
theorem numerical_past_prefix_eq (z w : Z)
    (hw : w.val = ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val) :
    (actualLiveSourceCells rate z.val rewards C_star C_h
      (sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1
      (n + 1) (by have hz := sourceStratum_facts rate rewards C_star C_h q t s hs z; omega)).take n =
    (actualLiveSourceCells rate w.val rewards C_star C_h
      (sourceStratum_facts rate rewards C_star C_h q t s hs w).2.1
      (n + 1) (by have hw := sourceStratum_facts rate rewards C_star C_h q t s hs w; omega)).take n := by
  rw [actualNumericalCells_take_successor rate rewards C_star C_h q t s hs control0 z,
    actualNumericalCells_take_successor rate rewards C_star C_h q t s hs control0 w]
  exact actualNumericalCells_eq_of_sourcePrefix rate rewards C_star C_h q t s hs control0 z w hw

/-- Running the existing queue machine on the strict past is exactly running
it on the count-`n` numerical list; this includes its complete final state. -/
theorem numerical_run_count_eq (control0 : ContinuousLearningRows.TimeControl p) (z : Z) :
    RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((actualLiveSourceCells rate z.val rewards C_star C_h
        (sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1
        (n + 1) (by have hz := sourceStratum_facts rate rewards C_star C_h q t s hs z; omega)).take n) =
    RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (actualLiveSourceCells rate z.val rewards C_star C_h
        (sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1
        n (by have hz := sourceStratum_facts rate rewards C_star C_h q t s hs z; omega)) := by
  exact congrArg (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate))
    (actualNumericalCells_take_successor rate rewards C_star C_h q t s hs control0 z)

/-- The literal strict-past queue run is invariant under the source prefix.
The equality is of the existing run state, with registers, overflow, and every
accepted chronological record retained. -/
theorem numerical_run_prefix_eq (z w : Z)
    (hw : w.val = ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val) :
    RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((actualLiveSourceCells rate z.val rewards C_star C_h
        (sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1
        (n + 1) (by have hz := sourceStratum_facts rate rewards C_star C_h q t s hs z; omega)).take n) =
    RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((actualLiveSourceCells rate w.val rewards C_star C_h
        (sourceStratum_facts rate rewards C_star C_h q t s hs w).2.1
        (n + 1) (by have hw := sourceStratum_facts rate rewards C_star C_h q t s hs w; omega)).take n) := by
  exact congrArg (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate))
    (numerical_past_prefix_eq rate rewards C_star C_h q t s hs control0 z w hw)

/-- Explicit projections of the complete strict-past state equality. These
are the existing queue machine's registers, persistent flag, and records. -/
theorem numerical_run_fields_prefix_eq (z w : Z)
    (hw : w.val = ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val) :
    let runZ := RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((actualLiveSourceCells rate z.val rewards C_star C_h
        (sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1
        (n + 1) (by have hz := sourceStratum_facts rate rewards C_star C_h q t s hs z; omega)).take n)
    let runW := RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((actualLiveSourceCells rate w.val rewards C_star C_h
        (sourceStratum_facts rate rewards C_star C_h q t s hs w).2.1
        (n + 1) (by have hw := sourceStratum_facts rate rewards C_star C_h q t s hs w; omega)).take n)
    runZ.registers = runW.registers ∧ runZ.overflow = runW.overflow ∧ runZ.records = runW.records := by
  have hrun := numerical_run_prefix_eq rate rewards C_star C_h q t s hs control0 z w hw
  exact ⟨congrArg RecordedQueueRun.RunState.registers hrun,
    congrArg RecordedQueueRun.RunState.overflow hrun,
    congrArg RecordedQueueRun.RunState.records hrun⟩

/-- The no-earlier-overflow test uses only the strict past. In particular,
this identity does not test or discard the current round's first overflow update. -/
theorem numerical_past_noOverflow_prefix_iff (z w : Z)
    (hw : w.val = ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val) :
    (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((actualLiveSourceCells rate z.val rewards C_star C_h
        (sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1
        (n + 1) (by have hz := sourceStratum_facts rate rewards C_star C_h q t s hs z; omega)).take n)).overflow = false ↔
    (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((actualLiveSourceCells rate w.val rewards C_star C_h
        (sourceStratum_facts rate rewards C_star C_h q t s hs w).2.1
        (n + 1) (by have hw := sourceStratum_facts rate rewards C_star C_h q t s hs w; omega)).take n)).overflow = false := by
  rw [numerical_run_prefix_eq rate rewards C_star C_h q t s hs control0 z w hw]

end Bandits.Support.ReferenceFirstLiveNumericalPrefixTemporal
