/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope

import Mathlib.Tactic

/-!
# Sharp canonical recording-rate feasibility on the empty-pending branch

The actual original first-live source record supplies the complete payload used
by the empty marker law. Its corrected launch and actual first-live replay then
prove the payload's first-window age and all-one anchor. The stopped numerical
queue envelope applies to the actual strict-past prefix, including the first
overflow update, and gives the sharp canonical all-arm rate bound.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Classical
open Bandits.Support.ReferenceSelectedPayloadChronology

namespace Bandits.Support.ReferenceFirstLiveEmptyPendingAnchorRateFeasibility

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "Ze" =>
  ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
    rate rewards C_star C_h q t s hs control0
local notation "queue" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "cells" =>
  ReferenceFirstLiveEmptyPendingSourceMoments.actualCells
    rate rewards C_star C_h q t s hs control0
local notation "n" => t.val - s
/-- The complete payload read by the actual empty marker's selected baseline. -/
def actualMarkerPayload (z : Ze) :=
  (ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty
    rate rewards C_star C_h q t s hs control0
    (ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty
      rate rewards C_star C_h q t s hs control0 z)).view.payload
local notation "payload" => actualMarkerPayload rate rewards C_star C_h q t s hs control0

/-- The complete actual current selection agrees with the empty marker's
canonical payload, whose sigma is the original launch and whose anchor is all
ones. -/
theorem actual_payload_anchor_origin (z : Ze) :
    (payload z).sigma.val = s ∧ ∀ j : Fin p.K, (payload z).anchor j = 1 := by
  classical
  let source := z.val.val
  let hc := z.val.property.2.1
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let count := n + 1
  let hspan := ReferenceFirstLiveEmptyPendingSourceMoments.actualSpan
    rate rewards C_star C_h q t s hs control0 z
  let initial := ReferenceFirstLaunchNumericalCell.launchState
    rate source rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  let run := ReferenceActivePhysicalHorizon.run initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan
    seed.activeAtStart
  let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan
  let hindex := (ReferenceFirstLiveEmptyPendingSourceMoments.currentOriginalWindowIndex
    rate rewards C_star C_h q t s hs control0 z).choose
  let index : Fin window.length := ⟨n, hindex⟩
  let windowRecord := window[n]'hindex
  let windowCell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hc count hspan index
  let currentRecord := ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
    rate rewards C_star C_h q t s hs control0 z.val
  obtain ⟨currentCell, _hinput, hcurrentSelection⟩ :=
    ReferenceFirstLiveEmptyPendingSourceMoments.cell_original_selection
      rate rewards C_star C_h q t s hs control0 z
  have hwindowRecord : windowRecord = currentRecord := by
    exact (ReferenceFirstLiveEmptyPendingSourceMoments.currentOriginalWindowIndex
      rate rewards C_star C_h q t s hs control0 z).choose_spec
  have hstart : start = s := by
    dsimp [start]
    simpa only [ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] using
      z.val.property.2.2
  have hwindowPrefix : window.IsPrefix run.records := by
    simpa [window, run, ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow] using
        (List.takeWhile_prefix
          (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
            !ReferenceCollectionPhaseHistory.cutoffChosen record.input))
  have hrunIndex : n < run.records.length :=
    lt_of_lt_of_le hindex hwindowPrefix.length_le
  have hwindowElem : windowRecord = run.records[n]'hrunIndex :=
    hwindowPrefix.getElem hindex
  have hwindowMem : windowRecord ∈ run.records := by
    rw [hwindowElem]
    exact List.getElem_mem hrunIndex
  have hselected : windowRecord.output.preparation.coordinator.selection =
      some windowCell.selected := by
    simpa [windowRecord, index] using windowCell.selection_actual
  have hselectedPayload : windowCell.selected.view.payload =
      currentCell.selected.view.payload := by
    have h := congrArg
      (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
        record.output.preparation.coordinator.selection.map
          (fun selected => selected.view.payload)) hwindowRecord
    rw [hselected, currentCell.selection_actual] at h
    exact Option.some.inj h
  have hcurrentPayload : windowCell.selected.view.payload = payload z := by
    calc
      windowCell.selected.view.payload = currentCell.selected.view.payload := hselectedPayload
      _ =
          (ReferenceFirstLiveEmptyPendingMarkerLaw.originalSelEmpty
            rate rewards C_star C_h q t s hs control0 z).view.payload :=
        congrArg (fun selected => selected.view.payload) hcurrentSelection
      _ = payload z :=
        ReferenceFirstLiveEmptyPendingMarkerLaw.originalSelEmpty_payload_eq
          rate rewards C_star C_h q t s hs control0 z
  have hgeometry := ReferenceFirstLiveDownNumericalRecovery.first_live_geometry
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hspan seed.activeAtStart seed.coordinatorFirst
    index windowCell.selected hselected
  have hcurrentSigma : windowCell.selected.view.payload.sigma.val = s :=
    hgeometry.1.trans hstart
  have hsigma : (payload z).sigma.val = s := by
    rw [← hcurrentPayload]
    exact hcurrentSigma
  have hwindowCount : count ≤ window.length := by
    dsimp [count, window, ReferenceFirstWindowNumericalStream.actualFirstLiveWindow]
    exact Nat.succ_le_of_lt hindex
  have hReplay := ReferenceFirstLiveComplementQueueReplay.actual_first_live_complement_prefix_replay
    rate source rewards C_star C_h hc count hspan count hwindowCount
  rcases hReplay with ⟨_, _, hpositive⟩
  have hcountPositive : 0 < count := by
    dsimp [count]
    omega
  rcases hpositive hcountPositive with
    ⟨endpoint, owned, base, hendpointCoord, _, hendpointSigma, _, _, _⟩
  have hendpointCoordRun : run.finalState.coordinator = .live endpoint owned base := by
    simpa [run, initial, start, seed,
      ReferenceFirstLaunchNumericalCell.launchState,
      ReferenceFirstWindowNumericalStream.actualFirstLiveSeed,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun] using hendpointCoord
  have hwindowBound : count ≤
      (ReferenceFirstComplementMassBudget.firstWindow initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count
        hspan seed.activeAtStart).length := by
    simpa [count, ReferenceFirstComplementMassBudget.firstWindow,
      ReferenceFirstComplementMassBudget.originalRun, window,
      ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun] using
        Nat.succ_le_of_lt hindex
  have hweight := ReferenceFirstLiveWeightEnvelope.run_first_live_weight_envelope
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hspan seed.activeAtStart seed.coordinatorFirst
    count le_rfl hwindowBound
  rw [hendpointCoordRun] at hweight
  have hanchorEndpoint : ∀ j : Fin p.K, endpoint.payload.anchor j = 1 := hweight.1
  have hendpointSigmaStart : endpoint.payload.sigma.val = start := by
    simpa [start] using hendpointSigma
  have hselectedSigma : windowCell.selected.view.payload.sigma.val =
      endpoint.payload.sigma.val := by
    exact hcurrentSigma.trans (hstart.symm.trans hendpointSigmaStart.symm)
  have hstored : ReferenceAssignmentPayloadPersistence.storedPayload
      run.finalState.coordinator = some endpoint.payload := by
    rw [hendpointCoordRun]
    rfl
  have hendpointPayload :=
    run_actualSelectedPayload_eq_of_prefix_storedPayload_equal_sigma
      initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards start count hspan seed.activeAtStart seed.coordinatorFirst
      windowRecord windowCell.selected hwindowMem hselected
      count le_rfl endpoint.payload hstored hselectedSigma
  have hpayloadEndpoint : payload z = endpoint.payload := by
    calc
      payload z = windowCell.selected.view.payload := hcurrentPayload.symm
      _ = endpoint.payload := hendpointPayload.1
  refine ⟨hsigma, ?_⟩
  intro j
  rw [hpayloadEndpoint]
  exact hanchorEndpoint j

/-- The actual current record's grid geometry bounds the complete first
window through its current update by one source episode horizon. -/
theorem actual_payload_episode_age (z : Ze) :
    t.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val (payload z).sigma ∧
      n + 1 ≤ ReplayWeightStability.episodeHorizon rate.eta.val := by
  classical
  let source := z.val.val
  let hc := z.val.property.2.1
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let count := n + 1
  let hspan := ReferenceFirstLiveEmptyPendingSourceMoments.actualSpan
    rate rewards C_star C_h q t s hs control0 z
  let initial := ReferenceFirstLaunchNumericalCell.launchState
    rate source rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan
  let hindex := (ReferenceFirstLiveEmptyPendingSourceMoments.currentOriginalWindowIndex
    rate rewards C_star C_h q t s hs control0 z).choose
  let index : Fin window.length := ⟨n, hindex⟩
  let windowRecord := window[n]'hindex
  let windowCell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hc count hspan index
  obtain ⟨currentCell, _hinput, _hcurrentSelection⟩ :=
    ReferenceFirstLiveEmptyPendingSourceMoments.cell_original_selection
      rate rewards C_star C_h q t s hs control0 z
  have hstart : start = s := by
    dsimp [start]
    simpa only [ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] using
      z.val.property.2.2
  have hcurrentPayload : currentCell.selected.view.payload = payload z := by
    calc
      currentCell.selected.view.payload =
          (ReferenceFirstLiveEmptyPendingMarkerLaw.originalSelEmpty
            rate rewards C_star C_h q t s hs control0 z).view.payload :=
        congrArg (fun selected => selected.view.payload) _hcurrentSelection
      _ = payload z :=
        ReferenceFirstLiveEmptyPendingMarkerLaw.originalSelEmpty_payload_eq
          rate rewards C_star C_h q t s hs control0 z
  have hwindowRecord : windowRecord =
      ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z.val :=
    (ReferenceFirstLiveEmptyPendingSourceMoments.currentOriginalWindowIndex
      rate rewards C_star C_h q t s hs control0 z).choose_spec
  have hselected : windowRecord.output.preparation.coordinator.selection =
      some windowCell.selected := by
    simpa [windowRecord, index] using windowCell.selection_actual
  have hselectedPayload : windowCell.selected.view.payload =
      currentCell.selected.view.payload := by
    have h := congrArg
      (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
        record.output.preparation.coordinator.selection.map
          (fun selected => selected.view.payload)) hwindowRecord
    rw [hselected, currentCell.selection_actual] at h
    exact Option.some.inj h
  have hwindowPayload : windowCell.selected.view.payload = payload z :=
    hselectedPayload.trans hcurrentPayload
  have hgeometry := ReferenceFirstLiveDownNumericalRecovery.first_live_geometry
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hspan seed.activeAtStart seed.coordinatorFirst
    index windowCell.selected hselected
  have htime : windowRecord.input.time.val = t.val := by
    have htimeGeometry := hgeometry.2.1
    have htimeSource :=
      ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord_time
        rate rewards C_star C_h q t s hs control0 z.val
    have hrecord := (ReferenceFirstLiveEmptyPendingSourceMoments.currentOriginalWindowIndex
      rate rewards C_star C_h q t s hs control0 z).choose_spec
    have hrecordTime := congrArg
      (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
        record.input.time.val) hrecord
    change windowRecord.input.time.val = t.val
    rw [hrecordTime, htimeSource]
  have hgridSelected : t.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val
      windowCell.selected.view.payload.sigma := by
    rw [← htime]
    exact hgeometry.2.2.1
  have hgrid : t.val + 2 ≤
      FollowerCutoffScan.gridBoundary p rate.eta.val (payload z).sigma := by
    rw [← hwindowPayload]
    exact hgridSelected
  have hH : 0 < ReplayWeightStability.episodeHorizon rate.eta.val :=
    FollowerCutoffScan.episodeHorizon_pos_of_source_cap p rate.eta.val
      rate.eta.property rate.sourceCap
  have hsourceEnd := RecordedEpisodeStability.sourceEpisodeEnd_bounds p.T
    (ReplayWeightStability.episodeHorizon rate.eta.val) (s + 1) hH
    (by omega) (by omega)
  have hboundary : FollowerCutoffScan.gridBoundary p rate.eta.val (payload z).sigma =
      RecordedEpisodeStability.sourceEpisodeEnd p.T
        (ReplayWeightStability.episodeHorizon rate.eta.val) (s + 1) := by
    have hsigma := (actual_payload_anchor_origin
      rate rewards C_star C_h q t s hs control0 z).1
    simp [FollowerCutoffScan.gridBoundary,
      RecordedEpisodeStability.sourceEpisodeEnd, hsigma]
  have hgridEnd : t.val + 2 ≤ RecordedEpisodeStability.sourceEpisodeEnd p.T
      (ReplayWeightStability.episodeHorizon rate.eta.val) (s + 1) := by
    rw [← hboundary]
    exact hgrid
  have hwindowAge : n + 1 ≤ ReplayWeightStability.episodeHorizon rate.eta.val := by
    omega
  exact ⟨hgrid, hwindowAge⟩

/-- Every prefix of the actual empty-pending source window has the canonical
anchor/current-score envelope, including the retained first overflow update. -/
theorem actual_prefix_anchor_weight_envelope (z : Ze) (b : ℕ)
    (hb : b ≤ n + 1) (j : Fin p.K) :
    0 < (payload z).anchor j ∧
      (payload z).anchor j ≤ RecordedQueueRun.scoreWeight queue
        (RecordedQueueRun.run queue ((cells z).take b)) j ∧
      RecordedQueueRun.scoreWeight queue (RecordedQueueRun.run queue ((cells z).take b)) j <
        2 * (payload z).anchor j := by
  have horigin := actual_payload_anchor_origin rate rewards C_star C_h q t s hs control0 z
  have hage := actual_payload_episode_age rate rewards C_star C_h q t s hs control0 z
  have hlength : ((cells z).take b).length ≤ b := by
    simp
  have hprefixHorizon : ((cells z).take b).length - 0 ≤
      ReplayWeightStability.episodeHorizon rate.eta.val := by
    simpa only [Nat.sub_zero] using hlength.trans (by omega : b ≤
      ReplayWeightStability.episodeHorizon rate.eta.val)
  have henv := RecordedWeightedDrift.actual_anchor_envelope queue
    ((cells z).take b) 0 (by omega) hprefixHorizon j
  have hstartOne : RecordedQueueRun.scoreWeight queue
      (RecordedQueueRun.run queue []) j = 1 := by
    simp [RecordedQueueRun.scoreWeight, RecordedQueueRun.run,
      RecordedQueueRun.initialState, RecordedQueueRun.execute, ScoreWeights.scoreWeight]
  refine ⟨?_, ?_, ?_⟩
  · simp [horigin.2 j]
  · simpa [horigin.2 j, hstartOne] using henv.2.1
  · simpa [horigin.2 j, hstartOne] using henv.2.2

/-- On every empty-pending source point, the actual strict-past all-arm
inclusion marginals divided by the actual canonical marker rates are bounded
by the sharp universal recording constant. -/
theorem sum_thetaBefore_div_xiEmpty_le_R (z : Ze) :
    (∑ j : Fin p.K,
      ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore
        rate rewards C_star C_h q t s hs control0 j z /
      ReferenceFirstLiveEmptyPendingMarkerLaw.xiEmpty
        rate rewards C_star C_h q t s hs control0
        (ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty
          rate rewards C_star C_h q t s hs control0 z) j) ≤
      CanonicalRecordingRates.R p := by
  have hweight := actual_prefix_anchor_weight_envelope
    rate rewards C_star C_h q t s hs control0 z n (by omega)
  have hsum := CanonicalRecordingRates.sum_theta_div_xi_le_R p rate.eta.property
    (payload z).anchor
    (fun j => RecordedQueueRun.scoreWeight queue
      (RecordedQueueRun.run queue ((cells z).take n)) j)
    (fun j => (hweight j).1)
    (fun j => ⟨(hweight j).2.1, le_of_lt (hweight j).2.2⟩)
  have hrate (j : Fin p.K) :
      ReferenceFirstLiveEmptyPendingMarkerLaw.xiEmpty
        rate rewards C_star C_h q t s hs control0
        (ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty
          rate rewards C_star C_h q t s hs control0 z) j =
        CanonicalRecordingRates.xi p rate.eta.val (payload z).anchor j := rfl
  calc
    (∑ j : Fin p.K,
        ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore
          rate rewards C_star C_h q t s hs control0 j z /
        ReferenceFirstLiveEmptyPendingMarkerLaw.xiEmpty
          rate rewards C_star C_h q t s hs control0
          (ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty
            rate rewards C_star C_h q t s hs control0 z) j) =
        ∑ j : Fin p.K,
          ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight queue
            (RecordedQueueRun.run queue ((cells z).take n))) j /
          CanonicalRecordingRates.xi p rate.eta.val (payload z).anchor j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore,
        ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.past_eq_actualCells_take,
        hrate j]
    _ ≤ CanonicalRecordingRates.R p := hsum

end Bandits.Support.ReferenceFirstLiveEmptyPendingAnchorRateFeasibility

end
