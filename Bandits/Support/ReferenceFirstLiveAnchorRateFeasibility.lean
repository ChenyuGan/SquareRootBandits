/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveAllArmAcceptedConditionalMoments
public import Bandits.Support.RecordedWeightedDrift

import Mathlib.Tactic

/-!
# Actual first-live anchor and recording-rate feasibility

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:84-188,245-318`
and `sources/zip4/manuscript/06_interruptions.tex:391-408,425-426`.

These results recover the corrected first-live launch, its actual anchor, and
the episode age from the unchanged physical source. They apply the existing
stopped numerical queue envelope to every first-window prefix, including the
retained first overflow update and later frozen prefixes. The final sum uses
the all-arm score weights of that same numerical run and the actual source
marker rates. It is an internal result on the continuing first-live carrier;
it does not close a manuscript theorem.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstLiveAnchorRateFeasibility

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "Zplus" =>
  ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
    rate rewards C_star C_h q t s hs control0
local notation "queue" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "cells" =>
  ReferenceFirstLiveSourceCellReadout.cells rate rewards C_star C_h q t s hs control0
local notation "sourceWindow" =>
  ReferenceFirstLiveSourceCellReadout.sourceCurrentWindow
    rate rewards C_star C_h q t s hs control0
local notation "currentCell" =>
  ReferenceFirstLiveSourceCellReadout.cell rate rewards C_star C_h q t s hs control0
local notation "payload" =>
  ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPayload
    rate rewards C_star C_h q t s hs control0
local notation "markerRate" =>
  ReferenceFirstLiveAllArmPrefixAdaptation.markerRatePlus
    rate rewards C_star C_h q t s hs control0
local notation "past" => fun z : Zplus =>
  RecordedQueueRun.run queue (List.take (t.val - s) (cells z))
local notation "n" => t.val - s

/-- Every actual selection in the current whole first-live window carries the
same complete payload as the source branch's current prepare selection.

The birth proof is made on the original corrected launch, and the chronology
lemma equates complete payloads after proving their actual common sigma. -/
theorem source_current_payloads_eq (z : Zplus)
    (k : Fin (sourceWindow z).length) :
    (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val.val rewards C_star C_h
      z.val.property.2.1 (ReferenceFirstLiveSourceCellReadout.sourceCurrentCount t s)
      (ReferenceFirstLiveSourceCellReadout.source_current_span
        rate rewards C_star C_h q t s hs control0 z) k).selected.view.payload =
      payload z := by
  classical
  let source := z.val.val
  let hc := z.val.property.2.1
  let count := ReferenceFirstLiveSourceCellReadout.sourceCurrentCount t s
  let start := ReferenceFirstLiveSourceCellReadout.sourceCurrentElapsed
    rate rewards C_star C_h q t s hs control0 z
  let hspan := ReferenceFirstLiveSourceCellReadout.source_current_span
    rate rewards C_star C_h q t s hs control0 z
  let initial := ReferenceFirstLaunchNumericalCell.launchState
    rate source rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  let run := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate source rewards C_star C_h hc count hspan
  let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan
  let selected := (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate z.val.val rewards C_star C_h z.val.property.2.1
    (ReferenceFirstLiveSourceCellReadout.sourceCurrentCount t s)
    (ReferenceFirstLiveSourceCellReadout.source_current_span
      rate rewards C_star C_h q t s hs control0 z) k).selected
  let selectedCurrent := (currentCell z).selected
  let kCurrent := ReferenceFirstLiveSourceCellReadout.sourceCurrentIndex
    rate rewards C_star C_h q t s hs control0 z
  have hrecords : window = run.records := by
    simpa [window, run, source, hc, count, hspan,
      ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
      ReferenceFirstLiveSourceCellReadout.sourceCurrentWindow,
      ReferenceFirstLiveSourceCellReadout.sourceCurrentCount] using
        (ReferenceFirstLiveSourceCellReadout.source_current_window
          rate rewards C_star C_h q t s hs control0 z).1
  have hrecord : window[k.val] ∈ run.records := by
    rw [← hrecords]
    exact List.getElem_mem k.isLt
  have hrecordCurrent : window[kCurrent.val] ∈ run.records := by
    rw [← hrecords]
    exact List.getElem_mem kCurrent.isLt
  have hselectedCurrent :
      window[kCurrent.val].output.preparation.coordinator.selection = some selectedCurrent :=
    (currentCell z).selection_actual
  have hselectedActual := (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate z.val.val rewards C_star C_h z.val.property.2.1
    (ReferenceFirstLiveSourceCellReadout.sourceCurrentCount t s)
    (ReferenceFirstLiveSourceCellReadout.source_current_span
      rate rewards C_star C_h q t s hs control0 z) k).selection_actual
  have hbirths := ReferenceFirstDownRecoveryBudget.run_first_selected_payload
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hspan seed.activeAtStart seed.coordinatorFirst
  obtain ⟨_, _, _, _, hsigma, _⟩ := hbirths k selected hselectedActual
  obtain ⟨_, _, _, _, hsigmaCurrent, _⟩ :=
    hbirths kCurrent selectedCurrent hselectedCurrent
  have hsameSigma : selected.view.payload.sigma.val =
      selectedCurrent.view.payload.sigma.val := by
    rw [hsigma, hsigmaCurrent]
  have hpayloadEq :=
    ReferenceSelectedPayloadChronology.run_two_actualSelectedPayloads_eq_of_equal_sigma
      initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards start count hspan seed.activeAtStart seed.coordinatorFirst
      window[k.val] window[kCurrent.val] selected selectedCurrent hrecord hrecordCurrent
      hselectedActual hselectedCurrent hsameSigma
  have hcurrentPayload : selectedCurrent.view.payload =
      payload z := by
    simpa [ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPayload,
      ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusRemainder] using
        (ReferenceFirstLiveSourceCellReadout.source_current_cell_payload
          rate rewards C_star C_h q t s hs control0 z)
  exact hpayloadEq.trans hcurrentPayload

/-- The selected current payload has the real first-launch clock and its
anchor is both the zero-prefix score weight and the all-one anchor installed
by the actual corrected launch. -/
theorem source_current_anchor_origin (z : Zplus) :
    (payload z).sigma.val = s ∧
      (payload z).anchor =
        RecordedQueueRun.scoreWeight queue
          (RecordedQueueRun.run queue
            ((cells z).take 0)) ∧
      (∀ j : Fin p.K,
        (payload z).anchor j = 1) := by
  classical
  let source := z.val.val
  let hc := z.val.property.2.1
  let count := ReferenceFirstLiveSourceCellReadout.sourceCurrentCount t s
  let start := ReferenceFirstLiveSourceCellReadout.sourceCurrentElapsed
    rate rewards C_star C_h q t s hs control0 z
  let hspan := ReferenceFirstLiveSourceCellReadout.source_current_span
    rate rewards C_star C_h q t s hs control0 z
  let initial := ReferenceFirstLaunchNumericalCell.launchState
    rate source rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  let run := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate source rewards C_star C_h hc count hspan
  let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan
  let current := currentCell z
  let kCurrent := ReferenceFirstLiveSourceCellReadout.sourceCurrentIndex
    rate rewards C_star C_h q t s hs control0 z
  have hrecords : window = run.records := by
    simpa [window, run, source, hc, count, hspan,
      ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
      ReferenceFirstLiveSourceCellReadout.sourceCurrentWindow,
      ReferenceFirstLiveSourceCellReadout.sourceCurrentCount] using
        (ReferenceFirstLiveSourceCellReadout.source_current_window
          rate rewards C_star C_h q t s hs control0 z).1
  have hrecordCurrent : window[kCurrent.val] ∈ run.records := by
    rw [← hrecords]
    exact List.getElem_mem kCurrent.isLt
  have hselectedCurrent :
      window[kCurrent.val].output.preparation.coordinator.selection = some current.selected := by
    exact current.selection_actual
  have hgeometry := ReferenceFirstLiveDownNumericalRecovery.first_live_geometry
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hspan seed.activeAtStart seed.coordinatorFirst
    kCurrent current.selected current.selection_actual
  have hstart : start = s :=
    ReferenceFirstLiveSourceCellReadout.source_current_elapsed_eq
      rate rewards C_star C_h q t s hs control0 z
  have hpayload : current.selected.view.payload =
      payload z :=
    source_current_payloads_eq rate rewards C_star C_h q t s hs control0 z kCurrent
  have hsigma :
      (payload z).sigma.val = s := by
    rw [← hpayload]
    exact hgeometry.1.trans hstart
  have hReplay := ReferenceFirstLiveComplementQueueReplay.actual_first_live_complement_prefix_replay
    rate source rewards C_star C_h hc count hspan count (by
      have hlength := ReferenceFirstLiveSourceCellReadout.source_current_window_length
        rate rewards C_star C_h q t s hs control0 z
      simpa [window, count, ReferenceFirstLiveSourceCellReadout.sourceCurrentWindow] using
        hlength.symm.le)
  rcases hReplay with ⟨_, _, hpositive⟩
  have hcountPositive : 0 < count := by
    dsimp [count, ReferenceFirstLiveSourceCellReadout.sourceCurrentCount]
    omega
  rcases hpositive hcountPositive with
    ⟨endpoint, owned, base, hendpointCoord, _, hendpointSigma, _, _, _⟩
  have hendpointCoordRun :
      (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count
        hspan seed.activeAtStart).finalState.coordinator =
        .live endpoint owned base := by
    simpa [initial, start, seed,
      ReferenceFirstLiveSourceCellReadout.sourceCurrentElapsed,
      ReferenceFirstLaunchNumericalCell.launchState,
      ReferenceFirstWindowNumericalStream.actualFirstLiveSeed] using hendpointCoord
  have hanchorEndpoint : ∀ j : Fin p.K, endpoint.payload.anchor j = 1 := by
    have hwindowBound : count ≤
        (ReferenceFirstComplementMassBudget.firstWindow initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          start count hspan seed.activeAtStart).length := by
      change count ≤ (sourceWindow z).length
      exact (ReferenceFirstLiveSourceCellReadout.source_current_window_length
        rate rewards C_star C_h q t s hs control0 z).symm.le
    have hweight := ReferenceFirstLiveWeightEnvelope.run_first_live_weight_envelope
      initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards start count hspan seed.activeAtStart seed.coordinatorFirst
      count le_rfl hwindowBound
    rw [hendpointCoordRun] at hweight
    exact hweight.1
  have hstored : ReferenceAssignmentPayloadPersistence.storedPayload
      (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count
        hspan seed.activeAtStart).finalState.coordinator = some endpoint.payload := by
    rw [hendpointCoordRun]
    rfl
  have hendpointSigmaStart : endpoint.payload.sigma.val = start := by
    simpa [start, ReferenceFirstLiveSourceCellReadout.sourceCurrentElapsed] using
      hendpointSigma
  have hselectedSigma : current.selected.view.payload.sigma.val = endpoint.payload.sigma.val :=
    hgeometry.1.trans hendpointSigmaStart.symm
  have hendpointPayload :=
    ReferenceSelectedPayloadChronology.run_actualSelectedPayload_eq_of_prefix_storedPayload_equal_sigma
      initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards start count hspan seed.activeAtStart seed.coordinatorFirst
      window[kCurrent.val]
      current.selected
      hrecordCurrent hselectedCurrent count le_rfl endpoint.payload hstored
      hselectedSigma
  have hpayloadEndpoint :
      payload z = endpoint.payload :=
    hpayload.symm.trans hendpointPayload.1
  have hanchorOne : ∀ j : Fin p.K,
      (payload z).anchor j = 1 := by
    intro j
    rw [hpayloadEndpoint]
    exact hanchorEndpoint j
  have hunit : (payload z).anchor =
      fun _ : Fin p.K => (1 : ℝ) := funext hanchorOne
  have hzero : RecordedQueueRun.scoreWeight queue
      (RecordedQueueRun.run queue
        ((cells z).take 0)) =
      fun _ : Fin p.K => (1 : ℝ) := by
    funext j
    simp [RecordedQueueRun.scoreWeight, RecordedQueueRun.run,
      RecordedQueueRun.initialState, RecordedQueueRun.execute,
      ScoreWeights.scoreWeight]
  exact ⟨hsigma, hunit.trans hzero.symm, hanchorOne⟩

/-- The actual current record has the source grid bound, and the entire first
window including its current update fits in the source episode horizon. -/
theorem source_current_episode_age (z : Zplus) :
    t.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val
      (payload z).sigma ∧
    n + 1 ≤ ReplayWeightStability.episodeHorizon rate.eta.val := by
  classical
  let source := z.val.val
  let hc := z.val.property.2.1
  let count := ReferenceFirstLiveSourceCellReadout.sourceCurrentCount t s
  let start := ReferenceFirstLiveSourceCellReadout.sourceCurrentElapsed
    rate rewards C_star C_h q t s hs control0 z
  let hspan := ReferenceFirstLiveSourceCellReadout.source_current_span
    rate rewards C_star C_h q t s hs control0 z
  let initial := ReferenceFirstLaunchNumericalCell.launchState
    rate source rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  let kCurrent := ReferenceFirstLiveSourceCellReadout.sourceCurrentIndex
    rate rewards C_star C_h q t s hs control0 z
  let current := currentCell z
  have hpayload : current.selected.view.payload =
      payload z :=
    source_current_payloads_eq rate rewards C_star C_h q t s hs control0 z kCurrent
  have hgeometry := ReferenceFirstLiveDownNumericalRecovery.first_live_geometry
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hspan seed.activeAtStart seed.coordinatorFirst
    kCurrent current.selected current.selection_actual
  let geometryWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan
      seed.activeAtStart).records
  let geometryRecord := geometryWindow[kCurrent.val]
  have hstart : start = s :=
    ReferenceFirstLiveSourceCellReadout.source_current_elapsed_eq
      rate rewards C_star C_h q t s hs control0 z
  have htimeStart : geometryRecord.input.time.val = start + kCurrent.val := by
    simpa [geometryRecord, geometryWindow] using hgeometry.2.1
  have htime : geometryRecord.input.time.val = t.val := by
    have hk := ReferenceFirstLiveSourceCellReadout.source_current_index_val
      rate rewards C_star C_h q t s hs control0 z
    omega
  have hgridCurrent : geometryRecord.input.time.val + 2 ≤
      FollowerCutoffScan.gridBoundary p rate.eta.val current.selected.view.payload.sigma := by
    simpa [geometryRecord, geometryWindow] using hgeometry.2.2.1
  have hgrid : t.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val
      (payload z).sigma := by
    rw [← hpayload]
    omega
  have hH : 0 < ReplayWeightStability.episodeHorizon rate.eta.val :=
    FollowerCutoffScan.episodeHorizon_pos_of_source_cap p rate.eta.val
      rate.eta.property rate.sourceCap
  have hsourceEnd := RecordedEpisodeStability.sourceEpisodeEnd_bounds p.T
    (ReplayWeightStability.episodeHorizon rate.eta.val) (s + 1) hH (by omega) (by omega)
  have hboundary : FollowerCutoffScan.gridBoundary p rate.eta.val (payload z).sigma =
      RecordedEpisodeStability.sourceEpisodeEnd p.T
        (ReplayWeightStability.episodeHorizon rate.eta.val) (s + 1) := by
    have hsigma := (source_current_anchor_origin
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

/-- Every actual stopped-run queue prefix through the current first-live
window obeys the anchor envelope, including the inclusive overflow update and
all later frozen prefixes. -/
theorem source_current_prefix_anchor_weight_envelope (z : Zplus) (b : ℕ)
    (hb : b ≤ n + 1) (j : Fin p.K) :
    0 < (payload z).anchor j ∧
      (payload z).anchor j ≤
        RecordedQueueRun.scoreWeight queue
          (RecordedQueueRun.run queue
            ((cells z).take b)) j ∧
      RecordedQueueRun.scoreWeight queue
          (RecordedQueueRun.run queue
            ((cells z).take b)) j <
        2 * (payload z).anchor j := by
  have horigin := source_current_anchor_origin
    rate rewards C_star C_h q t s hs control0 z
  have hage := source_current_episode_age rate rewards C_star C_h q t s hs control0 z
  have hlength : ((cells z).take b).length ≤ b := by
    simp
  have hprefixHorizon :
      ((cells z).take b).length - 0 ≤
        ReplayWeightStability.episodeHorizon rate.eta.val := by
    simpa using hlength.trans (by omega : b ≤ ReplayWeightStability.episodeHorizon rate.eta.val)
  have henv := RecordedWeightedDrift.actual_anchor_envelope queue
    ((cells z).take b) 0 (by omega)
    hprefixHorizon j
  have hstartOne : RecordedQueueRun.scoreWeight queue
      (RecordedQueueRun.run queue []) j = 1 := by
    simp [RecordedQueueRun.scoreWeight, RecordedQueueRun.run,
      RecordedQueueRun.initialState, RecordedQueueRun.execute, ScoreWeights.scoreWeight]
  refine ⟨?_, ?_, ?_⟩
  · simp [horigin.2.2 j]
  · simpa [horigin.2.2 j, hstartOne] using henv.2.1
  · simpa [horigin.2.2 j, hstartOne] using henv.2.2

/-- The current logical all-arm inclusion marginals, divided by the literal
actual marker rates, satisfy the shared canonical `R` bound on every point of
the continuing first-live source carrier. -/
theorem sum_thetaBefore_div_markerRatePlus_le_R (z : Zplus) :
    (∑ j : Fin p.K,
      ProductSetLaw.theta p.m
        (RecordedQueueRun.scoreWeight queue (past z)) j /
        markerRate j z) ≤
      CanonicalRecordingRates.R p := by
  have hweight := source_current_prefix_anchor_weight_envelope
    rate rewards C_star C_h q t s hs control0 z (n) (by omega)
  have hsum := CanonicalRecordingRates.sum_theta_div_xi_le_R p rate.eta.property
    (payload z).anchor
    (fun j => RecordedQueueRun.scoreWeight queue
      (RecordedQueueRun.run queue
        ((cells z).take n)) j)
    (fun j => (hweight j).1)
    (fun j => ⟨(hweight j).2.1, le_of_lt (hweight j).2.2⟩)
  have hrate (j : Fin p.K) :
      markerRate j z =
        CanonicalRecordingRates.xi p rate.eta.val
          (payload z).anchor j := rfl
  calc
    (∑ j : Fin p.K,
        ProductSetLaw.theta p.m
          (RecordedQueueRun.scoreWeight queue
            (past z)) j /
          markerRate j z) =
        ∑ j : Fin p.K,
          ProductSetLaw.theta p.m
            (RecordedQueueRun.scoreWeight queue
              (RecordedQueueRun.run queue
                ((cells z).take n))) j /
            CanonicalRecordingRates.xi p rate.eta.val
              (payload z).anchor j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hrate j]
    _ ≤ CanonicalRecordingRates.R p := hsum

end Bandits.Support.ReferenceFirstLiveAnchorRateFeasibility

end
