/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstWindowNumericalStream

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Coordinator arrivals on the actual first-live window

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-396`,
`sources/zip4/manuscript/06_interruptions.tex:192-233,246-295,391-397`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:34-64`.

For each actual first-live record, this module identifies the coordinator's
retained output with the coordinator-source projection of the complete
snapshot recording map and with the corresponding all-arm queue arrivals.
The actual branch and clock establish that the recorder is enabled; the
numerical cell's enabled field alone is not used as that argument.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceFirstWindowRecordingTruth
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.ReferenceCoordinatorRecorderCallTrace
open Bandits.Support.ReferenceCoordinatorRecorderCallCorrespondence
open Bandits.Support.ReferenceLiveDispatchOutputMeasurability
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.CoordinatorLiveServiceFinish
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CanonicalRecordingSlice
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.SnapshotRecordingKernel
open Bandits.Support.RecordedQueueRun
open Bandits.Support.ReferenceFirstLaunchNumericalCell
open Bandits.Support.AssignmentStartPayload
open Bandits.Support.RealRewardGridCount
open Bandits.Support.PublicDiscreteDraws

namespace Bandits.Support.ReferenceFirstLiveCoordinatorArrivals

variable {p : ConstructorDimensions.Parameters}
  {rate : ReferenceFirstWindowNumericalStream.RateInput p}

private theorem coordinator_floor_eq_queue_arrival
    (rate : ReferenceFirstWindowNumericalStream.RateInput p)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (round : RecordedQueueRun.RoundInput p.K)
    (arm : Fin p.K)
    (rewardValue : Fin p.K → ℝ)
    (hreward : ∀ j, round.reward j = rewardValue j)
    (hrate : round.rate = payload.rate)
    (hrecorded : round.recordedArm = some arm) :
    SnapshotRecordingKernel.recordedIncrement p rate.eta.val payload.anchor
        rewardValue (some arm) =
      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        round arm := by
  unfold SnapshotRecordingKernel.recordedIncrement RecordedQueueRun.quantizedArrival
  rw [hrecorded]
  simp only
  apply congrArg Nat.floor
  simp only [ReferenceFirstLaunchNumericalCell.queueParameters]
  rw [rate.n_scale]
  rw [hrate, payload.rate_eq_canonical arm, hreward arm]
  ring

/-- The actual snapshot source map keeps the complete pending set and every
follower status. Its `some arm` event is exactly the DATA, action, ownership,
full nonowner-pilot mask, and inclusive thinning tests of the kernel. -/
theorem sourceArm_some_iff_gate_tests
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (pending : Finset (ActiveRoundActions.Follower p.m))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (complement : FastArm payload.slowSet → ℝ)
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p))
    (hvalid : ChoiceInputsValid payload cutoff record.input.time complement)
    (arm : Fin p.K) :
    ReferenceFirstWindowNumericalStream.sourceArm record payload pending states
        complement cutoff hvalid = some arm ↔
      let slice := (record.input.row.2 record.input.time).1
      let regime : SnapshotRecordingKernel.Regime p :=
        .live payload.assignment { missing := pending, status := fun i => (states i).status }
      let weights := ReferenceFirstWindowNumericalStream.sourceWeights payload complement
      let source := CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec slice)
      slotFromScalar
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.slot slice) =
        dataSlot ∧
        SnapshotRecordingKernel.dataAction p regime rate.eta.val rate.eta.property
          rate.sourceCap payload.anchor weights payload.anchor_pos
          (ReferenceFirstWindowNumericalStream.sourceWeights_pos payload complement cutoff
            record.input.time hvalid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_lower payload complement cutoff
            record.input.time hvalid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_upper payload complement cutoff
            record.input.time hvalid) slice source = arm ∧
        SnapshotRecordingKernel.owns p regime source arm ∧
        recordingMask (ConstructorDimensions.K_pos p) source arm slice ∧
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin slice).val ≤
          SnapshotRecordingKernel.thinningThreshold p regime rate.eta.val rate.eta.property
            rate.sourceCap payload.anchor weights payload.anchor_pos
            (ReferenceFirstWindowNumericalStream.sourceWeights_pos payload complement cutoff
              record.input.time hvalid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_lower payload complement cutoff
              record.input.time hvalid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_upper payload complement cutoff
              record.input.time hvalid) source arm := by
  dsimp only [ReferenceFirstWindowNumericalStream.sourceArm]
  rw [SnapshotRecordingKernel.recordingMap_some_iff]

/-- A recorded arm has the unique source owner determined by the same live
assignment and full pre-round snapshot used in its map. -/
theorem sourceArm_ownerSource
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (pending : Finset (ActiveRoundActions.Follower p.m))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (complement : FastArm payload.slowSet → ℝ)
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p))
    (hvalid : ChoiceInputsValid payload cutoff record.input.time complement)
    (arm : Fin p.K)
    (hrecorded : ReferenceFirstWindowNumericalStream.sourceArm record payload pending states
      complement cutoff hvalid = some arm) :
    CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec
          ((record.input.row.2 record.input.time).1)) =
      SnapshotRecordingKernel.ownerSource p
        (.live payload.assignment { missing := pending, status := fun i => (states i).status }) arm := by
  let regime : SnapshotRecordingKernel.Regime p :=
    .live payload.assignment { missing := pending, status := fun i => (states i).status }
  let source := CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
    (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec
      ((record.input.row.2 record.input.time).1))
  have htests := (sourceArm_some_iff_gate_tests record payload pending states complement cutoff
    hvalid arm).mp hrecorded
  exact SnapshotRecordingKernel.owns_unique p regime arm source
    (SnapshotRecordingKernel.ownerSource p regime arm) htests.2.2.1
    (SnapshotRecordingKernel.owns_ownerSource p regime arm)

/-- The actual numerical cell's successful-source event retains every field
of its selected payload, pending set, follower-status snapshot, weights,
cutoff, and validity witness. -/
theorem actual_first_live_source_gate_tests
    (source : ReferenceFirstWindowNumericalStream.SourceInput p)
    (rewards : ReferenceFirstWindowNumericalStream.RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (k : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length) :
    let record := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan)[k.val]
    let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan k
    ∀ arm, ReferenceFirstWindowNumericalStream.sourceArm record cell.selected.view.payload
      cell.selected.view.pendingAtChoice cell.states cell.selected.view.complementWeights
      cell.selected.view.cutoff cell.choiceInputsValid = some arm ↔
      let slice := (record.input.row.2 record.input.time).1
      let regime : SnapshotRecordingKernel.Regime p :=
        .live cell.selected.view.payload.assignment
          { missing := cell.selected.view.pendingAtChoice, status := fun i => (cell.states i).status }
      let weights := ReferenceFirstWindowNumericalStream.sourceWeights
        cell.selected.view.payload cell.selected.view.complementWeights
      let source := CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec slice)
      slotFromScalar (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.slot slice) =
        dataSlot ∧
      SnapshotRecordingKernel.dataAction p regime rate.eta.val rate.eta.property
        rate.sourceCap cell.selected.view.payload.anchor weights
        cell.selected.view.payload.anchor_pos
        (ReferenceFirstWindowNumericalStream.sourceWeights_pos cell.selected.view.payload
          cell.selected.view.complementWeights cell.selected.view.cutoff record.input.time
          cell.choiceInputsValid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_lower cell.selected.view.payload
          cell.selected.view.complementWeights cell.selected.view.cutoff record.input.time
          cell.choiceInputsValid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_upper cell.selected.view.payload
          cell.selected.view.complementWeights cell.selected.view.cutoff record.input.time
          cell.choiceInputsValid) slice source = arm ∧
      SnapshotRecordingKernel.owns p regime source arm ∧
      recordingMask (ConstructorDimensions.K_pos p) source arm slice ∧
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin slice).val ≤
        SnapshotRecordingKernel.thinningThreshold p regime rate.eta.val rate.eta.property
          rate.sourceCap cell.selected.view.payload.anchor weights cell.selected.view.payload.anchor_pos
          (ReferenceFirstWindowNumericalStream.sourceWeights_pos cell.selected.view.payload
            cell.selected.view.complementWeights cell.selected.view.cutoff record.input.time
            cell.choiceInputsValid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_lower cell.selected.view.payload
            cell.selected.view.complementWeights cell.selected.view.cutoff record.input.time
            cell.choiceInputsValid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_upper cell.selected.view.payload
            cell.selected.view.complementWeights cell.selected.view.cutoff record.input.time
            cell.choiceInputsValid) source arm := by
  dsimp only
  intro arm
  exact sourceArm_some_iff_gate_tests _ _ _ _ _ _ _ arm

/-- Every successful actual source-map entry is assigned to the unique source
owner of that arm under the cell's unchanged assignment and full snapshot. -/
theorem actual_first_live_source_owner
    (source : ReferenceFirstWindowNumericalStream.SourceInput p)
    (rewards : ReferenceFirstWindowNumericalStream.RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (k : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length) :
    let record := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan)[k.val]
    let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan k
    ∀ arm,
      ReferenceFirstWindowNumericalStream.sourceArm record cell.selected.view.payload
        cell.selected.view.pendingAtChoice cell.states cell.selected.view.complementWeights
        cell.selected.view.cutoff cell.choiceInputsValid = some arm →
      CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec
            ((record.input.row.2 record.input.time).1)) =
        SnapshotRecordingKernel.ownerSource p
          (.live cell.selected.view.payload.assignment
            { missing := cell.selected.view.pendingAtChoice, status := fun i => (cell.states i).status }) arm := by
  dsimp only
  intro arm hrecorded
  exact sourceArm_ownerSource _ _ _ _ _ _ _ arm hrecorded

/-- A source-selected follower remains part of the full map, but the
coordinator-source projection is none on that same row. -/
theorem live_coordinator_part_none_of_other_source
    (input : CoordinatorRecordingOperation.Input p)
    (hvalid : CoordinatorRecordingOperation.InputsValid input)
    (assignment : Assignment p.m p.K)
    (snapshot : ActiveRoundActions.Snapshot assignment)
    (enabled : Bool)
    (hsource : CoordinatorRecordingOperation.selectedRecorder input ≠
      ActiveRoundActions.coordinator p.two_le_m) :
    CoordinatorRecordingOperation.liveCoordinatorSourceMapPart input hvalid assignment
      snapshot enabled = none := by
  unfold CoordinatorRecordingOperation.liveCoordinatorSourceMapPart
  simp [hsource]

private theorem finish_coordinator_arrival_projection
    (rate : ReferenceFirstWindowNumericalStream.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (input : RecordedQueueRun.RoundInput p.K)
    (hreward : ∀ j, input.reward j =
      RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        (record.input.rewards record.input.time j))
    (hrate : input.rate = payload.rate)
    (src : Fin p.m)
    (out : CoordinatorRecordingOperation.Output p)
    (E : Option (Fin p.K))
    (hrecording : record.output.coordinator.recording = some out)
    (hgate : out.gateArm = E)
    (hpart : E = if src = ActiveRoundActions.coordinator p.two_le_m then
      input.recordedArm else none)
    (hraw : out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
      payload.anchor
      (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        (record.input.rewards record.input.time j)) E)
    (htrace : ∀ arm : Fin p.K,
      ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
        (ReferenceActiveHorizonMeasurability.roundRecordCode record) arm =
        some (if out.gateArm = some arm then out.rawArrival else 0)) :
    ∃ actual : CoordinatorRecordingOperation.Output p,
      record.output.coordinator.recording = some actual ∧
      actual.gateArm =
        (if src = ActiveRoundActions.coordinator p.two_le_m then input.recordedArm else none) ∧
      (∀ arm : Fin p.K,
        ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) arm =
          some (if src = ActiveRoundActions.coordinator p.two_le_m then
            RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) input arm else 0)) ∧
      (∀ arm : Fin p.K, (record.input.rewards record.input.time arm).val = 0 →
        ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) arm = some 0) := by
  refine ⟨out, hrecording, ?_, ?_, ?_⟩
  · rw [hgate, hpart]
  · intro arm
    rw [htrace arm, hgate, hpart]
    by_cases hsrc : src = (ActiveRoundActions.coordinator p.two_le_m)
    · by_cases hrecorded : input.recordedArm = some arm
      ·
        have hfloor := coordinator_floor_eq_queue_arrival rate payload input arm
          (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (record.input.rewards record.input.time j)) hreward hrate hrecorded
        have houtFloor : out.rawArrival =
            RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) input arm := by
          calc
            out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
                payload.anchor
                (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
                  (record.input.rewards record.input.time j)) E := hraw
            _ = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
                payload.anchor
                (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
                  (record.input.rewards record.input.time j)) (some arm) := by
              rw [hpart, ite_eq_left hsrc, hrecorded]
            _ = RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) input arm := hfloor
        simp [hsrc, hrecorded, houtFloor]
      ·
        have hquantized : RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) input arm = 0 := by
          rw [RecordedQueueRun.quantizedArrival, ite_eq_right hrecorded]
        simp [hsrc, hrecorded, hquantized]
    · simp [hsrc]
  · intro arm hzero
    rw [htrace arm, hgate, hpart]
    by_cases hsrc : src = (ActiveRoundActions.coordinator p.two_le_m)
    · by_cases hrecorded : input.recordedArm = some arm
      ·
        have hfloor := coordinator_floor_eq_queue_arrival rate payload input arm
          (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (record.input.rewards record.input.time j)) hreward hrate hrecorded
        have hquantized : RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) input arm = 0 := by
          rw [RecordedQueueRun.quantizedArrival, ite_eq_left hrecorded, hreward arm]
          simp [RealRewardGridCount.realRewardGridValue, hzero,
            ReferenceFirstLaunchNumericalCell.queueParameters]
        have hrawZero : out.rawArrival = 0 := by
          calc
            out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
                payload.anchor
                (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
                  (record.input.rewards record.input.time j)) E := hraw
            _ = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
                payload.anchor
                (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
                  (record.input.rewards record.input.time j)) (some arm) := by
              rw [hpart, ite_eq_left hsrc, hrecorded]
            _ = RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) input arm := hfloor
            _ = 0 := hquantized
        simp [hsrc, hrecorded, hrawZero]
      · simp [hsrc, hrecorded]
    · simp [hsrc]

/-- The actual coordinator recorder output on one first-live record is the
coordinator-source part of the numerical cell's whole snapshot map. Its raw
diagnostic is `some` on every arm, including zero arrivals. -/
theorem actual_first_live_coordinator_source_arrivals
    (rate : ReferenceFirstWindowNumericalStream.RateInput p)
    (source : ReferenceFirstWindowNumericalStream.SourceInput p)
    (rewards : ReferenceFirstWindowNumericalStream.RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (k : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length) :
    let record :=
      (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate source rewards C_star C_h hc count hspan)[k.val]
    let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan k
    let src := PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
      ((record.input.row.2 record.input.time).1)
    ∃ out : CoordinatorRecordingOperation.Output p,
      record.output.coordinator.recording = some out ∧
      out.gateArm =
        (if src = ActiveRoundActions.coordinator p.two_le_m then cell.input.recordedArm else none) ∧
      (∀ arm : Fin p.K,
        ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) arm =
          some (if src = ActiveRoundActions.coordinator p.two_le_m then
            RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input arm else 0)) ∧
      (∀ arm : Fin p.K, (record.input.rewards record.input.time arm).val = 0 →
        ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) arm = some 0) := by
  classical
  dsimp only
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  let start := ReferenceInitializationRun.elapsed p b.completed
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  let physicalRun := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate source rewards C_star C_h hc count hspan
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow physicalRun.records
  let record := W[k.val]
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hc count hspan k
  let src := PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
    ((record.input.row.2 record.input.time).1)
  have hwindow := ReferenceFirstWindowRecordingTruth.run_first_live_window_recording_truth
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hspan seed.activeAtStart seed.coordinatorFirst
    seed.followers seed.memory seed.configuration seed.S_zero seed.delta_zero
    seed.backlog_zero seed.lastDown_none seed.unoccupied seed.bufferValid
    seed.chronologicalBuffer seed.bufferStamps seed.decoderValid
  have hentry := hwindow k
  rcases hentry with ⟨_hinputs, _hfailure, states, memories, hordinary, hbranch⟩
  rcases hbranch with hfirstBranch | hcontinuingBranch
  · rcases hfirstBranch with
      ⟨installed, arm, hbranch, _hfields, htime, selected, hselected,
        hselectionEq, _hinputSelection, _hselectedFields, out, hrecording,
        hidentity, _hlive, _hdata⟩
    cases hcell : cell with
    | mk cellStates cellMemories cellOrdinary cellSelected cellSelectionActual
        cellAssignmentLive cellChoiceInputsValid cellInput cellInputEq cellEnabled
        cellRecordedArmEq cellQuantizedArrivalEq cellCoordinatorProjection
        cellFollowerDataClaim cellFollowerRawArrivalGate cellFollowerRawArrivalNoGate =>
      have hsel : selected = cellSelected :=
        Option.some.inj (hselected.symm.trans cellSelectionActual)
      subst selected
      subst cellSelected
      let branchSelection := ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm record.input
        installed.registers.payload installed.startRoundResult installed.registers.time
        installed.registers.complementWeights arm htime
      let I := ReferenceActivePhysicalStep.liveRecordingInput
        (ReferenceActivePhysicalStep.prepare record.input) installed.registers
        installed.startRoundResult
      let valid := CoordinatorRecorderComplementBridge.recorderInput_inputsValid I
        (ReferenceCoordinatorLiveRecording.liveRecordingInput_valid
          record.output.preparation installed.registers installed.startRoundResult
          installed.registers.time arm)
      let E := CoordinatorRecordingOperation.liveCoordinatorSourceMapPart
        (CoordinatorRecorderComplementBridge.recorderInput I) valid
        installed.registers.payload.assignment
        { missing := installed.startRoundResult.pending
          status := fun i => (states i).status }
        (decide (¬ CoordinatorRecorderComplementBridge.isFrozen I))
      rcases hidentity with ⟨_hRun, hgate, hraw, htrace⟩
      have hstatuses : (fun i => (states i).status) = fun i => (cellStates i).status := by
        funext i
        have hconf := (hordinary i).symm.trans (cellOrdinary i)
        have hstatus := congrArg
          (fun c : DeclaredFollowerLocalRound.LocalConfiguration p rate =>
            match c with
            | .ordinary state _ => state.status
            | .dagger => FollowerStatus.unoccupied) hconf
        exact hstatus
      have hweights : CoordinatorRecorderComplementBridge.extendedCurrentWeights I =
          ReferenceFirstWindowNumericalStream.sourceWeights branchSelection.view.payload
            branchSelection.view.complementWeights := by
        funext j
        by_cases hslow : j ∈ installed.registers.payload.slowSet.1
        · simp [branchSelection, hslow,
            CoordinatorRecorderComplementBridge.extendedCurrentWeights,
            ReferenceFirstWindowNumericalStream.sourceWeights,
            ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm]
        · simp [branchSelection, hslow,
            CoordinatorRecorderComplementBridge.extendedCurrentWeights,
            ReferenceFirstWindowNumericalStream.sourceWeights,
            ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm]
          all_goals rfl
      have hslice : ContinuousLearningRows.sliceAt I.time I.row.2 =
          (record.input.row.2 record.input.time).1 := rfl
      have hsnapshot :
          ({ missing := installed.startRoundResult.pending, status := fun i => (states i).status } :
            ActiveRoundActions.Snapshot installed.registers.payload.assignment) =
          { missing := branchSelection.view.pendingAtChoice, status := fun i => (cellStates i).status } := by
        change ({ missing := installed.startRoundResult.pending, status := fun i => (states i).status } :
            ActiveRoundActions.Snapshot installed.registers.payload.assignment) =
          { missing := installed.startRoundResult.pending, status := fun i => (cellStates i).status }
        exact congrArg (fun status : Fin (p.m - 1) → FollowerStatus =>
          (⟨installed.startRoundResult.pending, status⟩ :
            ActiveRoundActions.Snapshot installed.registers.payload.assignment)) hstatuses
      have hmapActual : SnapshotRecordingKernel.recordingMap p
          (.live installed.registers.payload.assignment
            { missing := installed.startRoundResult.pending, status := fun i => (states i).status })
          true rate.eta.val rate.eta.property rate.sourceCap installed.registers.payload.anchor
          (CoordinatorRecorderComplementBridge.extendedCurrentWeights I)
          valid.anchor_pos valid.current_pos valid.anchor_le_current valid.current_le_twice_anchor
          (ContinuousLearningRows.sliceAt I.time I.row.2) =
        ReferenceFirstWindowNumericalStream.sourceArm record branchSelection.view.payload
          branchSelection.view.pendingAtChoice cellStates branchSelection.view.complementWeights
          branchSelection.view.cutoff cellChoiceInputsValid := by
        simp only [ReferenceFirstWindowNumericalStream.sourceArm, branchSelection,
          ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm,
          hweights, hslice, hsnapshot]
        all_goals rfl
      have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames record
      have hbranchRecord := hbranch
      change record.output.preparation.coordinator = _ at hbranchRecord
      rw [hbranchRecord] at hframes
      have hstrict : record.input.time.val + 1 < installed.startRoundResult.clock.g :=
        hframes.2.2
      have hnotFrozen : ¬ CoordinatorRecorderComplementBridge.isFrozen I := by
        intro hfrozen
        dsimp only [CoordinatorRecorderComplementBridge.isFrozen] at hfrozen
        have hround := hfrozen.2
        change record.input.time.val + 1 ≥ installed.startRoundResult.clock.g at hround
        omega
      have hsource : CoordinatorRecordingOperation.selectedRecorder
          (CoordinatorRecorderComplementBridge.recorderInput I) = src := by
        change CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec
            (ContinuousLearningRows.sliceAt record.input.time record.input.row.2)) = src
        rw [CanonicalRecordingSlice.recorderSourceFromScalar_coordinate]
        rfl
      have hcellRecordedArmEq : cellInput.recordedArm =
          ReferenceFirstWindowNumericalStream.sourceArm record branchSelection.view.payload
            branchSelection.view.pendingAtChoice cellStates branchSelection.view.complementWeights
            branchSelection.view.cutoff cellChoiceInputsValid := by
        have h := cellRecordedArmEq
        change cellInput.recordedArm = _ at h
        exact h
      have hpart : E =
          if src = ActiveRoundActions.coordinator p.two_le_m then cellInput.recordedArm else none := by
        unfold E CoordinatorRecordingOperation.liveCoordinatorSourceMapPart
        rw [hsource]
        by_cases hsrc : src = ActiveRoundActions.coordinator p.two_le_m
        · simp only [ite_eq_left hsrc, decide_eq_true hnotFrozen]
          rw [hcellRecordedArmEq]
          simpa [ReferenceFirstWindowNumericalStream.sourceArm,
            CoordinatorRecorderComplementBridge.recorderInput,
            CoordinatorRecorderComplementBridge.recorderInputWithWeights,
            ReferenceActivePhysicalStep.liveRecordingInput] using hmapActual
        · simp [hsrc]
      have hrawCell : out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
          branchSelection.view.payload.anchor
          (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (record.input.rewards record.input.time j)) E := by
        have h := hraw
        change out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
          branchSelection.view.payload.anchor
          (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (record.input.rewards record.input.time j)) E at h
        exact h
      have hreward : ∀ j, cellInput.reward j =
          RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (record.input.rewards record.input.time j) := by
        intro j
        rw [cellInputEq]
        rfl
      have hrate : cellInput.rate = branchSelection.view.payload.rate := by
        rw [cellInputEq]
        rfl
      have hactualInput :
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
            rate source rewards C_star C_h hc count hspan k).input = cellInput := by
        change cell.input = cellInput
        rw [hcell]
      have hresult := finish_coordinator_arrival_projection rate record branchSelection.view.payload
        cellInput hreward hrate src out E hrecording hgate hpart hrawCell htrace
      rw [← hactualInput] at hresult
      exact hresult

  · rcases hcontinuingBranch with
      ⟨r, q, base, dispatched, hstart, continuation, arm, hbranch, _hfields,
        selected, hselected, hselectionEq, _hinputSelection, _hselectedFields,
        out, hrecording, hidentity, _hlive, _hdata⟩
    cases hcell : cell with
    | mk cellStates cellMemories cellOrdinary cellSelected cellSelectionActual
        cellAssignmentLive cellChoiceInputsValid cellInput cellInputEq cellEnabled
        cellRecordedArmEq cellQuantizedArrivalEq cellCoordinatorProjection
        cellFollowerDataClaim cellFollowerRawArrivalGate cellFollowerRawArrivalNoGate =>
      have hsel : selected = cellSelected :=
        Option.some.inj (hselected.symm.trans cellSelectionActual)
      subst selected
      subst cellSelected
      let registers := ReferenceActivePhysicalStep.liveRegistersAt r record.input.time
      let branchSelection := ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm record.input r.payload
        dispatched.startResult record.input.time registers.complementWeights arm rfl
      let I := ReferenceActivePhysicalStep.liveRecordingInput
        (ReferenceActivePhysicalStep.prepare record.input) registers dispatched.startResult
      let valid := CoordinatorRecorderComplementBridge.recorderInput_inputsValid I
        (ReferenceCoordinatorLiveRecording.liveRecordingInput_valid
          record.output.preparation registers dispatched.startResult record.input.time arm)
      let E := CoordinatorRecordingOperation.liveCoordinatorSourceMapPart
        (CoordinatorRecorderComplementBridge.recorderInput I) valid r.payload.assignment
        { missing := dispatched.startResult.pending
          status := fun i => (states i).status }
        (decide (¬ CoordinatorRecorderComplementBridge.isFrozen I))
      rcases hidentity with ⟨_hRun, hgate, hraw, htrace⟩
      have hstatuses : (fun i => (states i).status) = fun i => (cellStates i).status := by
        funext i
        have hconf := (hordinary i).symm.trans (cellOrdinary i)
        have hstatus := congrArg
          (fun c : DeclaredFollowerLocalRound.LocalConfiguration p rate =>
            match c with
            | .ordinary state _ => state.status
            | .dagger => FollowerStatus.unoccupied) hconf
        exact hstatus
      have hweights : CoordinatorRecorderComplementBridge.extendedCurrentWeights I =
          ReferenceFirstWindowNumericalStream.sourceWeights branchSelection.view.payload
            branchSelection.view.complementWeights := by
        funext j
        by_cases hslow : j ∈ r.payload.slowSet.1
        · simp [registers, branchSelection, hslow,
            CoordinatorRecorderComplementBridge.extendedCurrentWeights,
            ReferenceActivePhysicalStep.liveRegistersAt_fields,
            ReferenceFirstWindowNumericalStream.sourceWeights,
            ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm]
        · simp [I, registers, branchSelection, hslow,
            CoordinatorRecorderComplementBridge.extendedCurrentWeights,
            ReferenceActivePhysicalStep.liveRegistersAt_fields,
            ReferenceFirstWindowNumericalStream.sourceWeights,
            ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm]
          all_goals rfl
      have hslice : ContinuousLearningRows.sliceAt I.time I.row.2 =
          (record.input.row.2 record.input.time).1 := rfl
      have hsnapshot :
          ({ missing := dispatched.startResult.pending, status := fun i => (states i).status } :
            ActiveRoundActions.Snapshot r.payload.assignment) =
          { missing := branchSelection.view.pendingAtChoice, status := fun i => (cellStates i).status } := by
        change ({ missing := dispatched.startResult.pending, status := fun i => (states i).status } :
            ActiveRoundActions.Snapshot r.payload.assignment) =
          { missing := dispatched.startResult.pending, status := fun i => (cellStates i).status }
        exact congrArg (fun status : Fin (p.m - 1) → FollowerStatus =>
          (⟨dispatched.startResult.pending, status⟩ : ActiveRoundActions.Snapshot r.payload.assignment))
          hstatuses
      have hmapActual : SnapshotRecordingKernel.recordingMap p
          (.live r.payload.assignment
            { missing := dispatched.startResult.pending, status := fun i => (states i).status })
          true rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor
          (CoordinatorRecorderComplementBridge.extendedCurrentWeights I)
          valid.anchor_pos valid.current_pos valid.anchor_le_current valid.current_le_twice_anchor
          (ContinuousLearningRows.sliceAt I.time I.row.2) =
        ReferenceFirstWindowNumericalStream.sourceArm record branchSelection.view.payload
          branchSelection.view.pendingAtChoice cellStates branchSelection.view.complementWeights
          branchSelection.view.cutoff cellChoiceInputsValid := by
        simp only [ReferenceFirstWindowNumericalStream.sourceArm, registers, branchSelection,
          ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm,
          ReferenceActivePhysicalStep.liveRegistersAt, hslice, hsnapshot]
        all_goals rfl
      have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames record
      have hbranchRecord := hbranch
      change record.output.preparation.coordinator = _ at hbranchRecord
      rw [hbranchRecord] at hframes
      have hstrict : record.input.time.val + 1 < dispatched.startResult.clock.g := hframes.2
      have hnotFrozen : ¬ CoordinatorRecorderComplementBridge.isFrozen I := by
        intro hfrozen
        dsimp only [CoordinatorRecorderComplementBridge.isFrozen] at hfrozen
        have hround := hfrozen.2
        change record.input.time.val + 1 ≥ dispatched.startResult.clock.g at hround
        omega
      have hsource : CoordinatorRecordingOperation.selectedRecorder
          (CoordinatorRecorderComplementBridge.recorderInput I) = src := by
        change CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec
            (ContinuousLearningRows.sliceAt record.input.time record.input.row.2)) = src
        rw [CanonicalRecordingSlice.recorderSourceFromScalar_coordinate]
        rfl
      have hcellRecordedArmEq : cellInput.recordedArm =
          ReferenceFirstWindowNumericalStream.sourceArm record branchSelection.view.payload
            branchSelection.view.pendingAtChoice cellStates branchSelection.view.complementWeights
            branchSelection.view.cutoff cellChoiceInputsValid := by
        have h := cellRecordedArmEq
        change cellInput.recordedArm = _ at h
        exact h
      have hpart : E =
          if src = ActiveRoundActions.coordinator p.two_le_m then cellInput.recordedArm else none := by
        unfold E CoordinatorRecordingOperation.liveCoordinatorSourceMapPart
        rw [hsource]
        by_cases hsrc : src = ActiveRoundActions.coordinator p.two_le_m
        · simp only [ite_eq_left hsrc, decide_eq_true hnotFrozen]
          rw [hcellRecordedArmEq]
          simpa [ReferenceFirstWindowNumericalStream.sourceArm,
            CoordinatorRecorderComplementBridge.recorderInput,
            CoordinatorRecorderComplementBridge.recorderInputWithWeights,
            ReferenceActivePhysicalStep.liveRecordingInput, registers,
            ReferenceActivePhysicalStep.liveRegistersAt_fields] using hmapActual
        · simp [hsrc]
      have hrawCell : out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
          branchSelection.view.payload.anchor
          (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (record.input.rewards record.input.time j)) E := by
        have h := hraw
        change out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
          branchSelection.view.payload.anchor
          (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (record.input.rewards record.input.time j)) E at h
        exact h
      have hreward : ∀ j, cellInput.reward j =
          RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (record.input.rewards record.input.time j) := by
        intro j
        rw [cellInputEq]
        rfl
      have hrate : cellInput.rate = branchSelection.view.payload.rate := by
        rw [cellInputEq]
        rfl
      have hactualInput :
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
            rate source rewards C_star C_h hc count hspan k).input = cellInput := by
        change cell.input = cellInput
        rw [hcell]
      have hresult := finish_coordinator_arrival_projection rate record branchSelection.view.payload
        cellInput hreward hrate src out E hrecording hgate hpart hrawCell htrace
      rw [← hactualInput] at hresult
      exact hresult

end Bandits.Support.ReferenceFirstLiveCoordinatorArrivals

end
