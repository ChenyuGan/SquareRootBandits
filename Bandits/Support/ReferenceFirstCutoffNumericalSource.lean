/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveComplementQueueReplay
public import Bandits.Support.ReferenceFirstLiveFollowerQueueReplay
public import Bandits.Support.ReferenceGeneratedFirstCutoffSurvival

import Lean.Elab.Tactic.Omega

/-!
# Actual numerical source at the first cutoff

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-174`,
`sources/zip4/manuscript/05_binary_transport.tex:354-396,426-431`,
`sources/zip4/manuscript/06_interruptions.tex:246-275,391-397`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

This module identifies the collection recorder's actual numerical queue input
on the first cutoff round of the original physical run. The round input is
constructed from that round's collection recorder and retains the full reward
table and actual payload rates. Enabled zero-arrival service and disabled
preservation remain distinct. This is an internal first-cutoff result, not a
later collection-stream or regret theorem. The next numerical consumer is
`ReferenceFirstCutoffKnownNumericalState`, which must separately join the
actual successful START, receiver rejection, and FINISH.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.CoordinatorCollectionUpRoundStep
open Bandits.Support.ReferenceCollectionRawBufferHistory
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceDownReception
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.SnapshotRecordingKernel

namespace Bandits.Support.ReferenceFirstCutoffNumericalSource

variable {p : ConstructorDimensions.Parameters}

/-- The actual collection source cell at the first cutoff of the same
initialization and physical execution used for its first live window.

The premises are only the physical rate/source/reward inputs, the actual
initialization crossing, the requested run length and its horizon bound, and
the first-window-short condition locating a cutoff inside that run. All
queues, payloads, follower states, dispatch inputs, and the collection
recorder are computed from those same inputs.
-/
theorem actual_first_cutoff_numerical_source
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (hshort : (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length < count) :
    let init := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let boot := ReferenceInitializationRun.output init
    let s := ReferenceInitializationRun.elapsed p boot.completed
    let initial := ReferenceFirstLaunchNumericalCell.launchState
      rate source rewards C_star C_h hc
    let execution := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate source rewards C_star C_h hc count hspan
    let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan
    let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
      rate source rewards C_star C_h hc count hspan
    let k := window.length
    let u := s + k + 1
    let qpar := ReferenceFirstLaunchNumericalCell.queueParameters rate
    ∃ cut suffix r q base,
      cut = execution.records[k]'(by
        have hk : k < count := by
          simpa [k, window, execution,
            ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
            ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
            ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using hshort
        have hlen : execution.records.length = count := by
          simpa [execution, ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
            ReferenceFirstWindowNumericalStream.actualFirstLiveSeed,
            ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using
            ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan
              (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
                rate source rewards C_star C_h hc s rfl)
        exact hk.trans_eq hlen.symm) ∧
      execution.records = window ++ cut :: suffix ∧
      cut.input.time.val = s + k ∧
      cut.input.rows = source.1.2 ∧
      cut.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      cut.input.rewards = rewards ∧
      cut.input.state.coordinator = .live r q base ∧
      r.payload.sigma.val = s ∧
      (∀ i : Fin (p.m - 1),
        (r.payload.downRecord (ActualReferenceInitializationBlock.refFollower i)).val.q = 0) ∧
      ∃ dispatched hstart ledger hinit hcand hdomain hclock hpending hnoAssignment selected,
        cut.output.preparation.coordinator = .live r q base
          (.cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending
            hnoAssignment selected) ∧
        u = s + k + 1 ∧ u ≤ p.T ∧ u ≤ r.gridBoundary ∧
        ledger.sigma = r.payload.sigma.val + 1 ∧ ledger.cutoff = u ∧
        (∀ i : Fin (p.m - 1),
          ∃ c μ logged d post,
            let prepared := cut.output.preparation.followers.followers i
            let own := cut.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)
            let view := cut.output.preparation.coordinator.downView
            prepared.configuration = .ordinary c μ ∧
            ActiveFollowerLogging.checkedLogging i cut.input.row
              (cut.input.state.activations i) cut.input.time (prepared.arm, own) c = .ok logged ∧
            logged.buffer = c.buffer ++ ReferencePrelaunchFollower.logAt i cut.input.row
              (cut.input.state.activations i) cut.input.time (prepared.arm, own) ∧
            d = ReferenceDownReception.referenceDownCut p view i cut.input.row cut.input.time own rate logged ∧
            (recordFollower view i cut.input.row (cut.input.state.activations i)
              cut.input.time (cut.input.active i) prepared.arm own c).result = .ok post ∧
            (recordFollower view i cut.input.row (cut.input.state.activations i)
              cut.input.time (cut.input.active i) prepared.arm own c).downInput = some logged ∧
            (recordFollower view i cut.input.row (cut.input.state.activations i)
              cut.input.time (cut.input.active i) prepared.arm own c).down = some d ∧
            DeclaredFollowerLocalRound.releaseAndFinish rate i cut.input.row cut.input.time
              own c μ post = .ok (post, μ) ∧
            (cut.output.followers i).configuration = .ordinary post μ ∧
            (cut.output.followers i).failure = none ∧
            post.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid post ∧
            post.S + post.backlog ≤ k * D p ∧
            post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
            (∀ saved ∈ post.buffer, saved.calendarRound < (cut.input.time.val + 1) + 1) ∧
            (cut.output.followers i).downInput = some logged ∧
            (cut.output.followers i).down = some d) ∧
        k > 0 ∧
        (∀ i : Fin (p.m - 1), ∃ before μ,
          cut.input.state.followers i = .ordinary before μ ∧
          let c : ReferencePrelaunchFollower.State p rate.eta :=
            { before with status := .unoccupied }
          ActiveFollowerLifecycle.startRound rate.eta cut.input.time before μ = .ok (c, μ) ∧
          (cut.output.preparation.followers.followers i).configuration = .ordinary c μ ∧
          c.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid c ∧
          c.S = before.S ∧ c.delta = before.delta ∧ c.backlog = before.backlog ∧
          c.lastDown = before.lastDown ∧ c.buffer = before.buffer ∧
          c.downBatch = before.downBatch ∧ c.initializationFailure = before.initializationFailure ∧
          let prepared := cut.output.preparation.followers.followers i
          let own := cut.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)
          let view := cut.output.preparation.coordinator.downView
          recordFollower view i cut.input.row (cut.input.state.activations i)
            cut.input.time (cut.input.active i) prepared.arm own c =
            (match ActiveFollowerLogging.checkedLogging i cut.input.row
                (cut.input.state.activations i) cut.input.time (prepared.arm, own) c with
            | .error reason => ⟨.error (.logging reason), none, none⟩
            | .ok logged =>
                let d := ReferenceDownReception.referenceDownCut p view i cut.input.row
                  cut.input.time own rate logged
                ⟨DeclaredFollowerLocalRound.consumeDownResult rate d.outcome,
                  some logged, some d⟩)) ∧
        (∀ i : Fin (p.m - 1), ∃ sb mb,
          cut.input.state.followers i = .ordinary sb mb ∧
          ∃ k0 : Fin window.length, k0.val = 0 ∧
            let P0 := (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
              rate source rewards C_star C_h hc count hspan k0).selected.view.payload
            let M0 := P0.downRecord i
            let arrivals := fun v => (cells.take v).map (fun c =>
              (c.enabled, RecordedQueueRun.quantizedArrival qpar c (P0.assignment.assigned i)))
            let replay := fun v => QueueReplay.replay (4 * rate.n) (0, 0) (arrivals v)
            (sb.status ≠ .unoccupied →
              sb.lastDown = some M0 ∧ (sb.S, sb.backlog) = replay k ∧
              sb.delta = (replay k).1 - (replay (k - 1)).1 ∧
              sb.S ≤ p.T * D p ∧ sb.delta ≤ D p ∧ sb.backlog ≤ p.T * D p ∧
              sb.S + sb.backlog ≤ k * D p ∧
              ∃ j : Fin window.length, j.val < k ∧
                ReferenceAcceptedUpFollowerHistory.RetainedDown window[j.val] i M0) ∧
            (sb.status = .unoccupied →
              sb.lastDown = none ∧ sb.S = 0 ∧ sb.delta = 0 ∧ sb.backlog = 0 ∧
              sb.buffer =
                ((ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
                  rate source rewards C_star C_h hc).followers i).buffer ++
                  (execution.records.take k).flatMap (ReferenceFollowerBufferProvenance.logEmission i) ∧
              ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                execution.records i k M0 k = arrivals k)) ∧
        (∀ j : Fin k,
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
            rate source rewards C_star C_h hc count hspan
            ⟨j.val, j.isLt⟩).selected.view.payload = r.payload) ∧
        let t := cut.input.time
        let P := r.payload
        let started := dispatched.startResult
        let l0 := ReferenceActivePhysicalStep.sharedLedger ledger
        let weights := (ReferenceActivePhysicalStep.liveRegistersAt r t).complementWeights
        let recordingInput := ReferenceActivePhysicalStep.collectionRecordingInput
          cut.output.preparation P started weights
        let a := CoordinatorRecorderComplementBridge.recorderInput recordingInput
        let localValid : CoordinatorRecorderComplementBridge.LocalInputsValid recordingInput :=
          ⟨selected.recorderBoundaryValid, fun j =>
            ⟨selected.choiceInputsValid.anchor_le_current j,
              selected.choiceInputsValid.current_le_twice_anchor j⟩⟩
        let hv := CoordinatorRecorderComplementBridge.recorderInput_inputsValid
          recordingInput localValid
        let e := ReferenceActivePhysicalStep.collectionEnabled l0 t
        let zeta := (1 - (1 : ℝ) / p.K) ^ (p.m - 1)
        let x := (cut.input.row.2 t).1
        let sourceDraw := CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec x)
        let c_u : RecordedQueueRun.RoundInput p.K := {
          enabled := e
          recordedArm := SnapshotRecordingKernel.recordingMap p .collection e
            a.eta hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights
            hv.anchor_pos hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
            (cut.input.row.2 t).1
          reward := fun j => ((rewards t j).val : ℝ) / (D p : ℝ)
          rate := P.rate
          reward_nonneg := by
            intro j
            exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
          reward_le_one := by
            intro j
            have hj : (rewards t j).val ≤ D p :=
              Nat.le_of_lt_succ (rewards t j).isLt
            apply (div_le_one (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))).2
            exact_mod_cast hj
          rate_pos := by
            intro j
            exact (CanonicalRecordingRates.beta_pos p rate.eta.property).trans_le
              (P.beta_le_rate j) }
        c_u.enabled = e ∧
        c_u.recordedArm = SnapshotRecordingKernel.recordingMap p .collection e
          a.eta hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights
          hv.anchor_pos hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
          x ∧
        (∀ j : Fin p.K, c_u.recordedArm = some j ↔
          e = true ∧
          PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.dataSlot ∧
          sourceDraw.val = 0 ∧
          PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p)
            (ActiveRoundActions.coordinator p.two_le_m) x = j ∧
          (∀ ell : Fin p.m,
            ell ≠ ActiveRoundActions.coordinator p.two_le_m →
              PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p) ell x ≠ j) ∧
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin x).val ≤
            4 * (p.K : ℝ) * P.rate j / zeta) ∧
        c_u.reward = (fun j => ((rewards t j).val : ℝ) / (D p : ℝ)) ∧
        c_u.rate = P.rate ∧
        (∀ arm : Fin p.K,
          a.currentWeights arm = ReferenceFirstWindowNumericalStream.sourceWeights P weights arm) ∧
        CoordinatorRecordingOperation.coordinatorThreshold a hv =
          SnapshotRecordingKernel.thinningThreshold p .collection a.eta
            hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos
            hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
            (ActiveRoundActions.coordinator p.two_le_m) a.ownArm ∧
        (∃ out,
          CoordinatorRecorderComplementBridge.run recordingInput = some out ∧
          cut.output.coordinator.recording = some out ∧
          out.gateArm = CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart a hv e ∧
          out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
            P.anchor
            (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
              (rewards t j)) out.gateArm ∧
          (c_u.recordedArm = none → out.rawArrival = 0) ∧
          ReferenceCollectionRawBufferHistory.rawDiagnostic cut =
            out.gateArm.map (fun j => (j, out.rawArrival)) ∧
          (∀ j : Fin p.K,
            CoordinatorCollectionLedger.localArrival
                (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) j =
              RecordedQueueRun.quantizedArrival qpar c_u j)) ∧
        e = decide (u < r.gridBoundary) ∧
        (u = r.gridBoundary → e = false ∧ c_u.recordedArm = none ∧
          ∀ j : Fin p.K, RecordedQueueRun.quantizedArrival qpar c_u j = 0) ∧
        (u < r.gridBoundary → e = true) ∧
        ((PublicDiscreteDraws.slotDraw x ≠ PublicDiscreteDraws.dataSlot ∨ sourceDraw.val ≠ 0) →
          c_u.recordedArm = none ∧
          ∀ j : Fin p.K, RecordedQueueRun.quantizedArrival qpar c_u j = 0) ∧
        (∀ j : Fin p.K, c_u.recordedArm = some j → c_u.reward j = 0 →
          ReferenceCollectionRawBufferHistory.rawDiagnostic cut = some (j, 0)) ∧
        (PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.dataSlot →
          ∀ player : Fin p.m,
            cut.output.preparation.arms.actions player =
              PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p) player x) ∧
        (∀ j : Fin p.K, c_u.recordedArm = some j →
          FiniteBanditModel.collisionFreeFor cut.output.preparation.arms.actions
            (ActiveRoundActions.coordinator p.two_le_m) ∧
          cut.output.preparation.feedback.feedback
              (ActiveRoundActions.coordinator p.two_le_m) = rewards t j ∧
          (cut.output.preparation.feedback.observations
              (ActiveRoundActions.coordinator p.two_le_m)).val.val =
            ((rewards t j).val : ℝ) / (D p : ℝ) ∧
          CoordinatorRecordingOperation.observationValue a = c_u.reward j) ∧
        (∀ j : Fin p.K,
          CoordinatorCollectionLedger.localArrival
              (ReferenceCollectionRawBufferHistory.rawDiagnostic cut) j =
            RecordedQueueRun.quantizedArrival qpar c_u j ∧
          ReferenceCollectionRawBufferHistory.physicalQueueRecord l0 j cut =
            (e, RecordedQueueRun.quantizedArrival qpar c_u j)) ∧
        (e = false → c_u.recordedArm = none ∧
          ∀ j : Fin p.K, RecordedQueueRun.quantizedArrival qpar c_u j = 0) ∧
        (cells ++ [c_u]).length = k + 1
  := by
  classical
  let init := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let boot := ReferenceInitializationRun.output init
  let s := ReferenceInitializationRun.elapsed p boot.completed
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let execution := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate source rewards C_star C_h hc count hspan
  let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan
  let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate source rewards C_star C_h hc count hspan
  let k := window.length
  let u := s + k + 1
  let qpar := ReferenceFirstLaunchNumericalCell.queueParameters rate
  have hactive := ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
    rate source rewards C_star C_h hc s rfl
  have hshortS : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hc s rfl count hspan).records).length < count := hshort
  have hshortActual : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan
        hactive).records).length < count := hshort
  have hsurvival := ReferenceGeneratedFirstCutoffSurvival.run_generated_first_cutoff_survival
    rate source rewards C_star C_h hc s rfl count hspan hshortS
  have hcomp := ReferenceFirstLiveComplementQueueReplay.actual_first_live_complement_prefix_replay
    rate source rewards C_star C_h hc count hspan k (by rfl)
  have hfollow := fun i : Fin (p.m - 1) =>
    ReferenceFirstLiveFollowerQueueReplay.actual_first_live_follower_prefix_replay
      rate source rewards C_star C_h hc count hspan i k (by rfl)
  rcases hsurvival with
    ⟨hseedActive, hfirst, hbank, hlearner, hregisters, hseed, hcut⟩
  dsimp only [execution, window, k] at hcut
  rcases hcut with
    ⟨cut, suffix, hsplit, hindex, htime, hprefix, hrows, hselectedRow, hrewards,
      hstateData⟩
  rcases hstateData with
    ⟨r, q, base, hlive, hsigma, hdownZero,
      dispatched, hstart, ledger, hinitLedger, hcand, hdomain, hclock, hpending,
      hnoAssignment, selected, hbranch, hcutFacts⟩
  rcases hcutFacts with ⟨hu, huT, huGrid, hledgerSigma, hledgerCut, hcutFollowers⟩
  let seed := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffSeed
    rate source rewards C_star C_h
  let memory := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffMemory (p := p)
  have hseedState : ∀ i, initial.followers i = .ordinary (seed i) (memory i) := by
    intro i
    rcases hseed i with ⟨hstate, _, _, _, _, _, _, _, _, _, _⟩
    exact hstate
  have hseedS : ∀ i, (seed i).S = 0 := by
    intro i
    rcases hseed i with ⟨_, _, hzero, _, _, _, _, _, _, _, _⟩
    exact hzero
  have hseedDelta : ∀ i, (seed i).delta = 0 := by
    intro i
    rcases hseed i with ⟨_, _, _, hzero, _, _, _, _, _, _, _⟩
    exact hzero
  have hseedBacklog : ∀ i, (seed i).backlog = 0 := by
    intro i
    rcases hseed i with ⟨_, _, _, _, hzero, _, _, _, _, _, _⟩
    exact hzero
  have hseedLastDown : ∀ i, (seed i).lastDown = none := by
    intro i
    rcases hseed i with ⟨_, hnone, _, _, _, _, _, _, _, _, _⟩
    exact hnone
  have hseedUnoccupied : ∀ i, (seed i).status = .unoccupied := by
    intro i
    rcases hseed i with ⟨_, _, _, _, _, hstatus, _, _, _, _, _⟩
    exact hstatus
  have hseedBufferValid : ∀ i, localBufferValid (seed i) := by
    intro i
    rcases hseed i with ⟨_, _, _, _, _, _, _, hvalid, _, _, _⟩
    exact hvalid
  have hseedPair : ∀ i, (seed i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) := by
    intro i
    rcases hseed i with ⟨_, _, _, _, _, _, _, _, hpair, _, _⟩
    exact hpair
  have hseedTime : ∀ i saved, saved ∈ (seed i).buffer → saved.calendarRound ≤ s := by
    intro i saved hsaved
    rcases hseed i with ⟨_, _, _, _, _, _, _, _, _, htime, _⟩
    exact htime saved hsaved
  have hseedDecoder : ∀ i, downDecoderStateValid (seed i) := by
    intro i
    rcases hseed i with ⟨_, _, _, _, _, _, _, _, _, _, hdecoder⟩
    exact hdecoder
  have hprep := ReferenceFirstCutoffFollowerPreparation.run_first_cutoff_follower_preparation
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    s count hspan hseedActive hfirst seed memory hseedState hseedS hseedDelta hseedBacklog
    hseedLastDown hseedUnoccupied hseedBufferValid hseedPair hseedTime hseedDecoder hshortActual
  rcases hprep with
    ⟨prepCut, prepSuffix, hprepSplit, hprepIndex, hprepTime, hprepState, hprepRows,
      hprepSelected, hprepRewards, hprepFollowers, hprepFeedback, hprepOwnEntries⟩
  have hkExecution : k < execution.records.length := by
    have hk : k < count := hshort
    have hlen : execution.records.length = count :=
      ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan hactive
    exact hk.trans_eq hlen.symm
  have hprepCutIndex : prepCut = execution.records[k]'hkExecution := by
    simpa [execution, window, k,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
      ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
      ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using hprepIndex
  have hsameCut : cut = prepCut := by
    have hindex' : cut = execution.records[k]'hkExecution := by
      simpa [execution, window, k,
        ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
        ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
        ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using hindex
    exact hindex'.trans hprepCutIndex.symm
  have hpreparationFrames : ∀ i : Fin (p.m - 1), ∃ before μ,
      cut.input.state.followers i = .ordinary before μ ∧
      let c : ReferencePrelaunchFollower.State p rate.eta :=
        { before with status := .unoccupied }
      ActiveFollowerLifecycle.startRound rate.eta cut.input.time before μ = .ok (c, μ) ∧
      (cut.output.preparation.followers.followers i).configuration = .ordinary c μ ∧
      c.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid c ∧
      c.S = before.S ∧ c.delta = before.delta ∧ c.backlog = before.backlog ∧
      c.lastDown = before.lastDown ∧ c.buffer = before.buffer ∧
      c.downBatch = before.downBatch ∧ c.initializationFailure = before.initializationFailure ∧
      let prepared := cut.output.preparation.followers.followers i
      let own := cut.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
      let view := cut.output.preparation.coordinator.downView
      recordFollower view i cut.input.row (cut.input.state.activations i)
        cut.input.time (cut.input.active i) prepared.arm own c =
        (match ActiveFollowerLogging.checkedLogging i cut.input.row
            (cut.input.state.activations i) cut.input.time (prepared.arm, own) c with
        | .error reason => ⟨.error (.logging reason), none, none⟩
        | .ok logged =>
            let d := ReferenceDownReception.referenceDownCut p view i cut.input.row
              cut.input.time own rate logged
            ⟨DeclaredFollowerLocalRound.consumeDownResult rate d.outcome,
              some logged, some d⟩) := by
    intro i
    rcases hprepFollowers i with
      ⟨before, μ, hbefore, _, _, hstartFollower, hconfiguration, hdomainFollower, _⟩
    refine ⟨before, μ, ?_, ?_⟩
    · rw [hsameCut, hprepState]
      exact hbefore
    · dsimp only
      refine ⟨?_, ?_, rfl, hdomainFollower, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      · simpa only [hsameCut] using hstartFollower
      · cases hsameCut
        exact hconfiguration
      · simp only [ReferenceActivePhysicalStep.recordFollower, dite_true]
        rfl
  have hprepStateAtCut : ∀ i, ∃ c μ,
      (cut.output.preparation.followers.followers i).configuration = .ordinary c μ ∧
      c.status = .unoccupied := by
    intro i
    rcases hpreparationFrames i with ⟨before, μ, _, _, hconfiguration, hstatus, _⟩
    exact ⟨{ before with status := .unoccupied }, μ, hconfiguration, hstatus⟩
  let cutoffStates : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta :=
    fun i => Classical.choose (hprepStateAtCut i)
  let cutoffMemories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p :=
    fun i => Classical.choose (Classical.choose_spec (hprepStateAtCut i))
  have hordinary : ∀ i,
      (cut.output.preparation.followers.followers i).configuration =
        .ordinary (cutoffStates i) (cutoffMemories i) := by
    intro i
    exact (Classical.choose_spec (Classical.choose_spec (hprepStateAtCut i))).1
  have hunoccupied : ∀ i, (cutoffStates i).status = .unoccupied := by
    intro i
    exact (Classical.choose_spec (Classical.choose_spec (hprepStateAtCut i))).2
  have hordinaryPrepared : ∀ i,
      ((ReferenceActivePhysicalStep.prepare cut.input).followers.followers i).configuration =
        .ordinary (cutoffStates i) (cutoffMemories i) := by
    intro i
    simpa only [cut.output_eq, ReferenceActivePhysicalStep.step] using hordinary i
  let t := cut.input.time
  let P := r.payload
  let started := dispatched.startResult
  let l0 := ReferenceActivePhysicalStep.sharedLedger ledger
  let weights := (ReferenceActivePhysicalStep.liveRegistersAt r t).complementWeights
  let recordingInput := ReferenceActivePhysicalStep.collectionRecordingInput
    cut.output.preparation P started weights
  let a := CoordinatorRecorderComplementBridge.recorderInput recordingInput
  let localValid : CoordinatorRecorderComplementBridge.LocalInputsValid recordingInput :=
    ⟨selected.recorderBoundaryValid, fun j =>
      ⟨selected.choiceInputsValid.anchor_le_current j,
        selected.choiceInputsValid.current_le_twice_anchor j⟩⟩
  let hv := CoordinatorRecorderComplementBridge.recorderInput_inputsValid recordingInput localValid
  let e := ReferenceActivePhysicalStep.collectionEnabled l0 t
  let zeta := (1 - (1 : ℝ) / p.K) ^ (p.m - 1)
  let x := (cut.input.row.2 t).1
  let sourceDraw := CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
    (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec x)
  let c_u : RecordedQueueRun.RoundInput p.K := {
    enabled := e
    recordedArm := SnapshotRecordingKernel.recordingMap p .collection e
      a.eta hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights
      hv.anchor_pos hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
      (cut.input.row.2 t).1
    reward := fun j => ((rewards t j).val : ℝ) / (D p : ℝ)
    rate := P.rate
    reward_nonneg := by
      intro j
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    reward_le_one := by
      intro j
      have hj : (rewards t j).val ≤ D p := Nat.le_of_lt_succ (rewards t j).isLt
      apply (div_le_one (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))).2
      exact_mod_cast hj
    rate_pos := by
      intro j
      exact (CanonicalRecordingRates.beta_pos p rate.eta.property).trans_le (P.beta_le_rate j) }
  have houtside := ReferenceFirstCutoffOutsideInitialization.run_first_cutoff_outside_initializer
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    s count hspan hseedActive hfirst hshortActual
  dsimp only [execution, window, k] at houtside
  rcases houtside with
    ⟨outsideCut, outsideSuffix, houtsideSplit, houtsideIndex, houtsideTime,
      houtsideActual, houtsideState⟩
  rcases houtsideState with ⟨outsideRegisters, outsideOwned, outsideBase,
    houtsidePrefix, houtsideLive, houtsideCall⟩
  rcases houtsideCall with
    ⟨outsideDispatch, outsideStart, outsideLedger, outsideInit, outsideLedgerEq,
      outsideDomain, outsideClock, outsidePending, outsideNoAssignment,
      outsideSelection, outsideBranch, hkpos, _, _, _, _, _, _⟩
  have hK : 0 < k := hkpos
  have hFollowerPrefixAtCut : ∀ i : Fin (p.m - 1), ∃ sb mb,
        cut.input.state.followers i = .ordinary sb mb ∧
        ∃ k0 : Fin window.length, k0.val = 0 ∧
          let P0 := (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
            rate source rewards C_star C_h hc count hspan k0).selected.view.payload
          let M0 := P0.downRecord i
          let arrivals := fun v => (cells.take v).map (fun c =>
            (c.enabled, RecordedQueueRun.quantizedArrival qpar c (P0.assignment.assigned i)))
          let replay := fun v => QueueReplay.replay (4 * rate.n) (0, 0) (arrivals v)
          (sb.status ≠ .unoccupied →
            sb.lastDown = some M0 ∧ (sb.S, sb.backlog) = replay k ∧
            sb.delta = (replay k).1 - (replay (k - 1)).1 ∧
            sb.S ≤ p.T * D p ∧ sb.delta ≤ D p ∧ sb.backlog ≤ p.T * D p ∧
            sb.S + sb.backlog ≤ k * D p ∧
            ∃ j : Fin window.length, j.val < k ∧
              ReferenceAcceptedUpFollowerHistory.RetainedDown window[j.val] i M0) ∧
          (sb.status = .unoccupied →
            sb.lastDown = none ∧ sb.S = 0 ∧ sb.delta = 0 ∧ sb.backlog = 0 ∧
            sb.buffer =
              ((ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
                rate source rewards C_star C_h hc).followers i).buffer ++
                (execution.records.take k).flatMap (ReferenceFollowerBufferProvenance.logEmission i) ∧
            ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
              execution.records i k M0 k = arrivals k) := by
    intro i
    rcases hfollow i with ⟨_, sb, mb, hstate, _, hpositive⟩
    refine ⟨sb, mb, ?_, hpositive hK⟩
    rw [hsameCut, hprepState]
    exact hstate
  have hcompPrefix := hcomp.2.2 hK
  rcases hcompPrefix with
    ⟨rComp, qComp, baseComp, hcompLive, hcompSpan, hcompSigma, hcompN,
      hcompZeroBase, hcompBirth, hcompArms⟩
  have hprefixLive :
      (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s k
        (by simpa [s, initial] using hcompSpan) hactive).finalState.coordinator = .live r q base := by
    have hcutLive : cut.input.state.coordinator = .live r q base := hlive
    rw [hprefix] at hcutLive
    exact hcutLive
  have hcompSame : ReferenceActivePhysicalStep.CoordinatorConfiguration.live
      rComp qComp baseComp = .live r q base := hcompLive.symm.trans hprefixLive
  have hcompRegisters : rComp = r := by injection hcompSame
  subst rComp
  have hcompOwned : qComp = q := by injection hcompSame
  have hcompBase : baseComp = base := by injection hcompSame
  subst qComp
  subst baseComp
  have hstored : ReferenceAssignmentPayloadPersistence.storedPayload
      ((ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s k
        (by simpa [s, initial] using hcompSpan) hactive).finalState.coordinator) = some r.payload := by
    rw [hcompLive]
    rfl
  have hgeometry := ReferenceFirstLiveDownNumericalRecovery.first_live_geometry
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards s count hspan hactive hfirst
  have hpayload : ∀ j : Fin k,
      (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
        rate source rewards C_star C_h hc count hspan ⟨j.val, j.isLt⟩).selected.view.payload = r.payload := by
    intro j
    let j' : Fin window.length := ⟨j.val, j.isLt⟩
    let record := window[j.val]
    let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan j'
    have hsplitActual : execution.records = window ++ cut :: suffix := hsplit
    have hrecordMem : record ∈ execution.records := by
      have hmem : record ∈ window := List.getElem_mem j.isLt
      rw [hsplitActual]
      exact List.mem_append.mpr (Or.inl hmem)
    have hselectedCell : record.output.preparation.coordinator.selection = some cell.selected := by
      simpa [record, cell, j', window,
        ReferenceFirstWindowNumericalStream.actualFirstLiveWindow] using cell.selection_actual
    have hgeom := hgeometry j' cell.selected hselectedCell
    have hsame := ReferenceSelectedPayloadChronology.run_actualSelectedPayload_eq_of_prefix_storedPayload_equal_sigma
      initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      s count hspan hactive hfirst record cell.selected hrecordMem hselectedCell k (Nat.le_of_lt hshort)
      r.payload hstored (hgeom.1.trans hsigma.symm)
    exact hsame.1
  have hbranchPrepared : (ReferenceActivePhysicalStep.prepare cut.input).coordinator =
      .live r q base (.cutoffChosen dispatched hstart ledger hinitLedger hcand hdomain hclock
        hpending hnoAssignment selected) := by
    have hbranchStep : (ReferenceActivePhysicalStep.step cut.input).preparation.coordinator =
        .live r q base (.cutoffChosen dispatched hstart ledger hinitLedger hcand hdomain hclock
          hpending hnoAssignment selected) := by
      simpa only [cut.output_eq] using hbranch
    simpa only [ReferenceActivePhysicalStep.step] using hbranchStep
  have hrecording := ReferenceCoordinatorCollectionRecording.cutoff_recording_identification
    (x := cut.input) r q base dispatched hstart ledger hinitLedger hcand hdomain
    hclock hpending hnoAssignment selected hbranchPrepared
    cutoffStates cutoffMemories
    hordinaryPrepared hunoccupied
  dsimp only [t, P, started, l0, recordingInput, a, hv, localValid, e] at hrecording
  rcases hrecording with ⟨hrecorder, henabled⟩
  rcases hrecorder with ⟨out, hrun, hstepRecorder, hgate, hraw⟩
  have hcutRecorder : cut.output.coordinator.recording = some out := by
    simpa only [cut.output_eq] using hstepRecorder
  have hprepEq : cut.output.preparation = ReferenceActivePhysicalStep.prepare cut.input := by
    calc
      _ = (ReferenceActivePhysicalStep.step cut.input).preparation := by rw [cut.output_eq]
      _ = ReferenceActivePhysicalStep.prepare cut.input := rfl
  have hrawDiagnostic : ReferenceCollectionRawBufferHistory.rawDiagnostic cut =
      out.gateArm.map (fun j => (j, out.rawArrival)) := by
    simp [ReferenceCollectionRawBufferHistory.rawDiagnostic, hcutRecorder]
  have hweights : ∀ arm : Fin p.K,
      a.currentWeights arm = ReferenceFirstWindowNumericalStream.sourceWeights P weights arm := by
    intro arm
    rfl
  have hslice : ContinuousLearningRows.sliceAt a.time a.row.2 =
      (cut.input.row.2 t).1 := by rfl
  have hmapFull :
      SnapshotRecordingKernel.recordingMap p .collection e a.eta
        hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos
        hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
        (cut.input.row.2 t).1 =
      CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart a hv e := by
    by_cases he : e = false
    · simp [he, SnapshotRecordingKernel.recordingMap_disabled,
        CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart]
    · have he' : e = true := Bool.eq_true_of_not_eq_false he
      by_cases hs : CoordinatorRecordingOperation.selectedRecorder a =
          ActiveRoundActions.coordinator p.two_le_m
      · unfold CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart
        rw [ite_eq_left hs, hslice]
      · have hnone : SnapshotRecordingKernel.recordingMap p .collection e a.eta
            hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos
            hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
            (cut.input.row.2 t).1 = none := by
          cases hm : SnapshotRecordingKernel.recordingMap p .collection e a.eta
              hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos
              hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
              (cut.input.row.2 t).1 with
          | none => rfl
          | some arm =>
              have hm' : SnapshotRecordingKernel.recordingMap p .collection true a.eta
                  hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos
                  hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
                  (cut.input.row.2 t).1 = some arm := by simpa [he'] using hm
              have htests := (SnapshotRecordingKernel.recordingMap_some_iff p .collection
                a.eta hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos
                hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
                (cut.input.row.2 t).1 arm).mp hm'
              have howns := htests.2.2.1
              have hsource : CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
                  (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec
                    (ContinuousLearningRows.sliceAt a.time a.row.2)) =
                    ActiveRoundActions.coordinator p.two_le_m := by
                simpa [SnapshotRecordingKernel.owns, hslice] using howns
              have hselected : CoordinatorRecordingOperation.selectedRecorder a =
                  ActiveRoundActions.coordinator p.two_le_m := by
                simpa [CoordinatorRecordingOperation.selectedRecorder, a,
                  CoordinatorRecorderComplementBridge.recorderInput,
                  CoordinatorRecorderComplementBridge.recorderInputWithWeights,
                  recordingInput, ReferenceActivePhysicalStep.collectionRecordingInput,
                  t, P, started, weights, hprepEq, ContinuousLearningRows.sliceAt] using hsource
              exact False.elim (hs hselected)
        unfold CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart
        rw [ite_eq_right hs]
        simp [hnone]
  have hsourceZero : sourceDraw.val = 0 ↔
      sourceDraw = ActiveRoundActions.coordinator p.two_le_m := by
    constructor
    · intro h
      apply Fin.ext
      simpa [ActiveRoundActions.coordinator] using h
    · intro h
      simpa [ActiveRoundActions.coordinator] using congrArg Fin.val h
  have hcollectionMode : a.mode = CoordinatorRecordingOperation.LocalMode.collection := by
    rfl
  have hcollectionThreshold :=
    CoordinatorRecordingOperation.collectionThreshold_eq_snapshot a hv hcollectionMode
  have hzeta : 0 < zeta := by
    have hz : (1 / 4 : ℝ) < zeta := by
      simpa [zeta, CanonicalRecordingSlice.recordingZeta] using
        CanonicalRecordingSlice.recordingZeta_gt_quarter p.two_le_m p.m_lt_K
    linarith
  have hthresholdSnapshot : ∀ j : Fin p.K,
      SnapshotRecordingKernel.thinningThreshold p .collection a.eta
        hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos
        hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
        (ActiveRoundActions.coordinator p.two_le_m) j =
          4 * (p.K : ℝ) * P.rate j / zeta := by
    intro j
    unfold SnapshotRecordingKernel.thinningThreshold SnapshotRecordingKernel.rawGateMass
    simp only [SnapshotRecordingKernel.actionProbability,
      ActiveRoundActions.coordinator]
    rw [PublicDiscreteDraws.recorderMass_coordinator p.two_le_m]
    simp only [CanonicalRecordingSlice.recordingZeta, zeta]
    have hxi : CanonicalRecordingRates.xi p a.eta a.anchor j = P.rate j := by
      change CanonicalRecordingRates.xi p rate.eta.val P.anchor j = P.rate j
      exact (P.rate_eq_canonical j).symm
    rw [hxi]
    have hK : (p.K : ℝ) ≠ 0 :=
      ne_of_gt (by exact_mod_cast ConstructorDimensions.K_pos p)
    have hz : zeta ≠ 0 := ne_of_gt hzeta
    field_simp [hK, hz]
    ring
  have hpilotEventSet : ∀ j : Fin p.K,
      {y : CanonicalRecordingSlice.Slice p.m p.K |
        SnapshotRecordingKernel.recordingMap p .collection true a.eta
          hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos
          hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor y = some j} =
        {y | CanonicalRecordingSlice.pilotRecordingGate p.two_le_m p.m_lt_K
          (ConstructorDimensions.K_pos p) (ActiveRoundActions.coordinator p.two_le_m)
          j (CanonicalRecordingRates.xi p a.eta a.anchor j /
            CanonicalRecordingSlice.pilotRecordingGateRawProbability
              (K := p.K) (ActiveRoundActions.coordinator p.two_le_m)) y} := by
    intro j
    apply SnapshotRecordingKernel.recordingMap_pilot_event_eq
    · simp [SnapshotRecordingKernel.owns]
    · intro y
      simp [SnapshotRecordingKernel.dataAction]
    · simp [SnapshotRecordingKernel.actionProbability]
  have hmapEvent : ∀ j : Fin p.K, c_u.recordedArm = some j ↔
      e = true ∧
      PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.dataSlot ∧
      sourceDraw.val = 0 ∧
      PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m) x = j ∧
      (∀ ell : Fin p.m,
        ell ≠ ActiveRoundActions.coordinator p.two_le_m →
          PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p) ell x ≠ j) ∧
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin x).val ≤
        4 * (p.K : ℝ) * P.rate j / zeta := by
    intro j
    constructor
    · intro hsome
      have henabled : e = true := by
        cases he : e with
        | false => simp [c_u, he] at hsome
        | true => rfl
      have hsomeTrue : SnapshotRecordingKernel.recordingMap p .collection true
          a.eta hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos
          hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor x = some j := by
        simpa [c_u, x, henabled] using hsome
      have htests := (SnapshotRecordingKernel.recordingMap_some_iff p .collection
        a.eta hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos
        hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor x j).mp hsomeTrue
      have hgateSet := (Set.ext_iff.mp (hpilotEventSet j)) x
      have hgate : CanonicalRecordingSlice.pilotRecordingGate p.two_le_m p.m_lt_K
          (ConstructorDimensions.K_pos p) (ActiveRoundActions.coordinator p.two_le_m)
          j (CanonicalRecordingRates.xi p a.eta a.anchor j /
            CanonicalRecordingSlice.pilotRecordingGateRawProbability
              (K := p.K) (ActiveRoundActions.coordinator p.two_le_m)) x := by
        apply hgateSet.mp
        simpa [c_u, x, henabled] using hsome
      rcases hgate with ⟨hslot, hsourceGate, hpilot, hmaskGate, _⟩
      rcases htests with ⟨_, _, _, _, hthinRaw⟩
      have hsourceFormula : CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec x) =
            ActiveRoundActions.coordinator p.two_le_m := by
        calc
          _ = PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K x := by
            exact CanonicalRecordingSlice.recorderSourceFromScalar_coordinate
              p.two_le_m p.m_lt_K x
          _ = ActiveRoundActions.coordinator p.two_le_m := hsourceGate
      have hsource : sourceDraw = ActiveRoundActions.coordinator p.two_le_m := by
        exact hsourceFormula
      have hthin : (ContinuousControlSlice.coordinate
          ContinuousControlSlice.Label.thin x).val ≤
          SnapshotRecordingKernel.thinningThreshold p .collection a.eta
            hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos
            hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
            (ActiveRoundActions.coordinator p.two_le_m) j := by
        simpa [hsourceFormula] using hthinRaw
      have hthin' :
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin x).val ≤
            4 * (p.K : ℝ) * P.rate j / zeta := by
        rw [hthresholdSnapshot j] at hthin
        exact hthin
      exact ⟨henabled, hslot, hsourceZero.mpr hsource,
        hpilot, hmaskGate, hthin'⟩
    · rintro ⟨henabled, hslot, hsourceZero', hpilot, hmask, hthin⟩
      have hsource : sourceDraw = ActiveRoundActions.coordinator p.two_le_m :=
        hsourceZero.mp hsourceZero'
      have hsourceFormula : CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec x) =
            ActiveRoundActions.coordinator p.two_le_m := by
        change sourceDraw = ActiveRoundActions.coordinator p.two_le_m
        exact hsource
      have howns : SnapshotRecordingKernel.owns p .collection sourceDraw j := by
        simpa [SnapshotRecordingKernel.owns] using hsource
      have hmask' : CanonicalRecordingSlice.recordingMask
          (ConstructorDimensions.K_pos p) sourceDraw j x := by
        intro ell hne
        apply hmask ell
        simpa [hsource] using hne
      have hthinSnapshot :
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin x).val ≤
            SnapshotRecordingKernel.thinningThreshold p .collection a.eta
              hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos
              hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
              sourceDraw j := by
        rw [hsource]
        rw [hthresholdSnapshot j]
        exact hthin
      have hrecord : SnapshotRecordingKernel.recordingMap p .collection true
          a.eta hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos
          hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor x = some j :=
        (SnapshotRecordingKernel.recordingMap_some_iff p .collection a.eta
          hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos
          hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor x j).2
          ⟨hslot, by simpa [SnapshotRecordingKernel.dataAction, hsourceFormula] using hpilot,
            howns, hmask', hthinSnapshot⟩
      simpa [c_u, x, henabled] using hrecord
  have henabledA : decide (¬ CoordinatorRecordingOperation.isFrozen a) = e := by
    have henabled' := henabled
    rw [← hprepEq] at henabled'
    change decide (¬ CoordinatorRecordingOperation.isFrozen a) = e at henabled'
    exact henabled'
  have hmapOut :
      CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart a hv
        (decide (¬ CoordinatorRecordingOperation.isFrozen a)) = c_u.recordedArm := by
    calc
      _ = CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart a hv e := by
        rw [henabledA]
      _ = SnapshotRecordingKernel.recordingMap p .collection e a.eta
          hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos
          hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
          (cut.input.row.2 t).1 := hmapFull.symm
      _ = c_u.recordedArm := rfl
  have hgateOutput : out.gateArm =
      CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart a hv
        (decide (¬ CoordinatorRecordingOperation.isFrozen a)) := by
    have hgate' := hgate
    rw [← hprepEq] at hgate'
    simpa [a, hv, recordingInput, t, P, started, weights] using hgate'
  have hgateExact : out.gateArm = c_u.recordedArm := by
    calc
      _ = CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart a hv
          (decide (¬ CoordinatorRecordingOperation.isFrozen a)) := hgateOutput
      _ = c_u.recordedArm := hmapOut
  have hrawExact : out.rawArrival =
      SnapshotRecordingKernel.recordedIncrement p rate.eta.val P.anchor
        (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (rewards t j)) c_u.recordedArm := by
    calc
      _ = SnapshotRecordingKernel.recordedIncrement p rate.eta.val P.anchor
          (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (rewards t j))
          (CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart a hv
            (decide (¬ CoordinatorRecordingOperation.isFrozen a))) := by
              have hraw' := hraw
              rw [← hprepEq] at hraw'
              simpa [a, hv, recordingInput, t, P, started, weights, hrewards] using hraw'
      _ = _ := by rw [hmapOut]
  have hfloor : ∀ arm : Fin p.K,
      SnapshotRecordingKernel.recordedIncrement p rate.eta.val P.anchor
          (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (rewards t j)) (some arm) =
        Nat.floor ((qpar.n : ℝ) * c_u.reward arm / c_u.rate arm) := by
    intro arm
    have hreward : RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        (rewards t arm) = ((rewards t arm).val : ℝ) / (D p : ℝ) := rfl
    change Nat.floor ((D p : ℝ) * rate.eta.val *
        RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t arm) /
          CanonicalRecordingRates.xi p rate.eta.val P.anchor arm) =
      Nat.floor ((qpar.n : ℝ) * c_u.reward arm / c_u.rate arm)
    apply congrArg Nat.floor
    rw [hreward]
    simp only [qpar, ReferenceFirstLaunchNumericalCell.queueParameters, c_u]
    rw [rate.n_scale]
    rw [P.rate_eq_canonical]
    field_simp [ne_of_gt (ConstructorDimensions.D_pos p),
      ne_of_gt (CanonicalRecordingRates.xi_pos p rate.eta.property P.anchor arm)]
  have hwindowEq :
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
          rate source rewards C_star C_h hc s rfl count hspan).records).length = k := rfl
  have hfreeze : ledger.freezeAt = r.gridBoundary := by
    rw [hcand]
    exact (CoordinatorStartRoundCutoffDispatch.collectionStartLedger_fields r q base t).2.2.2.1
  have hEnabledGrid : e = decide (u < r.gridBoundary) := by
    dsimp [e, l0, t, u, ReferenceActivePhysicalStep.collectionEnabled,
      ReferenceActivePhysicalStep.sharedLedger]
    simp [hledgerSigma, hledgerCut, hfreeze, htime, hwindowEq]
  have hdisabled : e = false → c_u.recordedArm = none ∧
      ∀ j : Fin p.K, RecordedQueueRun.quantizedArrival qpar c_u j = 0 := by
    intro he
    have hrecordNone : c_u.recordedArm = none := by
      change SnapshotRecordingKernel.recordingMap p .collection e a.eta
        hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos
        hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
        (cut.input.row.2 t).1 = none
      rw [he]
      exact SnapshotRecordingKernel.recordingMap_disabled p .collection
        a.eta hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos
        hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
        (cut.input.row.2 t).1
    constructor
    · exact hrecordNone
    · intro j
      simp [RecordedQueueRun.quantizedArrival, c_u, he]
  have hlocalArrival : ∀ j : Fin p.K,
      CoordinatorCollectionLedger.localArrival
        (ReferenceCollectionRawBufferHistory.rawDiagnostic cut) j =
          RecordedQueueRun.quantizedArrival qpar c_u j := by
    intro j
    cases hrecord : c_u.recordedArm with
    | none =>
        simp [ReferenceCollectionRawBufferHistory.rawDiagnostic, hcutRecorder,
          CoordinatorCollectionLedger.localArrival, hgateExact, hrecord,
          RecordedQueueRun.quantizedArrival]
    | some arm =>
        by_cases harmeq : arm = j
        · subst arm
          simp [ReferenceCollectionRawBufferHistory.rawDiagnostic, hcutRecorder,
            CoordinatorCollectionLedger.localArrival, hgateExact, hrecord,
            RecordedQueueRun.quantizedArrival, hrawExact, hfloor j]
        · simp [ReferenceCollectionRawBufferHistory.rawDiagnostic, hcutRecorder,
            CoordinatorCollectionLedger.localArrival, hgateExact, hrecord,
            RecordedQueueRun.quantizedArrival, hrawExact, hfloor arm, harmeq]
  have hrecorderArrival : ∀ j : Fin p.K,
      CoordinatorCollectionLedger.localArrival
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) j =
        RecordedQueueRun.quantizedArrival qpar c_u j := by
    intro j
    rw [CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder,
      ← hrawDiagnostic]
    exact hlocalArrival j
  have hphysicalQueueRecord : ∀ j : Fin p.K,
      ReferenceCollectionRawBufferHistory.physicalQueueRecord l0 j cut =
        (e, RecordedQueueRun.quantizedArrival qpar c_u j) := by
    intro j
    by_cases he : e = true
    · have hlt : cut.input.time.val + 1 < ledger.freezeAt := by
        have hdec : decide (u < r.gridBoundary) = true := by simpa [hEnabledGrid] using he
        have hu : u < r.gridBoundary := of_decide_eq_true hdec
        rw [hfreeze, htime]
        simpa [u, hwindowEq] using hu
      have hsigmaPos : 0 < ledger.sigma := by rw [hledgerSigma]; omega
      have hcutLE : ledger.cutoff ≤ cut.input.time.val + 1 := by
        rw [hledgerCut]
      have hcollectionEnabled :
          ReferenceActivePhysicalStep.collectionEnabled l0 cut.input.time = true := by
        simp [ReferenceActivePhysicalStep.collectionEnabled,
          ReferenceActivePhysicalStep.sharedLedger, l0, hsigmaPos, hcutLE, hlt]
      change
        (ReferenceActivePhysicalStep.collectionEnabled l0 cut.input.time &&
          decide (cut.input.time.val + 1 < l0.freezeAt),
          if cut.input.time.val + 1 < l0.freezeAt then
            CoordinatorCollectionLedger.localArrival
              (ReferenceCollectionRawBufferHistory.rawDiagnostic cut) j else 0) =
        (e, RecordedQueueRun.quantizedArrival qpar c_u j)
      apply Prod.ext
      · have hdb : decide (cut.input.time.val + 1 < l0.freezeAt) = true := by
          simp [l0, ReferenceActivePhysicalStep.sharedLedger, hlt]
        simp [hcollectionEnabled, hdb, he]
      · simp [hlt, l0, ReferenceActivePhysicalStep.sharedLedger, hlocalArrival]
    · have he0 : e = false := Bool.eq_false_of_not_eq_true he
      have hnotlt : ¬ cut.input.time.val + 1 < ledger.freezeAt := by
        intro hlt
        have hu : u < r.gridBoundary := by
          rw [hfreeze, htime] at hlt
          simpa [u, hwindowEq] using hlt
        have hdec : decide (u < r.gridBoundary) = true := by simp [hu]
        exact he (by simpa [hEnabledGrid] using hdec)
      have hzero := hdisabled he0
      have hcollectionDisabled :
          ReferenceActivePhysicalStep.collectionEnabled l0 cut.input.time = false := by
        simp [ReferenceActivePhysicalStep.collectionEnabled,
          ReferenceActivePhysicalStep.sharedLedger, l0, hnotlt]
      change
        (ReferenceActivePhysicalStep.collectionEnabled l0 cut.input.time &&
          decide (cut.input.time.val + 1 < l0.freezeAt),
          if cut.input.time.val + 1 < l0.freezeAt then
            CoordinatorCollectionLedger.localArrival
              (ReferenceCollectionRawBufferHistory.rawDiagnostic cut) j else 0) =
        (e, RecordedQueueRun.quantizedArrival qpar c_u j)
      apply Prod.ext
      · simp [hcollectionDisabled, he0]
      · simp [hnotlt, l0, ReferenceActivePhysicalStep.sharedLedger, hzero.2 j]
  have hlength : (cells ++ [c_u]).length = k + 1 := by
    simp [cells, k, ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length]
    rfl
  have hrunOutput : CoordinatorRecorderComplementBridge.run recordingInput = some out := by
    change CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput cut.output.preparation P started weights) =
        some out
    rw [hprepEq]
    exact hrun
  have hgateSource : out.gateArm =
      CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart a hv e := by
    calc
      _ = c_u.recordedArm := hgateExact
      _ = SnapshotRecordingKernel.recordingMap p .collection e a.eta
          hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos
          hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
          (cut.input.row.2 t).1 := rfl
      _ = CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart a hv e := hmapFull
  have hrawGate : out.rawArrival =
      SnapshotRecordingKernel.recordedIncrement p rate.eta.val P.anchor
        (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (rewards t j)) out.gateArm := by
    rw [hgateExact]
    exact hrawExact
  have hrawNone : c_u.recordedArm = none → out.rawArrival = 0 := by
    intro hnone
    rw [hrawGate, hgateExact, hnone]
    rfl
  have hgrid : u = r.gridBoundary → e = false ∧
      c_u.recordedArm = none ∧
      ∀ j : Fin p.K, RecordedQueueRun.quantizedArrival qpar c_u j = 0 := by
    intro hu
    have he : e = false := by simp [hEnabledGrid, hu]
    exact ⟨he, (hdisabled he).1, (hdisabled he).2⟩
  have hproposal : u < r.gridBoundary → e = true := by
    intro hu
    simp [hEnabledGrid, hu]
  have hnoDataRecording :
      (PublicDiscreteDraws.slotDraw x ≠ PublicDiscreteDraws.dataSlot ∨ sourceDraw.val ≠ 0) →
      c_u.recordedArm = none ∧
      ∀ j : Fin p.K, RecordedQueueRun.quantizedArrival qpar c_u j = 0 := by
    intro hfail
    have hnone : c_u.recordedArm = none := by
      cases hrecord : c_u.recordedArm with
      | none => rfl
      | some j =>
          rcases (hmapEvent j).mp hrecord with ⟨_, hdata, hsource, _⟩
          rcases hfail with hslot | hsourceFail
          · exact False.elim (hslot hdata)
          · exact False.elim (hsourceFail hsource)
    exact ⟨hnone, fun j => by simp [RecordedQueueRun.quantizedArrival, hnone]⟩
  have hzeroRewardDiagnostic : ∀ j : Fin p.K,
      c_u.recordedArm = some j → c_u.reward j = 0 →
      ReferenceCollectionRawBufferHistory.rawDiagnostic cut = some (j, 0) := by
    intro j hrecord hzero
    have hrawZero : out.rawArrival = 0 := by
      rw [hrawExact, hrecord, hfloor j, hzero]
      simp
    rw [hrawDiagnostic, hgateExact, hrecord, hrawZero]
    rfl
  have hnotFast : ¬ (CoordinatorLocalArmChoice.assignmentIsLive r.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
      cut.input.time ∧ dispatched.startResult.pending = ∅) := by
    rintro ⟨_, hempty⟩
    let i : Fin (p.m - 1) := ⟨0, PublicDiscreteDraws.followerCount_pos p.two_le_m⟩
    have hi : i ∈ dispatched.startResult.pending := by
      rw [hpending]
      exact Finset.mem_univ i
    rw [hempty] at hi
    exact Finset.notMem_empty i hi
  have hpreparedArm :
      (ReferenceActivePhysicalStep.prepare cut.input).coordinator.arm = selected.arm := by
    rw [hbranchPrepared]
    simpa using ReferenceActivePhysicalStep.live_arm_equation r q base
      (.cutoffChosen dispatched hstart ledger hinitLedger hcand hdomain hclock hpending
        hnoAssignment selected)
  have hcoordinatorPilot : ∀ hdata : PublicDiscreteDraws.slotDraw x =
      PublicDiscreteDraws.dataSlot,
      cut.output.preparation.arms.actions (ActiveRoundActions.coordinator p.two_le_m) =
        PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p)
          (ActiveRoundActions.coordinator p.two_le_m) x := by
    intro hdata
    have hchoiceData := CoordinatorLocalArmChoice.coordinatorArmChoiceCore_data
      r.payload dispatched.startResult.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
      t (ReferenceActivePhysicalStep.liveRegistersAt r t).complementWeights
      (cut.input.row.2 t) selected.choiceInputsValid hnotFast hdata
    have hselectedPilot' : selected.arm =
        PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p)
          (ActiveRoundActions.coordinator p.two_le_m) x := by
      have hchoiceEq := selected.armChoice_eq
      have hchoiceEq' :
          CoordinatorLocalArmChoice.coordinatorArmChoice r.payload
            dispatched.startResult.pending
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
            t (ReferenceActivePhysicalStep.liveRegistersAt r t).complementWeights cut.input.row =
              some (PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p)
                (ActiveRoundActions.coordinator p.two_le_m) x) := by
        simpa [t, x, CoordinatorLocalArmChoice.coordinatorArmChoice] using hchoiceData
      exact Option.some.inj (hchoiceEq.symm.trans hchoiceEq')
    rw [hprepEq]
    calc
      (ReferenceActivePhysicalStep.prepare cut.input).arms.actions
          (ActiveRoundActions.coordinator p.two_le_m) =
        (ReferenceActivePhysicalStep.prepare cut.input).coordinator.arm :=
          (ReferenceActivePhysicalStep.prepare cut.input).action_coordinator
      _ = selected.arm := hpreparedArm
      _ = PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p)
          (ActiveRoundActions.coordinator p.two_le_m) x := hselectedPilot'
  have hfollowersPilot : ∀ i : Fin (p.m - 1),
      ∀ hdata : PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.dataSlot,
        cut.output.preparation.arms.actions
            (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
          PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p)
            (PublicDiscreteDraws.followerPlayer p.two_le_m i) x := by
    intro i hdata
    have hlocalArm := ReferenceActiveDataOwnership.ordinary_data_arm P i cut.input.row
      (cut.input.state.activations i) t (cut.input.active i)
      (cut.input.state.followers i) (cutoffStates i) (cutoffMemories i)
      (hordinaryPrepared i) (by intro h; exact False.elim (h (hunoccupied i))) hdata
    have hprepAction :=
      (ReferenceActivePhysicalStep.prepare cut.input).action_follower i
    calc
      cut.output.preparation.arms.actions
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
        (ReferenceActivePhysicalStep.prepare cut.input).arms.actions
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by rw [hprepEq]
      _ = (DeclaredFollowerLocalRound.prepare rate i cut.input.row
          (cut.input.state.activations i) t (cut.input.active i)
          (cut.input.state.followers i)).arm := hprepAction
      _ = PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) x := by
        simpa [t, x, hunoccupied i] using hlocalArm
  have hpilotActions : PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.dataSlot →
      ∀ player : Fin p.m,
        cut.output.preparation.arms.actions player =
          PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p) player x := by
    intro hdata player
    by_cases hc : player = ActiveRoundActions.coordinator p.two_le_m
    · subst player
      exact hcoordinatorPilot hdata
    · let i := ActiveRoundActions.followerIndex p.two_le_m player hc
      have hplayer := ActiveRoundActions.followerPlayer_followerIndex p.two_le_m player hc
      simpa [i, hplayer] using hfollowersPilot i hdata
  have hfeedbackRule :
      cut.output.preparation.feedback.feedback
          (ActiveRoundActions.coordinator p.two_le_m) =
        if FiniteBanditModel.collisionFreeFor cut.output.preparation.arms.actions
            (ActiveRoundActions.coordinator p.two_le_m) then
          cut.input.rewards cut.input.time
            (cut.output.preparation.arms.actions (ActiveRoundActions.coordinator p.two_le_m))
        else 0 := by
    rw [hprepEq]
    exact (ReferenceActivePhysicalStep.prepare cut.input).feedback_rule _
  have hfeedbackRecorded : ∀ j : Fin p.K, c_u.recordedArm = some j →
      FiniteBanditModel.collisionFreeFor cut.output.preparation.arms.actions
        (ActiveRoundActions.coordinator p.two_le_m) ∧
      cut.output.preparation.feedback.feedback
          (ActiveRoundActions.coordinator p.two_le_m) = rewards t j ∧
      (cut.output.preparation.feedback.observations
          (ActiveRoundActions.coordinator p.two_le_m)).val.val =
        ((rewards t j).val : ℝ) / (D p : ℝ) ∧
      CoordinatorRecordingOperation.observationValue a = c_u.reward j := by
    intro j hsome
    rcases (hmapEvent j).mp hsome with
      ⟨_, hdata, _, hpilot, hmask, _⟩
    have hactions := hpilotActions hdata
    have hcoordAction := hactions (ActiveRoundActions.coordinator p.two_le_m)
    have hfree : FiniteBanditModel.collisionFreeFor
        cut.output.preparation.arms.actions (ActiveRoundActions.coordinator p.two_le_m) := by
      intro player hne
      rw [hactions player, hcoordAction, hpilot]
      exact hmask player hne
    have hfeedback : cut.output.preparation.feedback.feedback
        (ActiveRoundActions.coordinator p.two_le_m) = rewards t j := by
      rw [hfeedbackRule, ite_eq_left hfree, hcoordAction, hpilot, hrewards]
    have hfeedbackPrepared :
        (ReferenceActivePhysicalStep.prepare cut.input).feedback.feedback
          (ActiveRoundActions.coordinator p.two_le_m) = rewards t j := by
      have h := hfeedback
      rw [hprepEq] at h
      exact h
    have hnormalized :
        (cut.output.preparation.feedback.observations
          (ActiveRoundActions.coordinator p.two_le_m)).val.val =
            ((rewards t j).val : ℝ) / (D p : ℝ) := by
      rw [hprepEq]
      rw [(ReferenceActivePhysicalStep.prepare cut.input).feedback.observations_eq _]
      rw [hfeedbackPrepared]
      rfl
    have hgridObservation : a.observation = rewards t j := by
      change cut.output.preparation.coordinatorObservation = rewards t j
      rw [ReferenceActivePhysicalStep.PreparedRound.coordinatorObservation]
      exact hfeedback
    have hvalue : CoordinatorRecordingOperation.observationValue a = c_u.reward j := by
      change RealRewardGridCount.realRewardGridValue (D p) (D_pos p) a.observation =
        ((rewards t j).val : ℝ) / (D p : ℝ)
      rw [hgridObservation]
      rfl
    exact ⟨hfree, hfeedback, hnormalized, hvalue⟩
  refine ⟨cut, suffix, r, q, base, ?_, hsplit, htime, hrows, hselectedRow,
      hrewards, hlive, hsigma, hdownZero, ?_⟩
  · simpa [execution, window, k,
        ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
        ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
        ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using hindex
  · refine Exists.intro dispatched ?_
    refine Exists.intro hstart ?_
    refine Exists.intro ledger ?_
    refine Exists.intro hinitLedger ?_
    refine Exists.intro hcand ?_
    refine Exists.intro hdomain ?_
    refine Exists.intro hclock ?_
    refine Exists.intro hpending ?_
    refine Exists.intro hnoAssignment ?_
    refine Exists.intro selected ?_
    constructor
    · exact hbranch
    constructor
    · rfl
    constructor
    · simpa [htime, hwindowEq] using huT
    constructor
    · simpa [htime, hwindowEq] using huGrid
    constructor
    · exact hledgerSigma
    constructor
    · simpa [htime, hwindowEq] using hledgerCut
    constructor
    · exact hcutFollowers
    constructor
    · exact hK
    constructor
    · exact hpreparationFrames
    constructor
    · exact hFollowerPrefixAtCut
    constructor
    · exact hpayload
    constructor
    · rfl
    constructor
    · rfl
    constructor
    · exact hmapEvent
    constructor
    · rfl
    constructor
    · rfl
    constructor
    · exact hweights
    constructor
    · exact hcollectionThreshold
    constructor
    · exact ⟨out, hrunOutput, hcutRecorder, hgateSource, hrawGate, hrawNone,
        hrawDiagnostic, hrecorderArrival⟩
    constructor
    · exact hEnabledGrid
    constructor
    · exact hgrid
    constructor
    · exact hproposal
    constructor
    · exact hnoDataRecording
    constructor
    · exact hzeroRewardDiagnostic
    constructor
    · exact hpilotActions
    constructor
    · exact hfeedbackRecorded
    constructor
    · intro j
      exact ⟨hlocalArrival j, hphysicalQueueRecord j⟩
    constructor
    · exact hdisabled
    · exact hlength

end Bandits.Support.ReferenceFirstCutoffNumericalSource

end
