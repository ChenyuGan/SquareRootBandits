/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCutoffNumericalSource

import Lean.Elab.Tactic.Omega

/-!
# Known coordinator registers at the actual first cutoff

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`,
`sources/zip4/manuscript/06_interruptions.tex:246-295`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

This module joins the actual source cell at the first cutoff to its checked
coordinator service, receiver, and finish operations.  It is an internal
first-cutoff result; it does not identify later collection records or close a
manuscript theorem. The next consumers, `ReferenceFirstCollectionNumericalReplay`
and `ReferenceFirstCollectionQueueContinuation`, still need the actual epoch,
head/pre-ledger alignment and source identity on every later collection record.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.ReferenceFirstLaunchNumericalCell
open Bandits.Support.ReferenceGeneratedFirstCutoffSurvival
open Bandits.Support.ReferenceFirstCutoffNumericalSource
open Bandits.Support.ReferenceFirstCutoffRecordedService
open Bandits.Support.ReferenceFirstCutoffReceiverDomain
open Bandits.Support.ReferenceFirstCutoffFinishSafety
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorStartRoundCutoffDispatch
open Bandits.Support.CoordinatorCollectionUpRoundStep
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.ReferenceUpReception
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.QueueReplay
open scoped Classical

namespace Bandits.Support.ReferenceFirstCutoffKnownNumericalState

variable {p : ConstructorDimensions.Parameters}

private theorem physical_run_records_eq_of_same_initial
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial initial' : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (active' : ReferenceActivePhysicalHorizon.allActiveAtStart initial' start)
    (hstate : initial = initial') :
    (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records =
      (ReferenceActivePhysicalHorizon.run initial' rows J rewards start count hspan active').records := by
  cases hstate
  have hactive : active = active' := Subsingleton.elim _ _
  cases hactive
  rfl

/-- The known coordinator queues at the actual first cutoff agree with the
original source replay, including the cutoff update and the actual rejected
receiver and successful finish. All dispatch, recorder, and domain witnesses
are produced from the original initialization and physical execution. -/
theorem actual_first_cutoff_known_numerical_state
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
    ∃ (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      ∃ (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))),
      ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta),
      ∃ (q : CoordinatorLiveServiceFinish.OwnedRegisters r),
      ∃ (base : Fin (p.m - 1) → ℕ),
      ∃ (dispatched : CoordinatorStartRoundCutoffDispatch.Output
        (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers
        (ReferenceActivePhysicalStep.liveInput cut.input r q base).ownedRegisters base),
      ∃ (hstart : CoordinatorPhaseClock.startRound p rate.eta.val
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.priorClock
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.clockPending =
            .ok dispatched.startResult),
      ∃ (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger
        (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers),
      ∃ (hinit : dispatched.collectionInitialization = .success (some ledger)),
      ∃ (hledger : ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).ownedRegisters
          base (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time),
      ∃ (hdomain : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).ownedRegisters
          base (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time),
      ∃ (hclock : dispatched.startResult.clock =
          { (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.priorClock with
            u := some (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time }),
      ∃ (hpending : dispatched.startResult.pending = Finset.univ),
      ∃ (hnoAssignment : dispatched.startResult.assignmentStart = none),
      ∃ (selected : CoordinatorRoundDispatch.ArmSelection r.payload
          dispatched.startResult (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.complementWeights
          cut.input.row),
      ∃ (out : CoordinatorRecordingOperation.Output p),
      cut = execution.records[k]'(by
        have hk : k < count := by
          simpa [k, window, execution,
            ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
            ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
            ReferenceFirstWindowNumericalStream.actualFirstLiveSeed,
            ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using hshort
        simpa [execution, ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
          ReferenceFirstWindowNumericalStream.actualFirstLiveSeed,
          ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using
          hk.trans_eq (ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan
            (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
              rate source rewards C_star C_h hc).activeAtStart).symm) ∧
      execution.records = window ++ cut :: suffix ∧
      (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (k + 1)
        (by
          have hk : k < count := by
            simpa [k, window] using hshort
          have hspanS : s + count ≤ p.T := by
            simpa [s, boot, init] using hspan
          omega)
        (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
          rate source rewards C_star C_h hc).activeAtStart).finalState = cut.output.next ∧
      cut.input.time.val = s + k ∧
      cut.input.rows = source.1.2 ∧
      cut.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      cut.input.rewards = rewards ∧
      r.payload.sigma.val = s ∧ r.payload.n = rate.n ∧ (∀ i, base i = 0) ∧
      cut.input.state.coordinator = .live r q base ∧
      cut.output.preparation.coordinator = .live r q base
        (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
          hnoAssignment selected) ∧
      u = s + k + 1 ∧ u ≤ p.T ∧ u ≤ r.gridBoundary ∧ ledger.cutoff = u ∧
      k > 0 ∧
      (∀ j : Fin k,
        (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
          rate source rewards C_star C_h hc count hspan j).selected.view.payload = r.payload) ∧
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
      let c_u : RecordedQueueRun.RoundInput p.K := {
        enabled := e
        recordedArm := SnapshotRecordingKernel.recordingMap p .collection e
          a.eta hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos
          hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor (cut.input.row.2 t).1
        reward := fun j => ((rewards t j).val : ℝ) / (D p : ℝ)
        rate := P.rate
        reward_nonneg := by
          intro j
          exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        reward_le_one := by
          intro j
          have hj : (rewards t j).val ≤ D p := Nat.le_of_lt_succ (rewards t j).isLt
          apply (div_le_one (Nat.cast_pos.mpr (D_pos p))).2
          exact_mod_cast hj
        rate_pos := by
          intro j
          exact (CanonicalRecordingRates.beta_pos p rate.eta.property).trans_le (P.beta_le_rate j) }
      c_u.enabled = e ∧
      c_u.recordedArm = SnapshotRecordingKernel.recordingMap p .collection e
        a.eta hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos
        hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor (cut.input.row.2 t).1 ∧
      c_u.reward = (fun j => ((rewards t j).val : ℝ) / (D p : ℝ)) ∧
      c_u.rate = P.rate ∧
      e = decide (u < r.gridBoundary) ∧
      CoordinatorRecorderComplementBridge.run recordingInput = some out ∧
      cut.output.coordinator.recording = some out ∧
      (c_u.recordedArm = none → out.rawArrival = 0) ∧
      ReferenceCollectionRawBufferHistory.rawDiagnostic cut =
        out.gateArm.map (fun j => (j, out.rawArrival)) ∧
      (∀ j : Fin p.K, c_u.recordedArm = some j → c_u.reward j = 0 →
        ReferenceCollectionRawBufferHistory.rawDiagnostic cut = some (j, 0)) ∧
      (PublicDiscreteDraws.slotDraw (cut.input.row.2 t).1 ≠ PublicDiscreteDraws.dataSlot →
        c_u.recordedArm = none ∧ ∀ j : Fin p.K,
          RecordedQueueRun.quantizedArrival qpar c_u j = 0) ∧
      (∀ j : Fin p.K,
        CoordinatorCollectionLedger.localArrival
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) j =
            RecordedQueueRun.quantizedArrival qpar c_u j) ∧
      (∀ j : Fin p.K,
        CoordinatorCollectionLedger.localArrival
          (ReferenceCollectionRawBufferHistory.rawDiagnostic cut) j =
            RecordedQueueRun.quantizedArrival qpar c_u j ∧
        ReferenceCollectionRawBufferHistory.physicalQueueRecord l0 j cut =
          (e, RecordedQueueRun.quantizedArrival qpar c_u j)) ∧
      (e = false → c_u.recordedArm = none ∧ ∀ j : Fin p.K,
        RecordedQueueRun.quantizedArrival qpar c_u j = 0) ∧
      (u = r.gridBoundary → e = false ∧ c_u.recordedArm = none ∧
        ∀ j : Fin p.K, RecordedQueueRun.quantizedArrival qpar c_u j = 0) ∧
      (cells ++ [c_u]).length = k + 1 ∧
      (∀ arm : Fin p.K, arm ∈ P.slowSet.val → l0.cutoffRegisters arm = none) ∧
      ∃ ledgerStarted,
        let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out
        CoordinatorCollectionLedger.startRound l0 (t.val + 1) e raw =
          .success ledgerStarted ∧
        ledgerStarted = CoordinatorCollectionLedger.startRoundCandidate l0 t e raw ∧
        (∀ a : FastArm P.slowSet,
          let Da := cells.map fun c =>
            (c.enabled, RecordedQueueRun.quantizedArrival qpar c a.val)
          let Va := QueueReplay.replay (4 * rate.n) (0, 0) Da
          let Vplus := QueueReplay.transition (4 * rate.n) Va
            (e, RecordedQueueRun.quantizedArrival qpar c_u a.val)
          let oldLast := q.previousService a
          CoordinatorCollectionLedger.localQueueRecord l0 t e raw a.val =
            (e, RecordedQueueRun.quantizedArrival qpar c_u a.val) ∧
          l0.cutoffRegisters a.val = some ⟨Va.1, Va.2, oldLast⟩ ∧
          l0.currentRegisters a.val = some ⟨Va.2, oldLast⟩ ∧
          l0.increment a.val = 0 ∧
          ledgerStarted.currentRegisters a.val =
            some ⟨Vplus.2, Vplus.1 - Va.1⟩ ∧
          ledgerStarted.gammaLoc a.val = Vplus.1 - Va.1 ∧
          ledgerStarted.increment a.val = 0 ∧
          QueueReplay.replay (4 * rate.n) (0, 0)
            ((cells ++ [c_u]).map fun c =>
              (c.enabled, RecordedQueueRun.quantizedArrival qpar c a.val)) = Vplus ∧
          (e = true → RecordedQueueRun.quantizedArrival qpar c_u a.val = 0 →
            Vplus = (Va.1 + min (4 * rate.n) Va.2, Va.2 - min (4 * rate.n) Va.2)) ∧
          (e = false → Vplus = Va ∧ ledgerStarted.gammaLoc a.val = 0 ∧
            ledgerStarted.currentRegisters a.val = some ⟨Va.2, 0⟩ ∧
            ledgerStarted.cutoffRegisters a.val = l0.cutoffRegisters a.val)) ∧
        (∀ arm : Fin p.K, l0.cutoffRegisters arm = none →
          l0.currentRegisters arm = none ∧ ledgerStarted.currentRegisters arm = none ∧
          ledgerStarted.gammaLoc arm = 0 ∧ ledgerStarted.increment arm = 0) ∧
        (∀ arm amount, l0.currentRegisters arm = none → 0 < amount →
          CoordinatorCollectionLedger.sourceRound t < l0.freezeAt →
          raw = some (arm, amount) →
          ledgerStarted.rawBuffer arm t = some amount) ∧
        ∃ input diagnostic,
          input = ReferenceUpReception.receptionInputAtRow rate cut.input.row
            (ReferenceActivePhysicalStep.upInputs cut.output.preparation ledgerStarted) t ∧
          input.ledger = ledgerStarted ∧
          CoordinatorUpReception.receptionInputDomain input ∧
          CoordinatorUpReception.receptionInputCheck input = true ∧
          ReferenceUpReception.rawParsedOutput rate input = none ∧
          ReferenceUpReception.filterRawByExpected
            (CoordinatorUpReception.decoderTransition input).2
            (ReferenceActivePhysicalStep.upExpected cut.output.preparation) = none ∧
          CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
            (ReferenceUpReception.filterRawByExpected
              (CoordinatorUpReception.decoderTransition input).2
              (ReferenceActivePhysicalStep.upExpected cut.output.preparation)) = none ∧
          (ReferenceActivePhysicalStep.receiveUp cut.output.preparation ledgerStarted).result =
            .rejected ({input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded},
              CoordinatorUpReception.decoderBankAfter input) ∧
          (ReferenceActivePhysicalStep.receiveUp cut.output.preparation ledgerStarted).diagnostic =
            some diagnostic ∧
          diagnostic.input = input ∧ diagnostic.raw = none ∧ diagnostic.parsed = none ∧
          diagnostic.expected = ReferenceActivePhysicalStep.upExpected cut.output.preparation ∧
          diagnostic.decoderAfter = (CoordinatorUpReception.decoderTransition input).1 ∧
          diagnostic.locallyAccepted = false ∧
          diagnostic.rawMatches = decide
            (none = ReferenceActivePhysicalStep.upExpected cut.output.preparation) ∧
          diagnostic.wrongUniqueAccepted = false ∧
          (∀ i, i ≠ input.selectedFollower →
            (CoordinatorUpReception.decoderBankAfter input) i = input.upDecoderBank i) ∧
          CoordinatorUpReception.decoderBankAfter input =
            Function.update input.upDecoderBank input.selectedFollower
              (CoordinatorUpReception.decoderTransition input).1 ∧
          (CoordinatorUpReception.decoderTransition input).1.completed = [] ∧
          (CoordinatorUpReception.decoderTransition input).1.pending =
            (if CoordinatorUpReception.receptionGate input ∧ 0 < input.ownObservation.val then
              [AffineBatchDecoder.entry p (CoordinatorUpReception.traceAt input) input.time]
            else []) ∧
          ∃ finished,
            CoordinatorCollectionLedger.finishRound
              {input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded} =
                .success finished ∧
            finished = CoordinatorCollectionLedger.finishRoundCandidate
              {input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded} ∧
            finished.cutoffRegisters = l0.cutoffRegisters ∧
            (∀ a : FastArm P.slowSet,
              let Da := cells.map fun c =>
                (c.enabled, RecordedQueueRun.quantizedArrival qpar c a.val)
              let Va := QueueReplay.replay (4 * rate.n) (0, 0) Da
              let Vplus := QueueReplay.transition (4 * rate.n) Va
                (e, RecordedQueueRun.quantizedArrival qpar c_u a.val)
              finished.increment a.val = Vplus.1 - Va.1 ∧
              finished.currentRegisters a.val =
                some ⟨Vplus.2, Vplus.1 - Va.1⟩ ∧
              ((l0.cutoffRegisters a.val).getD { score := 0, queue := 0, lastService := 0 }).score +
                finished.increment a.val = Vplus.1 ∧
              (e = false → finished.increment a.val = 0 ∧
                finished.currentRegisters a.val = some ⟨Va.2, 0⟩)) ∧
            (∀ arm : Fin p.K, l0.cutoffRegisters arm = none →
              finished.currentRegisters arm = none ∧ finished.gammaLoc arm = 0 ∧
              finished.increment arm = 0) ∧
            cut.output.coordinator.configuration =
              .collection P finished dispatched.startResult.clock.lastProposal ∧
            cut.output.next.coordinator =
              .collection P finished dispatched.startResult.clock.lastProposal ∧
            cut.output.next.upDecoderBank = CoordinatorUpReception.decoderBankAfter input ∧
            cut.output.coordinator.upDecoderBank =
              CoordinatorUpReception.decoderBankAfter input ∧
            cut.output.coordinator.failure = none ∧
            cut.output.coordinator.recording = some out ∧
            cut.output.coordinator.up =
              (ReferenceActivePhysicalStep.receiveUp cut.output.preparation ledgerStarted).diagnostic
 := by
  classical
  dsimp only
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
  -- A supplies the actual cutoff constructor and literal collection source cell.
  have hsource := ReferenceFirstCutoffNumericalSource.actual_first_cutoff_numerical_source
    rate source rewards C_star C_h hc count hspan hshort
  dsimp only at hsource
  rcases hsource with
    ⟨cut, suffix, r, q, base, hindex, hsplit, htime, hrows, hselectedRow,
      hrewards, hstate, hsigma, hdownZero, hcutoff⟩
  rcases hcutoff with
    ⟨dispatched, hstart, ledger, hinit, hledger, hdomain, hclock, hpending,
      hnoAssignment, selected, htail⟩
  rcases htail with
    ⟨hbranch, hu, huT, huGrid, hledgerSigma, hledgerCut, hcutFollowers, hkpos,
      hprepFrames, hprefixFollowers, hpayloads, hnumerics⟩
  rcases hnumerics with
    ⟨henabled, hmap, hmapEvent, hreward, hrate, hweights, hthreshold, hout,
      hgridEnable, hgrid, hproposal, hnoData, hzeroReward, hpilot, hfeedback,
      hphysical, hdisabled, hlength⟩
  rcases hout with ⟨out, hrun, hrecording, hgate, hraw, hrawNone, hrawDiagnostic, hlocalArrival⟩
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
  let c_u : RecordedQueueRun.RoundInput p.K := {
    enabled := e
    recordedArm := SnapshotRecordingKernel.recordingMap p .collection e
      a.eta hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos
      hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor (cut.input.row.2 t).1
    reward := fun j => ((rewards t j).val : ℝ) / (D p : ℝ)
    rate := P.rate
    reward_nonneg := by
      intro j
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    reward_le_one := by
      intro j
      have hj : (rewards t j).val ≤ D p := Nat.le_of_lt_succ (rewards t j).isLt
      apply (div_le_one (Nat.cast_pos.mpr (D_pos p))).2
      exact_mod_cast hj
    rate_pos := by
      intro j
      exact (CanonicalRecordingRates.beta_pos p rate.eta.property).trans_le (P.beta_le_rate j) }
  have hCore : cut = execution.records[k]'(by
      have hk : k < count := by
        simpa [k, window, execution, ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
          ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
          ReferenceFirstWindowNumericalStream.actualFirstLiveSeed,
          ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using hshort
      simpa [execution, ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
        ReferenceFirstWindowNumericalStream.actualFirstLiveSeed,
        ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using
        hk.trans_eq (ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan
          (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
            rate source rewards C_star C_h hc).activeAtStart).symm) := by
    simpa [execution, window, k, ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
      ReferenceFirstWindowNumericalStream.actualFirstLiveWindow] using hindex
  have hshortRun :
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records).length < count := by
    simpa [execution, window, ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
      ReferenceFirstWindowNumericalStream.actualFirstLiveSeed,
      ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using hshort
  have hsT : s < p.T := by
    have hk : k < count := by
      simpa [k, window] using hshort
    have hspanS : s + count ≤ p.T := by
      simpa [s, boot, init] using hspan
    have hcount : 0 < count := by omega
    omega
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  let t0 : Fin p.T := ⟨s, hsT⟩
  let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p J t0 source
  have hrem : split.2 ∈
      (ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p J t0) := by
    change PrivateSourceStreams.coordinatorIndex p
      ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p J t0 source).2.2).1.2 = J
    rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_private]
    change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source = J
    rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
  have hstartRemainder : split.2 ∈
      ReferenceInitializationControlRemainder.launchStartRemainderEvent
        rate rewards C_star C_h J t0 s split.1 := by
    exact (ReferenceInitializationControlRemainder.launchStartRemainderEvent_iff_source
      rate rewards C_star C_h J t0 split.1 source rfl s (Nat.le_of_eq rfl)).mpr
        ⟨hc, rfl⟩
  let initialR := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h J t0 split.1 split.2 hrem s (Nat.le_of_eq rfl) hstartRemainder
  let activeR := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h J t0 split.1 split.2 hrem s (Nat.le_of_eq rfl)
    hstartRemainder).2.1
  -- Transport the generated receiver run back to the original initialization.
  have hseedEq : initialR = initial := by
    simpa [initialR, J, t0, split] using
      ReferenceGeneratedFirstCutoffSurvival.generatedLaunchSeed_eq_launchState
        rate source rewards C_star C_h hc s rfl hsT
  have hrunRecordsGenerated :
      (ReferenceActivePhysicalHorizon.run initialR source.1.2 J rewards s count hspan activeR).records =
        execution.records := by
    simpa [execution, initial, ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
      ReferenceFirstWindowNumericalStream.actualFirstLiveSeed] using
      physical_run_records_eq_of_same_initial initialR initial source.1.2 J rewards s count hspan
        activeR (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
          rate source rewards C_star C_h hc).activeAtStart hseedEq
  have hshortGenerated :
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceActivePhysicalHorizon.run initialR source.1.2 J rewards s count hspan
          activeR).records).length < count := by
    rw [hrunRecordsGenerated]
    simpa [execution] using hshortRun
  have hreceiver := ReferenceFirstCutoffReceiverDomain.run_generated_first_cutoff_receiver_domain
    rate source rewards C_star C_h hc s rfl hsT count hspan t0 rfl
  rcases hreceiver with ⟨_, _, _, _, _, hreceiverTail⟩
  have hreceiverCut := hreceiverTail hshortGenerated
  -- C supplies the incoming numerical registers; constructor injection below
  -- identifies the complete live configuration, including its payload and queues.
  have hprefix := ReferenceFirstLiveComplementQueueReplay.actual_first_live_complement_prefix_replay
    rate source rewards C_star C_h hc count hspan k le_rfl
  dsimp only at hprefix
  have hrecorded := ReferenceFirstCutoffRecordedService.run_first_cutoff_recorded_service
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards s count hspan
    (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate source rewards C_star C_h hc).activeAtStart
    (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate source rewards C_star C_h hc).coordinatorFirst hshortRun
  rcases hrecorded with
    ⟨cutRecorded, suffixRecorded, hsplitRecorded, hindexRecorded, htimeRecorded,
      rRecorded, qRecorded, baseRecorded, hstateRecorded, hprefixRecorded, hcallRecorded⟩
  have hrecordedIndex : cutRecorded = execution.records[k]'(by
      have hk : k < count := by
        simpa [k, window, execution, ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
          ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
          ReferenceFirstWindowNumericalStream.actualFirstLiveSeed,
          ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using hshort
      simpa [execution, ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
        ReferenceFirstWindowNumericalStream.actualFirstLiveSeed,
        ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using
        hk.trans_eq (ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan
          (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
            rate source rewards C_star C_h hc).activeAtStart).symm) := by
    simpa [execution, window, k, ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
      ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
      ReferenceFirstWindowNumericalStream.actualFirstLiveSeed,
      ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using hindexRecorded
  have hsameCut : cutRecorded = cut := by
    calc
      cutRecorded = execution.records[k]'_ := hrecordedIndex
      _ = cut := by rw [hCore]
  cases hsameCut
  have hprefixShape := hprefix.2.2
  rcases hprefixShape hkpos with
    ⟨rPrefix, qPrefix, basePrefix, hprefixCoord, hprefixTime, hsigmaPrefix,
      hnPrefix, hbaseZero, hprefixRest⟩
  have hcutServiceCoord : cut.input.state.coordinator =
      CoordinatorConfiguration.live rRecorded qRecorded baseRecorded := by
    exact (congrArg (fun state : ReferenceActivePhysicalHorizon.State p rate =>
      state.coordinator) hstateRecorded).trans hprefixRecorded
  have hEqRecorded : CoordinatorConfiguration.live rRecorded qRecorded baseRecorded =
      CoordinatorConfiguration.live r q base := hcutServiceCoord.symm.trans hstate
  cases hEqRecorded
  have hEqPrefix : CoordinatorConfiguration.live rPrefix qPrefix basePrefix =
      CoordinatorConfiguration.live r q base :=
    hprefixCoord.symm.trans hprefixRecorded
  cases hEqPrefix
  rcases hprefixRest with ⟨hprefixBirth, hprefixQueue⟩
  rcases hcallRecorded with
    ⟨dispatchedRecorded, hstartRecorded, ledgerRecorded, hinitRecorded,
      hledgerRecorded, hdomainRecorded, hclockRecorded, hpendingRecorded,
      hnoAssignmentRecorded, selectedRecorded, hbranchRecorded, hrecordRest⟩
  have hbranchEq := hbranch.symm.trans hbranchRecorded
  cases hbranchEq
  rcases hrecordRest with
    ⟨outRecorded, hactualInputRecorded, htraceRecorded, hdiagnosticRecorded,
      hrunRecorded, hnextRecorded⟩
  have houtEq : outRecorded = out := by
    have hEq : some out = some outRecorded := hrecording.symm.trans hdiagnosticRecorded
    exact (Option.some.inj hEq).symm
  subst outRecorded
  dsimp only at hnextRecorded
  rcases hnextRecorded with
    ⟨ledgerStarted, hstartSuccess, hstartCandidate, hknownTransition,
      hunknownStageOne, hrawArrival, hrawFrame, hqueueDomains⟩
  rcases hreceiverCut with
    ⟨cutReceiver, suffixReceiver, hsplitReceiver, htimeReceiver,
      rReceiver, qReceiver, baseReceiver, hstateReceiver, hcallReceiver⟩
  have hsplitReceiverGenerated :
      (ReferenceActivePhysicalHorizon.run initialR source.1.2 J rewards s count hspan
        activeR).records =
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceActivePhysicalHorizon.run initialR source.1.2 J rewards s count hspan
            activeR).records) ++ cutReceiver :: suffixReceiver := by
    simpa [initialR, activeR, J, t0, split] using hsplitReceiver
  have hsplitReceiverActual : execution.records = window ++ cutReceiver :: suffixReceiver := by
    rw [hrunRecordsGenerated] at hsplitReceiverGenerated
    simpa [execution, window,
      ReferenceFirstWindowNumericalStream.actualFirstLiveWindow] using hsplitReceiverGenerated
  have hcutReceiverEq : cutReceiver = cut := by
    have hEq :
        (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
          rate source rewards C_star C_h hc count hspan) ++ cut :: suffix =
        (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
          rate source rewards C_star C_h hc count hspan) ++ cutReceiver :: suffixReceiver := by
      simpa [window] using hsplit.symm.trans hsplitReceiverActual
    have htails := List.append_cancel_left hEq
    exact (List.cons.inj htails).1.symm
  cases hcutReceiverEq
  have hstateReceiverEq : CoordinatorConfiguration.live rReceiver qReceiver baseReceiver =
      CoordinatorConfiguration.live r q base := hstateReceiver.symm.trans hstate
  cases hstateReceiverEq
  rcases hcallReceiver with
    ⟨dispatchedReceiver, hstartReceiver, ledgerReceiver, hinitReceiver,
      hledgerReceiver, hdomainReceiver, hclockReceiver, hpendingReceiver,
      hnoAssignmentReceiver, selectedReceiver, hbranchReceiver, hrecordingReceiver⟩
  have hbranchReceiverEq := hbranch.symm.trans hbranchReceiver
  cases hbranchReceiverEq
  rcases hrecordingReceiver with
    ⟨recordingReceiver, hactualInputReceiver, htraceReceiver, hdiagnosticReceiver,
      hrunReceiver, hnextReceiver⟩
  rcases hnextReceiver with
    ⟨ledgerReceiverStarted, hstartReceiverSuccess, hstartReceiverCandidate,
      hinputReceiver⟩
  rcases hinputReceiver with
    ⟨inputReceiver, hinputReceiverEq, hinputDomain, hinputCheck, hdecoderTransition,
      hquota, hrawParsedNone, hfilterNone, hparseNone, hreceiveRejected,
      hbankAfterEq, hcompleted, hpendingDecoder, hdiagnosticRest⟩
  rcases hdiagnosticRest with
    ⟨diagnosticReceiver, hreceiveDiagnostic, hdiagnosticInput, hdiagnosticExpected,
      hdiagnosticDecoder, hdiagnosticRaw, hdiagnosticParsed, hlocallyAccepted,
      hrawMatches, hwrongUnique, hbankFrame, hfreezeGate⟩
  have hrecordingReceiver' : cut.output.coordinator.recording = some recordingReceiver := by
    change cut.output.coordinator.recording = some recordingReceiver at hdiagnosticReceiver
    exact hdiagnosticReceiver
  have hrecordingEq : recordingReceiver = out := by
    have h := hrecording.symm.trans hrecordingReceiver'
    exact (Option.some.inj h).symm
  have hstartReceiverCandidate' : ledgerReceiverStarted =
      CoordinatorCollectionLedger.startRoundCandidate l0 t e
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) := by
    simpa [l0, t, e, hrecordingEq] using hstartReceiverCandidate
  have hledgerReceiverStartedEq : ledgerReceiverStarted = ledgerStarted :=
    hstartReceiverCandidate'.trans hstartCandidate.symm
  subst recordingReceiver
  rw [hledgerReceiverStartedEq] at hinputReceiverEq hreceiveRejected hreceiveDiagnostic
  have hfinish := ReferenceFirstCutoffFinishSafety.run_first_cutoff_finish_domains
    initial source.1.2 J rewards s count hspan
    (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate source rewards C_star C_h hc).activeAtStart
    (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate source rewards C_star C_h hc).coordinatorFirst hshortRun
  dsimp only at hfinish
  rcases hfinish with
    ⟨cutFinish, suffixFinish, hsplitFinish, hindexFinish, htimeFinish,
      rFinish, qFinish, baseFinish, hfinishState, hfinishPrefix, hcallFinish⟩
  rcases hcallFinish with
    ⟨dispatchedFinish, hstartFinish, ledgerFinish0, hinitFinish, hledgerFinish,
      hdomainFinish, hclockFinish, hpendingFinish, hnoAssignmentFinish,
      selectedFinish, hbranchFinish, hfinishRecord⟩
  rcases hfinishRecord with
    ⟨outFinish, hactualInputFinish, htraceFinish, hdiagnosticFinish,
      hrecorderFinish, hfinishRest⟩
  rcases hfinishRest with
    ⟨ledgerStartedFinish, hstartFinishSuccess, hstartFinishCandidate,
      hknownFinishTransition, hunknownFinishStageOne, hrawFinishArrival,
      hrawFinishFrame, hfinishQueueDomains, hfinishDomains⟩
  have hsplitFinishActual : execution.records = window ++ cutFinish :: suffixFinish := by
    simpa [execution, window, ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
      ReferenceFirstWindowNumericalStream.actualFirstLiveSeed] using hsplitFinish
  have hfinishTailEq : cut :: suffix = cutFinish :: suffixFinish := by
    have hEq : window ++ cut :: suffix = window ++ cutFinish :: suffixFinish := by
      calc
        window ++ cut :: suffix = execution.records := hsplit.symm
        _ = window ++ cutFinish :: suffixFinish := hsplitFinishActual
    exact List.append_cancel_left hEq
  have hcutFinishEq : cutFinish = cut := (List.cons.inj hfinishTailEq).1.symm
  cases hcutFinishEq
  have hfinishStateCoordinator : cut.input.state.coordinator =
      CoordinatorConfiguration.live rFinish qFinish baseFinish :=
    (congrArg (fun state : ReferenceActivePhysicalHorizon.State p rate => state.coordinator)
      hfinishState).trans hfinishPrefix
  have hfinishConfigEq : CoordinatorConfiguration.live rFinish qFinish baseFinish =
      CoordinatorConfiguration.live r q base := hfinishStateCoordinator.symm.trans hstate
  cases hfinishConfigEq
  have hbranchFinishEq := hbranch.symm.trans hbranchFinish
  cases hbranchFinishEq
  have houtFinishEq : outFinish = out := by
    have hEq : some out = some outFinish := hrecording.symm.trans hdiagnosticFinish
    exact (Option.some.inj hEq).symm
  subst outFinish
  have hstartFinishCandidate' : ledgerStartedFinish =
      CoordinatorCollectionLedger.startRoundCandidate l0 t e
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) := by
    simpa [l0, t, e] using hstartFinishCandidate
  have hledgerStartedFinishEq : ledgerStartedFinish = ledgerStarted :=
    hstartFinishCandidate'.trans hstartCandidate.symm
  rw [hledgerStartedFinishEq] at hfinishDomains
  have hinputLedger : inputReceiver.ledger = ledgerStarted := by
    rw [hinputReceiverEq]
    rfl
  let decoded : ReferenceActivePhysicalStep.Ledger rate :=
    {inputReceiver.ledger with phase := CoordinatorCollectionLedger.Phase.decoded}
  let bankAfter := CoordinatorUpReception.decoderBankAfter inputReceiver
  -- FINISH consumes the rejection just produced by the actual receiver call.
  have hfinishProduced := hfinishDomains decoded bankAfter (Or.inr hreceiveRejected)
  rcases hfinishProduced with
    ⟨finished, hfinishSuccess, hfinishValid, hfinishClock,
      hfinishConfiguration, hfinishBank, hfinishFailure, hfinishRecording, hfinishUp⟩
  have hfinishedCandidate : finished =
      CoordinatorCollectionLedger.finishRoundCandidate decoded :=
    CoordinatorCollectionUpRoundStep.InputsValid.finishRound_success_candidate
      decoded finished hfinishSuccess
  have hstartedCutoffFrame : ledgerStarted.cutoffRegisters = l0.cutoffRegisters := by
    rw [hstartCandidate]
    rfl
  have hboundarySuccessor :
      (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s (k + 1)
        (by
          have hk : k < count := by simpa [k, window] using hshort
          have hspanS : s + count ≤ p.T := by simpa [s, boot, init] using hspan
          omega)
        (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
          rate source rewards C_star C_h hc).activeAtStart).finalState = cut.output.next := by
    have hkcount : k < count := by simpa only [k, window] using hshort
    have hspanS : s + count ≤ p.T := by simpa only [s, boot, init] using hspan
    have hsk : s + k < p.T := (Nat.add_lt_add_left hkcount s).trans_le hspanS
    have hprefixSpan : s + k ≤ p.T := hsk.le
    have hmode := (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate source rewards C_star C_h hc).activeAtStart
    let preRun := ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards
      s k hprefixSpan hmode
    let entry : ReferenceActivePhysicalHorizon.CalendarEntry p s :=
      ⟨s + k, Nat.le_add_right s k, hsk⟩
    let input := ReferenceActivePhysicalHorizon.roundInputAt
      initial source.1.2 J rewards s hmode preRun entry
    have hstateInput : cut.input.state = input.state := hstateRecorded
    have htimeInput : cut.input.time = input.time := Fin.ext htime
    have hrowInput : cut.input.row = input.row := by
      unfold ReferenceActivePhysicalStep.RoundInput.row
      rw [hrows, hselectedRow]
      rfl
    have hevidence := ReferenceActivePhysicalHorizon.computedEvidence_congr
      cut.input input hstateInput hselectedRow htimeInput hrewards hrowInput
    have hnext := congrArg ReferenceActivePhysicalHorizon.RoundEvidence.after hevidence
    change (ReferenceActivePhysicalStep.step cut.input).next =
      (ReferenceActivePhysicalStep.step input).next at hnext
    rw [ReferenceActivePhysicalHorizon.run_successor_step]
    change (ReferenceActivePhysicalStep.step input).next = cut.output.next
    rw [← hnext, cut.output_eq]
  have hcellsLength : cells.length = k := by
    simpa [cells, k, window] using
      ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
        rate source rewards C_star C_h hc count hspan
  let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out
  -- Read the literal cutoff initializer and START candidate using C and A.
  -- Enabled zero arrivals and disabled records remain separate queue inputs.
  have hserviceFacts :
      CoordinatorCollectionLedger.startRound l0 (t.val + 1) e raw = .success ledgerStarted ∧
      ledgerStarted = CoordinatorCollectionLedger.startRoundCandidate l0 t e raw ∧
      (∀ a : FastArm P.slowSet,
        let Da := cells.map fun c =>
          (c.enabled, RecordedQueueRun.quantizedArrival qpar c a.val)
        let Va := QueueReplay.replay (4 * rate.n) (0, 0) Da
        let Vplus := QueueReplay.transition (4 * rate.n) Va
          (e, RecordedQueueRun.quantizedArrival qpar c_u a.val)
        let oldLast := q.previousService a
        CoordinatorCollectionLedger.localQueueRecord l0 t e raw a.val =
          (e, RecordedQueueRun.quantizedArrival qpar c_u a.val) ∧
        l0.cutoffRegisters a.val = some ⟨Va.1, Va.2, oldLast⟩ ∧
        l0.currentRegisters a.val = some ⟨Va.2, oldLast⟩ ∧
        l0.increment a.val = 0 ∧
        ledgerStarted.currentRegisters a.val = some ⟨Vplus.2, Vplus.1 - Va.1⟩ ∧
        ledgerStarted.gammaLoc a.val = Vplus.1 - Va.1 ∧
        ledgerStarted.increment a.val = 0 ∧
        QueueReplay.replay (4 * rate.n) (0, 0)
          ((cells ++ [c_u]).map fun c =>
            (c.enabled, RecordedQueueRun.quantizedArrival qpar c a.val)) = Vplus ∧
        (e = true → RecordedQueueRun.quantizedArrival qpar c_u a.val = 0 →
          Vplus = (Va.1 + min (4 * rate.n) Va.2, Va.2 - min (4 * rate.n) Va.2)) ∧
        (e = false → Vplus = Va ∧ ledgerStarted.gammaLoc a.val = 0 ∧
          ledgerStarted.currentRegisters a.val = some ⟨Va.2, 0⟩ ∧
          ledgerStarted.cutoffRegisters a.val = l0.cutoffRegisters a.val)) ∧
      (∀ arm : Fin p.K, l0.cutoffRegisters arm = none →
        l0.currentRegisters arm = none ∧ ledgerStarted.currentRegisters arm = none ∧
          ledgerStarted.gammaLoc arm = 0 ∧ ledgerStarted.increment arm = 0) ∧
      (∀ arm amount, l0.currentRegisters arm = none → 0 < amount →
        CoordinatorCollectionLedger.sourceRound t < l0.freezeAt →
        raw = some (arm, amount) → ledgerStarted.rawBuffer arm t = some amount) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [l0, t, e, raw] using hstartSuccess
    · simpa [l0, t, e, raw] using hstartCandidate
    · intro a
      let Da := cells.map fun c =>
        (c.enabled, RecordedQueueRun.quantizedArrival qpar c a.val)
      let Va := QueueReplay.replay (4 * rate.n) (0, 0) Da
      have hqueue := hprefixQueue a
      have hqueueValues : (r.complementScores a, q.queue a) = Va := by
        have htake : cells.take k = cells := by
          simp [hcellsLength]
        have hqueueList : (r.complementScores a, q.queue a) =
            QueueReplay.replay (4 * rate.n) (0, 0)
              ((cells.take k).map (fun c =>
                (c.enabled, RecordedQueueRun.quantizedArrival qpar c a.val))) := by
          simpa [cells, qpar] using hqueue.2.2.1
        rw [htake] at hqueueList
        simpa [Va, Da] using hqueueList
      have hscore : r.complementScores a = Va.1 := congrArg Prod.fst hqueueValues
      have hqueueVal : q.queue a = Va.2 := congrArg Prod.snd hqueueValues
      have hcutoff : l0.cutoffRegisters a.val =
          some ⟨Va.1, Va.2, q.previousService a⟩ := by
        simp [l0, ReferenceActivePhysicalStep.sharedLedger, hledger,
          CoordinatorStartRoundCutoffDispatch.collectionStartLedger,
          CoordinatorStartRoundCutoffDispatch.outsideRegisters,
          CanonicalFastSampling.fastArmFinset, ReferenceActivePhysicalStep.liveInput,
          ReferenceActivePhysicalStep.liveOwnedAt, ReferenceActivePhysicalStep.liveRegistersAt,
          hscore, hqueueVal]
      have hcurrent : l0.currentRegisters a.val = some ⟨Va.2, q.previousService a⟩ := by
        simp [l0, ReferenceActivePhysicalStep.sharedLedger, hledger,
          CoordinatorStartRoundCutoffDispatch.collectionStartLedger,
          CoordinatorStartRoundCutoffDispatch.outsideRegisters,
          ReferenceActivePhysicalStep.liveInput, ReferenceActivePhysicalStep.liveOwnedAt,
          ReferenceActivePhysicalStep.liveRegistersAt,
          CanonicalFastSampling.fastArmFinset, hscore, hqueueVal]
      have hincrement : l0.increment a.val = 0 := by
        simp [l0, ReferenceActivePhysicalStep.sharedLedger, hledger,
          ReferenceActivePhysicalStep.liveInput, ReferenceActivePhysicalStep.liveRegistersAt,
          CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
      have hsourceRound : CoordinatorCollectionLedger.sourceRound t = u := by
        change cut.input.time.val + 1 = s + k + 1
        rw [htime]
      have hfreeze : l0.freezeAt = r.gridBoundary := by
        simp [l0, ReferenceActivePhysicalStep.sharedLedger, hledger,
          ReferenceActivePhysicalStep.liveInput, ReferenceActivePhysicalStep.liveRegistersAt,
          ReferenceActivePhysicalStep.liveOwnedAt,
          CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
      have henabledFreeze : e = decide
          (CoordinatorCollectionLedger.sourceRound t < l0.freezeAt) := by
        rw [hsourceRound, hfreeze]
        exact hgridEnable
      have hlocalQueue : CoordinatorCollectionLedger.localQueueRecord l0 t e raw a.val =
          (e, RecordedQueueRun.quantizedArrival qpar c_u a.val) := by
        have hcondition : u < r.gridBoundary ↔ e = true := by
          change u < r.gridBoundary ↔
            ReferenceActivePhysicalStep.collectionEnabled l0 t = true
          have hgridEnable' : ReferenceActivePhysicalStep.collectionEnabled l0 t =
              decide (u < r.gridBoundary) := by
            simpa [e] using hgridEnable
          rw [hgridEnable']
          simp
        have harrival : CoordinatorCollectionLedger.localArrival raw a.val =
            RecordedQueueRun.quantizedArrival qpar c_u a.val := by
          simpa [raw, qpar, c_u] using hlocalArrival a.val
        unfold CoordinatorCollectionLedger.localQueueRecord
        rw [hsourceRound, hfreeze]
        cases he : e with
        | false =>
            have hnlt : ¬ u < r.gridBoundary := by
              intro h
              have ht := hcondition.mp h
              simp [he] at ht
            have hzero := (hdisabled he).2 a.val
            have hz : RecordedQueueRun.quantizedArrival qpar c_u a.val = 0 := by
              simpa [qpar, c_u] using hzero
            simp [hnlt, hz]
        | true =>
            have hlt : u < r.gridBoundary := hcondition.mpr he
            simp [hlt, harrival]
      let Vplus := QueueReplay.transition (4 * rate.n) Va
        (e, RecordedQueueRun.quantizedArrival qpar c_u a.val)
      have hknown := hknownTransition a.val ⟨Va.2, q.previousService a⟩ hcurrent
      have hadd := CollectionKnownQueueContinuation.queueReplay_transition_add_score
        (4 * rate.n) Va.1 Va.2 (e, RecordedQueueRun.quantizedArrival qpar c_u a.val)
      have htransitionQueue :
          (QueueReplay.transition (4 * rate.n) (0, Va.2)
            (e, RecordedQueueRun.quantizedArrival qpar c_u a.val)).2 = Vplus.2 := by
        simp only [Vplus] at hadd ⊢
        rw [hadd]
      have htransitionScore :
          (QueueReplay.transition (4 * rate.n) (0, Va.2)
            (e, RecordedQueueRun.quantizedArrival qpar c_u a.val)).1 = Vplus.1 - Va.1 := by
        simp only [Vplus] at hadd ⊢
        rw [hadd]
        omega
      have hknownCurrent : ledgerStarted.currentRegisters a.val =
          some ⟨Vplus.2, Vplus.1 - Va.1⟩ := by
        calc
          ledgerStarted.currentRegisters a.val =
              some ⟨(QueueReplay.transition (4 * rate.n) (0, Va.2)
                (e, RecordedQueueRun.quantizedArrival qpar c_u a.val)).2,
                (QueueReplay.transition (4 * rate.n) (0, Va.2)
                  (e, RecordedQueueRun.quantizedArrival qpar c_u a.val)).1⟩ := by
                change ledgerStarted.currentRegisters a.val = some ⟨
                  (QueueReplay.transition (4 * rate.n) (0, Va.2)
                    (CoordinatorCollectionLedger.localQueueRecord l0 t e raw a.val)).2,
                  (QueueReplay.transition (4 * rate.n) (0, Va.2)
                    (CoordinatorCollectionLedger.localQueueRecord l0 t e raw a.val)).1⟩ at hknown
                rw [hlocalQueue] at hknown
                exact hknown
          _ = some ⟨Vplus.2, Vplus.1 - Va.1⟩ := by
                rw [htransitionQueue, htransitionScore]
      have hgamma : ledgerStarted.gammaLoc a.val = Vplus.1 - Va.1 := by
        rw [hstartCandidate]
        change (CoordinatorCollectionLedger.startRoundCandidate l0 t e raw).gammaLoc a.val = _
        dsimp only [CoordinatorCollectionLedger.startRoundCandidate]
        rw [hcurrent]
        dsimp only
        rw [hlocalQueue]
        exact htransitionScore
      have hstartedIncrement : ledgerStarted.increment a.val = 0 := by
        rw [hstartCandidate]
        change l0.increment a.val = 0
        exact hincrement
      have hreplayExtension : QueueReplay.replay (4 * rate.n) (0, 0)
          ((cells ++ [c_u]).map fun c =>
            (c.enabled, RecordedQueueRun.quantizedArrival qpar c a.val)) = Vplus := by
        rw [List.map_append, List.map_singleton, QueueReplay.replay_append]
        rfl
      have henabledZero : e = true → RecordedQueueRun.quantizedArrival qpar c_u a.val = 0 →
          Vplus = (Va.1 + min (4 * rate.n) Va.2, Va.2 - min (4 * rate.n) Va.2) := by
        intro he hz
        change QueueReplay.transition (4 * rate.n) Va
          (e, RecordedQueueRun.quantizedArrival qpar c_u a.val) = _
        rw [he, hz]
        exact QueueReplay.transition_enabled_zero_arrival (4 * rate.n) Va.1 Va.2
      have hdisabledQueue : e = false → Vplus = Va ∧ ledgerStarted.gammaLoc a.val = 0 ∧
          ledgerStarted.currentRegisters a.val = some ⟨Va.2, 0⟩ ∧
          ledgerStarted.cutoffRegisters a.val = l0.cutoffRegisters a.val := by
        intro he
        have hzero : RecordedQueueRun.quantizedArrival qpar c_u a.val = 0 := by
          simpa [qpar, c_u] using (hdisabled he).2 a.val
        constructor
        · simp [Vplus, QueueReplay.transition, he]
        constructor
        · have hgammaZero : Vplus.1 - Va.1 = 0 := by
            simp [Vplus, QueueReplay.transition, he]
          exact hgamma.trans hgammaZero
        · constructor
          · rw [hknownCurrent]
            simp [Vplus, QueueReplay.transition, he]
          · rw [hstartCandidate]
            rfl
      exact ⟨hlocalQueue, by simpa [Va, Da] using hcutoff, hcurrent,
        hincrement, hknownCurrent, hgamma, hstartedIncrement, hreplayExtension,
        henabledZero, hdisabledQueue⟩
    · intro arm hunknown
      have hcurrentUnknown : l0.currentRegisters arm = none := by
        simpa [l0, ReferenceActivePhysicalStep.sharedLedger, hledger,
          ReferenceActivePhysicalStep.liveInput, ReferenceActivePhysicalStep.liveOwnedAt,
          ReferenceActivePhysicalStep.liveRegistersAt,
          CoordinatorStartRoundCutoffDispatch.collectionStartLedger] using hunknown
      have hstage := hunknownStageOne arm hcurrentUnknown
      have hinc : ledgerStarted.increment arm = 0 := by
        rw [hstartCandidate]
        change l0.increment arm = 0
        simp [l0, ReferenceActivePhysicalStep.sharedLedger, hledger,
          ReferenceActivePhysicalStep.liveInput, ReferenceActivePhysicalStep.liveRegistersAt,
          CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
      exact ⟨hcurrentUnknown, hstage.1, hstage.2, hinc⟩
    · intro arm amount hcurrent hamount hbefore hraw
      exact hrawArrival arm amount hcurrent hamount hbefore (by simpa [raw] using hraw)
  rcases hserviceFacts with ⟨hstartSuccess, hstartCandidate, hknownAll, hunknownAll, hrawAll⟩
  have hslowUnknown : ∀ arm : Fin p.K, arm ∈ P.slowSet.val →
      l0.cutoffRegisters arm = none := by
    intro arm hslow
    simp [l0, ReferenceActivePhysicalStep.sharedLedger, hledger,
      CoordinatorStartRoundCutoffDispatch.collectionStartLedger,
      CoordinatorStartRoundCutoffDispatch.outsideRegisters,
      ReferenceActivePhysicalStep.liveInput, ReferenceActivePhysicalStep.liveRegistersAt,
      ReferenceActivePhysicalStep.liveOwnedAt, CanonicalFastSampling.fastArmFinset,
      P, hslow]
  have hnextConfiguration : cut.output.next.coordinator = cut.output.coordinator.configuration := by
    rw [cut.output_eq]
    rfl
  have hnextBank : cut.output.next.upDecoderBank = cut.output.coordinator.upDecoderBank := by
    rw [cut.output_eq]
    rfl
  refine ⟨cut, suffix, r, q, base, dispatched, hstart, ledger, hinit, hledger,
    hdomain, hclock, hpending, hnoAssignment, selected, out, hCore, hsplit,
    hboundarySuccessor, htime, hrows, hselectedRow, hrewards, hsigma, hnPrefix, hbaseZero,
    hstate, hbranch, hu, huT, huGrid, hledgerCut, hkpos, hpayloads, ?_⟩
  refine ⟨henabled, hmap, hreward, hrate, hgridEnable, hrun, hrecording,
    hrawNone, hrawDiagnostic, hzeroReward, (fun h => hnoData (Or.inl h)),
    hlocalArrival, hphysical, hdisabled,
    hgrid, hlength, hslowUnknown, ?_⟩
  refine ⟨ledgerStarted, hstartSuccess, hstartCandidate, hknownAll, hunknownAll, hrawAll, ?_⟩
  refine ⟨inputReceiver, diagnosticReceiver, hinputReceiverEq, hinputLedger, hinputDomain,
    hinputCheck, hrawParsedNone, hfilterNone, hparseNone, hreceiveRejected,
    hreceiveDiagnostic, hdiagnosticInput, hdiagnosticRaw, hdiagnosticParsed,
    hdiagnosticExpected, hdiagnosticDecoder, hlocallyAccepted, hrawMatches,
    hwrongUnique, hbankFrame, hbankAfterEq, hcompleted, hpendingDecoder, ?_⟩
  refine ⟨finished, hfinishSuccess, hfinishedCandidate, ?_, ?_, ?_, hfinishConfiguration,
    hnextConfiguration.trans hfinishConfiguration, hnextBank.trans hfinishBank,
    hfinishBank, hfinishFailure, hfinishRecording, hfinishUp⟩
  · rw [hfinishedCandidate]
    change inputReceiver.ledger.cutoffRegisters = _
    rw [hinputLedger]
    exact hstartedCutoffFrame
  · intro a
    let Da := cells.map fun c =>
      (c.enabled, RecordedQueueRun.quantizedArrival qpar c a.val)
    let Va := QueueReplay.replay (4 * rate.n) (0, 0) Da
    let Vplus := QueueReplay.transition (4 * rate.n) Va
      (e, RecordedQueueRun.quantizedArrival qpar c_u a.val)
    rcases hknownAll a with
      ⟨_, hcutoff, _, _, hknownCurrent, hgamma, hstartedIncrement, _, _, hdisabledKnown⟩
    have hfinishedIncrement : finished.increment a.val = Vplus.1 - Va.1 := by
      rw [hfinishedCandidate]
      change inputReceiver.ledger.increment a.val + inputReceiver.ledger.gammaLoc a.val = _
      rw [hinputLedger, hstartedIncrement, hgamma]
      exact Nat.zero_add _
    have hfinishedCurrent : finished.currentRegisters a.val =
        some ⟨Vplus.2, Vplus.1 - Va.1⟩ := by
      rw [hfinishedCandidate]
      change inputReceiver.ledger.currentRegisters a.val = _
      rw [hinputLedger]
      exact hknownCurrent
    have hcutoffScore :
        ((l0.cutoffRegisters a.val).getD { score := 0, queue := 0, lastService := 0 }).score =
          Va.1 := by
      rw [hcutoff]
      rfl
    refine ⟨hfinishedIncrement, hfinishedCurrent, ?_, ?_⟩
    · rw [hcutoffScore, hfinishedIncrement]
      change Va.1 + (Vplus.1 - Va.1) = Vplus.1
      have htranslation := congrArg Prod.fst
        (CollectionKnownQueueContinuation.queueReplay_transition_add_score
          (4 * rate.n) Va.1 Va.2 (e, RecordedQueueRun.quantizedArrival qpar c_u a.val))
      change Vplus.1 = Va.1 + _ at htranslation
      rw [htranslation, Nat.add_sub_cancel_left]
    · intro he
      have hpreserve : Vplus = Va := (hdisabledKnown he).1
      constructor
      · rw [hfinishedIncrement]
        rw [hpreserve, Nat.sub_self]
      · rw [hfinishedCurrent]
        rw [hpreserve, Nat.sub_self]
  · intro arm hcutoffNone
    rcases hunknownAll arm hcutoffNone with ⟨_, hcurrentNone, hgammaZero, hstartedIncrement⟩
    have hfinishedIncrement : finished.increment arm = 0 := by
      rw [hfinishedCandidate]
      change inputReceiver.ledger.increment arm + inputReceiver.ledger.gammaLoc arm = _
      rw [hinputLedger, hstartedIncrement, hgammaZero]
    refine ⟨?_, ?_, hfinishedIncrement⟩
    · rw [hfinishedCandidate]
      change inputReceiver.ledger.currentRegisters arm = none
      rw [hinputLedger]
      exact hcurrentNone
    · rw [hfinishedCandidate]
      rfl

end Bandits.Support.ReferenceFirstCutoffKnownNumericalState

end
