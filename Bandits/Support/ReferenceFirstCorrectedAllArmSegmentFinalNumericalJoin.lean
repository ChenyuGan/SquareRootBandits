/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedAcceptedUpSegmentNumericalJoin
public import Bandits.Support.ReferenceFirstCorrectedReplacementCollectionBoundaryHistory
public import Bandits.Support.ReferenceFirstCollectionCorrectedOutsideCutoffNumericalJoin

import Lean.Elab.Tactic.Omega

/-!
# All-arm numerical values at the actual first corrected collection endpoint

Source evidence: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-174`.

The original corrected-cell execution supplies the birth, LIVE prefix and
cutoff segment. Empty pending is a local implication at its final ledger.
Outside and assigned arms retain their separate literal replay words, while
both numerical conclusions concern this same final ledger. The actual
later-choice boundary supplies emptiness; no next assignment is constructed.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstCorrectedAllArmSegmentFinalNumericalJoin

open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceCollectionSegmentExtraction

variable {p : ConstructorDimensions.Parameters}

/-- On a nonempty physical word, the retained incoming last service is
replaced by the final round's score difference, even on a disabled round. -/
private theorem replayLastService_eq_difference
    (cap : ℕ) (initial : ℕ × ℕ) (retained : ℕ) (H : List (Bool × ℕ)) (hne : H ≠ []) :
    CollectionKnownQueueContinuation.replayLastService cap initial retained H =
      (QueueReplay.replay cap initial H).1 -
        (QueueReplay.replay cap initial (H.take (H.length - 1))).1 := by
  have hfull : QueueReplay.replay cap initial H =
      QueueReplay.transition cap (QueueReplay.replay cap initial (H.take (H.length - 1)))
        (H.getLast hne) := by
    calc
      QueueReplay.replay cap initial H = QueueReplay.replay cap initial
          (H.take (H.length - 1) ++ [H.getLast hne]) :=
        congrArg (QueueReplay.replay cap initial) (List.take_append_getLast H hne).symm
      _ = _ := by rw [QueueReplay.replay_append]; rfl
  rw [CollectionKnownQueueContinuation.replayLastService, List.getLast?_eq_some_getLast hne,
    List.dropLast_eq_take, hfull]

/-- The actual corrected-cell cutoff segment has all-arm numerical values at
its own final ledger whenever its pending set is empty. -/
theorem firstCell_all_arm_segment_final_numerical_values
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
    ∃ (L : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K)
      (birth : RoundRecord (p := p) (rate := rate)),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell rate rewards C_star C_h t z = some c ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
      L.length = b ∧ b = t.val - s ∧ s + b = t.val ∧ c.enabled = true ∧
      R[b]? = some birth ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some birth ∧
      birth.input.time = t ∧ birth.input.rows = z.1.2 ∧
      birth.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      birth.input.rewards = rewards ∧
      (match birth.output.preparation.coordinator with
      | .collection _ _ _ _
          (.laterChosen _ _ started _ instruction _ output _ clockData installed _) =>
        instruction.time = t ∧ instruction.kind = .corrected ∧
        installed = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
        installed.registers.payload = output.payload ∧ installed.registers.payload.sigma = t ∧
        installed.assignmentVector = output.assignmentVector ∧
        output.assignmentVector = LaterAssignmentStartOperation.ownAssignmentVector birth.input.row t ∧
        installed.reconstruction = output.reconstruction ∧
        (∀ a : Fin p.K,
          AssignmentScoreReconstruction.sourceScore output.reconstruction a =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).1 ∧
          AssignmentScoreReconstruction.initialQueue output.reconstruction a =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).2 ∧
          (output.reconstruction.registers.current a).lastService =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).1 -
            (UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (L.take (L.length - 1)) (L.take (L.length - 1)).length a).1 ∧
          installed.registers.payload.queues a =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).2) ∧
        (∀ i : Fin (p.m - 1),
          let a := installed.registers.payload.assignment.assigned i
          installed.retainedBaseScore i =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).1 ∧
          (installed.registers.payload.downRecord i).val.q =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).2) ∧
        (∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
          (installed.registers.complementScores j, installed.ownedRegisters.queue j) =
            UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length j.val ∧
          installed.ownedRegisters.previousService j =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length j.val).1 -
            (UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (L.take (L.length - 1)) (L.take (L.length - 1)).length j.val).1) ∧
        c.rate = installed.registers.payload.rate ∧
        c.reward = (fun a => ((rewards t a).val : ℝ) / (D p : ℝ)) ∧
        birth.output.coordinator = ReferenceActivePhysicalStep.livePostChoice
          birth.output.preparation installed.registers installed.ownedRegisters
          installed.retainedBaseScore started ∧
        birth.output.next.coordinator = birth.output.coordinator.configuration ∧
        (match birth.output.next.coordinator with
        | .live rout qout beta =>
          rout.payload = installed.registers.payload ∧ beta = installed.retainedBaseScore ∧
          ∃ (recording : CoordinatorRecordingOperation.Output p)
            (serviced : CoordinatorLiveServiceFinish.ServicedRegisters installed.registers installed.ownedRegisters)
            (pending : Finset (Fin (p.m - 1))) (finished : CoordinatorPhaseClock.FinishRoundResult p),
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation installed.registers started) =
                some recording ∧
            CoordinatorLiveServiceFinish.servicePass installed.registers installed.ownedRegisters recording = .ok serviced ∧
            CoordinatorLocalArmChoice.confirmationUpdate installed.registers.payload started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              birth.input.time birth.input.row birth.output.preparation.coordinatorObservation = some pending ∧
            CoordinatorPhaseClock.finishRound p rate.eta.val birth.input.time started.clock pending birth.input.row =
              .ok finished ∧
            birth.output.coordinator =
              ⟨.live {
                  payload := installed.registers.payload
                  priorClock := finished.clock
                  pendingAtChoice := finished.pending
                  time := birth.input.time
                  gridBoundary := finished.clock.g
                  complementScores := serviced.score }
                { queue := serviced.queue, previousService := serviced.previousService } installed.retainedBaseScore,
                birth.input.state.upDecoderBank, none, some recording, none⟩ ∧
            ∀ j : CanonicalFastSampling.FastArm rout.payload.slowSet,
              (rout.complementScores j, qout.queue j) =
                UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                  (L ++ [c]) (L ++ [c]).length j.val ∧
              qout.previousService j =
                (UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                  (L ++ [c]) (L ++ [c]).length j.val).1 -
                (UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length j.val).1
        | .dagger =>
          (CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation installed.registers started) = none ∧
            birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
              birth.input.state.upDecoderBank (.live .recorderRejected) none none) ∨
          (∃ recording reason,
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation installed.registers started) = some recording ∧
            CoordinatorLiveServiceFinish.servicePass installed.registers installed.ownedRegisters recording = .error reason ∧
            birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
              birth.input.state.upDecoderBank (.live reason) (some recording) none) ∨
          (∃ recording serviced,
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation installed.registers started) = some recording ∧
            CoordinatorLiveServiceFinish.servicePass installed.registers installed.ownedRegisters recording = .ok serviced ∧
            CoordinatorLocalArmChoice.confirmationUpdate installed.registers.payload started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              birth.input.time birth.input.row birth.output.preparation.coordinatorObservation = none ∧
            birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
              birth.input.state.upDecoderBank (.live .confirmationRejected) (some recording) none) ∨
          (∃ recording serviced pending reason,
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation installed.registers started) = some recording ∧
            CoordinatorLiveServiceFinish.servicePass installed.registers installed.ownedRegisters recording = .ok serviced ∧
            CoordinatorLocalArmChoice.confirmationUpdate installed.registers.payload started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              birth.input.time birth.input.row birth.output.preparation.coordinatorObservation = some pending ∧
            CoordinatorPhaseClock.finishRound p rate.eta.val birth.input.time started.clock pending birth.input.row =
              .error reason ∧
            birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
              birth.input.state.upDecoderBank
                (.live (CoordinatorLiveServiceFinish.finishFailureCode reason)) (some recording) none)
        | _ => False)
      | _ => False) ∧
      (∀ hq : t.val + 1 < p.T,
        ∃ next : RoundRecord (p := p) (rate := rate),
          R[b + 1]? = some next ∧
          ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h ⟨t.val + 1, hq⟩ z = some next ∧
          next.input.time = ⟨t.val + 1, hq⟩ ∧ next.input.state = birth.output.next ∧
          next.input.rows = z.1.2 ∧
          next.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
          next.input.rewards = rewards) ∧
      (birth.output.next.coordinator = .dagger ∨
        ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ),
          birth.output.next.coordinator = .live r q base) ∧
    ∀ (rout : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (qout : CoordinatorLiveServiceFinish.OwnedRegisters rout) (beta : Fin (p.m - 1) → ℕ),
      birth.output.next.coordinator = .live rout qout beta →
      rout.payload.sigma = t ∧
      (∀ a : Fin p.K, (∃ j : CanonicalFastSampling.FastArm rout.payload.slowSet, j.val = a) ∨
        ∃ i : Fin (p.m - 1), rout.payload.assignment.assigned i = a) ∧
    ∀ _hq : t.val + 1 < p.T,
    ∃ (next : RoundRecord (p := p) (rate := rate)) (hk : b + 1 < R.length)
      (hstate : R[b + 1].input.state.coordinator = .live rout qout beta)
      (hlater : s < rout.payload.sigma.val),
      R[b + 1]? = some next ∧ next.input.state = birth.output.next ∧
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix rate rewards C_star C_h z (b + 1)
    let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
      rewards C_star C_h z ⟨b + 1, hk⟩ rout qout beta hstate hlater
    let e := b + 1 + W.length
    let A := (L ++ [c]) ++ B;
      B.length = W.length ∧ e ≤ R.length ∧ t.val + 1 + W.length ≤ p.T ∧
      W.map (fun r => r.input.time.val) = List.range' (t.val + 1) W.length ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (t.val + 1 + W.length) z = some A ∧
      A.length = e ∧ s + e = t.val + 1 + W.length ∧
    ∃ (rE : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (qE : CoordinatorLiveServiceFinish.OwnedRegisters rE) (_hp : rE.payload = rout.payload),
      (∀ hpos : 0 < W.length,
        (W[W.length - 1]'(by omega)).output.next.coordinator = .live rE qE beta) ∧
      (∀ he : e < R.length, R[e].input.state.coordinator = .live rE qE beta) ∧
      (e = R.length ∨
      ∃ (he : e < R.length)
        (chosen : CoordinatorRoundDispatch.LiveOutcome
          (liveInput (p := p) (rate := rate) (R[e]'he).input rE qE beta)),
        chosen = CoordinatorRoundDispatch.dispatchLive
          (liveInput (p := p) (rate := rate) (R[e]'he).input rE qE beta) ∧
        R[e].output.preparation.coordinator = .live rE qE beta chosen ∧
      match (motive := ∀ _ : CoordinatorRoundDispatch.LiveOutcome
        (liveInput (p := p) (rate := rate) (R[e]'he).input rE qE beta), Prop) chosen with
      | .cutoffChosen _dispatched _ ledger _ _ _ _ _ _ _ =>
        let tau := R[e].input.time
        let uc := tau.val + 1
        let l0 := sharedLedger (rate := rate) ledger
        tau.val = s + e ∧
        uc = FollowerCutoffScan.firstCutoff p rate.eta.val rout.payload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) ∧
        ∃ (seg : Segment rate) (I : Initializer p),
          segmentAt R e = some seg ∧ seg.entry = R[e] ∧
          seg.context.payload = rout.payload ∧ seg.context.preLedger = l0 ∧
          seg.context.initializer = some I ∧
          I = cutoffInitializer (liveRegistersAt rE tau) (liveOwnedAt rE qE tau) beta tau ∧
          I.checkedStart rate = CoordinatorCollectionLedger.Checked.success l0 ∧
          I.assignment.arm = rout.payload.assignment.assigned ∧ I.sigma = t.val + 1 ∧
          I.cutoff = uc ∧ I.freezeAt = rE.gridBoundary ∧ I.base = beta ∧
          (∃ tail, seg.records = R[e] :: tail) ∧
          seg.records ++ seg.remaining = R.drop e ∧ seg.exit = exitOf seg.remaining ∧
          CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
            (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
            I.assignment I.sigma I.cutoff I.freezeAt I.base I.outside seg.inputs =
              CoordinatorCollectionLedger.Checked.success
                (CollectionCheckedExecution.Execution.mk l0 seg.accepted seg.final) ∧
          seg.inputs.map (fun (input : CollectionCheckedExecution.RoundInput
            (p := p) (eta := rate.eta.val)) => input.round.val) =
              List.range' tau.val seg.records.length ∧
          seg.inputs.length = seg.records.length ∧ 0 < seg.records.length ∧
          (∀ r ∈ R, r.input.rows = z.1.2 ∧
            r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
            r.input.rewards = rewards) ∧
          (∀ r ∈ seg.records, ∀ c, choice r.input = some c → c.payload = seg.context.payload) ∧
          (∃ during, seg.records = seg.entry :: during ∧
            R.take (e + seg.records.length) = R.take e ++ seg.records ∧
            ReferenceCollectionPhaseHistory.laterChosen seg.entry.input = false ∧
            (∀ r ∈ during, ReferenceCollectionPhaseHistory.cutoffChosen r.input = false ∧
              ReferenceCollectionPhaseHistory.laterChosen r.input = false) ∧
            seg.final.pending = Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels seg.records).toFinset ∧
            (ReferenceCollectionPhaseHistory.acceptedLabels seg.records).Nodup) ∧
        ∃ c_cut : RecordedQueueRun.RoundInput p.K,
          ReferenceFirstCollectionCurrentRetainedGate.cell0 rate R[e] = some c_cut ∧
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
            rate rewards C_star C_h (tau.val + 1) z = some (A ++ [c_cut]) ∧
        ∃ saved, (endpointState seg.entry.input.state seg.records).coordinator =
          CoordinatorConfiguration.collection seg.context.payload seg.final saved ∧
          seg.final.cursor = s + (e + seg.records.length) + 1 ∧
          e + seg.records.length ≤ R.length ∧
          (seg.final.pending = ∅ → ∀ i : Fin (p.m - 1),
            ∃ (k : Fin R.length) (U : ReferenceCollectionPhaseHistory.UpRecord p rate),
              e ≤ k.val ∧ k.val < e + seg.records.length ∧ R[k.val] ∈ seg.records ∧
              ReferenceCollectionPhaseHistory.AcceptedUp R[k.val].input i U ∧
              U.val.sigma = seg.final.sigma) ∧
          (e + seg.records.length = R.length ∨
            ∃ hv : e + seg.records.length < R.length,
              R[e + seg.records.length].input.state = endpointState seg.entry.input.state seg.records ∧
              R[e + seg.records.length].input.state.coordinator =
                CoordinatorConfiguration.collection seg.context.payload seg.final saved ∧
              R[e + seg.records.length].input.time.val = s + (e + seg.records.length) ∧
              R.drop (e + seg.records.length) = seg.remaining ∧
              (ReferenceCollectionPhaseHistory.laterChosen R[e + seg.records.length].input = false ∨
                ReferenceCollectionPhaseHistory.laterChosen R[e + seg.records.length].input = true ∧
                seg.final.pending = ∅ ∧ ∀ i : Fin (p.m - 1),
                  ∃ (k : Fin R.length) (U : ReferenceCollectionPhaseHistory.UpRecord p rate),
                    e ≤ k.val ∧ k.val < e + seg.records.length ∧ R[k.val] ∈ seg.records ∧
                    ReferenceCollectionPhaseHistory.AcceptedUp R[k.val].input i U ∧
                    U.val.sigma = seg.final.sigma)) ∧
          (seg.final.pending = ∅ → ∀ a : Fin p.K,
            (∃ j : CanonicalFastSampling.FastArm rout.payload.slowSet, j.val = a ∧
              let Qp := ReferenceFirstLaunchNumericalCell.queueParameters rate
              let E := A.map (fun cell => UnstoppedRecordedQueueComparison.unstoppedRecord Qp cell a)
              let Eprev := (A.take (A.length - 1)).map
                (fun cell => UnstoppedRecordedQueueComparison.unstoppedRecord Qp cell a)
              let H := CollectionKnownQueueContinuation.inputQueueRecords l0 a seg.inputs
              let V := QueueReplay.replay (4 * rate.n) (0, 0) E
              let Vprev := QueueReplay.replay (4 * rate.n) (0, 0) Eprev
              let Q := QueueReplay.replay (4 * rate.n) (0, 0) (E ++ H)
              let last := CollectionKnownQueueContinuation.replayLastService
                (4 * rate.n) (0, V.2) (V.1 - Vprev.1) H
              seg.final.cutoffRegisters a =
                some (CoordinatorCollectionLedger.CutoffRegister.mk V.1 V.2 (V.1 - Vprev.1)) ∧
              seg.final.currentRegisters a = some (CoordinatorCollectionLedger.CurrentRegister.mk Q.2 last) ∧
              V.1 + seg.final.increment a = Q.1 ∧
              H.length = seg.inputs.length ∧ H.length = seg.records.length ∧ 0 < H.length ∧
              last = (QueueReplay.replay (4 * rate.n) (0, V.2) H).1 -
                (QueueReplay.replay (4 * rate.n) (0, V.2) (H.take (H.length - 1))).1) ∨
            (∃ i : Fin (p.m - 1), rout.payload.assignment.assigned i = a ∧
              ∃ (k : Fin R.length) (U : ReferenceCollectionPhaseHistory.UpRecord p rate),
              e ≤ k.val ∧ k.val < e + seg.records.length ∧ R[k.val] ∈ seg.records ∧
              ReferenceCollectionPhaseHistory.AcceptedUp R[k.val].input i U ∧
              U.val.sigma = seg.final.sigma ∧
              ∃ c : Choice rate, choice R[k.val].input = some c ∧ c.payload = seg.context.payload ∧
              c.payload.assignment.assigned i = a ∧
              ∃ IA : Initializer p, seg.context.initializer = some IA ∧
                IA = I ∧ IA.checkedStart rate = CoordinatorCollectionLedger.Checked.success seg.context.preLedger ∧
              let P := c.payload
              let a := P.assignment.assigned i
              let sigma := P.sigma.val + 1
              let uc := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
                (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                  (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)))
              let N := uc - sigma
              let L := (R.drop b).take N
              N = e - b ∧
              L.map (fun (r : RoundRecord (p := p) (rate := rate)) => r.input.time.val + 1) =
                List.range' sigma N ∧
              ∃ (hLlen : L.length = N)
                (v : ∀ n : Fin N, Selection (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).input)
                (ho : ∀ n : Fin N, ReferenceLaterLiveNumericalReadout.preparedOrdinary
                  (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm))),
                (∀ n : Fin N, (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).output.preparation.coordinator.selection =
                  some (v n) ∧ (v n).view.payload = P ∧ (v n).view.cutoff = none ∧
                  CoordinatorLocalArmChoice.assignmentIsLive (v n).view.payload (v n).view.cutoff
                    (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).input.time) ∧
              (∀ (n : Fin N) (f : Fin (p.m - 1)), (ReferenceFollowerFixedReply.actualChoice
                  (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) f).configuration =
                DeclaredFollowerLocalRound.LocalConfiguration.ordinary
                  (ReferenceLaterLiveNumericalReadout.preparedStates
                    (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (ho n) f)
                  (ReferenceLaterLiveNumericalReadout.preparedMemories
                    (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (ho n) f)) ∧
              let Cells : Fin N → RecordedQueueRun.RoundInput p.K := fun n =>
                ReferenceFirstWindowNumericalStream.sourceCell
                  (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (v n).view.payload
                  (v n).view.pendingAtChoice
                  (ReferenceLaterLiveNumericalReadout.preparedStates
                    (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (ho n))
                  (v n).view.complementWeights (v n).view.cutoff
                  (ReferenceLaterLiveNumericalReadout.selection_choiceValid (v n))
              let A := List.ofFn (fun n => ((Cells n).enabled,
                RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) (Cells n) a))
              ∃ hc : (ReferenceInitializationRun.output
                (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true,
              ∃ hs : ReferenceFirstCollectionReadyStream.startTime (rate := rate) z rewards C_star C_h + (p.T - s) ≤ p.T,
              ∃ hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
                (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
                  z rewards C_star C_h hc (p.T - s) hs).records).length < p.T - s,
              ∃ f : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
                (rate := rate) z rewards C_star C_h (p.T - s) hc hs hshort,
              ∃ (head0 : Choice rate) (_valid0 : CoordinatorRecorderComplementBridge.LocalInputsValid
                (collectionRecordingInput f.stream.cutoff.cut.output.preparation head0.payload head0.started head0.weights))
                (D0 : List (RecordedQueueRun.RoundInput p.K)),
                choice f.stream.cutoff.cut.input = some head0 ∧ head0.payload = f.stream.payload ∧
                ∃ hDlen : D0.length = f.stream.ell,
                (∀ n : Fin f.stream.ell,
                  let r := f.stream.window[n.val]'(lt_of_lt_of_le n.isLt f.stream.withinWindow)
                  let cell := D0[n.val]'(by rw [hDlen]; exact n.isLt)
                  ∃ (call : Choice rate) (validCall : CoordinatorRecorderComplementBridge.LocalInputsValid
                    (collectionRecordingInput r.output.preparation call.payload call.started call.weights)),
                    choice r.input = some call ∧ call.payload = f.stream.payload ∧
                    cell = ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate r call rewards validCall ∧
                    r.input.rows = z.1.2 ∧ r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
                    r.input.rewards = rewards ∧
                    r.input.time.val = ReferenceFirstCollectionReadyStream.startTime (rate := rate) z rewards C_star C_h +
                      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
                        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
                          z rewards C_star C_h hc (p.T - s) hs).records).length + n.val) ∧
                f.stream.ell = (ReferenceCollectionPhaseHistory.collectionWindow R
                  (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length).length ∧
              let Cells0 := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
                rate z rewards C_star C_h hc (p.T - s) hs
              let E0 := ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells0 ++ D0)
              let E := E0 ++ A
              let H := seg.records.map (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a)
              let V := QueueReplay.replay (4 * rate.n) (0, 0) E
              let Vprev := QueueReplay.replay (4 * rate.n) (0, 0) (E0 ++ A.take (N - 1))
              let Q := QueueReplay.replay (4 * rate.n) (0, 0) (E ++ H)
              let Qprev := QueueReplay.replay (4 * rate.n) (0, 0)
                (E ++ (seg.records.take (seg.records.length - 1)).map
                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a))
              seg.final.cutoffRegisters a =
                some (CoordinatorCollectionLedger.CutoffRegister.mk V.1 V.2 (V.1 - Vprev.1)) ∧
              seg.final.currentRegisters a =
                some (CoordinatorCollectionLedger.CurrentRegister.mk Q.2 (Q.1 - Qprev.1)) ∧
              V.1 + seg.final.increment a = Q.1))
      | _ => False) := by
  classical
  intro R s b
  obtain ⟨L, c, birth, hL, hc, hprefix, hLb, hbsub, htime, henabled,
    hb, har, ht, hrows, hselected, hrewards, hcurrent, hnext, hcont⟩ :=
    ReferenceFirstCollectionCorrectedOutsideCutoffNumericalJoin.firstCell_outside_cutoff_numerical_join
      rate rewards C_star C_h u t z hz
  have hmode : birth.output.next.coordinator = .dagger ∨
      ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ),
        birth.output.next.coordinator = .live r q base := by
    cases hconfig : birth.output.next.coordinator with
    | dagger => exact Or.inl rfl
    | live r q base => exact Or.inr ⟨r, q, base, rfl⟩
    | first | collection _ _ _ =>
      cases hpreparedBirth : birth.output.preparation.coordinator with
      | collection P l clock cutoff outcome =>
        cases outcome <;> simp only [hpreparedBirth, hconfig, and_false] at hcurrent
      | first outcome => simp only [hpreparedBirth] at hcurrent
      | live r q base outcome => simp only [hpreparedBirth] at hcurrent
      | invalidCollectionCutoff => simp only [hpreparedBirth] at hcurrent
      | dagger => simp only [hpreparedBirth] at hcurrent
  refine ⟨L, c, birth, hL, hc, hprefix, hLb, hbsub, htime, henabled, hb, har, ht, hrows, hselected,
    hrewards, hcurrent, hnext, hmode, ?_⟩
  intro rout qout beta hlive
  obtain ⟨hsigma, hcont⟩ := hcont rout qout beta hlive
  refine ⟨hsigma, ?_, ?_⟩
  · intro a
    by_cases ha : a ∈ rout.payload.slowSet.1
    · right
      have hm : a ∈ Finset.univ.image rout.payload.assignment.assigned := by
        rw [rout.payload.assignment_image]
        exact ha
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
      exact ⟨i, hi⟩
    · exact Or.inl ⟨⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩, rfl⟩
  intro hq
  obtain ⟨next, hk, hstate, hlater, hnext, hnextState,
    hBlen, heR, heT, hWtimes, hprefixes, hprefixA, hAlen, hAdate,
    rE, qE, hp, hlastW, hstateE, houtsideE, hexit⟩ := hcont hq
  refine ⟨next, hk, hstate, hlater, hnext, hnextState, hBlen, heR, heT, hWtimes,
    hprefixA, hAlen, hAdate, rE, qE, hp, hlastW, hstateE, ?_⟩
  rcases hexit with hhor | ⟨he, chosen, hchosen, hprepared, hcut⟩
  · exact Or.inl hhor
  refine Or.inr ⟨he, chosen, hchosen, hprepared, ?_⟩
  cases chosen with
  | continuingChosen _ _ _ _ => exact hcut
  | clockFailure _ _ => exact hcut
  | localFailure _ _ _ => exact hcut
  | initializerFailure _ _ _ _ => exact hcut
  | cutoffChosen dispatched hstart ledger hinit hledger hvalid hclock hpending hnone selected =>
    let e := b + 1 + (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b + 1)).length
    let tau := R[e].input.time
    let uc := tau.val + 1
    let l0 := sharedLedger (rate := rate) ledger
    obtain ⟨htau, htau', huc, hscan, seg, I, hseg, hentry, hpay, hpre, hI,
      hIdef, hIchecked, hIarm, hIsigma, hIcutoff, hfreeze, hbase, hrecords,
      hpartition, hexit, hwhole, hcalendar, hcount, hpositive, houtside0, hassigned0,
      ccut, hcell, hreadout, hprefixCut, hcellEnabled, hcellRate, hcellReward,
      recording, started, decoded, bank, lf, clock, hrecording, hrecorder, hstarted,
      hreceive, hdecoded, hfinish, hfinishedClock, hnextCollection, hfailure,
      hbaseScore, hgamma, harrival, hfirstUpdate, houtside⟩ := hcut
    have hne : seg.records ≠ [] := List.length_pos_iff.mp hpositive
    have hcutChosen : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true := by
      rw [hentry]
      change ReferenceCollectionPhaseHistory.cutoffChosen R[e].input = true
      have heq : (prepare R[e].input).coordinator = R[e].output.preparation.coordinator := by
        exact congrArg (fun output => output.preparation.coordinator) (R[e]).output_eq.symm
      change R[e].output.preparation.coordinator = _ at hprepared
      rw [ReferenceCollectionPhaseHistory.cutoffChosen, heq, hprepared]
    obtain ⟨hle, hsourceRows, hpayAll, saved, hend, hcursor,
      during, hduringRecords, hprefixHistory, hnotlater, hduring, hpending,
      hnodup, hwitnesses, hboundary⟩ :=
      ReferenceFirstCorrectedReplacementCollectionBoundaryHistory.firstCell_collection_boundary_history
        rate rewards C_star C_h u t z hz e seg hseg hne hcutChosen
    refine ⟨htau, hscan, seg, I, hseg, hentry, hpay, hpre, hI, hIdef, hIchecked,
      hIarm, hIsigma, hIcutoff, hfreeze, hbase, hrecords, hpartition, hexit, hwhole, hcalendar, hcount, hpositive,
      hsourceRows, hpayAll,
      ⟨during, hduringRecords, hprefixHistory, hnotlater, hduring, hpending, hnodup⟩,
      ccut, hcell, hprefixCut, saved, hend, hcursor, hle, hwitnesses, hboundary, ?_⟩
    intro hempty a
    by_cases ha : a ∈ rout.payload.slowSet.1
    · right
      have hm : a ∈ Finset.univ.image rout.payload.assignment.assigned := by
        rw [rout.payload.assignment_image]
        exact ha
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
      refine ⟨i, hi, ?_⟩
      obtain ⟨k, U, hek, hkv, hmem, hacc, hUsigma⟩ := hwitnesses hempty i
      refine ⟨k, U, hek, hkv, hmem, hacc, hUsigma, ?_⟩
      -- Both geometric localizers come from this original cutoff branch.
      have hsig : seg.context.payload.sigma.val = s + b := by
        rw [hpay, hsigma]
        exact htime.symm
      have hcutoff : FollowerCutoffScan.firstCutoff p rate.eta.val seg.context.payload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) = s + e + 1 := by
        rw [hpay, ← hscan]
        change tau.val + 1 = s + e + 1
        exact congrArg (fun n : ℕ => n + 1) htau
      obtain ⟨cA, hcA, hpayA, IA, hIA, hcheckedIA, hvalues⟩ :=
        ReferenceFirstCorrectedAcceptedUpSegmentNumericalJoin.firstCell_accepted_up_same_segment_numerical_values
          rewards C_star C_h u t z hz e seg hseg hne hcutChosen k hmem i U hacc hsig hcutoff
      have hIAeq : IA = I := Option.some.inj (hIA.symm.trans hI)
      have harm : cA.payload.assignment.assigned i = a := by rw [hpayA, hpay]; exact hi
      exact ⟨cA, hcA, hpayA, harm, IA, hIA, hIAeq, hcheckedIA, hvalues⟩
    · left
      let j : CanonicalFastSampling.FastArm rout.payload.slowSet :=
        ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩
      refine ⟨j, rfl, ?_⟩
      intro Qp E Eprev H V Vprev Q last
      obtain ⟨hc, hq, hi, _, hf, hHinputs, hHrecords, hpos⟩ := houtside j
      have hcutoff : seg.final.cutoffRegisters a =
          some ⟨V.1, V.2, V.1 - Vprev.1⟩ := by
        simpa only [b, Qp, E, Eprev, V, Vprev, j,
          UnstoppedRecordedQueueComparison.unstoppedReplay, List.take_length,
          ReferenceFirstLaunchNumericalCell.queueParameters] using hc
      -- Compare the literal record maps on these same segment inputs.
      have hcurrent : seg.final.currentRegisters a = some ⟨Q.2, last⟩ := by
        simp only [b, Qp, E, Eprev, H, V, Vprev, Q, last, j,
          UnstoppedRecordedQueueComparison.unstoppedReplay, List.take_length,
          ReferenceFirstLaunchNumericalCell.queueParameters,
          CollectionKnownQueueContinuation.inputQueueRecords,
          CoordinatorCollectionLedger.localQueueRecord, sharedLedger] at hq ⊢
        convert hq using 1
        rfl
      have hincrement : seg.final.increment a =
          (QueueReplay.replay (4 * rate.n) (0, V.2) H).1 := by
        simp only [b, Qp, E, H, V, j,
          UnstoppedRecordedQueueComparison.unstoppedReplay, List.take_length,
          ReferenceFirstLaunchNumericalCell.queueParameters,
          CollectionKnownQueueContinuation.inputQueueRecords,
          CoordinatorCollectionLedger.localQueueRecord, sharedLedger] at hi ⊢
        convert hi using 1
        rfl
      have hfull : Q =
          (V.1 + (QueueReplay.replay (4 * rate.n) (0, V.2) H).1,
            (QueueReplay.replay (4 * rate.n) (0, V.2) H).2) := by
        simp only [b, Qp, E, H, V, Q, j,
          UnstoppedRecordedQueueComparison.unstoppedReplay, List.take_length,
          ReferenceFirstLaunchNumericalCell.queueParameters,
          CollectionKnownQueueContinuation.inputQueueRecords,
          CoordinatorCollectionLedger.localQueueRecord, sharedLedger] at hf ⊢
        convert hf using 1 <;> rfl
      exact ⟨hcutoff, hcurrent, by rw [hincrement, hfull], hHinputs, hHrecords, hpos,
        replayLastService_eq_difference (4 * rate.n) (0, V.2) (V.1 - Vprev.1) H
          (List.length_pos_iff.mp hpos)⟩

end Bandits.Support.ReferenceFirstCorrectedAllArmSegmentFinalNumericalJoin
