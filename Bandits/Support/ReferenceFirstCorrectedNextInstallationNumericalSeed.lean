/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedAllArmSegmentFinalNumericalJoin
public import Bandits.Support.ReferenceCompleteEmptyInstallationNumericalStep

/-!
# The next installation seeded by the actual first corrected collection

Sources: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-174`.

The original corrected-cell execution supplies every boundary and replay word.
Only an actual later-choice branch initializes another assignment. The old
assignment partitions the numerical evidence; the new assignment restricts the
reconstructed all-arm vector. No membership alignment is required. This stops
before recording or service of the new birth row and asserts no calendar law.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstCorrectedNextInstallationNumericalSeed

open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceCollectionSegmentExtraction CoordinatorPhaseClock CoordinatorRoundDispatch
open CoordinatorAssignmentRegisterInstall LaterAssignmentStartOperation

variable {p : ConstructorDimensions.Parameters}

/-- Literal ledger entries and their additive score equation pass through the
successful reconstruction, then restrict to either role in the new assignment.
The premises here are discharged from the original endpoint in the root proof. -/
private theorem installation_arm_values
    {eta : ReferencePrelaunchFollower.LearningRate}
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LocalLedger old} {instruction : AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : SuccessfulStart old ledger instruction row)
    (clockData : LaterStartRoundEvidence output)
    (a : Fin p.K) (V Vprev Q : ℕ × ℕ) (last : ℕ)
    (hcut : ledger.cutoffRegisters a = some
      (CoordinatorCollectionLedger.CutoffRegister.mk V.1 V.2 (V.1 - Vprev.1)))
    (hcur : ledger.currentRegisters a = some
      (CoordinatorCollectionLedger.CurrentRegister.mk Q.2 last))
    (hadd : V.1 + ledger.increment a = Q.1) :
    let installation := installLater output clockData
    output.reconstruction.registers.cutoff a =
      CoordinatorCollectionLedger.CutoffRegister.mk V.1 V.2 (V.1 - Vprev.1) ∧
    output.reconstruction.registers.current a =
      CoordinatorCollectionLedger.CurrentRegister.mk Q.2 last ∧
    AssignmentScoreReconstruction.sourceScore output.reconstruction a = Q.1 ∧
    AssignmentScoreReconstruction.initialQueue output.reconstruction a = Q.2 ∧
    installation.registers.payload.queues a = Q.2 ∧
    (∀ i, installation.registers.payload.assignment.assigned i = a →
      installation.retainedBaseScore i = Q.1 ∧
      (installation.registers.payload.downRecord i).val.q = Q.2) ∧
    (∀ j : CanonicalFastSampling.FastArm installation.registers.payload.slowSet,
      j.val = a → installation.registers.complementScores j = Q.1 ∧
        installation.ownedRegisters.queue j = Q.2 ∧
        installation.ownedRegisters.previousService j = last) := by
  intro installation
  obtain ⟨_, hcutoff, hcurrent, hscore, hqueue, _, _, _, _, _, _⟩ :=
    AssignmentScoreReconstruction.reconstructLaterStart_success_equations
      ledger instruction output.reconstruction output.reconstruction_eq
  have hc : output.reconstruction.registers.cutoff a =
      CoordinatorCollectionLedger.CutoffRegister.mk V.1 V.2 (V.1 - Vprev.1) :=
    Option.some.inj ((hcutoff a).symm.trans hcut)
  have hq : output.reconstruction.registers.current a =
      CoordinatorCollectionLedger.CurrentRegister.mk Q.2 last :=
    Option.some.inj ((hcurrent a).symm.trans hcur)
  have hs : AssignmentScoreReconstruction.sourceScore output.reconstruction a = Q.1 := by
    rw [hscore, hc]
    exact hadd
  have hi : AssignmentScoreReconstruction.initialQueue output.reconstruction a = Q.2 := by
    rw [hqueue, hq]
  have hp : installation.registers.payload.queues a = Q.2 :=
    (later_payload_queue_eq_initial_queue output clockData a).trans hi
  refine ⟨hc, hq, hs, hi, hp, ?_, ?_⟩
  · intro i hai
    constructor
    · change output.payload.assignment.assigned i = a at hai
      exact (later_retained_base_score_eq_source output clockData i).trans (by rw [hai]; exact hs)
    · rw [AssignmentStartPayload.Input.downRecord_initialQueue, hai]
      exact hp
  · intro j hja
    refine ⟨?_, ?_, ?_⟩
    · exact (later_complement_score_eq_source_score output clockData j).trans (by rw [hja]; exact hs)
    · exact (later_owned_queue_eq_initial_queue output clockData j).trans (by rw [hja]; exact hi)
    · exact (later_owned_previous_service_eq_current_register output clockData j).trans
        (by rw [hja, hq])

/-- Initialize the same actual next assignment from the accepted first-corrected
all-arm endpoint. Horizon and actual non-later alternatives remain explicit. -/
theorem firstCell_next_installation_numerical_seed
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
          (∀ (hv : e + seg.records.length < R.length),
            ReferenceCollectionPhaseHistory.laterChosen R[e + seg.records.length].input = true →
            let x := R[e + seg.records.length].input
            ∃ uNext : Fin p.T, uNext.val + 1 = seg.final.cutoff ∧
              let clock := collectionClock seg.context.payload seg.final saved uNext
              let input := collectionInput x seg.context.payload seg.final clock uNext
              ∃ (core : CollectionCoreValid input) (started : StartRoundResult p)
                (hstart : startRound p rate.eta.val x.time input.clock seg.final.pending = .ok started)
                (instruction : AssignmentStartInstruction p)
                (hassignment : started.assignmentStart = some instruction),
                instruction.time = x.time ∧
                instruction.kind =
                  (if x.time.val + 1 < seg.final.freezeAt then .corrected else .renewal) ∧
                let operation := collectionOperationLedger input core.payload_n_eq
                ∃ (consistent : LocalConsistency seg.context.payload operation)
                  (output : SuccessfulStart seg.context.payload operation instruction x.row)
                  (hlocal : output.localConsistency = consistent),
                  laterAssignmentStart seg.context.payload operation instruction x.row consistent =
                    .success output hlocal ∧
                  ∃ (clockData : LaterStartRoundEvidence output)
                    (installation : LaterInstallation output clockData)
                    (selected : ArmSelection installation.registers.payload started instruction.time
                      installation.registers.complementWeights x.row),
                    installation = installLater output clockData ∧ clockData.result = started ∧
                    dispatchCollection input = .laterChosen core consistent started hstart instruction
                      hassignment output hlocal clockData installation selected ∧
                    R[e + seg.records.length].output.preparation.coordinator =
                      .collection seg.context.payload seg.final clock uNext
                        (.laterChosen core consistent started hstart instruction hassignment
                          output hlocal clockData installation selected) ∧
                    installation.registers.payload = output.payload ∧
                    installation.assignmentVector = output.assignmentVector ∧
                    output.assignmentVector = ownAssignmentVector x.row x.time ∧
                    installation.reconstruction = output.reconstruction ∧
                    (instruction.kind = .corrected ↔ x.time.val + 1 < seg.final.freezeAt) ∧
                    (instruction.kind = .renewal ↔ seg.final.freezeAt ≤ x.time.val + 1) ∧
                    (if x.time.val + 1 < seg.final.freezeAt then
                      installation.registers.payload.anchor = seg.context.payload.anchor else
                      installation.registers.payload.anchor =
                        AssignmentScoreReconstruction.currentWeight output.reconstruction) ∧
                    (∀ a, AssignmentScoreReconstruction.currentWeight output.reconstruction a =
                        (1 + 1 / (D p : ℝ)) ^
                          AssignmentScoreReconstruction.sourceScore output.reconstruction a ∧
                      AssignmentScoreReconstruction.cutoffWeight output.reconstruction a =
                        (1 + 1 / (D p : ℝ)) ^
                          (output.reconstruction.registers.cutoff a).score) ∧
                    (instruction.kind = .corrected →
                      AssignmentScoreReconstruction.previousScore output.reconstruction =
                        some (fun a => (output.reconstruction.registers.cutoff a).score -
                          (output.reconstruction.registers.cutoff a).lastService) ∧
                      ∃ weights, AssignmentScoreReconstruction.previousWeight output.reconstruction =
                        some weights ∧ ∀ a, weights a = (1 + 1 / (D p : ℝ)) ^
                          ((output.reconstruction.registers.cutoff a).score -
                            (output.reconstruction.registers.cutoff a).lastService)) ∧
                    (instruction.kind = .renewal →
                      AssignmentScoreReconstruction.previousScore output.reconstruction = none ∧
                      AssignmentScoreReconstruction.previousWeight output.reconstruction = none) ∧
                    (∃ selection : Selection x,
                      R[e + seg.records.length].output.preparation.coordinator.selection = some selection ∧
                      selection.view.payload = installation.registers.payload ∧
                      selection.view.cutoff = none ∧
                      CoordinatorLocalArmChoice.assignmentIsLive
                        selection.view.payload selection.view.cutoff x.time) ∧
                    ∀ a : Fin p.K,
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
                          (QueueReplay.replay (4 * rate.n) (0, V.2) (H.take (H.length - 1))).1 ∧
                        output.reconstruction.registers.cutoff a =
                            CoordinatorCollectionLedger.CutoffRegister.mk V.1 V.2 (V.1 - Vprev.1) ∧
                          output.reconstruction.registers.current a =
                            CoordinatorCollectionLedger.CurrentRegister.mk Q.2 last ∧
                          AssignmentScoreReconstruction.sourceScore output.reconstruction a = Q.1 ∧
                          AssignmentScoreReconstruction.initialQueue output.reconstruction a = Q.2 ∧
                          installation.registers.payload.queues a = Q.2 ∧
                          (∀ i, installation.registers.payload.assignment.assigned i = a →
                            installation.retainedBaseScore i = Q.1 ∧
                            (installation.registers.payload.downRecord i).val.q = Q.2) ∧
                          (∀ j : CanonicalFastSampling.FastArm installation.registers.payload.slowSet,
                            j.val = a → installation.registers.complementScores j = Q.1 ∧
                              installation.ownedRegisters.queue j = Q.2 ∧
                              installation.ownedRegisters.previousService j = last)) ∨
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
                        V.1 + seg.final.increment a = Q.1 ∧
                        let last := Q.1 - Qprev.1
                        output.reconstruction.registers.cutoff a =
                            CoordinatorCollectionLedger.CutoffRegister.mk V.1 V.2 (V.1 - Vprev.1) ∧
                          output.reconstruction.registers.current a =
                            CoordinatorCollectionLedger.CurrentRegister.mk Q.2 last ∧
                          AssignmentScoreReconstruction.sourceScore output.reconstruction a = Q.1 ∧
                          AssignmentScoreReconstruction.initialQueue output.reconstruction a = Q.2 ∧
                          installation.registers.payload.queues a = Q.2 ∧
                          (∀ i, installation.registers.payload.assignment.assigned i = a →
                            installation.retainedBaseScore i = Q.1 ∧
                            (installation.registers.payload.downRecord i).val.q = Q.2) ∧
                          (∀ j : CanonicalFastSampling.FastArm installation.registers.payload.slowSet,
                            j.val = a → installation.registers.complementScores j = Q.1 ∧
                              installation.ownedRegisters.queue j = Q.2 ∧
                              installation.ownedRegisters.previousService j = last)))
      | _ => False) := by
  classical
  intro R s b
  obtain ⟨L, c, birth, hL, hc, hprefix, hLb, hbsub, htime, henabled,
    hb, har, ht, hrows, hselected, hrewards, _hcurrent, hnext, hmode, hcont⟩ :=
    ReferenceFirstCorrectedAllArmSegmentFinalNumericalJoin.firstCell_all_arm_segment_final_numerical_values
      rate rewards C_star C_h u t z hz
  refine ⟨L, c, birth, hL, hc, hprefix, hLb, hbsub, htime, henabled,
    hb, har, ht, hrows, hselected, hrewards, hnext, hmode, ?_⟩
  intro rout qout beta hlive
  obtain ⟨hsigma, hcover, hcont⟩ := hcont rout qout beta hlive
  refine ⟨hsigma, hcover, ?_⟩
  intro hq
  obtain ⟨next, hk, hstate, hlater, hnext, hnextState,
    hBlen, heR, heT, hWtimes, hprefixA, hAlen, hAdate,
    rE, qE, hp, hlastW, hstateE, hexit⟩ := hcont hq
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
    obtain ⟨htau, hscan, seg, I, hseg, hentry, hpay, hpre, hI, hIdef, hIchecked,
      hIarm, hIsigma, hIcutoff, hfreeze, hbase, hrecords, hpartition, hexit,
      hwhole, hcalendar, hcount, hpositive, hsourceRows, hpayAll, hduring,
      ccut, hcell, hprefixCut, saved, hend, hcursor, hle, hwitnesses,
      hboundary, hvalues⟩ := hcut
    refine ⟨htau, hscan, seg, I, hseg, hentry, hpay, hpre, hI, hIdef, hIchecked,
      hIarm, hIsigma, hIcutoff, hfreeze, hbase, hrecords, hpartition, hexit,
      hwhole, hcalendar, hcount, hpositive, hsourceRows, hpayAll, hduring,
      ccut, hcell, hprefixCut, saved, hend, hcursor, hle, hwitnesses, hboundary, ?_⟩
    intro hv hlaterV
    obtain ⟨hstateV, hempty⟩ :
        R[e + seg.records.length].input.state.coordinator =
          .collection seg.context.payload seg.final saved ∧ seg.final.pending = ∅ := by
      rcases hboundary with hhor | ⟨hv', _, hstateV, _, _, hchoice⟩
      · exact False.elim ((Nat.ne_of_lt hv) hhor)
      · rcases hchoice with hno | ⟨_, hempty, _⟩
        · rw [hlaterV] at hno
          cases hno
        · exact ⟨hstateV, hempty⟩
    have hn := ReferenceCompleteEmptyInstallationNumericalStep.complete_empty_installation_current_numerical_step
      rate rewards C_star C_h z ⟨_, hv⟩
    dsimp only at hn
    rw [hstateV] at hn
    obtain ⟨uNext, hu, core, started, hstartNext, instruction, hassignment,
      htimeNext, hkind, consistent, output, hlocal, hcall, clockData, installation,
      selectedNext, hinstall, hresult, hdispatch, hpreparedNext, hpayload,
      hvector, hownVector, _hbaseNext, _hqueuesNext, hanchor,
      selection, hselection, hvpayload, hvcutoff, hliveNext, _hstrict, _hrow⟩ := hn hempty
    subst installation
    obtain ⟨_, _, _, _, _, hcurrentWeight, hcutoffWeight, _, _, _, _⟩ :=
      AssignmentScoreReconstruction.reconstructLaterStart_success_equations
        _ instruction output.reconstruction output.reconstruction_eq
    have hcorrected := AssignmentScoreReconstruction.reconstructLaterStart_corrected_iff
      _ instruction output.reconstruction output.reconstruction_eq
    have hrenewal := AssignmentScoreReconstruction.reconstructLaterStart_renewal_iff
      _ instruction output.reconstruction output.reconstruction_eq
    rw [htimeNext] at hcorrected hrenewal
    refine ⟨uNext, hu, core, started, hstartNext, instruction, hassignment,
      htimeNext, hkind, consistent, output, hlocal, hcall, clockData, _, selectedNext,
      rfl, hresult, hdispatch, hpreparedNext, hpayload, hvector, hownVector,
      later_reconstruction_eq_source output clockData, hcorrected, hrenewal, hanchor,
      (fun a => ⟨hcurrentWeight a, hcutoffWeight a⟩), ?_, ?_,
      ⟨selection, hselection, hvpayload, hvcutoff, hliveNext⟩, ?_⟩
    · intro hcorr
      obtain ⟨hprev, _, hweights, _⟩ :=
        AssignmentScoreReconstruction.reconstructLaterStart_corrected_equations
          _ instruction output.reconstruction output.reconstruction_eq hcorr
      exact ⟨hprev, hweights⟩
    · exact AssignmentScoreReconstruction.reconstructLaterStart_renewal_equations
        _ instruction output.reconstruction output.reconstruction_eq
    · intro a
      rcases hvalues hempty a with hout | hassigned
      · left
        obtain ⟨j, hja, hcut, hcur, hadd, hHinputs, hHrecords, hpositiveH, hlast⟩ := hout
        exact ⟨j, hja, hcut, hcur, hadd, hHinputs, hHrecords, hpositiveH, hlast,
          installation_arm_values output clockData a _ _ _ _ hcut hcur hadd⟩
      · right
        obtain ⟨i, hia, k, U, hek, hkv, hmem, hacc, hUsigma,
          choice, hchoice, hchoicePay, hchoiceArm, IA, hIA, hIAeq, hchecked,
          hN, htimes, hLlen, selections, ho, hselections, hfollowers,
          hc0, hs, hshort, f, head0, valid0, D0, hhead0, hheadPay,
          hDlen, hDsource, hell, hcut, hcur, hadd⟩ := hassigned
        refine ⟨i, hia, k, U, hek, hkv, hmem, hacc, hUsigma,
          choice, hchoice, hchoicePay, hchoiceArm, IA, hIA, hIAeq, hchecked,
          hN, htimes, hLlen, selections, ho, hselections, hfollowers,
          hc0, hs, hshort, f, head0, valid0, D0, hhead0, hheadPay,
          hDlen, hDsource, hell, hcut, hcur, hadd, ?_⟩
        exact installation_arm_values output clockData _ _ _ _ _ hcut hcur hadd

end Bandits.Support.ReferenceFirstCorrectedNextInstallationNumericalSeed
