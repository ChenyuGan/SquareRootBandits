/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedCollectionCalendarNumericalJoin
public import Bandits.Support.ReferenceFirstCorrectedNextInstallationNumericalSeed

/-!
# The calendar seed at the next installation

Sources: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-174`.

This joins the one original corrected collection's calendar to the actual
later-chosen reconstruction and installation at its endpoint. It stops before
the new assignment's birth recorder or service.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstCorrectedNextInstallationCalendarSeed

open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceCollectionSegmentExtraction CoordinatorPhaseClock CoordinatorRoundDispatch
open CoordinatorAssignmentRegisterInstall LaterAssignmentStartOperation
open RecordedQueueRun

variable {p : ConstructorDimensions.Parameters}

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


/-- The calendar assembled from the first corrected collection is the same
calendar used by the actual next later-chosen reconstruction and installation.
The horizon and non-later branches remain explicit, and the result stops before
the new assignment's recorder or service. -/
theorem firstCell_next_installation_calendar_seed
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
    let Omega := ReferenceCompleteNumericalBranchObservation.completeBranchObservation rate rewards C_star C_h z
    ∃ (L : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K)
      (birth : RoundRecord (p := p) (rate := rate)),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell rate rewards C_star C_h t z = some c ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
      L.length = b ∧ s + b = t.val ∧ R[b]? = some birth ∧
      birth.input.time = t ∧ birth.input.rows = z.1.2 ∧
      birth.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      birth.input.rewards = rewards ∧ c.enabled = true ∧
      ReferenceLaterLiveNumericalReadout.laterLiveReadout s birth = some c ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate birth = some c ∧
      (birth.output.next.coordinator = .dagger ∨
        ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ),
          birth.output.next.coordinator = .live r q base) ∧
      ∀ (rout : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (qout : CoordinatorLiveServiceFinish.OwnedRegisters rout)
        (beta : Fin (p.m - 1) → ℕ),
        birth.output.next.coordinator = .live rout qout beta →
        rout.payload.sigma = t ∧
        ∀ _hq : t.val + 1 < p.T,
        ∃ (hk : b + 1 < R.length)
          (hstate : R[b + 1].input.state.coordinator = .live rout qout beta)
          (hlater : s < rout.payload.sigma.val),
          let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix rate rewards C_star C_h z (b + 1)
          let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
            rewards C_star C_h z ⟨b + 1, hk⟩ rout qout beta hstate hlater
          let e := b + 1 + W.length
          let A := (L ++ [c]) ++ B
          B.length = W.length ∧ e ≤ R.length ∧ t.val + 1 + W.length ≤ p.T ∧
          A.length = e ∧ s + e = t.val + 1 + W.length ∧
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
            rate rewards C_star C_h (s + e) z = some A ∧
          ∃ (rE : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
            (qE : CoordinatorLiveServiceFinish.OwnedRegisters rE),
            rE.payload = rout.payload ∧
            (∀ he : e < R.length, R[e].input.state.coordinator = .live rE qE beta) ∧
            (e = R.length ∨
              ∃ (he : e < R.length),
                ∃ (seg : Segment rate) (I : Initializer p)
                (l0 : Ledger rate),
                    segmentAt R e = some seg ∧ seg.entry = R[e] ∧
                    seg.context.payload = rout.payload ∧ seg.context.preLedger = l0 ∧
                    seg.context.initializer = some I ∧
                    I = cutoffInitializer (liveRegistersAt rE R[e].input.time)
                      (liveOwnedAt rE qE R[e].input.time) beta R[e].input.time ∧
                    I.checkedStart rate = .success l0 ∧
                    I.assignment.arm = rout.payload.assignment.assigned ∧
                    I.sigma = t.val + 1 ∧ I.cutoff = s + e + 1 ∧
                    I.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val rout.payload.sigma
                      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) ∧
                    I.freezeAt = rE.gridBoundary ∧ I.base = beta ∧
                    ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
                    (∃ during, seg.records = seg.entry :: during) ∧
                    seg.records ++ seg.remaining = R.drop e ∧
                    let q := e + seg.records.length
                    ∃ (dCells : List (RecordedQueueRun.RoundInput p.K)),
                      dCells.length = seg.records.length ∧
                      let G := A ++ dCells
                      ∃ (hG : G.length = q) (hq : q ≤ R.length),
                        s + q ≤ p.T ∧
                        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                          rate rewards C_star C_h (s + q) z = some G ∧
                        (∀ k : Fin q,
                          let r := R[k.val]'(Nat.lt_of_lt_of_le k.isLt hq)
                          let cell := G[k.val]'(by omega)
                          ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some cell ∧
                          r.input.time.val = s + k.val ∧
                          (Omega[k.val]'(by
                            simpa only [Omega, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
                              ReferenceCompleteNumericalBranchObservation.branchCalendar,
                              List.length_map, R] using
                                (Nat.lt_of_lt_of_le k.isLt hq))).1 = r.input.time ∧
                          ((Omega[k.val]'(by
                            simpa only [Omega, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
                              ReferenceCompleteNumericalBranchObservation.branchCalendar,
                              List.length_map, R] using
                                (Nat.lt_of_lt_of_le k.isLt hq))).2.2).map (Sum.elim id id) =
                            some (ReferenceCompleteNumericalBranchObservation.encodeNumerical cell)) ∧
                        (∀ cell ∈ G, cell.enabled = false → cell.recordedArm = none ∧ ∀ a,
                          quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a = 0) ∧
                        (∀ a, ∀ h,
                          (G.take h).map (fun cell =>
                            UnstoppedRecordedQueueComparison.unstoppedRecord
                              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a) =
                          (G.take h).map (fun cell => (cell.enabled,
                            quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a))) ∧
                        let raw := fun (a : Fin p.K) (C : List (RecordedQueueRun.RoundInput p.K)) =>
                          C.map (fun cell => (cell.enabled,
                            quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a))
                        let U := fun (a : Fin p.K) (h : ℕ) =>
                          QueueReplay.replay (4 * rate.n) (0, 0) (raw a (G.take h))
                        ∃ saved,
                          (endpointState seg.entry.input.state seg.records).coordinator =
                            .collection seg.context.payload seg.final saved ∧
                          seg.final.cursor = s + q + 1 ∧
                          (q = R.length ∨
                            ∃ (hv : q < R.length),
                              R[q].input.state = endpointState seg.entry.input.state seg.records ∧
                              R[q].input.state.coordinator = .collection seg.context.payload seg.final saved ∧
                              R[q].input.time.val = s + q ∧ R.drop q = seg.remaining ∧
                              (ReferenceCollectionPhaseHistory.laterChosen R[q].input = false ∨
                                ReferenceCollectionPhaseHistory.laterChosen R[q].input = true ∧
                                seg.final.pending = ∅ ∧
                                (∀ i : Fin (p.m - 1),
                                  ∃ (k : Fin R.length) (V : ReferenceCollectionPhaseHistory.UpRecord p rate),
                                    e ≤ k.val ∧ k.val < q ∧ R[k.val] ∈ seg.records ∧
                                    ReferenceCollectionPhaseHistory.AcceptedUp R[k.val].input i V ∧
                                    V.val.sigma = seg.final.sigma) ∧
                                (let x := R[q].input
                                 ∃ (uNext : Fin p.T), uNext.val + 1 = seg.final.cutoff ∧
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
                                        installation = installLater output clockData ∧
                                        clockData.result = started ∧
                                        dispatchCollection input = .laterChosen core consistent started hstart instruction
                                          hassignment output hlocal clockData installation selected ∧
                                        R[q].output.preparation.coordinator =
                                          .collection seg.context.payload seg.final clock uNext
                                            (.laterChosen core consistent started hstart instruction hassignment
                                              output hlocal clockData installation selected) ∧
                                        x.rows = z.1.2 ∧
                                        x.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
                                        x.rewards = rewards ∧
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
                                          R[q].output.preparation.coordinator.selection = some selection ∧
                                          selection.view.payload = installation.registers.payload ∧
                                          selection.view.cutoff = none ∧
                                          CoordinatorLocalArmChoice.assignmentIsLive
                                            selection.view.payload selection.view.cutoff x.time) ∧
                                        ∀ a : Fin p.K,
                                          (output.reconstruction.registers.cutoff a =
                                              ⟨(U a e).1, (U a e).2, (U a e).1 - (U a (e - 1)).1⟩ ∧
                                            output.reconstruction.registers.current a =
                                              ⟨(U a q).2, (U a q).1 - (U a (q - 1)).1⟩ ∧
                                            AssignmentScoreReconstruction.sourceScore output.reconstruction a = (U a q).1 ∧
                                            AssignmentScoreReconstruction.initialQueue output.reconstruction a = (U a q).2 ∧
                                            installation.registers.payload.queues a = (U a q).2 ∧
                                            (∀ i, installation.registers.payload.assignment.assigned i = a →
                                              installation.retainedBaseScore i = (U a q).1 ∧
                                              (installation.registers.payload.downRecord i).val.q = (U a q).2) ∧
                                            (∀ j : CanonicalFastSampling.FastArm installation.registers.payload.slowSet,
                                              j.val = a → installation.registers.complementScores j = (U a q).1 ∧
                                                installation.ownedRegisters.queue j = (U a q).2 ∧
                                                installation.ownedRegisters.previousService j =
                                                  (U a q).1 - (U a (q - 1)).1)))))
                )
    := by
  classical
  intro R s b Omega
  obtain ⟨L, c, birth, hL, hc, hprefix, hLb, htime, hb, ht,
    hrows, hselected, hrewards, henabled, hread, hcell0, hmode, hcont⟩ :=
    ReferenceFirstCorrectedCollectionCalendarNumericalJoin.firstCell_collection_calendar_numerical_values
      rate rewards C_star C_h u t z hz
  refine ⟨L, c, birth, hL, hc, hprefix, hLb, htime, hb, ht,
    hrows, hselected, hrewards, henabled, hread, hcell0, hmode, ?_⟩
  intro rout qout beta hlive
  obtain ⟨hsigma, hcont⟩ := hcont rout qout beta hlive
  refine ⟨hsigma, ?_⟩
  intro hq
  obtain ⟨hk, hstate, hlater, hBlen, heR, heT, hAlen, hAdate, hprefixA,
    _hwindow, _hWread, rE, qE, hp, hstateE, hexit⟩ := hcont hq
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z (b + 1)
  let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
    rewards C_star C_h z ⟨b + 1, hk⟩ rout qout beta hstate hlater
  let e := b + 1 + W.length
  let A := (L ++ [c]) ++ B
  refine ⟨hk, hstate, hlater, hBlen, heR, heT, hAlen, hAdate, hprefixA,
    rE, qE, hp, hstateE, ?_⟩
  by_cases heq : e = R.length
  · exact Or.inl heq
  · rcases hexit with hhor | hseg
    · exact False.elim (heq hhor)
    · rcases hseg with ⟨he, seg, I, l0, hrest⟩
      rcases hrest with ⟨hseg, hentry, hpay, hpre, hI, hIdef, hchecked,
        harm, hIsigma, hIcut, hIscan, hfreeze, hbase, hcutchosen,
        hDuring, hpartition, hrest⟩
      rcases hrest with ⟨dCells, hD, hDcells, hrest⟩
      rcases hrest with ⟨hH, hrest⟩
      rcases hrest with ⟨hG, hq, hT, _hRtake, hprefixG, hcoordinates,
        hdisabled, hunstopped, hvalues, saved, hend, hcursor, hboundary⟩
      let q := e + seg.records.length
      let G := A ++ dCells
      let raw := fun (a : Fin p.K) (C : List (RecordedQueueRun.RoundInput p.K)) =>
        C.map (fun cell => (cell.enabled,
          quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a))
      let U := fun (a : Fin p.K) (h : ℕ) =>
        QueueReplay.replay (4 * rate.n) (0, 0) (raw a (G.take h))
      have hqdef : q = e + seg.records.length := rfl
      refine Or.inr ⟨he, seg, I, l0, hseg, hentry, hpay, hpre, hI, hIdef,
        hchecked, harm, hIsigma, hIcut, hIscan, hfreeze, hbase, hcutchosen,
        hDuring, hpartition, ?_⟩
      refine ⟨dCells, hD, hG, hq, hT, hprefixG, ?_, hdisabled, ?_, saved,
        hend, hcursor, ?_⟩
      · intro k
        simpa only [G] using hcoordinates k
      · intro a h
        simpa only [G] using (hunstopped a).2.2 h
      · rcases hboundary with hhorQ | ⟨hv, hstateQ, hcoordQ, htimeQ, hdropQ, hchoiceQ⟩
        · exact Or.inl hhorQ
        · refine Or.inr ⟨hv, hstateQ, hcoordQ, htimeQ, hdropQ, ?_⟩
          rcases hchoiceQ with hnotLater | ⟨hlaterQ, hempty, haccepted⟩
          · exact Or.inl hnotLater
          · refine Or.inr ⟨hlaterQ, hempty, haccepted, ?_⟩
            have hn := ReferenceCompleteEmptyInstallationNumericalStep.complete_empty_installation_current_numerical_step
              rate rewards C_star C_h z ⟨q, hv⟩
            dsimp only at hn
            rw [hcoordQ] at hn
            obtain ⟨uNext, huNext, core, started, hstartNext, instruction, hassignment,
              htimeNext, hkind, consistent, output, hlocal, hcall, clockData, installation,
              selectedNext, hinstall, hresult, hdispatch, hpreparedNext, hpayload,
              hvector, hownVector, _hbaseNext, _hqueuesNext, hanchor,
              selection, hselection, hvpayload, hvcutoff, hliveNext, _hstrict, hrow⟩ :=
                hn hempty
            subst installation
            obtain ⟨_, _, _, _, _, hcurrentWeight, hcutoffWeight, _, _, _, _⟩ :=
              AssignmentScoreReconstruction.reconstructLaterStart_success_equations
                _ instruction output.reconstruction output.reconstruction_eq
            have hcorrected := AssignmentScoreReconstruction.reconstructLaterStart_corrected_iff
              _ instruction output.reconstruction output.reconstruction_eq
            have hrenewal := AssignmentScoreReconstruction.reconstructLaterStart_renewal_iff
              _ instruction output.reconstruction output.reconstruction_eq
            rw [htimeNext] at hcorrected hrenewal
            obtain ⟨cLive, ho, liveCell, hreadQ, hcellInput, hcellSelected,
              hcellStates, hcellMemories, hunoccupied, hcEnabled, hcRate, hcReward,
              hmarker, hrowsQ, hselectedQ, hrewardsQ, _harrivals, _hsaved, _hraw, _howner, _hfinish⟩ := hrow
            refine ⟨uNext, huNext, core, started, hstartNext, instruction, hassignment,
              htimeNext, hkind, consistent, output, hlocal, hcall, clockData, _, selectedNext,
              rfl, hresult, hdispatch, hpreparedNext, ?_, ?_, ?_, ?_, ?_, hownVector,
              later_reconstruction_eq_source output clockData, hcorrected, hrenewal,
              hanchor, (fun a => ⟨hcurrentWeight a, hcutoffWeight a⟩), ?_, ?_,
              ⟨selection, hselection, hvpayload, hvcutoff, hliveNext⟩, ?_⟩
            · exact hrowsQ
            · exact hselectedQ
            · exact hrewardsQ
            · exact hpayload
            · exact hvector
            · intro hcorr
              obtain ⟨hprev, _, hweights, _⟩ :=
                AssignmentScoreReconstruction.reconstructLaterStart_corrected_equations
                  _ instruction output.reconstruction output.reconstruction_eq hcorr
              exact ⟨hprev, hweights⟩
            · exact AssignmentScoreReconstruction.reconstructLaterStart_renewal_equations
                _ instruction output.reconstruction output.reconstruction_eq
            · intro a
              obtain ⟨hcutoff, hcurrent, hadd, _⟩ := hvalues hempty a
              simpa only [raw, U, q, G] using
                (installation_arm_values output clockData a (U a e) (U a (e - 1))
                  (U a q) ((U a q).1 - (U a (q - 1)).1) hcutoff hcurrent hadd)

end Bandits.Support.ReferenceFirstCorrectedNextInstallationCalendarSeed
