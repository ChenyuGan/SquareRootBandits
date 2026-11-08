/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedNextInstallationCalendarSeed
public import Bandits.Support.ReferenceCorrectedSuccessorOutsideNumericalStep

/-!
# Initialized first-successor outside-calendar replay

Apply the accepted first corrected common-calendar seed to its actual first
later-chosen installation.  The source-score and initial-queue replay equations
are derived for that same installed reconstruction from the original source.
The actual birth is appended once, and every following continuing LIVE prefix
is replayed from that same zero-origin common calendar.

Sources: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-174`.

The calendar seed supplies `G.length = q`; hence `G.take q = G` discharges both
initial replay equations. The accepted empty-installation numerical step
supplies the actual service. Its start result, instruction, successful output,
clock evidence and installation are identified in that order by deterministic
constructor equations. The accepted complete later-LIVE complement prefix
then supplies the continuing states, services and maximal cutoff boundary.
-/

@[expose] public section
noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CoordinatorAssignmentRegisterInstall
open Bandits.Support.LaterAssignmentStartOperation
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.RecordedQueueRun
open Bandits.Support.ReferenceCollectionSegmentExtraction

namespace Bandits.Support.ReferenceFirstCorrectedNextOutsideCalendarReplay

variable {p : ConstructorDimensions.Parameters}

private theorem birth_replay
    (capacity : ℕ) (E : List (Bool × ℕ)) (initialScore initialQueue arrival : ℕ)
    (hscore : initialScore = (QueueReplay.replay capacity (0, 0) E).1)
    (hqueue : initialQueue = (QueueReplay.replay capacity (0, 0) E).2) :
    QueueReplay.transition capacity (initialScore, initialQueue) (true, arrival) =
      QueueReplay.replay capacity (0, 0) (E ++ [(true, arrival)]) := by
  rw [QueueReplay.replay_append]
  have hpair : (initialScore, initialQueue) = QueueReplay.replay capacity (0, 0) E :=
    Prod.ext hscore hqueue
  rw [← hpair]
  rfl

/-- The accepted common-calendar first successor carries the exact original
prefix and the actual constructor witnesses at its endpoint.  At an actual
later-chosen endpoint, every installed arm's reconstructed score and queue,
the payload queue, retained assignment base, and new complement registers are
the zero-origin replay of the same complete calendar `G`. The actual birth
and every continuing complement prefix retain their service differences,
original dated readouts and actual excluded cutoff constructor. Horizon,
dagger and non-later alternatives remain explicit. -/
theorem firstCell_next_outside_calendar_seed
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
    let Omega := ReferenceCompleteNumericalBranchObservation.completeBranchObservation
      rate rewards C_star C_h z
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
          (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
          (base : Fin (p.m - 1) → ℕ), birth.output.next.coordinator = .live r q base) ∧
      ∀ (rout : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (qout : CoordinatorLiveServiceFinish.OwnedRegisters rout)
        (beta : Fin (p.m - 1) → ℕ),
        birth.output.next.coordinator = .live rout qout beta →
        rout.payload.sigma = t ∧
        ∀ _hq : t.val + 1 < p.T,
        ∃ (hk : b + 1 < R.length)
          (hstate : R[b + 1].input.state.coordinator = .live rout qout beta)
          (hlater : s < rout.payload.sigma.val),
          let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
            rate rewards C_star C_h z (b + 1)
          let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
            rewards C_star C_h z ⟨b + 1, hk⟩ rout qout beta hstate hlater
          let e := b + 1 + W.length
          let A := (L ++ [c]) ++ B
          B.length = W.length ∧ e ≤ R.length ∧
          t.val + 1 + W.length ≤ p.T ∧ A.length = e ∧
          s + e = t.val + 1 + W.length ∧
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
            rate rewards C_star C_h (s + e) z = some A ∧
          ∃ (rE : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
            (qE : CoordinatorLiveServiceFinish.OwnedRegisters rE),
            rE.payload = rout.payload ∧
            (∀ he : e < R.length, R[e].input.state.coordinator = .live rE qE beta) ∧
            (e = R.length ∨
              ∃ (he : e < R.length) (seg : Segment rate) (I : Initializer p)
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
                  let G := ((L ++ [c]) ++ B) ++ dCells
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
                    let raw := fun (a : Fin p.K)
                        (C : List (RecordedQueueRun.RoundInput p.K)) =>
                      C.map (fun cell => (cell.enabled,
                        quantizedArrival
                          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a))
                    let U := fun (a : Fin p.K) (h : ℕ) =>
                      QueueReplay.replay (4 * rate.n) (0, 0) (raw a (G.take h))
                    ∃ saved,
                      (endpointState seg.entry.input.state seg.records).coordinator =
                        .collection seg.context.payload seg.final saved ∧
                      seg.final.cursor = s + q + 1 ∧
                      (q = R.length ∨
                        ∃ (hv : q < R.length),
                          R[q].input.state = endpointState seg.entry.input.state seg.records ∧
                          R[q].input.state.coordinator =
                            .collection seg.context.payload seg.final saved ∧
                          R[q].input.time.val = s + q ∧ R.drop q = seg.remaining ∧
                          (ReferenceCollectionPhaseHistory.laterChosen R[q].input = false ∨
                            ReferenceCollectionPhaseHistory.laterChosen R[q].input = true ∧
                            seg.final.pending = ∅ ∧
                            (∀ i : Fin (p.m - 1),
                              ∃ (ki : Fin R.length)
                                (V : ReferenceCollectionPhaseHistory.UpRecord p rate),
                                e ≤ ki.val ∧ ki.val < q ∧ R[ki.val] ∈ seg.records ∧
                                ReferenceCollectionPhaseHistory.AcceptedUp R[ki.val].input i V ∧
                                V.val.sigma = seg.final.sigma) ∧
                            let x := R[q].input
                            ∃ (uNext : Fin p.T), uNext.val + 1 = seg.final.cutoff ∧
                              let clock := collectionClock seg.context.payload seg.final saved uNext
                              let input := collectionInput x seg.context.payload seg.final clock uNext
                              ∃ (core : CollectionCoreValid input)
                                (started : StartRoundResult p)
                                (hstart : startRound p rate.eta.val x.time input.clock
                                  seg.final.pending = .ok started)
                                (instruction : AssignmentStartInstruction p)
                                (hassignment : started.assignmentStart = some instruction),
                                instruction.time = x.time ∧
                                instruction.kind =
                                  (if x.time.val + 1 < seg.final.freezeAt then .corrected else .renewal) ∧
                                let operation := collectionOperationLedger input core.payload_n_eq
                                ∃ (consistent : LocalConsistency seg.context.payload operation)
                                  (output : SuccessfulStart seg.context.payload operation instruction x.row)
                                  (hlocal : output.localConsistency = consistent),
                                  laterAssignmentStart seg.context.payload operation instruction x.row
                                    consistent = LaterAssignmentStartOperation.Result.success
                                      output hlocal ∧
                                  ∃ (clockData : LaterStartRoundEvidence output)
                                    (installation : LaterInstallation output clockData)
                                    (selected : ArmSelection installation.registers.payload started
                                      instruction.time installation.registers.complementWeights x.row),
                                    installation = installLater output clockData ∧
                                    clockData.result = started ∧
                                    dispatchCollection input = .laterChosen core consistent started
                                      hstart instruction hassignment output hlocal clockData
                                      installation selected ∧
                                    R[q].output.preparation.coordinator =
                                      .collection seg.context.payload seg.final clock uNext
                                        (.laterChosen core consistent started hstart instruction
                                          hassignment output hlocal clockData installation selected) ∧
                                    x.rows = z.1.2 ∧
                                    x.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
                                    x.rewards = rewards ∧
                                    installation.registers.payload = output.payload ∧
                                    installation.assignmentVector = output.assignmentVector ∧
                                    output.assignmentVector = ownAssignmentVector x.row x.time ∧
                                    installation.reconstruction = output.reconstruction ∧
                                    (∀ a, AssignmentScoreReconstruction.currentWeight
                                        output.reconstruction a =
                                          (1 + 1 / (D p : ℝ)) ^
                                            AssignmentScoreReconstruction.sourceScore
                                              output.reconstruction a ∧
                                      AssignmentScoreReconstruction.cutoffWeight
                                        output.reconstruction a =
                                          (1 + 1 / (D p : ℝ)) ^
                                            (output.reconstruction.registers.cutoff a).score) ∧
                                    (∃ selection : Selection x,
                                      R[q].output.preparation.coordinator.selection = some selection ∧
                                      selection.view.payload = installation.registers.payload ∧
                                      selection.view.cutoff = none ∧
                                      CoordinatorLocalArmChoice.assignmentIsLive
                                        selection.view.payload selection.view.cutoff x.time) ∧
                                    (∀ a : Fin p.K,
                                      AssignmentScoreReconstruction.sourceScore
                                        output.reconstruction a =
                                          (QueueReplay.replay (4 * rate.n) (0, 0)
                                            (raw a G)).1 ∧
                                      AssignmentScoreReconstruction.initialQueue
                                        output.reconstruction a =
                                          (QueueReplay.replay (4 * rate.n) (0, 0)
                                            (raw a G)).2 ∧
                                      installation.registers.payload.queues a =
                                        (QueueReplay.replay (4 * rate.n) (0, 0)
                                          (raw a G)).2 ∧
                                      (∀ i, installation.registers.payload.assignment.assigned i = a →
                                        installation.retainedBaseScore i =
                                            (QueueReplay.replay (4 * rate.n) (0, 0)
                                              (raw a G)).1 ∧
                                          (installation.registers.payload.downRecord i).val.q =
                                            (QueueReplay.replay (4 * rate.n) (0, 0)
                                              (raw a G)).2) ∧
                                      (∀ j : FastArm installation.registers.payload.slowSet,
                                        j.val = a →
                                          installation.registers.complementScores j =
                                              (QueueReplay.replay (4 * rate.n) (0, 0)
                                                (raw a G)).1 ∧
                                            installation.ownedRegisters.queue j =
                                              (QueueReplay.replay (4 * rate.n) (0, 0)
                                                (raw a G)).2 ∧
                                            installation.ownedRegisters.previousService j =
                                              (U a q).1 - (U a (q - 1)).1)) ∧
                                    let x := R[q].input
                                    ∃ (birthSelection : Selection x)
                                      (cNext : RecordedQueueRun.RoundInput p.K)
                                      (_ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary
                                        (R[q]))
                                      (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell
                                        (R[q])),
                                      R[q].output.preparation.coordinator.selection =
                                        some birthSelection ∧
                                      birthSelection.view.payload = installation.registers.payload ∧
                                      birthSelection.view.cutoff = none ∧
                                      CoordinatorLocalArmChoice.assignmentIsLive
                                        birthSelection.view.payload birthSelection.view.cutoff x.time ∧
                                      ReferenceLaterLiveNumericalReadout.laterLiveReadout s (R[q]) =
                                        some cNext ∧
                                      cell.input = cNext ∧ cell.selected = birthSelection ∧
                                      cNext.enabled = true ∧
                                      cNext.rate = installation.registers.payload.rate ∧
                                      cNext.reward =
                                        (fun arm => ((rewards x.time arm).val : ℝ) / (D p : ℝ)) ∧
                                      x.rows = z.1.2 ∧
                                      x.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
                                      x.rewards = rewards ∧
                                      ∃ (o : CoordinatorRecordingOperation.Output p)
                                        (serviced : CoordinatorLiveServiceFinish.ServicedRegisters
                                          installation.registers installation.ownedRegisters)
                                        (pending : Finset (Fin (p.m - 1)))
                                        (finished : FinishRoundResult p),
                                        R[q].output.coordinator.recording = some o ∧
                                        serviced.recording = o ∧
                                        (∀ j : FastArm installation.registers.payload.slowSet,
                                          serviced.arrival j =
                                            RecordedQueueRun.quantizedArrival
                                              (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                                              cNext j.val ∧
                                          (serviced.score j, serviced.queue j) =
                                            QueueReplay.transition (4 * rate.n)
                                              (AssignmentScoreReconstruction.sourceScore
                                                output.reconstruction j.val,
                                               AssignmentScoreReconstruction.initialQueue
                                                output.reconstruction j.val)
                                              (true, RecordedQueueRun.quantizedArrival
                                                (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                                                cNext j.val) ∧
                                          serviced.previousService j = serviced.score j -
                                            AssignmentScoreReconstruction.sourceScore
                                              output.reconstruction j.val) ∧
                                        finishRound p rate.eta.val x.time started.clock pending x.row =
                                          .ok finished ∧
                                        let birthRegisters :
                                            CoordinatorLiveChoiceRecorderStep.Registers p rate.eta :=
                                          { payload := installation.registers.payload
                                            priorClock := finished.clock
                                            pendingAtChoice := finished.pending
                                            time := x.time
                                            gridBoundary := finished.clock.g
                                            complementScores := serviced.score }
                                        let birthOwned :
                                            CoordinatorLiveServiceFinish.OwnedRegisters birthRegisters :=
                                          { queue := serviced.queue
                                            previousService := serviced.previousService }
                                        R[q].output.next.coordinator =
                                          .live birthRegisters birthOwned installation.retainedBaseScore ∧
                                        (∀ j : FastArm installation.registers.payload.slowSet,
                                          (serviced.score j, serviced.queue j) =
                                            QueueReplay.replay (4 * rate.n) (0, 0)
                                              (raw j.val G ++ [(true,
                                                RecordedQueueRun.quantizedArrival
                                                  (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                                                  cNext j.val)]) ∧
                                          serviced.previousService j = serviced.score j -
                                            (QueueReplay.replay (4 * rate.n) (0, 0)
                                              (raw j.val G)).1) ∧
                                        (q + 1 = R.length ∨
                                          ∃ (hnext : q + 1 < R.length)
                                            (hstateNext :
                                              (R[q + 1]'hnext).input.state.coordinator =
                                                .live birthRegisters birthOwned
                                                  installation.retainedBaseScore)
                                            (hlaterNext : s < birthRegisters.payload.sigma.val),
                                            let nextIndex : Fin R.length := ⟨q + 1, hnext⟩
                                            let WNext := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
                                              rate rewards C_star C_h z (q + 1)
                                            let BNext := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
                                              rewards C_star C_h z nextIndex birthRegisters birthOwned
                                              installation.retainedBaseScore hstateNext hlaterNext
                                            ∃ _hlength : BNext.length = WNext.length,
                                            WNext.map (ReferenceLaterLiveNumericalReadout.laterLiveReadout
                                              (ReferenceCompletePhysicalHistory.physicalStart
                                                rate z rewards C_star C_h)) = BNext.map some ∧
                                            (∀ cells : List (RecordedQueueRun.RoundInput p.K),
                                              WNext.map (ReferenceLaterLiveNumericalReadout.laterLiveReadout
                                                (ReferenceCompletePhysicalHistory.physicalStart
                                                  rate z rewards C_star C_h)) = cells.map some → cells = BNext) ∧
                                            WNext.map (fun r => (r.input.time,
                                              ReferenceLaterLiveNumericalReadout.laterLiveReadout
                                                (ReferenceCompletePhysicalHistory.physicalStart
                                                  rate z rewards C_star C_h) r)) =
                                              ((ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar
                                                rate rewards C_star C_h z).drop nextIndex.val).take WNext.length ∧
                                            WNext.map (fun r => r.input.time.val) =
                                              List.range' (ReferenceCompletePhysicalHistory.physicalStart
                                                rate z rewards C_star C_h + nextIndex.val) WNext.length ∧
                                            (∀ i : Fin WNext.length,
                                              let r := R[nextIndex.val + i.val]'(by
                                                have hlengthBound := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_length_le
                                                  (rate := rate) rewards C_star C_h z nextIndex
                                                have hi : nextIndex.val + WNext.length ≤ R.length := by
                                                  exact hlengthBound
                                                omega)
                                              let cell := BNext[i.val]'(by
                                                rw [ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_length
                                                  (rate := rate) rewards C_star C_h z nextIndex birthRegisters birthOwned
                                                  installation.retainedBaseScore hstateNext hlaterNext]
                                                exact i.isLt)
                                              ∃ (rv : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                                                (qv : CoordinatorLiveServiceFinish.OwnedRegisters rv),
                                                rv.payload = birthRegisters.payload ∧
                                                r.input.state.coordinator = .live rv qv installation.retainedBaseScore ∧
                                                r.input.rows = z.1.2 ∧
                                                r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
                                                r.input.rewards = rewards ∧
                                                ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest r = true ∧
                                                ∃ (serviced : CoordinatorLiveServiceFinish.ServicedRegisters
                                                    (liveRegistersAt rv r.input.time) (liveOwnedAt rv qv r.input.time))
                                                  (finished : FinishRoundResult p),
                                                  ReferenceLaterLiveNumericalReadout.laterLiveReadout
                                                    (ReferenceCompletePhysicalHistory.physicalStart
                                                      rate z rewards C_star C_h) r = some cell ∧
                                                  cell.enabled = true ∧
                                                  cell.reward = (fun arm => ((rewards r.input.time arm).val : ℝ) / (D p : ℝ)) ∧
                                                  cell.rate = birthRegisters.payload.rate ∧
                                                  (∃ (selected : Selection r.input)
                                                    (ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary r),
                                                    r.output.preparation.coordinator.selection = some selected ∧
                                                    selected.view.payload = birthRegisters.payload ∧
                                                    cell = ReferenceFirstWindowNumericalStream.sourceCell r
                                                      selected.view.payload selected.view.pendingAtChoice
                                                      (ReferenceLaterLiveNumericalReadout.preparedStates r ho)
                                                      selected.view.complementWeights selected.view.cutoff
                                                      (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)) ∧
                                                  r.output.coordinator.recording = some serviced.recording ∧
                                                  r.output.coordinator.failure = none ∧
                                                  (∀ a, serviced.arrival a = RecordedQueueRun.quantizedArrival
                                                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a.val ∧
                                                    QueueReplay.transition (4 * rate.n)
                                                      (rv.complementScores a, qv.queue a)
                                                      (cell.enabled, RecordedQueueRun.quantizedArrival
                                                        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a.val) =
                                                      (serviced.score a, serviced.queue a) ∧
                                                    serviced.previousService a = serviced.service a ∧
                                                    serviced.previousService a = serviced.score a - rv.complementScores a) ∧
                                                  r.output.next.coordinator =
                                                    .live { payload := rv.payload
                                                            priorClock := finished.clock
                                                            pendingAtChoice := finished.pending
                                                            time := r.input.time
                                                            gridBoundary := finished.clock.g
                                                            complementScores := serviced.score }
                                                      { queue := serviced.queue, previousService := serviced.previousService }
                                                      installation.retainedBaseScore) ∧
                                            (∀ (v : ℕ) (hv : v ≤ WNext.length),
                                              let V := fun (j : FastArm birthRegisters.payload.slowSet) (w : ℕ) =>
                                                QueueReplay.replay (4 * rate.n) (0, 0)
                                                  (raw j.val G ++ [(true, quantizedArrival
                                                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) cNext j.val)] ++
                                                    raw j.val (BNext.take w))
                                              ∃ (rv : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                                                (qv : CoordinatorLiveServiceFinish.OwnedRegisters rv)
                                                (hp : rv.payload = birthRegisters.payload),
                                                (∀ hpos : 0 < v,
                                                  (WNext[v - 1]'(by omega)).output.next.coordinator =
                                                    .live rv qv installation.retainedBaseScore) ∧
                                                (∀ hboundary : nextIndex.val + v < R.length,
                                                  (R[nextIndex.val + v]'hboundary).input.state.coordinator =
                                                    .live rv qv installation.retainedBaseScore) ∧
                                                ∀ j : FastArm birthRegisters.payload.slowSet,
                                                  let jv : FastArm rv.payload.slowSet :=
                                                    ⟨j.val, by simpa only [hp] using j.property⟩
                                                  (rv.complementScores jv, qv.queue jv) = V j v ∧
                                                  qv.previousService jv =
                                                    if v = 0 then
                                                      (QueueReplay.replay (4 * rate.n) (0, 0)
                                                        (raw j.val G ++ [(true, quantizedArrival
                                                          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                                                          cNext j.val)])).1 -
                                                        (QueueReplay.replay (4 * rate.n) (0, 0) (raw j.val G)).1
                                                    else (V j v).1 - (V j (v - 1)).1) ∧
                                            (nextIndex.val + WNext.length = R.length ∨
                                              ∃ (hcutoff : nextIndex.val + WNext.length < R.length)
                                                (rv : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                                                (qv : CoordinatorLiveServiceFinish.OwnedRegisters rv),
                                                rv.payload = birthRegisters.payload ∧
                                                (R[nextIndex.val + WNext.length]'hcutoff).input.state.coordinator =
                                                  .live rv qv installation.retainedBaseScore ∧
                                                ∃ (dispatched : CoordinatorStartRoundCutoffDispatch.Output
                                                    (liveInput (rate := rate)
                                                      (R[nextIndex.val + WNext.length]'hcutoff).input rv qv
                                                      installation.retainedBaseScore).registers
                                                    (liveInput (rate := rate)
                                                      (R[nextIndex.val + WNext.length]'hcutoff).input rv qv
                                                      installation.retainedBaseScore).ownedRegisters
                                                    (liveInput (rate := rate)
                                                      (R[nextIndex.val + WNext.length]'hcutoff).input rv qv
                                                      installation.retainedBaseScore).followerBaseScore)
                                                  (startRound_eq : CoordinatorPhaseClock.startRound p
                                                    (liveInput (rate := rate)
                                                      (R[nextIndex.val + WNext.length]'hcutoff).input rv qv
                                                      installation.retainedBaseScore).eta.val
                                                    (liveInput (rate := rate)
                                                      (R[nextIndex.val + WNext.length]'hcutoff).input rv qv
                                                      installation.retainedBaseScore).registers.time
                                                    (liveInput (rate := rate)
                                                      (R[nextIndex.val + WNext.length]'hcutoff).input rv qv
                                                      installation.retainedBaseScore).registers.priorClock
                                                    (liveInput (rate := rate)
                                                      (R[nextIndex.val + WNext.length]'hcutoff).input rv qv
                                                      installation.retainedBaseScore).registers.clockPending =
                                                        .ok dispatched.startResult)
                                                  (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger
                                                    (liveInput (rate := rate)
                                                      (R[nextIndex.val + WNext.length]'hcutoff).input rv qv
                                                      installation.retainedBaseScore).registers)
                                                  (initialization_eq :
                                                    dispatched.collectionInitialization = .success (some ledger))
                                                  (ledger_eq_candidate : ledger =
                                                    CoordinatorStartRoundCutoffDispatch.collectionStartLedger
                                                      (liveInput (rate := rate)
                                                        (R[nextIndex.val + WNext.length]'hcutoff).input rv qv
                                                        installation.retainedBaseScore).registers
                                                      (liveInput (rate := rate)
                                                        (R[nextIndex.val + WNext.length]'hcutoff).input rv qv
                                                        installation.retainedBaseScore).ownedRegisters
                                                      (liveInput (rate := rate)
                                                        (R[nextIndex.val + WNext.length]'hcutoff).input rv qv
                                                        installation.retainedBaseScore).followerBaseScore
                                                      (liveInput (rate := rate)
                                                        (R[nextIndex.val + WNext.length]'hcutoff).input rv qv
                                                        installation.retainedBaseScore).registers.time)
                                                  (initializationDomainValid :
                                                    CoordinatorStartRoundCutoffDispatch.initializationDomainValid
                                                      (liveInput (rate := rate)
                                                        (R[nextIndex.val + WNext.length]'hcutoff).input rv qv
                                                        installation.retainedBaseScore).registers
                                                      (liveInput (rate := rate)
                                                        (R[nextIndex.val + WNext.length]'hcutoff).input rv qv
                                                        installation.retainedBaseScore).ownedRegisters
                                                      (liveInput (rate := rate)
                                                        (R[nextIndex.val + WNext.length]'hcutoff).input rv qv
                                                        installation.retainedBaseScore).followerBaseScore
                                                      (liveInput (rate := rate)
                                                        (R[nextIndex.val + WNext.length]'hcutoff).input rv qv
                                                        installation.retainedBaseScore).registers.time)
                                                  (cutoff_clock : dispatched.startResult.clock =
                                                    { (liveInput (rate := rate)
                                                        (R[nextIndex.val + WNext.length]'hcutoff).input rv qv
                                                        installation.retainedBaseScore).registers.priorClock with
                                                      u := some (liveInput (rate := rate)
                                                        (R[nextIndex.val + WNext.length]'hcutoff).input rv qv
                                                        installation.retainedBaseScore).registers.time })
                                                  (cutoff_pending : dispatched.startResult.pending = Finset.univ)
                                                  (no_assignment : dispatched.startResult.assignmentStart = none)
                                                  (selection : ArmSelection
                                                    (liveInput (rate := rate)
                                                      (R[nextIndex.val + WNext.length]'hcutoff).input rv qv
                                                      installation.retainedBaseScore).registers.payload
                                                    dispatched.startResult
                                                    (liveInput (rate := rate)
                                                      (R[nextIndex.val + WNext.length]'hcutoff).input rv qv
                                                      installation.retainedBaseScore).registers.time
                                                    (liveInput (rate := rate)
                                                      (R[nextIndex.val + WNext.length]'hcutoff).input rv qv
                                                      installation.retainedBaseScore).registers.complementWeights
                                                    (liveInput (rate := rate)
                                                      (R[nextIndex.val + WNext.length]'hcutoff).input rv qv
                                                      installation.retainedBaseScore).row),
                                                  (R[nextIndex.val + WNext.length]'hcutoff).output.preparation.coordinator =
                                                    .live rv qv installation.retainedBaseScore
                                                      (.cutoffChosen dispatched startRound_eq ledger initialization_eq
                                                        ledger_eq_candidate initializationDomainValid cutoff_clock
                                                        cutoff_pending no_assignment selection))))))
    := by
  classical
  intro R s b Omega
  obtain ⟨L, c, birth, hL, hc, hprefix, hLb, hdate, hb, hbirthTime,
    hbirthRows, hbirthSelected, hbirthRewards, henabled, hread, hcell0,
    hmode, hcont⟩ :=
    ReferenceFirstCorrectedNextInstallationCalendarSeed.firstCell_next_installation_calendar_seed
      rate rewards C_star C_h u t z hz
  refine ⟨L, c, birth, hL, hc, hprefix, hLb, hdate, hb, hbirthTime,
    hbirthRows, hbirthSelected, hbirthRewards, henabled, hread, hcell0,
    hmode, ?_⟩
  intro rout qout beta hlive
  obtain ⟨hsigma, hcont⟩ := hcont rout qout beta hlive
  refine ⟨hsigma, ?_⟩
  intro hq
  obtain ⟨hk, hstate, hlater, hBlen, heR, heT, hAlen, hAdate, hprefixA,
    rE, qE, hp, hstateE, hexit⟩ := hcont hq
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
      rcases hrest with ⟨hsegment, hentry, hpay, hpre, hI, hIdef, hchecked,
        harm, hIsigma, hIcut, hIscan, hfreeze, hbase, hcutchosen,
        hDuring, hpartition, dCells, hD, hrest⟩
      rcases hrest with ⟨hG, hq, hT, hprefixG, hcoordinates, _hdisabled,
        _hunstopped, saved, hend, hcursor, hboundary⟩
      let q := e + seg.records.length
      let G := A ++ dCells
      let raw := fun (a : Fin p.K) (C : List (RecordedQueueRun.RoundInput p.K)) =>
        C.map (fun cell => (cell.enabled,
          quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a))
      let U := fun (a : Fin p.K) (h : ℕ) =>
        QueueReplay.replay (4 * rate.n) (0, 0) (raw a (G.take h))
      refine Or.inr ⟨he, seg, I, l0, hsegment, hentry, hpay, hpre, hI,
        hIdef, hchecked, harm, hIsigma, hIcut, hIscan, hfreeze, hbase,
        hcutchosen, hDuring, hpartition, dCells, hD, hG, hq, hT,
        hprefixG, hcoordinates, ?_⟩
      · refine ⟨saved, hend, hcursor, ?_⟩
        rcases hboundary with hqterminal | ⟨hv, hstateQ, hcoordQ, htimeQ,
          hdropQ, hchoiceQ⟩
        · exact Or.inl hqterminal
        · refine Or.inr ⟨hv, hstateQ, hcoordQ, htimeQ, hdropQ, ?_⟩
          rcases hchoiceQ with hnotLater | ⟨hlaterQ, hempty, haccepted,
              uNext, huNext, core, started, hstartNext, instruction, hassignment,
              htimeNext, hkind, consistent, output, hlocal, hcall, clockData,
              installation, selectedNext, hinstall, hresult, hdispatch,
              hpreparedNext, hrows, hselected, hrewards, hpayload, hvector,
              hownVector, hreconstruction, hcorrected, hrenewal, hanchor,
              hweights, hprevious, hrenewalPrevious, hselection, hvalues⟩
          · exact Or.inl hnotLater
          · refine Or.inr ⟨hlaterQ, hempty, haccepted, ?_⟩
            refine ⟨uNext, huNext, core, started, hstartNext, instruction,
              hassignment, htimeNext, hkind, consistent, output, hlocal, hcall,
              clockData, installation, selectedNext, hinstall, hresult,
              hdispatch, hpreparedNext, hrows, hselected, hrewards, hpayload,
              hvector, hownVector, hreconstruction, hweights, hselection, ?_⟩
            refine ⟨?_, ?_⟩
            · intro a
              rcases hvalues a with ⟨_hcut, _hcurrent, hscore, hqueue, hpq,
                hbaseScore, hcomplement⟩
              have hlenG : G.length = e + seg.records.length := by
                simpa only [q] using hG
              have htake : G.take (e + seg.records.length) = G := by
                rw [← hlenG, List.take_length]
              have hscoreG : AssignmentScoreReconstruction.sourceScore
                  output.reconstruction a =
                    (QueueReplay.replay (4 * rate.n) (0, 0) (raw a G)).1 := by
                change AssignmentScoreReconstruction.sourceScore output.reconstruction a =
                  (QueueReplay.replay (4 * rate.n) (0, 0)
                    (raw a (G.take (e + seg.records.length)))).1 at hscore
                rw [htake] at hscore
                exact hscore
              have hqueueG : AssignmentScoreReconstruction.initialQueue
                  output.reconstruction a =
                    (QueueReplay.replay (4 * rate.n) (0, 0) (raw a G)).2 := by
                change AssignmentScoreReconstruction.initialQueue output.reconstruction a =
                  (QueueReplay.replay (4 * rate.n) (0, 0)
                    (raw a (G.take (e + seg.records.length)))).2 at hqueue
                rw [htake] at hqueue
                exact hqueue
              have hUscore : (U a q).1 =
                  (QueueReplay.replay (4 * rate.n) (0, 0) (raw a G)).1 :=
                hscore.symm.trans hscoreG
              have hUqueue : (U a q).2 =
                  (QueueReplay.replay (4 * rate.n) (0, 0) (raw a G)).2 :=
                hqueue.symm.trans hqueueG
              refine ⟨hscoreG, hqueueG, ?_, ?_, ?_⟩
              · exact hpq.trans hUqueue
              · intro i hai
                rcases hbaseScore i hai with ⟨hbaseScore, hdown⟩
                exact ⟨hbaseScore.trans hUscore, hdown.trans hUqueue⟩
              · intro j hja
                rcases hcomplement j hja with ⟨hscoreJ, hqueueJ, hprev⟩
                exact ⟨hscoreJ.trans hUscore, hqueueJ.trans hUqueue,
                  hprev⟩
            · have hstep :=
                ReferenceCompleteEmptyInstallationNumericalStep.complete_empty_installation_current_numerical_step
                  (rate := rate) rewards C_star C_h z ⟨q, hv⟩
              simp only at hstep
              rw [hcoordQ] at hstep
              obtain ⟨uS, huS, coreS, startedS, hstartS, instructionS,
                hassignmentS, htimeS, hkindS, consistentS, outputS, hlocalS,
                hcallS, clockDataS, installationS, selectedS, hinstallS,
                hresultS, hdispatchS, hpreparedS, hpayloadS, hvectorS,
                hownVectorS, hbaseS, hqueuesS, hanchorS, birthSelection,
                hselectionS, hvpayloadS, hvcutoffS, hliveS, hstrictS, cNext,
                ho, cell, hreadout, hcell, hcellSelected, _hstates, _hmemories,
                _hunoccupied, henabled, hrate, hreward, hmarker, hrowsS,
                hselectedS, hrewardsS, _hfloor, _hcontribution, _hfollower,
                _howners, o, serviced, pending, finished, _hbridge, hrecord,
                hserviceRecord, _hraw, hservice, _hconfirmation, hfinish,
                hpostChoice, _hcoordinator, hnext, _hup⟩ := hstep hempty
              have huEq : uS = uNext := by
                apply Fin.ext
                omega
              subst uS
              have hstartedEq : startedS = started := by
                exact Except.ok.inj (hstartS.symm.trans hstartNext)
              clear hresultS
              subst startedS
              have hinstructionEq : instructionS = instruction := by
                exact Option.some.inj (hassignmentS.symm.trans hassignment)
              subst instructionS
              dsimp only [collectionInput] at hdispatchS hdispatch
              have hdispatchEq := hdispatchS.symm.trans hdispatch
              have houtputEq : outputS = output := by
                injection hdispatchEq
              subst outputS
              have hclockDataEq : clockDataS = clockData := by
                injection hdispatchEq
              subst clockDataS
              have hinstallationEq : installationS = installation := by
                injection hdispatchEq
              clear hinstallS
              subst installationS
              have hselectedEq : selectedS = selectedNext := by
                injection hdispatchEq
              subst selectedS
              have hlenG : G.length = e + seg.records.length := by
                simpa only [q] using hG
              have htake : G.take (e + seg.records.length) = G := by
                rw [← hlenG, List.take_length]
              have hnextLive : R[q].output.next.coordinator =
                  .live
                    { payload := installation.registers.payload
                      priorClock := finished.clock
                      pendingAtChoice := finished.pending
                      time := R[q].input.time
                      gridBoundary := finished.clock.g
                      complementScores := serviced.score }
                    { queue := serviced.queue
                      previousService := serviced.previousService }
                    installation.retainedBaseScore := by
                rw [hnext, hpostChoice]
              have hbirthAll : ∀ j : FastArm installation.registers.payload.slowSet,
                  (serviced.score j, serviced.queue j) =
                    QueueReplay.replay (4 * rate.n) (0, 0)
                      (raw j.val G ++ [(true, quantizedArrival
                        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cNext j.val)]) ∧
                  serviced.previousService j = serviced.score j -
                    (QueueReplay.replay (4 * rate.n) (0, 0) (raw j.val G)).1 := by
                intro j
                rcases hvalues j.val with ⟨_hcut, _hcurrent, hscore,
                  hqueue, _hpq, _hbaseScore, _hcomplement⟩
                have hscoreG : AssignmentScoreReconstruction.sourceScore
                    output.reconstruction j.val =
                      (QueueReplay.replay (4 * rate.n) (0, 0)
                        (raw j.val G)).1 := by
                  change AssignmentScoreReconstruction.sourceScore output.reconstruction j.val =
                    (QueueReplay.replay (4 * rate.n) (0, 0)
                      (raw j.val (G.take (e + seg.records.length)))).1 at hscore
                  rw [htake] at hscore
                  exact hscore
                have hqueueG : AssignmentScoreReconstruction.initialQueue
                    output.reconstruction j.val =
                      (QueueReplay.replay (4 * rate.n) (0, 0)
                        (raw j.val G)).2 := by
                  change AssignmentScoreReconstruction.initialQueue output.reconstruction j.val =
                    (QueueReplay.replay (4 * rate.n) (0, 0)
                      (raw j.val (G.take (e + seg.records.length)))).2 at hqueue
                  rw [htake] at hqueue
                  exact hqueue
                have hbirth : (serviced.score j, serviced.queue j) =
                    QueueReplay.replay (4 * rate.n) (0, 0)
                      (raw j.val G ++ [(true,
                        RecordedQueueRun.quantizedArrival
                          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                          cNext j.val)]) :=
                  (hservice j).2.1.trans (birth_replay (4 * rate.n)
                    (raw j.val G)
                    (AssignmentScoreReconstruction.sourceScore
                      output.reconstruction j.val)
                    (AssignmentScoreReconstruction.initialQueue
                      output.reconstruction j.val)
                    (RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                      cNext j.val) hscoreG hqueueG)
                have hprevious : serviced.previousService j = serviced.score j -
                    (QueueReplay.replay (4 * rate.n) (0, 0)
                      (raw j.val G)).1 := by
                  exact (hservice j).2.2.trans
                    (congrArg (fun score => serviced.score j - score) hscoreG)
                exact ⟨hbirth, hprevious⟩
              refine ⟨birthSelection, cNext, ho, cell, hselectionS,
                hvpayloadS, hvcutoffS, hliveS, hreadout, hcell,
                hcellSelected, henabled, hrate, hreward, hrowsS, hselectedS,
                hrewardsS, o, serviced, pending, finished, hrecord,
                hserviceRecord, (fun j => hservice j), hfinish, hnextLive, hbirthAll, ?_⟩
              by_cases hnextIndex : q + 1 < R.length
              · right
                refine ⟨hnextIndex, ?_⟩
                let nextIndex : Fin R.length := ⟨q + 1, hnextIndex⟩
                let birthRegisters :
                    CoordinatorLiveChoiceRecorderStep.Registers p rate.eta :=
                  { payload := installation.registers.payload
                    priorClock := finished.clock
                    pendingAtChoice := finished.pending
                    time := R[q].input.time
                    gridBoundary := finished.clock.g
                    complementScores := serviced.score }
                let birthOwned :
                    CoordinatorLiveServiceFinish.OwnedRegisters birthRegisters :=
                  { queue := serviced.queue
                    previousService := serviced.previousService }
                have hstateNext :
                    R[q + 1].input.state.coordinator =
                      .live birthRegisters birthOwned installation.retainedBaseScore := by
                  have hadj :=
                    ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
                      (rate := rate) rewards C_star C_h z q (by omega)
                  have hstateeq := congrArg
                    ReferenceActivePhysicalStep.State.coordinator hadj
                  rw [hnextLive] at hstateeq
                  simpa only [birthRegisters, birthOwned] using hstateeq
                have hlaterNext : s < birthRegisters.payload.sigma.val := by
                  simpa only [birthRegisters] using hstrictS
                refine ⟨hstateNext, hlaterNext, ?_⟩
                let WNext := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
                  rate rewards C_star C_h z (q + 1)
                let BNext := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
                  rewards C_star C_h z nextIndex birthRegisters birthOwned
                  installation.retainedBaseScore hstateNext hlaterNext
                obtain ⟨hlength, hmap, hunique, hcalendar, htimes, hsteps,
                  hprefixReplay, hmax⟩ :=
                  ReferenceCompleteLaterLiveComplementPrefixReplay.complete_later_live_complement_prefix_replay
                    (rate := rate) rewards C_star C_h z nextIndex birthRegisters birthOwned
                    installation.retainedBaseScore hstateNext hlaterNext
                refine ⟨hlength, hmap, hunique, hcalendar, htimes, ?_, ?_, ?_⟩
                · intro i
                  have hbound : nextIndex.val + i.val < R.length := by
                    have hlengthBound :=
                      ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_length_le
                        (rate := rate) rewards C_star C_h z nextIndex
                    have hi : i.val < WNext.length := i.isLt
                    exact Nat.lt_of_lt_of_le
                      (Nat.add_lt_add_left hi nextIndex.val) hlengthBound
                  obtain ⟨rv, qv, hp, hstateI, servicedI, finishedI, hreadI, henabledI,
                    hrewardI, hrateI, hcanonicalI, hrecordI, hfailureI, htransitionI,
                    hnextI⟩ := hsteps i
                  obtain ⟨physicalCell, _hcellI, _henabledI, _hliveI, _hrecordEnabledI,
                    hrowsI, hselectedI, hrewardsI, _hphysicalI⟩ :=
                    ReferenceLaterLiveNumericalReadout.laterLiveReadout_physical
                      rate rewards C_star C_h z ⟨nextIndex.val + i.val, hbound⟩ _ hreadI
                  have htest := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_test
                    (rate := rate) rewards C_star C_h z nextIndex i.val i.isLt
                  rw [ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_index
                    (rate := rate) rewards C_star C_h z nextIndex i.val i.isLt] at htest
                  exact ⟨rv, qv, hp, hstateI, hrowsI, hselectedI, hrewardsI, htest,
                    servicedI, finishedI, hreadI, henabledI, hrewardI, hrateI,
                    hcanonicalI, hrecordI, hfailureI, htransitionI, hnextI⟩
                · intro v hv
                  obtain ⟨rv, qv, hp, hlast, hboundary, hregisters⟩ := hprefixReplay v hv
                  refine ⟨rv, qv, hp, hlast, hboundary, ?_⟩
                  intro j
                  let jv : FastArm rv.payload.slowSet :=
                    ⟨j.val, by simpa only [hp] using j.property⟩
                  let Vseed := fun w => QueueReplay.replay (4 * rate.n)
                    (birthRegisters.complementScores j, birthOwned.queue j)
                    (raw j.val (BNext.take w))
                  have hseed := hregisters j
                  change (rv.complementScores jv, qv.queue jv) = Vseed v ∧
                    qv.previousService jv =
                      if v = 0 then birthOwned.previousService j
                      else (Vseed v).1 - (Vseed (v - 1)).1 at hseed
                  have hfull (w : ℕ) : Vseed w =
                      QueueReplay.replay (4 * rate.n) (0, 0)
                        (raw j.val G ++ [(true, quantizedArrival
                          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cNext j.val)] ++
                          raw j.val (BNext.take w)) := by
                    change QueueReplay.replay (4 * rate.n)
                      (serviced.score j, serviced.queue j) _ = _
                    rw [QueueReplay.replay_append, ← (hbirthAll j).1]
                  refine ⟨hseed.1.trans (hfull v), ?_⟩
                  by_cases hvzero : v = 0
                  · subst v
                    have hprevious : qv.previousService jv = serviced.previousService j := by
                      exact hseed.2.trans (ite_eq_left (show (0 : ℕ) = 0 from rfl))
                    have hbirthScore := congrArg Prod.fst (hbirthAll j).1
                    have hpreviousFull := hprevious.trans ((hbirthAll j).2.trans
                      (congrArg (fun score => score -
                        (QueueReplay.replay (4 * rate.n) (0, 0) (raw j.val G)).1)
                        hbirthScore))
                    exact hpreviousFull.trans
                      (ite_eq_left (show (0 : ℕ) = 0 from rfl)).symm
                  · have hprevious := hseed.2
                    simp only [ite_eq_right hvzero] at hprevious ⊢
                    rw [hfull v, hfull (v - 1)] at hprevious
                    exact hprevious
                · rcases hmax with hterminal | ⟨hcutoff, rv, qv, hp, hstateCutoff,
                    chosen, hpreparedCutoff, hcutoffOnly⟩
                  · left
                    exact hterminal
                  · cases chosen with
                    | cutoffChosen dispatched startRound_eq ledger initialization_eq
                        ledger_eq_candidate initializationDomainValid cutoff_clock cutoff_pending
                        no_assignment selection =>
                        right
                        exact ⟨hcutoff, rv, qv, hp, hstateCutoff, dispatched, startRound_eq,
                          ledger, initialization_eq, ledger_eq_candidate, initializationDomainValid,
                          cutoff_clock, cutoff_pending, no_assignment, selection, hpreparedCutoff⟩
                    | clockFailure failure dispatch_eq => cases hcutoffOnly
                    | initializerFailure dispatched startRound_eq checked checked_eq =>
                        cases hcutoffOnly
                    | localFailure dispatched startRound_eq reason => cases hcutoffOnly
                    | continuingChosen dispatched startRound_eq continuation selection =>
                        cases hcutoffOnly
              · left
                exact Nat.le_antisymm (Nat.succ_le_of_lt hv)
                  (Nat.le_of_not_gt hnextIndex)

end Bandits.Support.ReferenceFirstCorrectedNextOutsideCalendarReplay

end
