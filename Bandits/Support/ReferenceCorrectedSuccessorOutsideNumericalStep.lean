/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedNextInstallationNumericalSeed
public import Bandits.Support.ReferenceCompleteLaterLiveComplementPrefixReplay

/-!
# Actual birth and continuing outside-complement numerical preservation

This module joins the accepted actual empty-installation birth readout to the
accepted continuing later-LIVE complement prefix. The only conditional input
is a literal per-arm past word whose zero-origin replay agrees with the actual
reconstructed initial score and queue.

Sources: `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-174` under `sources/zip4/manuscript/`.
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

namespace Bandits.Support.ReferenceCorrectedSuccessorOutsideNumericalStep

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

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

/-- Extend the actual empty-collection installation through its current birth
row, and conditionally continue its actual outside-complement registers along
every following continuing live prefix. `E` is the unchanged literal past
word; the two equations are supplied by the actual first-successor seed (and
remain an explicit input for later cycles). -/
theorem complete_actual_birth_outside_complement_prefix_replay
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    let r := R[k.val]'k.isLt
    let x := r.input
    match x.state.coordinator with
    | .collection P l saved => l.pending = ∅ →
    ∃ u : Fin p.T, u.val + 1 = l.cutoff ∧
      let clock := collectionClock P l saved u
      let input := collectionInput x P l clock u
      ∃ (core : CollectionCoreValid input) (started : StartRoundResult p)
        (hstart : startRound p rate.eta.val x.time input.clock l.pending = .ok started)
        (instruction : AssignmentStartInstruction p)
        (hassignment : started.assignmentStart = some instruction),
        instruction.time = x.time ∧
        let operation := collectionOperationLedger input core.payload_n_eq
        ∃ (consistent : LocalConsistency P operation)
          (output : SuccessfulStart P operation instruction x.row)
          (hlocal : output.localConsistency = consistent)
          (clockData : LaterStartRoundEvidence output)
          (installation : LaterInstallation output clockData)
          (selected : ArmSelection installation.registers.payload started instruction.time
            installation.registers.complementWeights x.row),
          installation = installLater output clockData ∧
          ∃ (v : Selection x),
            r.output.preparation.coordinator.selection = some v ∧
            v.view.payload = installation.registers.payload ∧
            v.view.cutoff = none ∧
            CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff x.time ∧
            ∃ (c : RecordedQueueRun.RoundInput p.K)
              (ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary r)
              (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r),
              ReferenceLaterLiveNumericalReadout.laterLiveReadout
                (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) r =
                  some c ∧
              cell.input = c ∧ cell.selected = v ∧ c.enabled = true ∧
              c.rate = installation.registers.payload.rate ∧
              c.reward = (fun arm => ((rewards x.time arm).val : ℝ) / (D p : ℝ)) ∧
              r.input.rows = source.1.2 ∧ r.input.rewards = rewards ∧
              ∃ (o : CoordinatorRecordingOperation.Output p)
                (serviced : CoordinatorLiveServiceFinish.ServicedRegisters
                  installation.registers installation.ownedRegisters)
                (pending : Finset (Fin (p.m - 1)))
                (finished : FinishRoundResult p),
                r.output.coordinator.recording = some o ∧ serviced.recording = o ∧
                (∀ j, (serviced.score j, serviced.queue j) =
                  QueueReplay.transition (4 * rate.n)
                    (AssignmentScoreReconstruction.sourceScore output.reconstruction j.val,
                      AssignmentScoreReconstruction.initialQueue output.reconstruction j.val)
                    (true, RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val) ∧
                  serviced.previousService j = serviced.score j -
                    AssignmentScoreReconstruction.sourceScore output.reconstruction j.val) ∧
                finishRound p rate.eta.val x.time started.clock pending x.row = .ok finished ∧
                r.output.next.coordinator =
                  .live { payload := installation.registers.payload
                          priorClock := finished.clock
                          pendingAtChoice := finished.pending
                          time := x.time
                          gridBoundary := finished.clock.g
                          complementScores := serviced.score }
                    { queue := serviced.queue, previousService := serviced.previousService }
                    installation.retainedBaseScore ∧
                ∃ hstrict :
                  ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h <
                    installation.registers.payload.sigma.val,
                (∀ (j : FastArm installation.registers.payload.slowSet)
                  (E : List (Bool × ℕ)),
                  AssignmentScoreReconstruction.sourceScore output.reconstruction j.val =
                    (QueueReplay.replay (4 * rate.n) (0, 0) E).1 →
                  AssignmentScoreReconstruction.initialQueue output.reconstruction j.val =
                    (QueueReplay.replay (4 * rate.n) (0, 0) E).2 →
                  (serviced.score j, serviced.queue j) =
                    QueueReplay.replay (4 * rate.n) (0, 0)
                      (E ++ [(true, RecordedQueueRun.quantizedArrival
                        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val)]) ∧
                  serviced.previousService j = serviced.score j -
                    (QueueReplay.replay (4 * rate.n) (0, 0) E).1) ∧
                (k.val + 1 = R.length ∨
                  ∃ hnext : k.val + 1 < R.length,
                    let nextIndex : Fin R.length := ⟨k.val + 1, hnext⟩
                    let birthRegisters : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta :=
                      { payload := installation.registers.payload
                        priorClock := finished.clock
                        pendingAtChoice := finished.pending
                        time := x.time
                        gridBoundary := finished.clock.g
                        complementScores := serviced.score }
                    let birthOwned : CoordinatorLiveServiceFinish.OwnedRegisters birthRegisters :=
                      { queue := serviced.queue, previousService := serviced.previousService }
                    ∃ hstateNext :
                      (R[nextIndex.val]'nextIndex.isLt).input.state.coordinator =
                        .live birthRegisters birthOwned installation.retainedBaseScore,
                    ∃ hlater : ReferenceCompletePhysicalHistory.physicalStart
                      rate source rewards C_star C_h < birthRegisters.payload.sigma.val,
                    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
                      rate rewards C_star C_h source (k.val + 1)
                    let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
                      rewards C_star C_h source nextIndex birthRegisters birthOwned
                      installation.retainedBaseScore hstateNext hlater
                    ∃ hlength : B.length = W.length,
                    W.map (ReferenceLaterLiveNumericalReadout.laterLiveReadout
                      (ReferenceCompletePhysicalHistory.physicalStart
                        rate source rewards C_star C_h)) = B.map some ∧
                    (∀ cells : List (RecordedQueueRun.RoundInput p.K),
                      W.map (ReferenceLaterLiveNumericalReadout.laterLiveReadout
                        (ReferenceCompletePhysicalHistory.physicalStart
                          rate source rewards C_star C_h)) = cells.map some → cells = B) ∧
                    W.map (fun r => (r.input.time,
                      ReferenceLaterLiveNumericalReadout.laterLiveReadout
                        (ReferenceCompletePhysicalHistory.physicalStart
                          rate source rewards C_star C_h) r)) =
                      ((ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar
                        rate rewards C_star C_h source).drop nextIndex.val).take W.length ∧
                    W.map (fun r => r.input.time.val) =
                      List.range' (ReferenceCompletePhysicalHistory.physicalStart
                        rate source rewards C_star C_h + nextIndex.val) W.length ∧
                    (∀ i : Fin W.length,
                      let r := R[nextIndex.val + i.val]'(by
                        have hlengthBound := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_length_le
                          (rate := rate) rewards C_star C_h source nextIndex
                        have hi : nextIndex.val + W.length ≤ R.length := by
                          change nextIndex.val + W.length ≤ R.length
                          exact hlengthBound
                        omega)
                      let cell := B[i.val]'(by
                        rw [ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_length
                          (rate := rate) rewards C_star C_h source nextIndex birthRegisters birthOwned
                          installation.retainedBaseScore hstateNext hlater]
                        exact i.isLt)
                      ∃ (rv : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                        (qv : CoordinatorLiveServiceFinish.OwnedRegisters rv),
                        rv.payload = birthRegisters.payload ∧
                        r.input.state.coordinator = .live rv qv installation.retainedBaseScore ∧
                        ∃ (serviced : CoordinatorLiveServiceFinish.ServicedRegisters
                            (liveRegistersAt rv r.input.time) (liveOwnedAt rv qv r.input.time))
                          (finished : FinishRoundResult p),
                          ReferenceLaterLiveNumericalReadout.laterLiveReadout
                            (ReferenceCompletePhysicalHistory.physicalStart
                              rate source rewards C_star C_h) r = some cell ∧
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
                    (∀ (j : FastArm birthRegisters.payload.slowSet)
                      (E : List (Bool × ℕ)),
                      AssignmentScoreReconstruction.sourceScore output.reconstruction j.val =
                        (QueueReplay.replay (4 * rate.n) (0, 0) E).1 →
                      AssignmentScoreReconstruction.initialQueue output.reconstruction j.val =
                        (QueueReplay.replay (4 * rate.n) (0, 0) E).2 →
                      ∀ (v : ℕ) (hv : v ≤ W.length),
                        ∃ (rv : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                          (qv : CoordinatorLiveServiceFinish.OwnedRegisters rv)
                          (hp : rv.payload = birthRegisters.payload),
                          (∀ hpos : 0 < v,
                            (W[v - 1]'(by omega)).output.next.coordinator =
                              .live rv qv installation.retainedBaseScore) ∧
                          (∀ hboundary : nextIndex.val + v < R.length,
                            (R[nextIndex.val + v]'hboundary).input.state.coordinator =
                              .live rv qv installation.retainedBaseScore) ∧
                          let jv : FastArm rv.payload.slowSet :=
                            ⟨j.val, by simpa only [hp] using j.property⟩
                          (rv.complementScores jv, qv.queue jv) =
                            QueueReplay.replay (4 * rate.n) (0, 0)
                              (E ++ [(true, RecordedQueueRun.quantizedArrival
                                (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val)] ++
                                (B.take v).map (fun cell =>
                                  (cell.enabled, RecordedQueueRun.quantizedArrival
                                    (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                                      cell j.val))) ∧
                          qv.previousService jv =
                            (if v = 0 then
                              (QueueReplay.replay (4 * rate.n) (0, 0)
                                (E ++ [(true, RecordedQueueRun.quantizedArrival
                                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val)])).1 -
                                (QueueReplay.replay (4 * rate.n) (0, 0) E).1
                            else
                              (QueueReplay.replay (4 * rate.n) (0, 0)
                                (E ++ [(true, RecordedQueueRun.quantizedArrival
                                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val)] ++
                                  (B.take v).map (fun cell =>
                                    (cell.enabled, RecordedQueueRun.quantizedArrival
                                      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                                        cell j.val)))).1 -
                              (QueueReplay.replay (4 * rate.n) (0, 0)
                                (E ++ [(true, RecordedQueueRun.quantizedArrival
                                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val)] ++
                              (B.take (v - 1)).map (fun cell =>
                                    (cell.enabled, RecordedQueueRun.quantizedArrival
                                      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                                        cell j.val)))).1)) ∧
                    (nextIndex.val + W.length = R.length ∨
                      ∃ (hcutoff : nextIndex.val + W.length < R.length)
                        (rv : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                        (qv : CoordinatorLiveServiceFinish.OwnedRegisters rv),
                        rv.payload = birthRegisters.payload ∧
                        (R[nextIndex.val + W.length]'hcutoff).input.state.coordinator =
                          .live rv qv installation.retainedBaseScore ∧
                        ∃ (dispatched : CoordinatorStartRoundCutoffDispatch.Output
                            (liveInput (rate := rate)
                              (R[nextIndex.val + W.length]'hcutoff).input rv qv
                              installation.retainedBaseScore).registers
                            (liveInput (rate := rate)
                              (R[nextIndex.val + W.length]'hcutoff).input rv qv
                              installation.retainedBaseScore).ownedRegisters
                            (liveInput (rate := rate)
                              (R[nextIndex.val + W.length]'hcutoff).input rv qv
                              installation.retainedBaseScore).followerBaseScore)
                          (startRound_eq : CoordinatorPhaseClock.startRound p
                            (liveInput (rate := rate)
                              (R[nextIndex.val + W.length]'hcutoff).input rv qv
                              installation.retainedBaseScore).eta.val
                            (liveInput (rate := rate)
                              (R[nextIndex.val + W.length]'hcutoff).input rv qv
                              installation.retainedBaseScore).registers.time
                            (liveInput (rate := rate)
                              (R[nextIndex.val + W.length]'hcutoff).input rv qv
                              installation.retainedBaseScore).registers.priorClock
                            (liveInput (rate := rate)
                              (R[nextIndex.val + W.length]'hcutoff).input rv qv
                              installation.retainedBaseScore).registers.clockPending =
                                .ok dispatched.startResult)
                          (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger
                            (liveInput (rate := rate)
                              (R[nextIndex.val + W.length]'hcutoff).input rv qv
                              installation.retainedBaseScore).registers)
                          (initialization_eq :
                            dispatched.collectionInitialization = .success (some ledger))
                          (ledger_eq_candidate : ledger =
                            CoordinatorStartRoundCutoffDispatch.collectionStartLedger
                              (liveInput (rate := rate)
                                (R[nextIndex.val + W.length]'hcutoff).input rv qv
                                installation.retainedBaseScore).registers
                              (liveInput (rate := rate)
                                (R[nextIndex.val + W.length]'hcutoff).input rv qv
                                installation.retainedBaseScore).ownedRegisters
                              (liveInput (rate := rate)
                                (R[nextIndex.val + W.length]'hcutoff).input rv qv
                                installation.retainedBaseScore).followerBaseScore
                              (liveInput (rate := rate)
                                (R[nextIndex.val + W.length]'hcutoff).input rv qv
                                installation.retainedBaseScore).registers.time)
                          (initializationDomainValid :
                            CoordinatorStartRoundCutoffDispatch.initializationDomainValid
                              (liveInput (rate := rate)
                                (R[nextIndex.val + W.length]'hcutoff).input rv qv
                                installation.retainedBaseScore).registers
                              (liveInput (rate := rate)
                                (R[nextIndex.val + W.length]'hcutoff).input rv qv
                                installation.retainedBaseScore).ownedRegisters
                              (liveInput (rate := rate)
                                (R[nextIndex.val + W.length]'hcutoff).input rv qv
                                installation.retainedBaseScore).followerBaseScore
                              (liveInput (rate := rate)
                                (R[nextIndex.val + W.length]'hcutoff).input rv qv
                                installation.retainedBaseScore).registers.time)
                          (cutoff_clock : dispatched.startResult.clock =
                            { (liveInput (rate := rate)
                                (R[nextIndex.val + W.length]'hcutoff).input rv qv
                                installation.retainedBaseScore).registers.priorClock with
                              u := some (liveInput (rate := rate)
                                (R[nextIndex.val + W.length]'hcutoff).input rv qv
                                installation.retainedBaseScore).registers.time })
                          (cutoff_pending : dispatched.startResult.pending = Finset.univ)
                          (no_assignment : dispatched.startResult.assignmentStart = none)
                          (selection : ArmSelection
                            (liveInput (rate := rate)
                              (R[nextIndex.val + W.length]'hcutoff).input rv qv
                              installation.retainedBaseScore).registers.payload
                            dispatched.startResult
                            (liveInput (rate := rate)
                              (R[nextIndex.val + W.length]'hcutoff).input rv qv
                              installation.retainedBaseScore).registers.time
                            (liveInput (rate := rate)
                              (R[nextIndex.val + W.length]'hcutoff).input rv qv
                              installation.retainedBaseScore).registers.complementWeights
                            (liveInput (rate := rate)
                              (R[nextIndex.val + W.length]'hcutoff).input rv qv
                              installation.retainedBaseScore).row),
                          (R[nextIndex.val + W.length]'hcutoff).output.preparation.coordinator =
                            .live rv qv installation.retainedBaseScore
                              (.cutoffChosen dispatched startRound_eq ledger initialization_eq
                                ledger_eq_candidate initializationDomainValid cutoff_clock
                                cutoff_pending no_assignment selection)))
    | .first => x.state.coordinator = .first
    | .live registers owned base => x.state.coordinator = .live registers owned base
    | .dagger => x.state.coordinator = .dagger := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let r := R[k.val]'k.isLt
  let x := r.input
  cases hstate : x.state.coordinator with
  | first => rfl
  | live registers owned base => rfl
  | dagger => rfl
  | collection P l saved =>
      intro hempty
      have hstep :=
        ReferenceCompleteEmptyInstallationNumericalStep.complete_empty_installation_current_numerical_step
          (rate := rate) rewards C_star C_h source k
      simp only at hstep
      have hstateActual :
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator =
            .collection P l saved := by
        change x.state.coordinator = .collection P l saved at hstate
        exact hstate
      simp only [hstateActual] at hstep
      obtain ⟨u, hu, core, started, hstart, instruction, hassignment, htime,
        hkind, consistent, output, hlocal, hlaterStart, clockData, installation, selected,
        hinstall, hresult, hdispatch, hprepared, hpayload, hvector, hassignmentVector,
        hbase, hqueues, hanchor, v, hselection, hvpayload, hvcutoff, hlive, hstrict,
        c, ho, cell, hreadout, hcell, hcellSelected, hstates, hmemories,
        hunoccupiedAll, henabled, hrate, hreward, hmarker, hrows, hselected, hrewards,
        hfloor, hcontribution, hfollower, howners, o, serviced, pending, finished,
        hbridge, hrecord, hserviceRecord, hraw, hservice, hconfirmation, hfinish,
        hpostChoice, hcoordinator, hnext, hup⟩ := hstep hempty
      have hnextLive : r.output.next.coordinator =
          .live { payload := installation.registers.payload
                  priorClock := finished.clock
                  pendingAtChoice := finished.pending
                  time := x.time
                  gridBoundary := finished.clock.g
                  complementScores := serviced.score }
            { queue := serviced.queue, previousService := serviced.previousService }
            installation.retainedBaseScore := by
        rw [hnext, hpostChoice]
      have hserviceOutside : ∀ j : FastArm installation.registers.payload.slowSet,
          (serviced.score j, serviced.queue j) =
            QueueReplay.transition (4 * rate.n)
              (AssignmentScoreReconstruction.sourceScore output.reconstruction j.val,
                AssignmentScoreReconstruction.initialQueue output.reconstruction j.val)
              (true, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val) ∧
          serviced.previousService j = serviced.score j -
            AssignmentScoreReconstruction.sourceScore output.reconstruction j.val := by
        intro j
        exact ⟨(hservice j).2.1, (hservice j).2.2⟩
      refine ⟨u, hu, core, started, hstart, instruction, hassignment, htime,
        consistent, output, hlocal, clockData, installation, selected, hinstall,
        v, hselection, hvpayload, hvcutoff, hlive, c, ho, cell, hreadout, hcell,
        hcellSelected, henabled, hrate, hreward, hrows, hrewards, o, serviced,
        pending, finished, hrecord, hserviceRecord, hserviceOutside, hfinish, hnextLive,
        ⟨hstrict, ?_, ?_⟩⟩
      · intro j E hscore hqueue
        constructor
        · have htransition := (hserviceOutside j).1
          have hb := birth_replay (4 * rate.n) E
            (AssignmentScoreReconstruction.sourceScore output.reconstruction j.val)
            (AssignmentScoreReconstruction.initialQueue output.reconstruction j.val)
            (RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val) hscore hqueue
          rw [htransition]
          exact hb
        · simpa only [hscore] using (hserviceOutside j).2
      · by_cases hnextIndex : k.val + 1 < R.length
        · right
          refine ⟨hnextIndex, ?_⟩
          let nextIndex : Fin R.length := ⟨k.val + 1, hnextIndex⟩
          let birthRegisters : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta :=
            { payload := installation.registers.payload
              priorClock := finished.clock
              pendingAtChoice := finished.pending
              time := x.time
              gridBoundary := finished.clock.g
              complementScores := serviced.score }
          let birthOwned : CoordinatorLiveServiceFinish.OwnedRegisters birthRegisters :=
            { queue := serviced.queue, previousService := serviced.previousService }
          have hnextActual : (R[nextIndex.val]'nextIndex.isLt).input.state.coordinator =
              .live birthRegisters birthOwned installation.retainedBaseScore := by
            have hadj :=
              ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
                (rate := rate) rewards C_star C_h source k.val (by omega)
            have hstateeq := congrArg ReferenceActivePhysicalStep.State.coordinator hadj
            rw [hnextLive] at hstateeq
            simpa only [nextIndex, birthRegisters, birthOwned] using hstateeq
          have hlater' : ReferenceCompletePhysicalHistory.physicalStart
              rate source rewards C_star C_h < birthRegisters.payload.sigma.val := by
            simpa only [birthRegisters] using hstrict
          refine ⟨hnextActual, hlater', ?_⟩
          let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
            rate rewards C_star C_h source (k.val + 1)
          let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
            rewards C_star C_h source nextIndex birthRegisters birthOwned
            installation.retainedBaseScore hnextActual hlater'
          have hprefix :=
            ReferenceCompleteLaterLiveComplementPrefixReplay.complete_later_live_complement_prefix_replay
              (rate := rate) rewards C_star C_h source nextIndex birthRegisters birthOwned
              installation.retainedBaseScore hnextActual hlater'
          rcases hprefix with ⟨hlength, hmap, hunique, hcalendar, htimes, hsteps,
            hprefixReplay, hmax⟩
          refine ⟨hlength, ?_⟩
          constructor
          · exact hmap
          constructor
          · exact hunique
          constructor
          · exact hcalendar
          constructor
          · exact htimes
          constructor
          · simpa only [B] using hsteps
          constructor
          · intro j E hscore hqueue vIndex hvIndex
            have hcase := hprefixReplay vIndex hvIndex
            dsimp only at hcase
            rcases hcase with ⟨rv, qv, hp, hlast, hboundary, hregisters⟩
            let jv : FastArm rv.payload.slowSet :=
              ⟨j.val, by simpa only [hp] using j.property⟩
            have hregisters' := hregisters j
            have hbirth : (serviced.score j, serviced.queue j) =
                QueueReplay.replay (4 * rate.n) (0, 0)
                  (E ++ [(true, RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val)]) :=
              (hserviceOutside j).1.trans (birth_replay (4 * rate.n) E
                (AssignmentScoreReconstruction.sourceScore output.reconstruction j.val)
                (AssignmentScoreReconstruction.initialQueue output.reconstruction j.val)
                (RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val)
                hscore hqueue)
            have hqueueReplay : (rv.complementScores jv, qv.queue jv) =
                QueueReplay.replay (4 * rate.n) (0, 0)
                  (E ++ [(true, RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val)] ++
                    (B.take vIndex).map (fun cell =>
                      (cell.enabled, RecordedQueueRun.quantizedArrival
                        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                          cell j.val))) := by
              have hseeded := hregisters'.1
              change (rv.complementScores jv, qv.queue jv) =
                QueueReplay.replay (4 * rate.n)
                  (birthRegisters.complementScores j, birthOwned.queue j)
                  ((B.take vIndex).map (fun cell =>
                    (cell.enabled, RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                        cell j.val))) at hseeded
              dsimp only [birthRegisters, birthOwned] at hseeded
              rw [hbirth] at hseeded
              rw [← QueueReplay.replay_append] at hseeded
              simpa only [List.append_assoc, B] using hseeded
            have hprevious : qv.previousService jv =
                if vIndex = 0 then
                  (QueueReplay.replay (4 * rate.n) (0, 0)
                    (E ++ [(true, RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val)])).1 -
                    (QueueReplay.replay (4 * rate.n) (0, 0) E).1
                else
                  (QueueReplay.replay (4 * rate.n) (0, 0)
                    (E ++ [(true, RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val)] ++
                      (B.take vIndex).map (fun cell =>
                        (cell.enabled, RecordedQueueRun.quantizedArrival
                          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                            cell j.val)))).1 -
                  (QueueReplay.replay (4 * rate.n) (0, 0)
                    (E ++ [(true, RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val)] ++
                      (B.take (vIndex - 1)).map (fun cell =>
                        (cell.enabled, RecordedQueueRun.quantizedArrival
                          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                            cell j.val)))).1 := by
              by_cases hvzero : vIndex = 0
              · subst vIndex
                have hscoreBirth : serviced.score j =
                    (QueueReplay.replay (4 * rate.n) (0, 0)
                      (E ++ [(true, RecordedQueueRun.quantizedArrival
                        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val)])).1 := by
                  simpa only using congrArg Prod.fst hbirth
                calc
                  qv.previousService jv = birthOwned.previousService j := hregisters'.2
                  _ = serviced.previousService j := rfl
                  _ = serviced.score j -
                      AssignmentScoreReconstruction.sourceScore output.reconstruction j.val :=
                      (hserviceOutside j).2
                  _ = (QueueReplay.replay (4 * rate.n) (0, 0)
                        (E ++ [(true, RecordedQueueRun.quantizedArrival
                          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val)])).1 -
                      (QueueReplay.replay (4 * rate.n) (0, 0) E).1 := by
                    rw [hscoreBirth, hscore]
              · have hvpos : 0 < vIndex := Nat.pos_of_ne_zero hvzero
                simp only [if_neg hvzero] at hregisters'
                have hVnow : QueueReplay.replay (4 * rate.n)
                    (birthRegisters.complementScores j, birthOwned.queue j)
                    ((B.take vIndex).map (fun cell =>
                      (cell.enabled, RecordedQueueRun.quantizedArrival
                        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                          cell j.val))) =
                    QueueReplay.replay (4 * rate.n) (0, 0)
                      (E ++ [(true, RecordedQueueRun.quantizedArrival
                        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val)] ++
                        (B.take vIndex).map (fun cell =>
                          (cell.enabled, RecordedQueueRun.quantizedArrival
                            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                              cell j.val))) := by
                  have hnow := hregisters'.1
                  change (rv.complementScores jv, qv.queue jv) = _ at hnow
                  exact hnow.symm.trans hqueueReplay
                have hvPrev : vIndex - 1 ≤ W.length := Nat.le_trans (Nat.sub_le _ _) hvIndex
                have hcasePrev := hprefixReplay (vIndex - 1)
                  (by simpa only [W, nextIndex] using hvPrev)
                dsimp only at hcasePrev
                rcases hcasePrev with ⟨rvPrev, qvPrev, hpPrev, _, _, hregistersPrev⟩
                let jvPrev : FastArm rvPrev.payload.slowSet :=
                  ⟨j.val, by simpa only [hpPrev] using j.property⟩
                have hregistersPrev' := hregistersPrev j
                have hprevSeeded := hregistersPrev'.1
                change (rvPrev.complementScores jvPrev, qvPrev.queue jvPrev) =
                  QueueReplay.replay (4 * rate.n)
                    (birthRegisters.complementScores j, birthOwned.queue j)
                    ((B.take (vIndex - 1)).map (fun cell =>
                      (cell.enabled, RecordedQueueRun.quantizedArrival
                        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                          cell j.val))) at hprevSeeded
                dsimp only [birthRegisters, birthOwned] at hprevSeeded
                rw [hbirth] at hprevSeeded
                rw [← QueueReplay.replay_append] at hprevSeeded
                have hprevReplay : (rvPrev.complementScores jvPrev, qvPrev.queue jvPrev) =
                    QueueReplay.replay (4 * rate.n) (0, 0)
                      (E ++ [(true, RecordedQueueRun.quantizedArrival
                        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val)] ++
                        (B.take (vIndex - 1)).map (fun cell =>
                          (cell.enabled, RecordedQueueRun.quantizedArrival
                            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                              cell j.val))) := by
                  simpa only [List.append_assoc, B] using hprevSeeded
                have hVprev : QueueReplay.replay (4 * rate.n)
                    (birthRegisters.complementScores j, birthOwned.queue j)
                    ((B.take (vIndex - 1)).map (fun cell =>
                      (cell.enabled, RecordedQueueRun.quantizedArrival
                        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                          cell j.val))) =
                    QueueReplay.replay (4 * rate.n) (0, 0)
                      (E ++ [(true, RecordedQueueRun.quantizedArrival
                        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val)] ++
                        (B.take (vIndex - 1)).map (fun cell =>
                          (cell.enabled, RecordedQueueRun.quantizedArrival
                            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                              cell j.val))) := by
                  have hnow := hregistersPrev'.1
                  change (rvPrev.complementScores jvPrev, qvPrev.queue jvPrev) = _ at hnow
                  exact hnow.symm.trans hprevReplay
                have hpreviousSeed := hregisters'.2
                rw [hVnow, hVprev] at hpreviousSeed
                simpa only [if_neg hvzero] using hpreviousSeed
            exact ⟨rv, qv, hp, hlast, hboundary, hqueueReplay, hprevious⟩
          · rcases hmax with hterminal | ⟨hcutoff, rv, qv, hp, hstate,
              chosen, hpreparedCutoff, hcutoffOnly⟩
            · left
              simpa only [W, nextIndex, R] using hterminal
            · cases chosen with
              | cutoffChosen dispatched startRound_eq ledger initialization_eq
                  ledger_eq_candidate initializationDomainValid cutoff_clock cutoff_pending
                  no_assignment selection =>
                  right
                  refine ⟨?_, rv, qv, hp, hstate, dispatched, startRound_eq, ledger,
                    initialization_eq, ledger_eq_candidate, initializationDomainValid,
                    cutoff_clock, cutoff_pending, no_assignment, selection, hpreparedCutoff⟩
                  simpa only [W, nextIndex, R] using hcutoff
              | clockFailure failure dispatch_eq => cases hcutoffOnly
              | initializerFailure dispatched startRound_eq checked checked_eq =>
                  cases hcutoffOnly
              | localFailure dispatched startRound_eq reason => cases hcutoffOnly
              | continuingChosen dispatched startRound_eq continuation selection =>
                  cases hcutoffOnly
        · left
          change k.val + 1 =
            (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate source rewards C_star C_h).length
          have hk := k.isLt
          change ¬ k.val + 1 <
            (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate source rewards C_star C_h).length at hnextIndex
          omega

end Bandits.Support.ReferenceCorrectedSuccessorOutsideNumericalStep

end
