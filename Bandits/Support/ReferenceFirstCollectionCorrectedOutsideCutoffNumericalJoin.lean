/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCorrectedOutsideNumericalPrefix
public import Bandits.Support.ReferenceCompleteLaterLiveOutsideCutoffBoundary

import Mathlib.Data.List.TakeDrop

/-!
# Initialized corrected-birth outside cutoff and collection ledger

Sources: ZIP4 `06_interruptions.tex:23-100,192-233,246-299`,
`appendix_a_local_protocol.tex:28-64`, and `04_slow_fast_learner.tex:157-187`.
This is an internal deterministic join on the original physical execution.
The follower continuation and all-arm later-start consumer are separate.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstCollectionCorrectedOutsideCutoffNumericalJoin

open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open CanonicalFastSampling ReferenceCollectionSegmentExtraction

variable {p : ConstructorDimensions.Parameters}

/-- A score translation commutes with the physical queue fold. -/
private theorem replay_add_score (cap score queue : ℕ) (H : List (Bool × ℕ)) :
    QueueReplay.replay cap (score, queue) H =
      (score + (QueueReplay.replay cap (0, queue) H).1,
        (QueueReplay.replay cap (0, queue) H).2) := by
  induction H generalizing score queue with
  | nil => exact Prod.ext (Nat.add_zero score).symm rfl
  | cons record H ih =>
    change QueueReplay.replay cap (QueueReplay.transition cap (score, queue) record) H =
      (score + (QueueReplay.replay cap (QueueReplay.transition cap (0, queue) record) H).1,
        (QueueReplay.replay cap (QueueReplay.transition cap (0, queue) record) H).2)
    rw [CollectionKnownQueueContinuation.queueReplay_transition_add_score]
    let v := QueueReplay.transition cap (0, queue) record
    change QueueReplay.replay cap (score + v.1, v.2) H =
      (score + (QueueReplay.replay cap (v.1, v.2) H).1,
        (QueueReplay.replay cap (v.1, v.2) H).2)
    rw [ih (score + v.1) v.2, ih v.1 v.2]
    exact Prod.ext (Nat.add_assoc score v.1 _ ) rfl

/-- Both windows test the identical actual continuing constructor. -/
private theorem continuing_tests_eq {rate : ReferenceActivePhysicalStep.RateInput p} :
    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest (p := p) (rate := rate) =
      ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen := by
  funext r
  unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
    ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
  cases r.output.preparation.coordinator with
  | live r q base chosen => cases chosen <;> rfl
  | first _ | collection _ _ _ _ _ | invalidCollectionCutoff | dagger => rfl

/-- Actual segment extraction retains one input for every physical date. -/
private theorem segment_calendar {rate : ReferenceActivePhysicalStep.RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (e : ℕ) (seg : Segment rate)
    (hseg : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg) :
    seg.inputs.map (fun input => input.round.val) =
      List.range' (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e)
        seg.records.length ∧ seg.inputs.length = seg.records.length := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hb := (segmentAt_branch R e seg hseg).1
  have hcal := segment_input_calendar (R.drop e) seg hb
  have hcount := segment_input_count (R.drop e) seg hb
  have hpart := segmentAt_partition R e seg hseg
  have hle : seg.records.length ≤ R.length - e := by
    have hh := congrArg List.length hpart
    simp only [List.length_append, List.length_drop] at hh
    omega
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  change R.map (fun r => r.input.time.val) = List.range' s (p.T - s) at htimes
  have hlen : R.length = p.T - s := by
    have hh := congrArg List.length htimes
    simpa only [List.length_map, List.length_range'] using hh
  rw [List.map_drop, htimes, List.drop_range', Nat.mul_one,
    List.take_range'_of_length_ge (by omega)] at hcal
  exact ⟨hcal, hcount⟩

/-- The collection freeze guard is already part of its enabled bit. -/
private theorem local_record_eq {rate : ReferenceActivePhysicalStep.RateInput p}
    (l : Ledger rate) (tau : Fin p.T) (c : RecordedQueueRun.RoundInput p.K)
    (raw : Option (Fin p.K × ℕ)) (a : Fin p.K)
    (henabled : c.enabled = collectionEnabled l tau)
    (harrival : CoordinatorCollectionLedger.localArrival raw a =
      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) :
    CoordinatorCollectionLedger.localQueueRecord l tau (collectionEnabled l tau) raw a =
      UnstoppedRecordedQueueComparison.unstoppedRecord
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a := by
  unfold CoordinatorCollectionLedger.localQueueRecord
    UnstoppedRecordedQueueComparison.unstoppedRecord
  rw [henabled]
  by_cases he : collectionEnabled l tau = true
  · have hfreeze : tau.val + 1 < l.freezeAt := (of_decide_eq_true he).2.2
    simp only [he, CoordinatorCollectionLedger.sourceRound, hfreeze, decide_true,
      Bool.and_self, ite_true, harrival]
  · have he' : collectionEnabled l tau = false := Bool.eq_false_iff.mpr he
    simp only [he', Bool.false_and, Bool.false_eq_true, ite_false]

/-- Initialize the actual corrected-birth outside cutoff from the original
numerical prefix, apply its first collection update once, and identify the
whole same segment's final ledger. Horizon and current failure cases remain
literal; no successful later assignment or analytical survival is assumed. -/
theorem firstCell_outside_cutoff_numerical_join
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
      let R := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h z
    let s := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h z
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
      ∃ (L : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
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
        ∃ next : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
          R[b + 1]? = some next ∧
          ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h ⟨t.val + 1, hq⟩ z = some next ∧
          next.input.time = ⟨t.val + 1, hq⟩ ∧ next.input.state = birth.output.next ∧
          next.input.rows = z.1.2 ∧
          next.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
          next.input.rewards = rewards) ∧
      (∀ (rout : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (qout : CoordinatorLiveServiceFinish.OwnedRegisters rout)
        (beta : Fin (p.m - 1) → ℕ),
        birth.output.next.coordinator = .live rout qout beta →
        rout.payload.sigma = t ∧
        ∀ _hq : t.val + 1 < p.T,
          ∃ (next : RoundRecord (p := p) (rate := rate))
            (hk : b + 1 < R.length)
            (hstate : (R[b + 1]'hk).input.state.coordinator = .live rout qout beta)
            (hlater : s < rout.payload.sigma.val),
            R[b + 1]? = some next ∧ next.input.state = birth.output.next ∧
            let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
              rate rewards C_star C_h z (b + 1)
            let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
              rewards C_star C_h z ⟨b + 1, hk⟩ rout qout beta hstate hlater
            B.length = W.length ∧ b + 1 + W.length ≤ R.length ∧
            t.val + 1 + W.length ≤ p.T ∧
            W.map (fun r => r.input.time.val) = List.range' (t.val + 1) W.length ∧
            (∀ (v : ℕ) (hv : v ≤ W.length),
              let A := (L ++ [c]) ++ B.take v
              ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                rate rewards C_star C_h (t.val + 1 + v) z = some A ∧
              A.length = b + 1 + v ∧ s + A.length = t.val + 1 + v ∧
              (∀ hi : b + 1 + v < R.length,
                (R[b + 1 + v]).input.time.val = t.val + 1 + v) ∧
              ∃ (rv : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                (qv : CoordinatorLiveServiceFinish.OwnedRegisters rv)
                (hp : rv.payload = rout.payload),
                (∀ hpos : 0 < v,
                  (W[v - 1]'(by omega)).output.next.coordinator = .live rv qv beta) ∧
                (∀ hi : b + 1 + v < R.length,
                  (R[b + 1 + v]).input.state.coordinator = .live rv qv beta) ∧
                ∀ j : FastArm rout.payload.slowSet,
                  let jv : FastArm rv.payload.slowSet :=
                    ⟨j.val, by simpa only [hp] using j.property⟩
                  (rv.complementScores jv, qv.queue jv) =
                    UnstoppedRecordedQueueComparison.unstoppedReplay
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) A A.length j.val ∧
                  qv.previousService jv =
                    (UnstoppedRecordedQueueComparison.unstoppedReplay
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) A A.length j.val).1 -
                    (UnstoppedRecordedQueueComparison.unstoppedReplay
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                      (A.take (A.length - 1)) (A.take (A.length - 1)).length j.val).1) ∧
            let n := W.length
            let e := b + 1 + n
            let A := (L ++ [c]) ++ B
            let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
            let P := fun (j : FastArm rout.payload.slowSet) =>
              UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length j.val
            let d := fun (j : FastArm rout.payload.slowSet) => (P j).1 -
              (UnstoppedRecordedQueueComparison.unstoppedReplay Q
                (A.take (A.length - 1)) (A.take (A.length - 1)).length j.val).1
            ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
              rate rewards C_star C_h (t.val + 1 + n) z = some A ∧
            A.length = e ∧ s + e = t.val + 1 + n ∧
            ∃ (rE : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
              (qE : CoordinatorLiveServiceFinish.OwnedRegisters rE)
              (hp : rE.payload = rout.payload),
              (∀ hpos : 0 < n, (W[n - 1]'(by omega)).output.next.coordinator = .live rE qE beta) ∧
              (∀ he : e < R.length, (R[e]'he).input.state.coordinator = .live rE qE beta) ∧
              (∀ j : FastArm rout.payload.slowSet,
                let jE : FastArm rE.payload.slowSet := ⟨j.val, by simpa only [hp] using j.property⟩
                (rE.complementScores jE, qE.queue jE) = P j ∧ qE.previousService jE = d j) ∧
              (e = R.length ∨
                ∃ (he : e < R.length)
                  (chosen : CoordinatorRoundDispatch.LiveOutcome
                    (liveInput (R[e]'he).input rE qE beta)),
                  chosen = CoordinatorRoundDispatch.dispatchLive
                    (liveInput (R[e]'he).input rE qE beta) ∧
                  (R[e]'he).output.preparation.coordinator = .live rE qE beta chosen ∧
                  match chosen with
                  | .cutoffChosen dispatched _ ledger _ _ _ _ _ _ _ =>
                    let cut := R[e]'he
                    let tau := cut.input.time
                    let uc := tau.val + 1
                    let l0 := sharedLedger ledger
                    tau.val = s + e ∧ tau.val = t.val + 1 + n ∧
                    uc = s + e + 1 ∧
                    uc = FollowerCutoffScan.firstCutoff p rate.eta.val rout.payload.sigma
                      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) ∧
                    ∃ (seg : Segment rate) (I : Initializer p),
                      segmentAt R e = some seg ∧ seg.entry = cut ∧
                      seg.context.payload = rout.payload ∧ seg.context.preLedger = l0 ∧
                      seg.context.initializer = some I ∧
                      I = cutoffInitializer (liveRegistersAt rE tau) (liveOwnedAt rE qE tau) beta tau ∧
                      I.checkedStart rate = .success l0 ∧
                      I.assignment.arm = rout.payload.assignment.assigned ∧
                      I.sigma = t.val + 1 ∧ I.cutoff = uc ∧
                      I.freezeAt = rE.gridBoundary ∧ I.base = beta ∧
                      (∃ tail, seg.records = cut :: tail) ∧
                      seg.records ++ seg.remaining = R.drop e ∧ seg.exit = exitOf seg.remaining ∧
                      CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
                        (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
                        I.assignment I.sigma I.cutoff I.freezeAt I.base I.outside seg.inputs =
                          .success ⟨l0, seg.accepted, seg.final⟩ ∧
                      seg.inputs.map (fun input => input.round.val) =
                        List.range' tau.val seg.records.length ∧
                      seg.inputs.length = seg.records.length ∧ 0 < seg.records.length ∧
                      (∀ j : FastArm rout.payload.slowSet,
                        I.outside j.val = some ⟨(P j).1, (P j).2, d j⟩ ∧
                        l0.cutoffRegisters j.val = some ⟨(P j).1, (P j).2, d j⟩ ∧
                        l0.currentRegisters j.val = some ⟨(P j).2, d j⟩ ∧ l0.increment j.val = 0) ∧
                      (∀ i, l0.cutoffRegisters (rout.payload.assignment.assigned i) = none ∧
                        l0.currentRegisters (rout.payload.assignment.assigned i) = none) ∧
                      ∃ c_cut : RecordedQueueRun.RoundInput p.K,
                        ReferenceFirstCollectionCurrentRetainedGate.cell0 rate cut = some c_cut ∧
                        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 cut = some c_cut ∧
                        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                          rate rewards C_star C_h (tau.val + 1) z = some (A ++ [c_cut]) ∧
                        c_cut.enabled = collectionEnabled l0 tau ∧
                        c_cut.rate = rout.payload.rate ∧
                        c_cut.reward = (fun a => ((rewards tau a).val : ℝ) / (D p : ℝ)) ∧
                      ∃ (recording : CoordinatorRecordingOperation.Output p)
                        (started decoded : Ledger rate) (bank : CoordinatorUpReception.UpDecoderBank p)
                        (lf : Ledger rate) (clock : CoordinatorPhaseClock.FinishRoundResult p),
                        cut.output.coordinator.recording = some recording ∧
                        CoordinatorRecorderComplementBridge.run
                          (collectionRecordingInput cut.output.preparation rE.payload
                            dispatched.startResult (liveRegistersAt rE tau).complementWeights) = some recording ∧
                        CoordinatorCollectionLedger.startRound l0 uc (collectionEnabled l0 tau)
                          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) = .success started ∧
                        (receiveUp cut.output.preparation started).result = .rejected (decoded, bank) ∧
                        decoded = { started with phase := CoordinatorCollectionLedger.Phase.decoded } ∧
                        CoordinatorCollectionLedger.finishRound decoded = .success lf ∧
                        CoordinatorPhaseClock.finishRound p rate.eta.val tau
                          dispatched.startResult.clock lf.pending cut.input.row = .ok clock ∧
                        cut.output.next.coordinator = .collection rout.payload lf clock.clock.lastProposal ∧
                        cut.output.coordinator.failure = none ∧
                        lf.baseScore = beta ∧ lf.gammaLoc = (fun _ => 0) ∧
                        (∀ a, CoordinatorCollectionLedger.localArrival
                          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) a =
                            RecordedQueueRun.quantizedArrival Q c_cut a) ∧
                        (∀ j : FastArm rout.payload.slowSet,
                          let D_j := CoordinatorCollectionLedger.localQueueRecord l0 tau
                            (collectionEnabled l0 tau)
                            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) j.val
                          let Pplus := UnstoppedRecordedQueueComparison.unstoppedReplay Q
                            (A ++ [c_cut]) (A ++ [c_cut]).length j.val
                          D_j = UnstoppedRecordedQueueComparison.unstoppedRecord Q c_cut j.val ∧
                          Pplus = QueueReplay.transition (4 * rate.n) (P j) D_j ∧
                          lf.cutoffRegisters j.val = some ⟨(P j).1, (P j).2, d j⟩ ∧
                          lf.currentRegisters j.val = some ⟨Pplus.2, Pplus.1 - (P j).1⟩ ∧
                          lf.increment j.val = Pplus.1 - (P j).1) ∧
                        (∀ j : FastArm rout.payload.slowSet,
                          let H := CollectionKnownQueueContinuation.inputQueueRecords l0 j.val seg.inputs
                          let Y := QueueReplay.replay (4 * rate.n) (0, (P j).2) H
                          let F := QueueReplay.replay (4 * rate.n) (0, 0)
                            ((A.map fun x => UnstoppedRecordedQueueComparison.unstoppedRecord Q x j.val) ++ H)
                          let last := CollectionKnownQueueContinuation.replayLastService
                            (4 * rate.n) (0, (P j).2) (d j) H
                          seg.final.cutoffRegisters j.val = some ⟨(P j).1, (P j).2, d j⟩ ∧
                          seg.final.currentRegisters j.val = some ⟨F.2, last⟩ ∧
                          seg.final.increment j.val = Y.1 ∧
                          seg.final.increment j.val = F.1 - (P j).1 ∧
                          F = ((P j).1 + Y.1, Y.2) ∧
                          H.length = seg.inputs.length ∧ H.length = seg.records.length ∧
                          0 < H.length)
                  | _ => False)) := by
  classical
  intro R s b
  obtain ⟨L, c, birth, hL, hc, hprefix, hLb, hbsub, htime, henabled,
    hb, har, ht, hrows, hselected, hrewards, hcurrent, hnext, hcont⟩ :=
    ReferenceFirstCollectionCorrectedOutsideNumericalPrefix.firstCell_outside_prefix
      rate rewards C_star C_h u t z hz
  dsimp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] at hcont
  refine ⟨L, c, birth, hL, hc, hprefix, hLb, hbsub, htime, henabled,
    hb, har, ht, hrows, hselected, hrewards, hcurrent, hnext, ?_⟩
  intro rout qout beta hlive
  obtain ⟨hsigma, htail⟩ := hcont rout qout beta hlive
  refine ⟨hsigma, ?_⟩
  intro hq
  obtain ⟨next, hk, hstate, hlater, hn, hnstate, hB, hbound, hT, htimes, hends⟩ := htail hq
  refine ⟨next, hk, hstate, hlater, hn, hnstate, hB, hbound, hT, htimes, hends, ?_⟩
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix rate rewards C_star C_h z (b + 1)
  let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
    rewards C_star C_h z ⟨b + 1, hk⟩ rout qout beta hstate hlater
  let n := W.length
  let e := b + 1 + n
  let A := (L ++ [c]) ++ B
  let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let P := fun (j : FastArm rout.payload.slowSet) =>
    UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length j.val
  let d := fun (j : FastArm rout.payload.slowSet) => (P j).1 -
    (UnstoppedRecordedQueueComparison.unstoppedReplay Q
      (A.take (A.length - 1)) (A.take (A.length - 1)).length j.val).1
  change b + 1 < (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h).length at hk
  change ((ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h)[b + 1]'hk).input.state.coordinator = .live rout qout beta at hstate
  change ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h <
    rout.payload.sigma.val at hlater
  have hO := ReferenceCompleteLaterLiveOutsideCutoffBoundary.complete_later_live_outside_cutoff_boundary
    rate rewards C_star C_h z ⟨b + 1, hk⟩
  dsimp only at hO
  split at hO
  next r0 q0 base hconfig =>
    have heq := hconfig.symm.trans hstate
    cases heq
    obtain ⟨rE, qE, hp, hout, hin, hvalues, hboundary⟩ := hO hlater
    obtain ⟨hAprefix, hAlength, hAdate, hEdate, rv, qv, hpv, hvout, hvin, hvvalues⟩ := hends n le_rfl
    have htB : B.take n = B := List.take_of_length_le (le_of_eq hB)
    rw [htB] at hAprefix hAlength hAdate hvvalues
    have hsame : CoordinatorConfiguration.live rv qv beta = .live rE qE beta := by
      by_cases he : e < R.length
      · exact (hvin he).symm.trans (hin he)
      · have hpos : 0 < n := by
          change b + 1 + n ≤ R.length at hbound
          change b + 1 < R.length at hk
          omega
        exact (hvout hpos).symm.trans (hout hpos)
    have hseed : ∀ j : FastArm rout.payload.slowSet,
        (QueueReplay.replay (4 * rate.n) (rout.complementScores j, qout.queue j)
          ((B.take n).map fun c => (c.enabled, RecordedQueueRun.quantizedArrival Q c j.val))) = P j ∧
        (if n = 0 then qout.previousService j else
          (QueueReplay.replay (4 * rate.n) (rout.complementScores j, qout.queue j)
            ((B.take n).map fun c => (c.enabled, RecordedQueueRun.quantizedArrival Q c j.val))).1 -
          (QueueReplay.replay (4 * rate.n) (rout.complementScores j, qout.queue j)
            ((B.take (n - 1)).map fun c => (c.enabled, RecordedQueueRun.quantizedArrival Q c j.val))).1) = d j := by
      cases hsame
      intro j
      exact ⟨(hvalues j).1.symm.trans (hvvalues j).1,
        (hvalues j).2.symm.trans (hvvalues j).2⟩
    change A.length = e at hAlength
    change s + A.length = t.val + 1 + n at hAdate
    have hdate : s + e = t.val + 1 + n := by
      rw [← hAlength]
      exact hAdate
    refine ⟨hAprefix, hAlength, hdate, rE, qE, hp, hout, hin, ?_, ?_⟩
    · intro j
      exact ⟨(hvalues j).1.trans (hseed j).1, (hvalues j).2.trans (hseed j).2⟩
    · rcases hboundary with hend | ⟨he, chosen, hchosen, hprep, hcut⟩
      · exact Or.inl hend
      · refine Or.inr ⟨he, chosen, hchosen, hprep, ?_⟩
        cases chosen with
        | clockFailure => exact hcut
        | initializerFailure => exact hcut
        | localFailure => exact hcut
        | continuingChosen => exact hcut
        | cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending hno selected =>
          let cut := R[e]'he
          let tau := cut.input.time
          let uc := tau.val + 1
          let l0 := sharedLedger ledger
          obtain ⟨huc, hfirstCutoff, seg, I, hseg, hentry, hpayload, hpre, hI,
            hinitializer, hchecked, hassignment, hIsigma, hIcutoff, hfreeze, hbase,
            hnonempty, hpartition, hexit, hfold, hknown, hfollowers,
            recording, started, decoded, bank, lf, clock, hrecord, hrun,
            hstartLedger, hreceive, hdecoded, hfinish, hclockFinish, hnextCollection,
            hfailure, hbaseScore, hgamma, hfirstUpdate, hfinal⟩ := hcut
          have htau' : tau.val = t.val + 1 + n := hEdate he
          have htau : tau.val = s + e := htau'.trans hdate.symm
          have hknown' (j : FastArm rout.payload.slowSet) :
              I.outside j.val = some ⟨(P j).1, (P j).2, d j⟩ ∧
              l0.cutoffRegisters j.val = some ⟨(P j).1, (P j).2, d j⟩ ∧
              l0.currentRegisters j.val = some ⟨(P j).2, d j⟩ ∧ l0.increment j.val = 0 := by
            have hh := hknown j
            rw [(hseed j).2, (hseed j).1] at hh
            exact hh
          have hW : W = ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
              rate rewards C_star C_h z := by
            unfold W ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
              ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
              ReferenceFirstReplacementLiveFollowerPrefix.continuingTail
              ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
            rw [continuing_tests_eq]
          have hcc := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_cutoff_cell
            rate rewards C_star C_h u t z hz
          rw [← hW] at hcc
          have hget : (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
              rate rewards C_star C_h z)[b + 1 + W.length]? = some cut :=
            List.getElem?_eq_getElem he
          change cut.output.preparation.coordinator = _ at hprep
          rw [hget] at hcc
          dsimp only at hcc
          rw [hprep] at hcc
          dsimp only at hcc
          obtain ⟨_hcutTime, _hgrid, _hcause, _hcutRows, _hcutJ, hcutRewards,
            c_cut, hcell, _hcutEnabled, hreward⟩ := hcc
          have hnotLive : ¬ CoordinatorLocalArmChoice.assignmentIsLive rE.payload
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u) tau := by
            rw [hclock]
            change ¬ (CoordinatorLocalArmChoice.assignmentStart rE.payload ≤ tau.val + 1 ∧
              tau.val + 1 < tau.val + 1)
            exact fun h => Nat.lt_irrefl _ h.2
          have hnoLiveReadout : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 cut = none := by
            simp only [ReferenceLaterLiveNumericalReadout.laterLiveReadout, hprep,
              DispatchCut.selection, selectionAt]
            exact ite_eq_right (fun h => hnotLive h.2)
          have hcollection : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 cut =
              some c_cut := by
            simpa only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hnoLiveReadout,
              Option.none_or] using hcell
          obtain ⟨payload', ledger', started', weights', out, hcall, _hpost, _houtRun,
            hcellEnabled, _hclockEnabled, hcellRate, _hcellReward, hdiagnostic, _hgate, harrival⟩ :=
            ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call 0 cut c_cut hcollection
          have hunoccupied := ((ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain
            0 cut).mp (by rw [hcollection]; rfl)).1
          have hpositive : 0 < rE.payload.sigma.val := by
            rw [hp]
            omega
          have hcall' : ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 cut =
              some ⟨rE.payload, l0, dispatched.startResult,
                (liveRegistersAt rE tau).complementWeights⟩ := by
            simp only [ReferenceLaterCollectionArrivalReadout.laterCollectionCall,
              hunoccupied, ite_true, hprep, hpositive]
            rfl
          have hargs := Option.some.inj (hcall'.symm.trans hcall)
          have hledger : l0 = ledger' := congrArg (fun args => args.2.1) hargs
          have hpay : rE.payload = payload' := congrArg Sigma.fst hargs
          rw [← hledger] at hcellEnabled
          rw [← hpay, hp] at hcellRate
          have houtEq : out = recording := Option.some.inj (hdiagnostic.symm.trans hrecord)
          subst out
          have hprefixCut : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
              rate rewards C_star C_h (tau.val + 1) z = some (A ++ [c_cut]) := by
            have hprefixTau : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                rate rewards C_star C_h tau.val z = some A := by
              rw [htau']
              exact hAprefix
            exact ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_append_one
              rate rewards C_star C_h tau.val z A hprefixTau cut c_cut
              (by change R[tau.val - s]? = some cut; rw [htau, Nat.add_sub_cancel_left];
                  exact List.getElem?_eq_getElem he) hcell
          obtain ⟨hcalendar, hcount⟩ := segment_calendar rewards C_star C_h z e seg hseg
          change seg.inputs.map (fun input => input.round.val) =
            List.range' (s + e) seg.records.length at hcalendar
          rw [← htau] at hcalendar
          have hnonzero : 0 < seg.records.length := by
            obtain ⟨tail, htail⟩ := hnonempty
            rw [htail, List.length_cons]
            omega
          refine ⟨htau, htau', huc, hfirstCutoff, seg, I, hseg, hentry, hpayload, hpre,
            hI, hinitializer, hchecked, hassignment, ?_, hIcutoff, hfreeze, hbase,
            hnonempty, hpartition, hexit, hfold, hcalendar, hcount, hnonzero,
            hknown', hfollowers, c_cut, hcell, hcollection, hprefixCut, hcellEnabled,
            hcellRate, hreward, recording, started, decoded, bank, lf, clock,
            hrecord, hrun, hstartLedger, hreceive, hdecoded, hfinish, hclockFinish,
            hnextCollection, hfailure, hbaseScore, hgamma, harrival, ?_, ?_⟩
          · exact hIsigma.trans (by rw [hsigma])
          · intro j
            let Dj := CoordinatorCollectionLedger.localQueueRecord l0 tau
              (collectionEnabled l0 tau)
              (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) j.val
            have hD : Dj = UnstoppedRecordedQueueComparison.unstoppedRecord Q c_cut j.val :=
              local_record_eq l0 tau c_cut _ j.val hcellEnabled (harrival j.val)
            have hplus : UnstoppedRecordedQueueComparison.unstoppedReplay Q
                (A ++ [c_cut]) (A ++ [c_cut]).length j.val =
                QueueReplay.transition (4 * rate.n) (P j) Dj := by
              rw [hD]
              unfold UnstoppedRecordedQueueComparison.unstoppedReplay
              rw [List.take_length, List.map_append, QueueReplay.replay_append]
              change QueueReplay.transition (4 * rate.n)
                (QueueReplay.replay (4 * rate.n) (0, 0)
                  (A.map fun x => UnstoppedRecordedQueueComparison.unstoppedRecord Q x j.val))
                (UnstoppedRecordedQueueComparison.unstoppedRecord Q c_cut j.val) = _
              have hpref : QueueReplay.replay (4 * rate.n) (0, 0)
                  (A.map fun x => UnstoppedRecordedQueueComparison.unstoppedRecord Q x j.val) = P j := by
                change _ = UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length j.val
                unfold UnstoppedRecordedQueueComparison.unstoppedReplay
                rw [List.take_length]
                rfl
              rw [hpref]
            have hh := hfirstUpdate j
            rw [(hseed j).1] at hh
            change lf.cutoffRegisters j.val = l0.cutoffRegisters j.val ∧
              lf.currentRegisters j.val = some
                ⟨(QueueReplay.transition (4 * rate.n) (P j) Dj).2,
                  (QueueReplay.transition (4 * rate.n) (P j) Dj).1 - (P j).1⟩ ∧
              lf.increment j.val = (QueueReplay.transition (4 * rate.n) (P j) Dj).1 - (P j).1 at hh
            rw [← hplus] at hh
            exact ⟨hD, hplus, hh.1.trans (hknown' j).2.1, hh.2⟩
          · intro j H Y F last
            have hh := hfinal j
            rw [(hseed j).2, (hseed j).1] at hh
            have hF : F = ((P j).1 + Y.1, Y.2) := by
              change QueueReplay.replay (4 * rate.n) (0, 0)
                ((A.map fun x => UnstoppedRecordedQueueComparison.unstoppedRecord Q x j.val) ++ H) = _
              rw [QueueReplay.replay_append]
              have hpref : QueueReplay.replay (4 * rate.n) (0, 0)
                  (A.map fun x => UnstoppedRecordedQueueComparison.unstoppedRecord Q x j.val) = P j := by
                change _ = UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length j.val
                unfold UnstoppedRecordedQueueComparison.unstoppedReplay
                rw [List.take_length]
                rfl
              rw [hpref]
              exact replay_add_score (4 * rate.n) (P j).1 (P j).2 H
            have hHlength : H.length = seg.inputs.length := List.length_map _
            refine ⟨hh.1, ?_, hh.2.2.1, ?_, hF, hHlength, hHlength.trans hcount, ?_⟩
            · rw [hF]
              exact hh.2.1
            · rw [hF, Nat.add_sub_cancel_left]
              exact hh.2.2.1
            · rw [hHlength, hcount]
              exact hnonzero
  all_goals
    rename_i hconfig
    exact False.elim (hconfig rout qout beta hstate)

end Bandits.Support.ReferenceFirstCollectionCorrectedOutsideCutoffNumericalJoin
