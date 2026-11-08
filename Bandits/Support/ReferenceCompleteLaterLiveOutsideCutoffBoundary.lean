/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteLaterLiveComplementPrefixReplay
public import Bandits.Support.ReferenceCompleteAcceptedUpLedgerNumericalReplay

import Lean.Elab.Tactic.Omega

/-!
# Actual later-LIVE complement cutoff and collection boundary

Sources: ZIP4 `06_interruptions.tex:80-100,192-233,246-299`,
`appendix_a_local_protocol.tex:42-64`, and
`04_slow_fast_learner.tex:157-174,182-187`.

This internal deterministic join retains the queried, possibly nonzero live
seed, the original selected complete row, and the actual collection segment.
Its consumer is deterministic all-arm later-start reconstruction, together
with the retained-follower branch. Global seed truth and empty-prefix prior
service truth remain separate producer obligations. No regret closure is claimed.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteLaterLiveOutsideCutoffBoundary

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open CanonicalFastSampling ReferenceCollectionSegmentExtraction

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem initialized_segment_at
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (c : Choice rate) (I : Initializer p)
    (hc : choice (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input = some c)
    (hI : c.initializer = some I)
    (hhead : (extractRound (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]).isSome = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∃ seg : Segment rate,
      segmentAt R k.val = some seg ∧ seg.entry = R[k.val] ∧ seg.context = c ∧
      (∃ tail, seg.records = R[k.val] :: tail) ∧
      seg.records ++ seg.remaining = R.drop k.val ∧
      seg.exit = exitOf seg.remaining ∧
      I.checkedStart rate = .success seg.context.preLedger ∧
      CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
        (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
        I.assignment I.sigma I.cutoff I.freezeAt I.base I.outside seg.inputs =
          .success ⟨seg.context.preLedger, seg.accepted, seg.final⟩ ∧
      CollectionCheckedExecution.checkedRounds seg.context.preLedger seg.inputs =
        some (seg.accepted, seg.final) := by
  intro R
  let rest := R.drop (k.val + 1)
  let seg : Segment rate :=
    ⟨R[k.val], c, R[k.val] :: rest.takeWhile continuing, rest.dropWhile continuing⟩
  have hseg : segment (R.drop k.val) = some seg := by
    rw [List.drop_eq_getElem_cons k.isLt]
    simp only [ReferenceCollectionSegmentExtraction.segment, hc, Option.map_some, hhead, ite_true]
    rfl
  have hat : segmentAt R k.val = some seg := by
    simp only [segmentAt, hseg, Option.bind_some]
    have : seg.context.initializer.isSome = true := by simp only [seg, hI, Option.isSome_some]
    simp only [this, or_true, ite_true]
  have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h).isSome = true := by
    cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h with
    | none =>
        have hnil := (ReferenceCompletePhysicalHistory.no_launch_complete_history
          rate source rewards C_star C_h hl).2.1
        have hk := k.isLt
        change k.val < R.length at hk
        have hlen : R.length = 0 := congrArg List.length hnil
        omega
    | some initial => rfl
  have hcross := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate source rewards C_star C_h).mp hsome
  obtain ⟨initial, hl, hfirst, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
      rate source rewards C_star C_h hcross
  have hrun := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate source rewards C_star C_h initial hl
  have hatRun := (congrArg (fun records : List (RoundRecord (p := p) (rate := rate)) =>
    segmentAt records k.val) hrun).symm.trans hat
  obtain ⟨I', hI', hfold⟩ := run_collection_initialized_segment_at
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards _ _ _ _ hfirst k.val seg hatRun
  have hsame : I' = I := Option.some.inj (hI'.symm.trans hI)
  subst I'
  have hinit : I.checkedStart rate = .success seg.context.preLedger :=
    choice_initializer _ c I hc hI
  have hchecked : CollectionCheckedExecution.checkedRounds seg.context.preLedger seg.inputs =
      some (seg.accepted, seg.final) := by
    unfold CollectionCheckedExecution.startAndRunChecked at hfold
    change CoordinatorCollectionLedger.startCollectionChecked _ _ _ _ _ _
      I.assignment I.sigma I.cutoff I.freezeAt I.base I.outside = _ at hinit
    rw [hinit] at hfold
    cases hh : CollectionCheckedExecution.checkedRounds seg.context.preLedger seg.inputs with
    | none => simp only [hh, reduceCtorEq] at hfold
    | some result =>
        simp only [hh, CoordinatorCollectionLedger.Checked.success.injEq,
          CollectionCheckedExecution.Execution.mk.injEq] at hfold
        rcases hfold with ⟨_, hacc, hfinal⟩
        exact congrArg some (Prod.ext hacc hfinal)
  exact ⟨seg, hat, rfl, rfl, ⟨_, rfl⟩, segmentAt_partition R k.val seg hat,
    rfl, hinit, hfold, hchecked⟩

/-- Join the actual later-LIVE complement prefix to its own cutoff initializer,
first physical collection update, and whole initialized checked segment.
The root supplies only the original complete execution and a physical index;
the LIVE equation and all checked-operation inputs are constructed internally. -/
theorem complete_later_live_outside_cutoff_boundary
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    match hstate : R[b.val].input.state.coordinator with
    | .live r0 q0 beta =>
      ∀ hlater : s < r0.payload.sigma.val,
      let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h source b.val
      let A := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
        rewards C_star C_h source b r0 q0 beta hstate hlater
      let n := W.length
      let e := b.val + n
      let V := fun (j : FastArm r0.payload.slowSet) (v : ℕ) =>
        QueueReplay.replay (4 * rate.n) (r0.complementScores j, q0.queue j)
          ((A.take v).map fun c => (c.enabled, RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val))
      let d := fun j => if n = 0 then q0.previousService j else (V j n).1 - (V j (n - 1)).1
      ∃ (rE : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (qE : CoordinatorLiveServiceFinish.OwnedRegisters rE)
        (hp : rE.payload = r0.payload),
        (∀ hpos : 0 < n, (W[n - 1]'(by omega)).output.next.coordinator = .live rE qE beta) ∧
        (∀ he : e < R.length, (R[e]'he).input.state.coordinator = .live rE qE beta) ∧
        (∀ j : FastArm r0.payload.slowSet,
          let jE : FastArm rE.payload.slowSet := ⟨j.val, by simpa only [hp] using j.property⟩
          (rE.complementScores jE, qE.queue jE) = V j n ∧ qE.previousService jE = d j) ∧
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
              let t := cut.input.time
              let u := t.val + 1
              let l0 := sharedLedger ledger
              u = s + e + 1 ∧
              u = FollowerCutoffScan.firstCutoff p rate.eta.val r0.payload.sigma
                (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                  (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) ∧
              ∃ (seg : Segment rate) (I : Initializer p),
                segmentAt R e = some seg ∧ seg.entry = cut ∧
                seg.context.payload = r0.payload ∧ seg.context.preLedger = l0 ∧
                seg.context.initializer = some I ∧
                I = cutoffInitializer (liveRegistersAt rE t) (liveOwnedAt rE qE t) beta t ∧
                I.checkedStart rate = .success l0 ∧
                I.assignment.arm = r0.payload.assignment.assigned ∧
                I.sigma = r0.payload.sigma.val + 1 ∧ I.cutoff = u ∧
                I.freezeAt = rE.gridBoundary ∧ I.base = beta ∧
                (∃ tail, seg.records = cut :: tail) ∧
                seg.records ++ seg.remaining = R.drop e ∧ seg.exit = exitOf seg.remaining ∧
                CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
                  (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
                  I.assignment I.sigma I.cutoff I.freezeAt I.base I.outside seg.inputs =
                    .success ⟨l0, seg.accepted, seg.final⟩ ∧
                (∀ j : FastArm r0.payload.slowSet,
                  I.outside j.val = some ⟨(V j n).1, (V j n).2, d j⟩ ∧
                  l0.cutoffRegisters j.val = some ⟨(V j n).1, (V j n).2, d j⟩ ∧
                  l0.currentRegisters j.val = some ⟨(V j n).2, d j⟩ ∧ l0.increment j.val = 0) ∧
                (∀ i, l0.cutoffRegisters (r0.payload.assignment.assigned i) = none ∧
                  l0.currentRegisters (r0.payload.assignment.assigned i) = none) ∧
                ∃ (recording : CoordinatorRecordingOperation.Output p)
                  (started decoded : Ledger rate) (bank : CoordinatorUpReception.UpDecoderBank p)
                  (lf : Ledger rate) (clock : CoordinatorPhaseClock.FinishRoundResult p),
                  cut.output.coordinator.recording = some recording ∧
                  CoordinatorRecorderComplementBridge.run
                    (collectionRecordingInput cut.output.preparation rE.payload
                      dispatched.startResult (liveRegistersAt rE t).complementWeights) = some recording ∧
                  CoordinatorCollectionLedger.startRound l0 u (collectionEnabled l0 t)
                    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) = .success started ∧
                  (receiveUp cut.output.preparation started).result = .rejected (decoded, bank) ∧
                  decoded = { started with phase := CoordinatorCollectionLedger.Phase.decoded } ∧
                  CoordinatorCollectionLedger.finishRound decoded = .success lf ∧
                  CoordinatorPhaseClock.finishRound p rate.eta.val t
                    dispatched.startResult.clock lf.pending cut.input.row = .ok clock ∧
                  cut.output.next.coordinator = .collection r0.payload lf clock.clock.lastProposal ∧
                  cut.output.coordinator.failure = none ∧
                  lf.baseScore = beta ∧ lf.gammaLoc = (fun _ => 0) ∧
                  (∀ j : FastArm r0.payload.slowSet,
                    let D_j := CoordinatorCollectionLedger.localQueueRecord l0 t
                      (collectionEnabled l0 t)
                      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) j.val
                    let Vplus := QueueReplay.transition (4 * rate.n) (V j n) D_j
                    lf.cutoffRegisters j.val = l0.cutoffRegisters j.val ∧
                    lf.currentRegisters j.val = some ⟨Vplus.2, Vplus.1 - (V j n).1⟩ ∧
                    lf.increment j.val = Vplus.1 - (V j n).1) ∧
                  (∀ j : FastArm r0.payload.slowSet,
                    let H := CollectionKnownQueueContinuation.inputQueueRecords l0 j.val seg.inputs
                    let Y := QueueReplay.replay (4 * rate.n) (0, (V j n).2) H
                    seg.final.cutoffRegisters j.val = some ⟨(V j n).1, (V j n).2, d j⟩ ∧
                    seg.final.currentRegisters j.val = some ⟨Y.2,
                      CollectionKnownQueueContinuation.replayLastService
                        (4 * rate.n) (0, (V j n).2) (d j) H⟩ ∧
                    seg.final.increment j.val = Y.1 ∧
                    ((V j n).1 + seg.final.increment j.val, Y.2) = ((V j n).1 + Y.1, Y.2))
            | _ => False)
    | _ => True := by
  intro R s
  split
  next r0 q0 beta hstate =>
    intro hlater
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h source b.val
    let A := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
      rewards C_star C_h source b r0 q0 beta hstate hlater
    let n := W.length
    let e := b.val + n
    let V := fun (j : FastArm r0.payload.slowSet) (v : ℕ) =>
      QueueReplay.replay (4 * rate.n) (r0.complementScores j, q0.queue j)
        ((A.take v).map fun c => (c.enabled, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val))
    let d := fun j => if n = 0 then q0.previousService j else (V j n).1 - (V j (n - 1)).1
    change ∃ (rE : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (qE : CoordinatorLiveServiceFinish.OwnedRegisters rE)
      (hp : rE.payload = r0.payload),
      (∀ hpos : 0 < n, (W[n - 1]'(by omega)).output.next.coordinator = .live rE qE beta) ∧
      (∀ he : e < R.length, (R[e]'he).input.state.coordinator = .live rE qE beta) ∧
      (∀ j : FastArm r0.payload.slowSet,
        let jE : FastArm rE.payload.slowSet := ⟨j.val, by simpa only [hp] using j.property⟩
        (rE.complementScores jE, qE.queue jE) = V j n ∧ qE.previousService jE = d j) ∧
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
            let t := cut.input.time
            let u := t.val + 1
            let l0 := sharedLedger ledger
            u = s + e + 1 ∧
            u = FollowerCutoffScan.firstCutoff p rate.eta.val r0.payload.sigma
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) ∧
            ∃ (seg : Segment rate) (I : Initializer p),
              segmentAt R e = some seg ∧ seg.entry = cut ∧
              seg.context.payload = r0.payload ∧ seg.context.preLedger = l0 ∧
              seg.context.initializer = some I ∧
              I = cutoffInitializer (liveRegistersAt rE t) (liveOwnedAt rE qE t) beta t ∧
              I.checkedStart rate = .success l0 ∧
              I.assignment.arm = r0.payload.assignment.assigned ∧
              I.sigma = r0.payload.sigma.val + 1 ∧ I.cutoff = u ∧
              I.freezeAt = rE.gridBoundary ∧ I.base = beta ∧
              (∃ tail, seg.records = cut :: tail) ∧
              seg.records ++ seg.remaining = R.drop e ∧ seg.exit = exitOf seg.remaining ∧
              CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
                (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
                I.assignment I.sigma I.cutoff I.freezeAt I.base I.outside seg.inputs =
                  .success ⟨l0, seg.accepted, seg.final⟩ ∧
              (∀ j : FastArm r0.payload.slowSet,
                I.outside j.val = some ⟨(V j n).1, (V j n).2, d j⟩ ∧
                l0.cutoffRegisters j.val = some ⟨(V j n).1, (V j n).2, d j⟩ ∧
                l0.currentRegisters j.val = some ⟨(V j n).2, d j⟩ ∧ l0.increment j.val = 0) ∧
              (∀ i, l0.cutoffRegisters (r0.payload.assignment.assigned i) = none ∧
                l0.currentRegisters (r0.payload.assignment.assigned i) = none) ∧
              ∃ (recording : CoordinatorRecordingOperation.Output p)
                (started decoded : Ledger rate) (bank : CoordinatorUpReception.UpDecoderBank p)
                (lf : Ledger rate) (clock : CoordinatorPhaseClock.FinishRoundResult p),
                cut.output.coordinator.recording = some recording ∧
                CoordinatorRecorderComplementBridge.run
                  (collectionRecordingInput cut.output.preparation rE.payload
                    dispatched.startResult (liveRegistersAt rE t).complementWeights) = some recording ∧
                CoordinatorCollectionLedger.startRound l0 u (collectionEnabled l0 t)
                  (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) = .success started ∧
                (receiveUp cut.output.preparation started).result = .rejected (decoded, bank) ∧
                decoded = { started with phase := CoordinatorCollectionLedger.Phase.decoded } ∧
                CoordinatorCollectionLedger.finishRound decoded = .success lf ∧
                CoordinatorPhaseClock.finishRound p rate.eta.val t
                  dispatched.startResult.clock lf.pending cut.input.row = .ok clock ∧
                cut.output.next.coordinator = .collection r0.payload lf clock.clock.lastProposal ∧
                cut.output.coordinator.failure = none ∧
                lf.baseScore = beta ∧ lf.gammaLoc = (fun _ => 0) ∧
                (∀ j : FastArm r0.payload.slowSet,
                  let D_j := CoordinatorCollectionLedger.localQueueRecord l0 t
                    (collectionEnabled l0 t)
                    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) j.val
                  let Vplus := QueueReplay.transition (4 * rate.n) (V j n) D_j
                  lf.cutoffRegisters j.val = l0.cutoffRegisters j.val ∧
                  lf.currentRegisters j.val = some ⟨Vplus.2, Vplus.1 - (V j n).1⟩ ∧
                  lf.increment j.val = Vplus.1 - (V j n).1) ∧
                (∀ j : FastArm r0.payload.slowSet,
                  let H := CollectionKnownQueueContinuation.inputQueueRecords l0 j.val seg.inputs
                  let Y := QueueReplay.replay (4 * rate.n) (0, (V j n).2) H
                  seg.final.cutoffRegisters j.val = some ⟨(V j n).1, (V j n).2, d j⟩ ∧
                  seg.final.currentRegisters j.val = some ⟨Y.2,
                    CollectionKnownQueueContinuation.replayLastService
                      (4 * rate.n) (0, (V j n).2) (d j) H⟩ ∧
                  seg.final.increment j.val = Y.1 ∧
                  ((V j n).1 + seg.final.increment j.val, Y.2) = ((V j n).1 + Y.1, Y.2))
          | _ => False)
    obtain ⟨rE, qE, hp, hout, hin, hvalues⟩ :=
      ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_replay
        rewards C_star C_h source b r0 q0 beta hstate hlater n le_rfl
    refine ⟨rE, qE, hp, hout, hin, hvalues, ?_⟩
    rcases ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_maximal
        rewards C_star C_h source b r0 q0 beta hstate hlater with hend | hcut
    · exact Or.inl hend
    · obtain ⟨he, rM, qM, _hMp, _hMin, chosenM, hMprep, hMcut⟩ := hcut
      have hfalse : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
          (R[e]'he) = false := by
        unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
        rw [hMprep]
        cases chosenM <;> first | exact False.elim hMcut | rfl
      let cut := R[e]'he
      change ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest cut = false at hfalse
      have hactual : cut.output.preparation = prepare cut.input := by
        rw [cut.output_eq]
        rfl
      obtain ⟨hprep, hbranch⟩ := complete_live_cutoff_post_choice
        rate rewards C_star C_h source ⟨e, he⟩ rE qE beta (hin he)
      dsimp only at hprep hbranch
      refine Or.inr ⟨he, CoordinatorRoundDispatch.dispatchLive
        (liveInput cut.input rE qE beta), rfl, ?_, ?_⟩
      · rw [hactual]
        exact hprep
      · generalize hd : CoordinatorRoundDispatch.dispatchLive
          (liveInput cut.input rE qE beta) = outcome at hbranch ⊢
        cases outcome with
        | continuingChosen =>
          have hpr : cut.output.preparation.coordinator = .live rE qE beta
              (CoordinatorRoundDispatch.dispatchLive (liveInput cut.input rE qE beta)) := by
            rw [hactual]
            exact hprep
          rw [hd] at hpr
          simp only [ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest, hpr] at hfalse
          contradiction
        | clockFailure => exact False.elim hbranch
        | initializerFailure => exact False.elim hbranch
        | localFailure => exact False.elim hbranch
        | cutoffChosen dispatched hstart ledger hinit hcandidate hdomain hclock hpending hno selected =>
          obtain ⟨_hcommand, _hclock, _hpending, _hno, _hinitialized, hledger,
            hsigma, hcutoff, hfreeze, _hlpending, _hcursor, hinc, _hgamma,
            _hraw, _hphase, _hchoice, _hgrid, _harm, physical, hphysical,
            _hphysicalPayload, _hphysicalPending, _hphysicalCutoff, _hphysicalStarted,
            _hphysicalArm, _hphysicalPendingStarted, _hphysicalCutoffStarted,
            _hphysicalChoice, recording, hrecord, started, hstartLedger,
            hstarted, _hvalid, _hstartedPhase, _hstartedCursor, _hstartedInc,
            _hstartedHistory, _hstartedRaw, _hknown, _hunknown, _hlocal,
            _hdisabled, _hzero, _hbankPending, decoded, bank, hreceive,
            hdecoded, _hbank, lf, clock, diagnostic, hfinish, hfinished,
            _hfinishedValid, _hfinishedInc, hfinishedGamma, _hfinishedCursor,
            _hfinishedPhase, _hfinishedCut, _hfinishedCurrent, _hfinishedRaw,
            _hfinishedPending, hclockFinish, _hclockEq, _hclockPending,
            _hclockCommand, _hdiagnostic, _hdiagnosticInput, _hdiagnosticRaw,
            _hpost, _hobserve, hcoord, hnext, _hnextBank⟩ := hbranch
          change cut.output.coordinator = _ at hcoord
          change cut.output.next.coordinator = _ at hnext
          let l0 := sharedLedger ledger
          change (receiveUp (prepare cut.input) started).result = .rejected (decoded, bank) at hreceive
          let I := cutoffInitializer (liveRegistersAt rE cut.input.time)
            (liveOwnedAt rE qE cut.input.time) beta cut.input.time
          let c : Choice rate := ⟨rE.payload, l0, dispatched.startResult,
            (liveRegistersAt rE cut.input.time).complementWeights, some I⟩
          have hprepared : (prepare cut.input).coordinator =
              .live rE qE beta (.cutoffChosen dispatched hstart ledger hinit
                hcandidate hdomain hclock hpending hno selected) := by
            rw [← hd]
            exact hprep
          have hphysical' : (prepare cut.input).coordinator.selection = some physical := by
            exact hphysical
          have hc : choice cut.input = some c := by
            unfold choice
            rw [hphysical']
            simp only [reduceCtorEq, ↓reduceIte, hprepared, choiceOfCut]
            rfl
          have hhead : (extractRound cut).isSome = true := by
            simp only [extractRound, hc, Option.bind_some, extractWith, hcoord]
            change (match CoordinatorCollectionLedger.startRound l0
              (cut.input.time.val + 1) (collectionEnabled l0 cut.input.time)
              (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
              | .success st => match (receiveUp (prepare cut.input) st).result with
                | .success _ => some _ | .rejected _ => some _ | .invalid => none
              | _ => none).isSome = true
            rw [hstartLedger]
            dsimp only
            rw [hreceive]
            rfl
          obtain ⟨seg, hseg, hentry, hcontext, hnonempty, hpartition, hexit,
            hcheckedInit, hfold, hchecked⟩ := initialized_segment_at
              rewards C_star C_h source ⟨e, he⟩ c I hc rfl hhead
          have hpre : seg.context.preLedger = l0 := congrArg Choice.preLedger hcontext
          have hsegPayload : seg.context.payload = r0.payload :=
            (congrArg Choice.payload hcontext).trans hp
          obtain ⟨_birth, _hbefore, _hbirth, _hassignment, _hbirthSigma, hfirst, _hbase⟩ :=
            ReferenceAssignmentRetainedBirthProvenance.complete_collection_choice_birth_provenance
              rate rewards C_star C_h source ⟨e, he⟩ c hc
          have htime : cut.input.time.val = s + e := by
            have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
              rate source rewards C_star C_h
            change R.map (fun r => r.input.time.val) = calendar s (p.T - s) at htimes
            have hcal : e < (calendar s (p.T - s)).length := by
              rw [← htimes, List.length_map]
              exact he
            have hget : (R.map (fun r => r.input.time.val))[e]'(by simpa only [List.length_map] using he) =
                (calendar s (p.T - s))[e]'hcal := by
              simp only [htimes]
            simpa only [List.getElem_map, calendar, List.getElem_range', Nat.one_mul] using hget
          have hstartInit : I.checkedStart rate = .success l0 := by
            exact hcheckedInit.trans (congrArg CoordinatorCollectionLedger.Checked.success hpre)
          have hledgerCut : l0.cutoffRegisters =
              CoordinatorStartRoundCutoffDispatch.outsideRegisters
                (liveRegistersAt rE cut.input.time) (liveOwnedAt rE qE cut.input.time) := by
            rw [(sharedLedger_fields ledger).2.2.2.2.2.2.1, hcandidate]
            rfl
          have hledgerCurrent : l0.currentRegisters = fun a =>
              (CoordinatorStartRoundCutoffDispatch.outsideRegisters
                (liveRegistersAt rE cut.input.time) (liveOwnedAt rE qE cut.input.time) a).map
                  (fun reg => ⟨reg.queue, reg.lastService⟩) := by
            rw [(sharedLedger_fields ledger).2.2.2.2.2.2.2.1, hcandidate]
            rfl
          have hledgerInc : l0.increment = fun _ => 0 := by
            exact (sharedLedger_fields ledger).2.2.2.2.2.2.2.2.1.trans hinc
          have houtside (j : FastArm r0.payload.slowSet) :
              I.outside j.val = some ⟨(V j n).1, (V j n).2, d j⟩ := by
            let jE : FastArm rE.payload.slowSet := ⟨j.val, by simpa only [hp] using j.property⟩
            have hpair := (hvalues j).1
            have hlast := (hvalues j).2
            change (rE.complementScores jE, qE.queue jE) = V j n at hpair
            change qE.previousService jE = d j at hlast
            have ho : I.outside j.val = some
                ⟨rE.complementScores jE, qE.queue jE, qE.previousService jE⟩ := by
              have hj : j.val ∈ fastArmFinset rE.payload.slowSet := jE.property
              simp only [I, cutoffInitializer, CoordinatorStartRoundCutoffDispatch.outsideRegisters,
                liveRegistersAt, liveOwnedAt, hj, ↓reduceDIte]
              rfl
            have hscore : rE.complementScores jE = (V j n).1 := congrArg Prod.fst hpair
            have hqueue : qE.queue jE = (V j n).2 := congrArg Prod.snd hpair
            rw [ho, hlast, hscore, hqueue]
          have hknown (j : FastArm r0.payload.slowSet) :
              l0.cutoffRegisters j.val = some ⟨(V j n).1, (V j n).2, d j⟩ ∧
              l0.currentRegisters j.val = some ⟨(V j n).2, d j⟩ ∧ l0.increment j.val = 0 := by
            rw [hledgerCut, hledgerCurrent, hledgerInc]
            change I.outside j.val = _ ∧ (I.outside j.val).map _ = _ ∧ 0 = 0
            rw [houtside j]
            exact ⟨rfl, rfl, rfl⟩
          refine ⟨?_, ?_, seg, I, hseg, hentry, hsegPayload, hpre,
            ?_, rfl, hstartInit, ?_, ?_, rfl, rfl, rfl, hnonempty,
            hpartition, hexit, ?_, ?_, ?_, recording, started, decoded, bank,
            lf, clock, ?_, ?_, hstartLedger, ?_, hdecoded, hfinish, hclockFinish,
            ?_, ?_, ?_, hfinishedGamma, ?_, ?_⟩
          · change cut.input.time.val + 1 = s + e + 1
            rw [htime]
          · have hcutoff0 : l0.cutoff = cut.input.time.val + 1 :=
              (sharedLedger_fields ledger).2.2.1.trans hcutoff
            change l0.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val rE.payload.sigma
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) at hfirst
            exact hcutoff0.symm.trans (hfirst.trans (by rw [hp]))
          · exact (congrArg Choice.initializer hcontext).trans rfl
          · change rE.payload.assignment.assigned = r0.payload.assignment.assigned
            rw [hp]
          · change rE.payload.sigma.val + 1 = r0.payload.sigma.val + 1
            rw [hp]
          · simpa only [hpre] using hfold
          · intro j
            exact ⟨houtside j, hknown j⟩
          · intro i
            have hslow : r0.payload.assignment.assigned i ∈ r0.payload.slowSet.val := by
              rw [← AssignmentStartPayload.Input.assignment_image]
              exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
            have hnot : r0.payload.assignment.assigned i ∉ fastArmFinset rE.payload.slowSet := by
              simpa only [hp, fastArmFinset, Finset.mem_sdiff, Finset.mem_univ, true_and,
                not_not] using hslow
            rw [hledgerCut, hledgerCurrent]
            simp only [CoordinatorStartRoundCutoffDispatch.outsideRegisters,
              show r0.payload.assignment.assigned i ∉ fastArmFinset
                (liveRegistersAt rE cut.input.time).payload.slowSet from hnot, ↓reduceDIte,
              Option.map_none, and_self]
          · rw [hcoord]
          · change CoordinatorRecorderComplementBridge.run
              (collectionRecordingInput cut.output.preparation rE.payload dispatched.startResult
                (liveRegistersAt rE cut.input.time).complementWeights) = some recording
            rw [hactual]
            exact hrecord
          · change (receiveUp cut.output.preparation started).result = .rejected (decoded, bank)
            rw [hactual]
            exact hreceive
          · simpa only [hp] using hnext
          · rw [hcoord]
          · rw [hfinished, hdecoded, hstarted]
            change (sharedLedger ledger).baseScore = beta
            rw [(sharedLedger_fields ledger).2.2.2.2.1, hcandidate]
            rfl
          · intro j
            change lf.cutoffRegisters j.val = l0.cutoffRegisters j.val ∧
              lf.currentRegisters j.val = some
                ⟨(QueueReplay.transition (4 * rate.n) (V j n)
                  (CoordinatorCollectionLedger.localQueueRecord l0 cut.input.time
                    (collectionEnabled l0 cut.input.time)
                    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) j.val)).2,
                  (QueueReplay.transition (4 * rate.n) (V j n)
                    (CoordinatorCollectionLedger.localQueueRecord l0 cut.input.time
                      (collectionEnabled l0 cut.input.time)
                      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) j.val)).1 -
                    (V j n).1⟩ ∧
              lf.increment j.val = (QueueReplay.transition (4 * rate.n) (V j n)
                (CoordinatorCollectionLedger.localQueueRecord l0 cut.input.time
                  (collectionEnabled l0 cut.input.time)
                  (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) j.val)).1 -
                    (V j n).1
            have hk := hknown j
            have hcandidateStarted := collection_started_candidate l0 started cut.input.time
              (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) hstartLedger
            rw [hfinished, hdecoded, hcandidateStarted]
            have htransition :
                QueueReplay.transition (4 * rate.n) (V j n)
                  (CoordinatorCollectionLedger.localQueueRecord l0 cut.input.time
                    (collectionEnabled l0 cut.input.time)
                    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) j.val) =
                ((V j n).1 + (QueueReplay.transition (4 * rate.n) (0, (V j n).2)
                  (CoordinatorCollectionLedger.localQueueRecord l0 cut.input.time
                    (collectionEnabled l0 cut.input.time)
                    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) j.val)).1,
                  (QueueReplay.transition (4 * rate.n) (0, (V j n).2)
                    (CoordinatorCollectionLedger.localQueueRecord l0 cut.input.time
                      (collectionEnabled l0 cut.input.time)
                      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) j.val)).2) := by
              cases hr : CoordinatorCollectionLedger.localQueueRecord l0 cut.input.time
                (collectionEnabled l0 cut.input.time)
                (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) j.val with
              | mk enabled arrival => cases enabled <;> simp [QueueReplay.transition]
            simp only [htransition, Nat.add_sub_cancel_left]
            simp only [CoordinatorCollectionLedger.finishRoundCandidate,
              CoordinatorCollectionLedger.startRoundCandidate, hk.2.1, hk.2.2]
            simp only [Nat.zero_add, and_self]
          · intro j
            have hcontinuation := CollectionKnownQueueContinuation.checkedRounds_known_queue_continuation
              l0 seg.final j.val ⟨(V j n).2, d j⟩ seg.inputs seg.accepted (hknown j).2.1
                (by simpa only [hpre] using hchecked)
            dsimp only at hcontinuation ⊢
            rw [(hknown j).2.2] at hcontinuation
            obtain ⟨hcur, hincFinal, _hassign, _hsigma, _hcutoff, _hfreeze, hfixed⟩ := hcontinuation
            exact ⟨hfixed.trans (hknown j).1, hcur, hincFinal, by rw [hincFinal]⟩

  all_goals trivial

end Bandits.Support.ReferenceCompleteLaterLiveOutsideCutoffBoundary
