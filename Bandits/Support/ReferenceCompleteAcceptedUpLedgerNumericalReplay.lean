/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteAcceptedUpCollectionLocalization

import Lean.Elab.Tactic.Omega

/-!
# Numerical replay of one actual accepted-UP collection ledger

Source evidence: ZIP4 04:157-168; 06:40-100,192-233,246-299,329-348;
Appendix A:28-64. The live and collection lists belong to the same original
complete suffix and retained payload. Initial base scores and queues remain
payload-relative; this module makes no global queue or regret assertion.

The numerical result is available to actual known-arm continuation and all-arm
later-start reconstruction. Those consumers still require the physical initial
score/queue identities, outside-arm cutoff truth, and online continuation laws;
no later assignment start is asserted here.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteAcceptedUpLedgerNumericalReplay

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceCollectionSegmentExtraction

section

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem replay_score_translation (cap score : ℕ) (initial : ℕ × ℕ)
    (records : List (Bool × ℕ)) :
    QueueReplay.replay cap (score + initial.1, initial.2) records =
      (score + (QueueReplay.replay cap initial records).1,
        (QueueReplay.replay cap initial records).2) := by
  induction records generalizing initial with
  | nil => rfl
  | cons record rest ih =>
      have hstep : QueueReplay.transition cap (score + initial.1, initial.2) record =
          (score + (QueueReplay.transition cap initial record).1,
            (QueueReplay.transition cap initial record).2) := by
        cases record with
        | mk enabled arrival =>
            cases enabled <;> simp [QueueReplay.transition, Nat.add_assoc]
      change QueueReplay.replay cap
          (QueueReplay.transition cap (score + initial.1, initial.2) record) rest = _
      rw [hstep, ih]
      rfl

private theorem live_choice_payload
    (x : RoundInput p rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ) (c : Choice rate)
    (hc : choice x = some c)
    (hprep : (prepare x).coordinator = .live registers owned base
      (CoordinatorRoundDispatch.dispatchLive (liveInput x registers owned base))) :
    c.payload = registers.payload := by
  unfold choice at hc
  split at hc
  · contradiction
  next =>
    rw [hprep] at hc
    cases hd : CoordinatorRoundDispatch.dispatchLive (liveInput x registers owned base) <;>
      simp only [hd, choiceOfCut, reduceCtorEq] at hc
    all_goals cases Option.some.inj hc; rfl

private theorem original_run
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    ∃ (initial : ReferenceActivePhysicalStep.State p rate) (span : s + (p.T - s) ≤ p.T)
      (active : allActiveAtStart initial s),
      ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h = some initial ∧
      initial.coordinator = .first ∧
      R = (run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s (p.T - s) span active).records := by
  intro R s
  have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h).isSome = true := by
    cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h with
    | none =>
        have hnil := (ReferenceCompletePhysicalHistory.no_launch_complete_history
          rate source rewards C_star C_h hl).2.1
        have hk := k.isLt
        have hlen := congrArg List.length hnil
        simp only [List.length_nil] at hlen
        omega
    | some initial => rfl
  have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate source rewards C_star C_h).mp hsome
  obtain ⟨initial, hl, hfirst, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
      rate source rewards C_star C_h hc
  have span : s + (p.T - s) ≤ p.T := by
    have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
      rate source rewards C_star C_h
    change s ≤ p.T at hs
    omega
  let active := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
    rate source rewards C_star C_h initial hl
  exact ⟨initial, span, active, hl, hfirst,
    ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate source rewards C_star C_h initial hl⟩

private theorem next_collection_payload
    (record : RoundRecord (p := p) (rate := rate)) (c : Choice rate)
    (hc : choice record.input = some c)
    (payload : Payload rate) (finished : Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hout : record.output.next.coordinator = .collection payload finished saved) :
    payload = c.payload := by
  have htail : record.output.next.coordinator =
      (collectionPostChoice (prepare record.input) c.payload c.preLedger
        c.started c.weights).configuration := by
    rw [record.output_eq]
    exact congrArg CoordinatorObservation.configuration (choice_tail record.input c hc)
  rw [htail] at hout
  unfold collectionPostChoice at hout
  cases hr : CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput (prepare record.input) c.payload c.started c.weights) with
  | none => simp only [hr, coordinatorFailure, reduceCtorEq] at hout
  | some recording =>
      simp only [hr] at hout
      cases hs : CoordinatorCollectionLedger.startRound c.preLedger
          (record.input.time.val + 1) (collectionEnabled c.preLedger record.input.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp only [hs, coordinatorFailure, reduceCtorEq] at hout
      | rejected bad => simp only [hs, coordinatorFailure, reduceCtorEq] at hout
      | success started =>
          simp only [hs] at hout
          unfold collectionFinish at hout
          cases hu : (receiveUp (prepare record.input) started).result with
          | invalid => simp only [hu, coordinatorFailure, reduceCtorEq] at hout
          | success pair | rejected pair =>
              rcases pair with ⟨decoded, bank⟩
              simp only [hu] at hout
              cases hf : CoordinatorCollectionLedger.finishRound decoded with
              | invalid => simp only [hf, coordinatorFailure, reduceCtorEq] at hout
              | rejected bad => simp only [hf, coordinatorFailure, reduceCtorEq] at hout
              | success final =>
                  simp only [hf] at hout
                  cases hk : CoordinatorPhaseClock.finishRound p rate.eta.val record.input.time
                      c.started.clock final.pending record.input.row with
                  | error reason => simp only [hk, coordinatorFailure, reduceCtorEq] at hout
                  | ok clock =>
                      simp only [hk, CoordinatorConfiguration.collection.injEq] at hout
                      exact hout.1.symm

private theorem localized_replay_join
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (o n : ℕ) (seg : Segment rate) (done : CompletedRound rate)
    (c0 : Choice rate) (I : Initializer p)
    (hn : n < seg.records.length)
    (hsegment : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h) o = some seg)
    (hrecord : ∀ hn : n < seg.records.length, seg.records[n]'hn =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val])
    (hdone : extractRound (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val] = some done)
    (haccepted : done.accepted = true) (hparsed : done.input.parsed = some U)
    (hsender : done.input.selectedFollower = i)
    (hsegContext : seg.context = c0) (hI : c0.initializer = some I) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
      ∃ (initial : ReferenceActivePhysicalStep.State p rate) (span : s + (p.T - s) ≤ p.T)
        (active : allActiveAtStart initial s),
        ReferenceCorrectedInitializationLaunch.correctedLaunch
          rate source rewards C_star C_h = some initial ∧
        initial.coordinator = .first ∧
        R = (run initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards s (p.T - s) span active).records ∧
        CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
        (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
        I.assignment I.sigma I.cutoff I.freezeAt
        I.base I.outside seg.inputs =
          .success ⟨seg.context.preLedger, seg.accepted, seg.final⟩ ∧
      ∃ prefixExecution : CollectionCheckedExecution.Execution p rate.eta.val
          rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
          rate.n rate.n_scale,
          CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
            (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
            I.assignment I.sigma I.cutoff I.freezeAt
            I.base I.outside (seg.inputs.take n) =
              .success prefixExecution ∧
          prefixExecution.initial = seg.context.preLedger ∧
          prefixExecution.final = ReferenceCollectionSegmentExtraction.endpointLedger
            seg.context.preLedger (seg.records.take n) ∧
          ∃ recording started decoded bank finished,
            ((R[k.val]'k.isLt)).output.coordinator.recording = some recording ∧
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.collectionRecordingInput
                (ReferenceActivePhysicalStep.prepare ((R[k.val]'k.isLt)).input) done.context.payload
                done.context.started done.context.weights) = some recording ∧
            CoordinatorCollectionLedger.startRound done.context.preLedger
              (((R[k.val]'k.isLt)).input.time.val + 1)
              (ReferenceActivePhysicalStep.collectionEnabled done.context.preLedger
                ((R[k.val]'k.isLt)).input.time)
              (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                .success started ∧
            (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare ((R[k.val]'k.isLt)).input) started).result =
                .success (decoded, bank) ∧
            CoordinatorCollectionLedger.decodeUp started i (some U) = .success decoded ∧
            CoordinatorCollectionLedger.finishRound decoded = .success finished ∧
            finished = done.final ∧
            done.input = ReferenceCollectionSegmentExtraction.inputOf ((R[k.val]'k.isLt)).input
              done.context.preLedger recording started ∧
            let arm := started.assignment.arm i
            ∃ hbound : started.cutoff - 1 + (started.cursor - started.cutoff) ≤ p.T,
              ∃ lastIndex : Fin p.T,
                CoordinatorCollectionLedger.sourceRound lastIndex = started.cursor ∧
                lastIndex = ((R[k.val]'k.isLt)).input.time ∧
                started.cursor - started.cutoff = n ∧
                started.assignment = I.assignment ∧
                started.sigma = I.sigma ∧
                started.cutoff = I.cutoff ∧
                started.freezeAt = I.freezeAt ∧
                started.baseScore = I.base ∧
                1 ≤ started.cutoff ∧ started.cutoff ≤ started.cursor ∧
                started.cursor ≤ p.T ∧
                prefixExecution.final.currentRegisters arm = none ∧
                started.currentRegisters arm = none ∧
                ∃ past current,
                CoordinatorCollectionLedger.replayRecords? started arm
                    (CoordinatorCollectionLedger.calendarIndices p.T
                      (started.cutoff - 1) (started.cursor - started.cutoff) hbound) =
                  some past ∧
                CoordinatorCollectionLedger.replayRecords? started arm [lastIndex] =
                  some [current] ∧
                CollectionBufferProvenance.suppliedReplayRecords?
                    (seg.inputs.take n ++ [done.input]) arm started.freezeAt
                    (CoordinatorCollectionLedger.calendarIndices p.T
                      (started.cutoff - 1) (started.cursor - started.cutoff) hbound ++
                      [lastIndex]) =
                  some (past ++ [current]) ∧
                past = (seg.records.take n).map
                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                    seg.context.preLedger arm) ∧
                current = ReferenceCollectionRawBufferHistory.physicalQueueRecord
                  seg.context.preLedger arm ((R[k.val]'k.isLt)) ∧
                past ++ [current] = (seg.records.take (n + 1)).map
                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                    seg.context.preLedger arm) ∧
                (seg.records.take n).map
                    (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                      seg.context.preLedger arm) ++
                  [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                    seg.context.preLedger arm ((R[k.val]'k.isLt))] =
                  (seg.records.take (n + 1)).map
                    (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                      seg.context.preLedger arm) ∧
                finished.currentRegisters arm =
                  some ⟨(QueueReplay.replay (4 * rate.n) (0, U.val.q)
                    ((seg.records.take n).map
                      (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                        seg.context.preLedger arm) ++
                      [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                        seg.context.preLedger arm ((R[k.val]'k.isLt))])).2,
                    (QueueReplay.replay (4 * rate.n) (0, U.val.q)
                      ((seg.records.take n).map
                        (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                          seg.context.preLedger arm) ++
                        [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                          seg.context.preLedger arm ((R[k.val]'k.isLt))])).1 -
                    (QueueReplay.replay (4 * rate.n) (0, U.val.q)
                      ((seg.records.take n).map
                        (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                          seg.context.preLedger arm))).1⟩ ∧
                finished.increment arm =
                  (QueueReplay.replay (4 * rate.n) (0, U.val.q)
                    ((seg.records.take n).map
                      (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                        seg.context.preLedger arm) ++
                      [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                        seg.context.preLedger arm ((R[k.val]'k.isLt))])).1 ∧
                finished.cutoffRegisters arm =
                  some ⟨started.baseScore i + U.val.S, U.val.q, U.val.delta⟩ := by
  intro R s
  obtain ⟨initial, span, active, hlaunch, hfirst, hrun⟩ :=
    original_run (rate := rate) rewards C_star C_h source k
  have hsegmentRun : segmentAt
      (run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s (p.T - s) span active).records o = some seg := by
    rw [← hrun]
    exact hsegment
  have hjoin := ReferenceCollectionUpReplayHistory.actual_accepted_up_physical_replay_join
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards s (p.T - s) span active hfirst o seg hsegmentRun n hn done
    (by rw [hrecord hn]; exact hdone) haccepted U hparsed i hsender
  dsimp only at hjoin
  rw [hrecord hn] at hjoin
  obtain ⟨I', hI', _, hrest⟩ := hjoin
  have hII : I' = I := Option.some.inj (hI'.symm.trans (by rw [hsegContext]; exact hI))
  subst I'
  exact ⟨initial, span, active, hlaunch, hfirst, hrun, hrest⟩

private theorem collection_ledger_replay
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input i U)
    (c : Choice rate)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (A : List (Bool × ℕ))
    (hc : choice (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input = some c)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[b.val] c.payload)
    (hAlen : A.length = FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) -
          (c.payload.sigma.val + 1))
    (hUNumerical : (U.val.S, U.val.q) = QueueReplay.replay (4 * rate.n)
      (0, (c.payload.downRecord i).val.q) A)
    (hUDNumerical : U.val.delta =
      (QueueReplay.replay (4 * rate.n) (0, (c.payload.downRecord i).val.q) A).1 -
      (QueueReplay.replay (4 * rate.n) (0, (c.payload.downRecord i).val.q)
        (A.take ((FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) -
              (c.payload.sigma.val + 1)) - 1))).1) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let P := c.payload
    let M := P.downRecord i
    let a := P.assignment.assigned i
    let sigma := P.sigma.val + 1
    let cap := 4 * rate.n
    let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
    let u := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits
    let N := u - sigma
            let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
            let o := u - (s + 1)
            let n := k.val - o
              ∃ (seg : Segment rate) (done : CompletedRound rate)
                (c0 : Choice rate) (I : Initializer p),
                o ≤ k.val ∧ o < R.length ∧ n < seg.records.length ∧
                segmentAt R o = some seg ∧
                (∀ ho : o < R.length, seg.entry = R[o]'ho) ∧ seg.context = c0 ∧
                choice seg.entry.input = some c0 ∧ c0.payload = c.payload ∧
                c0.initializer = some I ∧ I.checkedStart rate = .success seg.context.preLedger ∧
                I.sigma = sigma ∧ I.cutoff = u ∧ seg.entry.input.time.val + 1 = u ∧
                (∃ (liveInit : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                  (ownedInit : CoordinatorLiveServiceFinish.OwnedRegisters liveInit)
                  (baseInit : Fin (p.m - 1) → ℕ),
                  seg.entry.input.state.coordinator = .live liveInit ownedInit baseInit ∧
                  I = cutoffInitializer (liveRegistersAt liveInit seg.entry.input.time)
                    (liveOwnedAt liveInit ownedInit seg.entry.input.time) baseInit seg.entry.input.time ∧
                  (prepare seg.entry.input).coordinator = .live liveInit ownedInit baseInit
                    (CoordinatorRoundDispatch.dispatchLive (liveInput seg.entry.input liveInit ownedInit baseInit)) ∧
                  ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true) ∧
                (∀ hn : n < seg.records.length, seg.records[n]'hn = (R[k.val]'k.isLt)) ∧ extractRound (R[k.val]'k.isLt) = some done ∧
                done.context = c ∧ done.accepted = true ∧ done.input.parsed = some U ∧
                done.input.selectedFollower = i ∧
                seg.records.take (n + 1) = (R.drop o).take (n + 1) ∧
                (seg.records.take (n + 1)).map (fun (r : RoundRecord (p := p) (rate := rate)) => r.input.time.val + 1) =
                  List.range' u (n + 1) ∧
                seg.records ++ seg.remaining = R.drop o ∧ seg.exit = exitOf seg.remaining ∧
                o = b.val + N ∧ I.assignment.arm = P.assignment.assigned ∧
                I.freezeAt = c.preLedger.freezeAt ∧ I.base = c.preLedger.baseScore ∧
                ∃ (initial : ReferenceActivePhysicalStep.State p rate) (span : s + (p.T - s) ≤ p.T)
                  (active : allActiveAtStart initial s),
                  ReferenceCorrectedInitializationLaunch.correctedLaunch
                    rate source rewards C_star C_h = some initial ∧
                  initial.coordinator = .first ∧
                  R = (run initial source.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p source)
                    rewards s (p.T - s) span active).records ∧
                  CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
                  (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
                  I.assignment I.sigma I.cutoff I.freezeAt
                  I.base I.outside seg.inputs =
                    .success ⟨seg.context.preLedger, seg.accepted, seg.final⟩ ∧
                ∃ prefixExecution : CollectionCheckedExecution.Execution p rate.eta.val
                    rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
                    rate.n rate.n_scale,
                    CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
                      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
                      I.assignment I.sigma I.cutoff I.freezeAt
                      I.base I.outside (seg.inputs.take n) =
                        .success prefixExecution ∧
                    prefixExecution.initial = seg.context.preLedger ∧
                    prefixExecution.final = ReferenceCollectionSegmentExtraction.endpointLedger
                      seg.context.preLedger (seg.records.take n) ∧
                    ∃ recording started decoded bank finished,
                      ((R[k.val]'k.isLt)).output.coordinator.recording = some recording ∧
                      CoordinatorRecorderComplementBridge.run
                        (ReferenceActivePhysicalStep.collectionRecordingInput
                          (ReferenceActivePhysicalStep.prepare ((R[k.val]'k.isLt)).input) done.context.payload
                          done.context.started done.context.weights) = some recording ∧
                      CoordinatorCollectionLedger.startRound done.context.preLedger
                        (((R[k.val]'k.isLt)).input.time.val + 1)
                        (ReferenceActivePhysicalStep.collectionEnabled done.context.preLedger
                          ((R[k.val]'k.isLt)).input.time)
                        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                          .success started ∧
                      (ReferenceActivePhysicalStep.receiveUp
                        (ReferenceActivePhysicalStep.prepare ((R[k.val]'k.isLt)).input) started).result =
                          .success (decoded, bank) ∧
                      CoordinatorCollectionLedger.decodeUp started i (some U) = .success decoded ∧
                      CoordinatorCollectionLedger.finishRound decoded = .success finished ∧
                      finished = done.final ∧
                      done.input = ReferenceCollectionSegmentExtraction.inputOf ((R[k.val]'k.isLt)).input
                        done.context.preLedger recording started ∧
                      let arm := started.assignment.arm i
                      ∃ hbound : started.cutoff - 1 + (started.cursor - started.cutoff) ≤ p.T,
                        ∃ lastIndex : Fin p.T,
                          CoordinatorCollectionLedger.sourceRound lastIndex = started.cursor ∧
                          lastIndex = ((R[k.val]'k.isLt)).input.time ∧
                          started.cursor - started.cutoff = n ∧
                          started.assignment = I.assignment ∧
                          started.sigma = I.sigma ∧
                          started.cutoff = I.cutoff ∧
                          started.freezeAt = I.freezeAt ∧
                          started.baseScore = I.base ∧
                          1 ≤ started.cutoff ∧ started.cutoff ≤ started.cursor ∧
                          started.cursor ≤ p.T ∧
                          prefixExecution.final.currentRegisters arm = none ∧
                          started.currentRegisters arm = none ∧
                          ∃ past current,
                          CoordinatorCollectionLedger.replayRecords? started arm
                              (CoordinatorCollectionLedger.calendarIndices p.T
                                (started.cutoff - 1) (started.cursor - started.cutoff) hbound) =
                            some past ∧
                          CoordinatorCollectionLedger.replayRecords? started arm [lastIndex] =
                            some [current] ∧
                          CollectionBufferProvenance.suppliedReplayRecords?
                              (seg.inputs.take n ++ [done.input]) arm started.freezeAt
                              (CoordinatorCollectionLedger.calendarIndices p.T
                                (started.cutoff - 1) (started.cursor - started.cutoff) hbound ++
                                [lastIndex]) =
                            some (past ++ [current]) ∧
                          past = (seg.records.take n).map
                            (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                              seg.context.preLedger arm) ∧
                          current = ReferenceCollectionRawBufferHistory.physicalQueueRecord
                            seg.context.preLedger arm ((R[k.val]'k.isLt)) ∧
                          past ++ [current] = (seg.records.take (n + 1)).map
                            (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                              seg.context.preLedger arm) ∧
                          (seg.records.take n).map
                              (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                seg.context.preLedger arm) ++
                            [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                              seg.context.preLedger arm ((R[k.val]'k.isLt))] =
                            (seg.records.take (n + 1)).map
                              (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                seg.context.preLedger arm) ∧
                          finished.currentRegisters arm =
                            some ⟨(QueueReplay.replay (4 * rate.n) (0, U.val.q)
                              ((seg.records.take n).map
                                (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                  seg.context.preLedger arm) ++
                                [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                  seg.context.preLedger arm ((R[k.val]'k.isLt))])).2,
                              (QueueReplay.replay (4 * rate.n) (0, U.val.q)
                                ((seg.records.take n).map
                                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                    seg.context.preLedger arm) ++
                                  [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                    seg.context.preLedger arm ((R[k.val]'k.isLt))])).1 -
                              (QueueReplay.replay (4 * rate.n) (0, U.val.q)
                                ((seg.records.take n).map
                                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                    seg.context.preLedger arm))).1⟩ ∧
                          finished.increment arm =
                            (QueueReplay.replay (4 * rate.n) (0, U.val.q)
                              ((seg.records.take n).map
                                (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                  seg.context.preLedger arm) ++
                                [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                  seg.context.preLedger arm ((R[k.val]'k.isLt))])).1 ∧
                          finished.cutoffRegisters arm =
                            some ⟨started.baseScore i + U.val.S, U.val.q, U.val.delta⟩ ∧
                          started.cutoff = u ∧
                          (∃ saved, ((R[k.val]'k.isLt)).output.next.coordinator = .collection P finished saved) ∧
                          let B0 := I.base i
                          let X := fun v => QueueReplay.replay cap (B0, M.val.q) (A.take v)
                          let H := fun m => (seg.records.take m).map
                            (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a)
                          let Y := fun m => QueueReplay.replay cap (B0, M.val.q) (A ++ H m)
                          H (n + 1) = H n ++
                            [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                              seg.context.preLedger a ((R[k.val]'k.isLt))] ∧
                          finished.cutoffRegisters a =
                            some ⟨(X N).1, (X N).2, (X N).1 - (X (N - 1)).1⟩ ∧
                          finished.currentRegisters a =
                            some ⟨(Y (n + 1)).2, (Y (n + 1)).1 - (Y n).1⟩ ∧
                          finished.increment a = (QueueReplay.replay cap (0, U.val.q) (H (n + 1))).1 ∧
                          finished.increment a = (Y (n + 1)).1 - (X N).1 ∧
                          ((X N).1 + finished.increment a, (Y (n + 1)).2) = Y (n + 1) := by
  classical
  intro R P M a sigma cap bits u N s o n
  obtain ⟨seg, done, c0, I, hok, hoR, hn, hsegment, hentry, hsegContext,
    hc0, hP0, hI, hIchecked, hIsigma, hIcutoff, hentryTime, hlive,
    hrecord, hdone, hcontext, haccepted, hparsed, hsender, hprefix,
    hlabels, hpartition, hexit⟩ :=
    ReferenceCompleteAcceptedUpCollectionLocalization.complete_accepted_up_collection_localization
      (rate := rate) rewards C_star C_h source k i U hacc c hc
  have hbirthTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    (R[b.val]'b.isLt) c.payload hbirth
  have hbclock := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h source b
  change c.payload.sigma.val = (R[b.val]'b.isLt).input.time.val at hbirthTime
  change (R[b.val]'b.isLt).input.time.val = s + b.val at hbclock
  have hcutBounds := FollowerCutoffScan.firstCutoff_bounds p rate.eta.val
    rate.eta.property rate.sourceCap P.sigma bits
  have hoffset : o = b.val + N := by
    dsimp only [o, N, sigma]
    have hcut : P.sigma.val + 1 < u := hcutBounds.1
    have hstamp : P.sigma.val = s + b.val := hbirthTime.trans hbclock
    omega
  obtain ⟨live, owned, base, hstate0, hIliteral, hprepare0, hcutoff0⟩ := hlive
  have hPentry := live_choice_payload seg.entry.input live owned base c0 hc0 hprepare0
  have hIarm : I.assignment.arm = P.assignment.assigned := by
    rw [hIliteral]
    change live.payload.assignment.assigned = P.assignment.assigned
    rw [← hPentry, hP0]
  obtain ⟨initial, span, active, hlaunch, hfirst, hrun, hwhole,
    prefixExecution, hprefixRun, hprefixInitial, hprefixFinal,
    recording, started, decoded, bank, finished, hrecording, hrecorder,
    hstart, hreceive, hdecode, hfinish, hfinished, hinput,
    hbound, lastIndex, hlastRound, hlastIndex, hcursor, hassignment, hstartedSigma,
    hstartedCutoff, hstartedFreeze, hstartedBase, hcutpos, hcutcursor, hcursorT,
    hprefixUnknown, hstartedUnknown, past, current, hpast, hcurrent, hsupplied,
    hpastPhysical, hcurrentPhysical, hpastCurrent, hphysicalAppend,
    hcurrentRegisters, hincrement, hcutoffRegisters⟩ :=
    localized_replay_join rewards C_star C_h source k i U o n seg done c0 I
      hn hsegment hrecord hdone haccepted hparsed hsender hsegContext hI
  have hstartContext := CollectionBufferProvenance.startRound_success_context
    done.context.preLedger started ((R[k.val]'k.isLt).input.time.val + 1)
    (collectionEnabled done.context.preLedger (R[k.val]'k.isLt).input.time)
    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) hstart
  have hfreeze : I.freezeAt = c.preLedger.freezeAt := by
    have hf := congrArg (fun x => x.2.2.2.1) hstartContext
    change started.freezeAt = done.context.preLedger.freezeAt at hf
    rw [hcontext, hstartedFreeze] at hf
    exact hf
  have hbase : I.base = c.preLedger.baseScore := by
    have hb := congrArg (fun x => x.2.2.2.2) hstartContext
    change started.baseScore = done.context.preLedger.baseScore at hb
    rw [hcontext, hstartedBase] at hb
    exact hb
  have harm : started.assignment.arm i = a := by
    rw [hassignment, hIarm]
  obtain ⟨Pout, saved, hnext⟩ :=
    (actual_collection_round_checked (p := p) (rate := rate) (R[k.val]'k.isLt) done hdone).2.2.2
  have hPout := next_collection_payload (p := p) (rate := rate) (R[k.val]'k.isLt) c hc Pout done.final saved hnext
  have hnextActual : (R[k.val]'k.isLt).output.next.coordinator = .collection P finished saved := by
    rw [hnext, hPout, hfinished]
  refine ⟨seg, done, c0, I, hok, hoR, hn, hsegment, hentry, hsegContext,
    hc0, hP0, hI, hIchecked, hIsigma, hIcutoff, hentryTime,
    ⟨live, owned, base, hstate0, hIliteral, hprepare0, hcutoff0⟩,
    hrecord, hdone, hcontext, haccepted, hparsed, hsender, hprefix,
    hlabels, hpartition, hexit, hoffset, hIarm, hfreeze, hbase,
    initial, span, active, hlaunch, hfirst, hrun, hwhole,
    prefixExecution, hprefixRun, hprefixInitial, hprefixFinal,
    recording, started, decoded, bank, finished, hrecording, hrecorder,
    hstart, hreceive, hdecode, hfinish, hfinished, hinput,
    hbound, lastIndex, hlastRound, hlastIndex, hcursor, hassignment, hstartedSigma,
    hstartedCutoff, hstartedFreeze, hstartedBase, hcutpos, hcutcursor, hcursorT,
    hprefixUnknown, hstartedUnknown, past, current, hpast, hcurrent, hsupplied,
    hpastPhysical, hcurrentPhysical, hpastCurrent, hphysicalAppend,
    hcurrentRegisters, hincrement, hcutoffRegisters,
    hstartedCutoff.trans hIcutoff, ⟨saved, hnextActual⟩, ?_⟩
  let B0 := I.base i
  let X := fun count => QueueReplay.replay cap (B0, M.val.q) (A.take count)
  let H := fun count => (seg.records.take count).map
    (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a)
  let Y := fun count => QueueReplay.replay cap (B0, M.val.q) (A ++ H count)
  have hH : H (n + 1) = H n ++
      [ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a (R[k.val]'k.isLt)] := by
    rw [harm] at hphysicalAppend
    exact hphysicalAppend.symm
  have htake : A.take N = A := by
    apply List.take_of_length_le
    change A.length = N at hAlen
    omega
  have hU : (U.val.S, U.val.q) = QueueReplay.replay cap (0, M.val.q) A := hUNumerical
  have hXN : X N = (B0 + U.val.S, U.val.q) := by
    dsimp only [X]
    rw [htake]
    simpa only [Nat.add_zero, hU.symm] using
      replay_score_translation cap B0 (0, M.val.q) A
  have hdelta : (X N).1 - (X (N - 1)).1 = U.val.delta := by
    have hprev := replay_score_translation cap B0 (0, M.val.q) (A.take (N - 1))
    have hfull := replay_score_translation cap B0 (0, M.val.q) A
    change U.val.delta = (QueueReplay.replay cap (0, M.val.q) A).1 -
      (QueueReplay.replay cap (0, M.val.q) (A.take (N - 1))).1 at hUDNumerical
    dsimp only [X]
    rw [htake]
    simp only [Nat.add_zero] at hprev hfull
    rw [hfull, hprev]
    simp only [Nat.add_sub_add_left]
    exact hUDNumerical.symm
  have hY (count : ℕ) : Y count =
      ((X N).1 + (QueueReplay.replay cap (0, U.val.q) (H count)).1,
        (QueueReplay.replay cap (0, U.val.q) (H count)).2) := by
    dsimp only [Y]
    rw [QueueReplay.replay_append]
    have hstartX : QueueReplay.replay cap (B0, M.val.q) A = X N := by
      dsimp only [X]
      rw [htake]
    rw [hstartX, hXN]
    simpa only [Nat.add_zero] using
      replay_score_translation cap (B0 + U.val.S) (0, U.val.q) (H count)
  have hfinishedCutoff : finished.cutoffRegisters a =
      some ⟨(X N).1, (X N).2, (X N).1 - (X (N - 1)).1⟩ := by
    rw [harm, hstartedBase] at hcutoffRegisters
    rw [hcutoffRegisters, hdelta, hXN]
  have hfinishedCurrent : finished.currentRegisters a =
      some ⟨(Y (n + 1)).2, (Y (n + 1)).1 - (Y n).1⟩ := by
    rw [harm] at hcurrentRegisters
    change finished.currentRegisters a = some
      ⟨(QueueReplay.replay cap (0, U.val.q) (H n ++
          [ReferenceCollectionRawBufferHistory.physicalQueueRecord
            seg.context.preLedger a (R[k.val]'k.isLt)])).2,
        (QueueReplay.replay cap (0, U.val.q) (H n ++
          [ReferenceCollectionRawBufferHistory.physicalQueueRecord
            seg.context.preLedger a (R[k.val]'k.isLt)])).1 -
        (QueueReplay.replay cap (0, U.val.q) (H n)).1⟩ at hcurrentRegisters
    rw [← hH] at hcurrentRegisters
    rw [hcurrentRegisters, hY (n + 1), hY n]
    simp only [Nat.add_sub_add_left]
  have hfinishedIncrement : finished.increment a =
      (QueueReplay.replay cap (0, U.val.q) (H (n + 1))).1 := by
    rw [harm] at hincrement
    rw [hH]
    exact hincrement
  refine ⟨hH, hfinishedCutoff, hfinishedCurrent, hfinishedIncrement, ?_, ?_⟩
  · change finished.increment a = (Y (n + 1)).1 - (X N).1
    rw [hY (n + 1), hfinishedIncrement]
    simp only [Nat.add_sub_cancel_left]
  · change ((X N).1 + finished.increment a, (Y (n + 1)).2) = Y (n + 1)
    rw [hY (n + 1), hfinishedIncrement]


end

/-- The same accepted terminal reply and cutoff collection, with the original
live cells, checked collection prefix, actual calls, and numerical registers.
Only acceptance in the original complete suffix is a logical root input. -/
theorem complete_accepted_up_collection_ledger_numerical_replay
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input i U) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    ∃ (c : ReferenceCollectionSegmentExtraction.Choice rate)
      (b j : Fin R.length)
      (logged after : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
      (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
      (scan : FollowerCutoffScan.ScanResult p.T)
      (registers : ℕ × ℕ) (lastService : ℕ),
      ReferenceCollectionSegmentExtraction.choice (R[k.val]'k.isLt).input = some c ∧
      b.val ≤ j.val ∧ j.val < k.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth (R[b.val]'b.isLt) c.payload ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i (c.payload.downRecord i) ∧
      (R[j.val].output.followers i).downInput = some logged ∧
      (R[j.val].output.followers i).down = some cut ∧
      cut.outcome = .accepted logged after raw (c.payload.downRecord i) scan registers lastService ∧
      let P := c.payload
      let M := P.downRecord i
      let a := P.assignment.assigned i
      let sigma := P.sigma.val + 1
      let cap := 4 * rate.n
      let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
      let u := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits
      let ell := min u (R[j.val].input.time.val + 2)
      let N := u - sigma
      let d := ell - sigma
      let z := max (b.val + N) (j.val + 1)
      let L := (R.drop b.val).take N
      let qp := ReferenceFirstLaunchNumericalCell.queueParameters rate
      ell = scan.endpoint ∧
      ActiveFollowerDownAcceptance.checkedRecovery p rate M logged ell =
        .ok ⟨registers, lastService⟩ ∧
      M.val.q = P.queues a ∧ 0 < d ∧ d ≤ N ∧
      L.map (fun (r : RoundRecord (p := p) (rate := rate)) => r.input.time.val + 1) = List.range' sigma N ∧
      ∃ (hLlen : L.length = N)
        (v : ∀ n : Fin N, Selection
          (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).input)
        (ho : ∀ n : Fin N, ReferenceLaterLiveNumericalReadout.preparedOrdinary
          (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm))),
        (∀ n, (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).output.preparation.coordinator.selection =
            some (v n) ∧ (v n).view.payload = P ∧ (v n).view.cutoff = none ∧
            CoordinatorLocalArmChoice.assignmentIsLive (v n).view.payload
              (v n).view.cutoff (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).input.time) ∧
        (∀ n f, (ReferenceFollowerFixedReply.actualChoice
            (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) f).configuration =
          .ordinary
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
        let A := List.ofFn (fun n : Fin N =>
          ((Cells n).enabled, RecordedQueueRun.quantizedArrival qp (Cells n) a))
        let V := fun count => QueueReplay.replay cap (0, M.val.q) (A.take count)
        let Ed := ((R.drop b.val).take d).map
          (fun r => (true, ReferenceFollowerSparseEmissionRecovery.emissionContribution M i r))
        let Q := ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged ell
        Q = Ed ∧ Ed = A.take d ∧ A.length = N ∧
        (∀ x ∈ A, x.1 = true) ∧ registers = V d ∧
        lastService = (V d).1 - (V (d - 1)).1 ∧
        let W := fun count => QueueReplay.replay cap registers ((A.drop d).take (count - d))
        ∃ hz : z < R.length, z ≤ k.val ∧
          ∃ (terminal : ReferencePrelaunchFollower.State p rate.eta)
            (terminalMemory : ActiveFollowerLifecycle.LocalMemory p),
            (ReferenceFollowerFixedReply.actualChoice (R[z]'hz) i).configuration =
              .ordinary terminal terminalMemory ∧
            terminal.status = .unoccupied ∧ terminal.lastDown = some M ∧
            (terminal.S, terminal.backlog) = W N ∧
            terminal.delta = (if d < N then (W N).1 - (W (N - 1)).1 else lastService) ∧
            U.val.sigma = sigma ∧ U.val.S = terminal.S ∧
            U.val.delta = terminal.delta ∧ U.val.q = terminal.backlog ∧
            (U.val.S, U.val.q) = QueueReplay.replay cap (0, M.val.q) A ∧
            U.val.delta =
              (QueueReplay.replay cap (0, M.val.q) A).1 -
                (QueueReplay.replay cap (0, M.val.q) (A.take (N - 1))).1 ∧
            let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
            let o := u - (s + 1)
            let n := k.val - o
              ∃ (seg : Segment rate) (done : CompletedRound rate)
                (c0 : Choice rate) (I : Initializer p),
                o ≤ k.val ∧ o < R.length ∧ n < seg.records.length ∧
                segmentAt R o = some seg ∧
                (∀ ho : o < R.length, seg.entry = R[o]'ho) ∧ seg.context = c0 ∧
                choice seg.entry.input = some c0 ∧ c0.payload = c.payload ∧
                c0.initializer = some I ∧ I.checkedStart rate = .success seg.context.preLedger ∧
                I.sigma = sigma ∧ I.cutoff = u ∧ seg.entry.input.time.val + 1 = u ∧
                (∃ (liveInit : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                  (ownedInit : CoordinatorLiveServiceFinish.OwnedRegisters liveInit)
                  (baseInit : Fin (p.m - 1) → ℕ),
                  seg.entry.input.state.coordinator = .live liveInit ownedInit baseInit ∧
                  I = cutoffInitializer (liveRegistersAt liveInit seg.entry.input.time)
                    (liveOwnedAt liveInit ownedInit seg.entry.input.time) baseInit seg.entry.input.time ∧
                  (prepare seg.entry.input).coordinator = .live liveInit ownedInit baseInit
                    (CoordinatorRoundDispatch.dispatchLive (liveInput seg.entry.input liveInit ownedInit baseInit)) ∧
                  ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true) ∧
                (∀ hn : n < seg.records.length, seg.records[n]'hn = (R[k.val]'k.isLt)) ∧ extractRound (R[k.val]'k.isLt) = some done ∧
                done.context = c ∧ done.accepted = true ∧ done.input.parsed = some U ∧
                done.input.selectedFollower = i ∧
                seg.records.take (n + 1) = (R.drop o).take (n + 1) ∧
                (seg.records.take (n + 1)).map (fun (r : RoundRecord (p := p) (rate := rate)) => r.input.time.val + 1) =
                  List.range' u (n + 1) ∧
                seg.records ++ seg.remaining = R.drop o ∧ seg.exit = exitOf seg.remaining ∧
                o = b.val + N ∧ I.assignment.arm = P.assignment.assigned ∧
                I.freezeAt = c.preLedger.freezeAt ∧ I.base = c.preLedger.baseScore ∧
                ∃ (initial : ReferenceActivePhysicalStep.State p rate) (span : s + (p.T - s) ≤ p.T)
                  (active : allActiveAtStart initial s),
                  ReferenceCorrectedInitializationLaunch.correctedLaunch
                    rate source rewards C_star C_h = some initial ∧
                  initial.coordinator = .first ∧
                  R = (run initial source.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p source)
                    rewards s (p.T - s) span active).records ∧
                  CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
                  (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
                  I.assignment I.sigma I.cutoff I.freezeAt
                  I.base I.outside seg.inputs =
                    .success ⟨seg.context.preLedger, seg.accepted, seg.final⟩ ∧
                ∃ prefixExecution : CollectionCheckedExecution.Execution p rate.eta.val
                    rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
                    rate.n rate.n_scale,
                    CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
                      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
                      I.assignment I.sigma I.cutoff I.freezeAt
                      I.base I.outside (seg.inputs.take n) =
                        .success prefixExecution ∧
                    prefixExecution.initial = seg.context.preLedger ∧
                    prefixExecution.final = ReferenceCollectionSegmentExtraction.endpointLedger
                      seg.context.preLedger (seg.records.take n) ∧
                    ∃ recording started decoded bank finished,
                      ((R[k.val]'k.isLt)).output.coordinator.recording = some recording ∧
                      CoordinatorRecorderComplementBridge.run
                        (ReferenceActivePhysicalStep.collectionRecordingInput
                          (ReferenceActivePhysicalStep.prepare ((R[k.val]'k.isLt)).input) done.context.payload
                          done.context.started done.context.weights) = some recording ∧
                      CoordinatorCollectionLedger.startRound done.context.preLedger
                        (((R[k.val]'k.isLt)).input.time.val + 1)
                        (ReferenceActivePhysicalStep.collectionEnabled done.context.preLedger
                          ((R[k.val]'k.isLt)).input.time)
                        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                          .success started ∧
                      (ReferenceActivePhysicalStep.receiveUp
                        (ReferenceActivePhysicalStep.prepare ((R[k.val]'k.isLt)).input) started).result =
                          .success (decoded, bank) ∧
                      CoordinatorCollectionLedger.decodeUp started i (some U) = .success decoded ∧
                      CoordinatorCollectionLedger.finishRound decoded = .success finished ∧
                      finished = done.final ∧
                      done.input = ReferenceCollectionSegmentExtraction.inputOf ((R[k.val]'k.isLt)).input
                        done.context.preLedger recording started ∧
                      let arm := started.assignment.arm i
                      ∃ hbound : started.cutoff - 1 + (started.cursor - started.cutoff) ≤ p.T,
                        ∃ lastIndex : Fin p.T,
                          CoordinatorCollectionLedger.sourceRound lastIndex = started.cursor ∧
                          lastIndex = ((R[k.val]'k.isLt)).input.time ∧
                          started.cursor - started.cutoff = n ∧
                          started.assignment = I.assignment ∧
                          started.sigma = I.sigma ∧
                          started.cutoff = I.cutoff ∧
                          started.freezeAt = I.freezeAt ∧
                          started.baseScore = I.base ∧
                          1 ≤ started.cutoff ∧ started.cutoff ≤ started.cursor ∧
                          started.cursor ≤ p.T ∧
                          prefixExecution.final.currentRegisters arm = none ∧
                          started.currentRegisters arm = none ∧
                          ∃ past current,
                          CoordinatorCollectionLedger.replayRecords? started arm
                              (CoordinatorCollectionLedger.calendarIndices p.T
                                (started.cutoff - 1) (started.cursor - started.cutoff) hbound) =
                            some past ∧
                          CoordinatorCollectionLedger.replayRecords? started arm [lastIndex] =
                            some [current] ∧
                          CollectionBufferProvenance.suppliedReplayRecords?
                              (seg.inputs.take n ++ [done.input]) arm started.freezeAt
                              (CoordinatorCollectionLedger.calendarIndices p.T
                                (started.cutoff - 1) (started.cursor - started.cutoff) hbound ++
                                [lastIndex]) =
                            some (past ++ [current]) ∧
                          past = (seg.records.take n).map
                            (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                              seg.context.preLedger arm) ∧
                          current = ReferenceCollectionRawBufferHistory.physicalQueueRecord
                            seg.context.preLedger arm ((R[k.val]'k.isLt)) ∧
                          past ++ [current] = (seg.records.take (n + 1)).map
                            (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                              seg.context.preLedger arm) ∧
                          (seg.records.take n).map
                              (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                seg.context.preLedger arm) ++
                            [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                              seg.context.preLedger arm ((R[k.val]'k.isLt))] =
                            (seg.records.take (n + 1)).map
                              (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                seg.context.preLedger arm) ∧
                          finished.currentRegisters arm =
                            some ⟨(QueueReplay.replay (4 * rate.n) (0, U.val.q)
                              ((seg.records.take n).map
                                (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                  seg.context.preLedger arm) ++
                                [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                  seg.context.preLedger arm ((R[k.val]'k.isLt))])).2,
                              (QueueReplay.replay (4 * rate.n) (0, U.val.q)
                                ((seg.records.take n).map
                                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                    seg.context.preLedger arm) ++
                                  [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                    seg.context.preLedger arm ((R[k.val]'k.isLt))])).1 -
                              (QueueReplay.replay (4 * rate.n) (0, U.val.q)
                                ((seg.records.take n).map
                                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                    seg.context.preLedger arm))).1⟩ ∧
                          finished.increment arm =
                            (QueueReplay.replay (4 * rate.n) (0, U.val.q)
                              ((seg.records.take n).map
                                (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                  seg.context.preLedger arm) ++
                                [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                  seg.context.preLedger arm ((R[k.val]'k.isLt))])).1 ∧
                          finished.cutoffRegisters arm =
                            some ⟨started.baseScore i + U.val.S, U.val.q, U.val.delta⟩ ∧
                          started.cutoff = u ∧
                          (∃ saved, ((R[k.val]'k.isLt)).output.next.coordinator = .collection P finished saved) ∧
                          let B0 := I.base i
                          let X := fun v => QueueReplay.replay cap (B0, M.val.q) (A.take v)
                          let H := fun m => (seg.records.take m).map
                            (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a)
                          let Y := fun m => QueueReplay.replay cap (B0, M.val.q) (A ++ H m)
                          H (n + 1) = H n ++
                            [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                              seg.context.preLedger a ((R[k.val]'k.isLt))] ∧
                          finished.cutoffRegisters a =
                            some ⟨(X N).1, (X N).2, (X N).1 - (X (N - 1)).1⟩ ∧
                          finished.currentRegisters a =
                            some ⟨(Y (n + 1)).2, (Y (n + 1)).1 - (Y n).1⟩ ∧
                          finished.increment a = (QueueReplay.replay cap (0, U.val.q) (H (n + 1))).1 ∧
                          finished.increment a = (Y (n + 1)).1 - (X N).1 ∧
                          ((X N).1 + finished.increment a, (Y (n + 1)).2) = Y (n + 1) := by
  classical
  intro R
  obtain ⟨c, b, j, logged, after, cut, raw, scan, registers, lastService,
    hc, hbj, hjk, hbirth, hretained, hlogged, hdown, houtcome,
    hscan, hchecked, hq, hdpos, hdle, htimes, hLlen, v, ho,
    hselected, hprepared, hQ, hEd, hAlen, hAenabled, hregisters, hlastService,
    hz, hzk, terminal, terminalMemory, hterminalChoice, hterminalStatus,
    hterminalDown, hterminalRegisters, hterminalDelta, hUsigma,
    hUSterminal, hUdterminal, hUqterminal, hUNumerical, hUDNumerical⟩ :=
    ReferenceCompleteFollowerTerminalUpNumericalReplay.complete_accepted_up_terminal_up_numerical_replay
      (rate := rate) rewards C_star C_h source k i U hacc
  let P := c.payload
  let M := P.downRecord i
  let a := P.assignment.assigned i
  let sigma := P.sigma.val + 1
  let cap := 4 * rate.n
  let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
    (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
  let u := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits
  let ell := min u (R[j.val].input.time.val + 2)
  let N := u - sigma
  let d := ell - sigma
  let L := (R.drop b.val).take N
  let qp := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let Cells : Fin N → RecordedQueueRun.RoundInput p.K := fun n =>
    ReferenceFirstWindowNumericalStream.sourceCell
      (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (v n).view.payload
      (v n).view.pendingAtChoice
      (ReferenceLaterLiveNumericalReadout.preparedStates
        (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (ho n))
      (v n).view.complementWeights (v n).view.cutoff
      (ReferenceLaterLiveNumericalReadout.selection_choiceValid (v n))
  let A := List.ofFn (fun n : Fin N =>
    ((Cells n).enabled, RecordedQueueRun.quantizedArrival qp (Cells n) a))
  let V := fun count => QueueReplay.replay cap (0, M.val.q) (A.take count)
  let W := fun count => QueueReplay.replay cap registers ((A.drop d).take (count - d))
  refine ⟨c, b, j, logged, after, cut, raw, scan, registers, lastService,
    hc, hbj, hjk, hbirth, hretained, hlogged, hdown, houtcome,
    hscan, hchecked, hq, hdpos, hdle, htimes, hLlen, v, ho,
    hselected, hprepared, hQ, hEd, hAlen, hAenabled, hregisters, hlastService,
    hz, hzk, terminal, terminalMemory, hterminalChoice, hterminalStatus,
    hterminalDown, hterminalRegisters, hterminalDelta, hUsigma,
    hUSterminal, hUdterminal, hUqterminal, hUNumerical, hUDNumerical, ?_⟩
  exact collection_ledger_replay rewards C_star C_h source k i U hacc c b A
    hc hbirth hAlen hUNumerical hUDNumerical

end Bandits.Support.ReferenceCompleteAcceptedUpLedgerNumericalReplay
