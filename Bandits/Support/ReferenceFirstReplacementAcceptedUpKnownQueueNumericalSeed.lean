/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementAcceptedUpNumericalSeed
public import Bandits.Support.ReferenceCompleteAcceptedUpKnownQueueContinuation

import Lean.Elab.Tactic.Omega

/-!
# Initialized first-replacement accepted-UP continuation

Source evidence: ZIP4 Appendix A:28-64; 06:40-100,192-233,246-299,329-348;
04:157-174. The original accepted UP supplies one retained payload, initializer,
LIVE source-cell list and physical collection. On its first replacement branch,
the actual initialized prefix seeds every remaining prefix of this same
collection, including the empty continuation and the actual final ledger.

This internal deterministic component ends before all-arm next-start
reconstruction. It asserts no probability law or manuscript closure.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstReplacementAcceptedUpKnownQueueNumericalSeed

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceCollectionSegmentExtraction

/-- Translating the initial score preserves the queue and translates every
subsequent score by the same amount, including on disabled records. -/
private theorem replay_score_origin (cap origin : ℕ) (state : ℕ × ℕ)
    (records : List (Bool × ℕ)) :
    QueueReplay.replay cap (origin + state.1, state.2) records =
      (origin + (QueueReplay.replay cap state records).1,
        (QueueReplay.replay cap state records).2) := by
  have commute (s : ℕ × ℕ) (r : Bool × ℕ) :
      QueueReplay.transition cap (origin + s.1, s.2) r =
        (origin + (QueueReplay.transition cap s r).1,
          (QueueReplay.transition cap s r).2) := by
    rcases r with ⟨enabled, arrival⟩
    cases enabled <;> simp only [QueueReplay.transition, Bool.false_eq_true,
      ↓reduceIte, Nat.add_assoc]
  exact List.foldl_hom (fun s : ℕ × ℕ => (origin + s.1, s.2)) commute


/-- Continue the actual initialized first-replacement seed through this accepted
UP's own remaining collection. The only logical root premise is the original
acceptance; the first-replacement condition remains inside the conclusion. -/
theorem complete_accepted_up_first_replacement_known_queue_numerical_seed
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
                          ((X N).1 + finished.increment a, (Y (n + 1)).2) = Y (n + 1) ∧
                          (b.val =
                            (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length +
                              (ReferenceCollectionPhaseHistory.collectionWindow R
                                (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length).length →
                            ∃ hcross : (ReferenceInitializationRun.output
                              (ActualReferenceInitializationBlock.referenceInput
                                source rewards C_star C_h rate)).crossing.isSome = true,
                            ∃ hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
                              source rewards C_star C_h + (p.T - s) ≤ p.T,
                            ∃ hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
                              (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
                                source rewards C_star C_h hcross (p.T - s) hspan).records).length < p.T - s,
                            (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
                              source rewards C_star C_h hcross (p.T - s) hspan).records = R ∧
                            let s0 := ReferenceFirstCollectionReadyStream.startTime (rate := rate)
                              source rewards C_star C_h
                            let L0 := ReferenceFirstLiveConfirmationHistory.firstLiveWindow
                              (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
                                source rewards C_star C_h hcross (p.T - s) hspan).records
                            let Cells0 := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
                              rate source rewards C_star C_h hcross (p.T - s) hspan
                            ∃ seedDispatch : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
                              (p := p) (rate := rate) source rewards C_star C_h (p.T - s) hcross hspan hshort,
                            let out := seedDispatch.stream
                            ∃ (head0 : Choice rate) (initializer0 : Initializer p)
                              (valid0 : CoordinatorRecorderComplementBridge.LocalInputsValid
                                (ReferenceActivePhysicalStep.collectionRecordingInput out.cutoff.cut.output.preparation
                                  head0.payload head0.started head0.weights))
                              (D0 : List (RecordedQueueRun.RoundInput p.K)),
                              choice out.cutoff.cut.input = some head0 ∧ head0.payload = out.payload ∧
                              head0.initializer = some initializer0 ∧
                              initializer0.checkedStart rate = .success head0.preLedger ∧
                              ∃ hDlen : D0.length = out.ell,
                              D0[0]'(by rw [hDlen]; have h := out.positiveLength; omega) =
                                ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate out.cutoff.cut head0 rewards valid0 ∧
                              (∀ n : Fin out.ell,
                                let record := out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)
                                let cell := D0[n.val]'(by rw [hDlen]; exact n.isLt)
                                ∃ (call : Choice rate)
                                  (validCall : CoordinatorRecorderComplementBridge.LocalInputsValid
                                    (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
                                      call.payload call.started call.weights)),
                                  choice record.input = some call ∧ call.payload = out.payload ∧
                                  CollectionBufferProvenance.collectionContext call.preLedger =
                                    CollectionBufferProvenance.collectionContext head0.preLedger ∧
                                  cell = ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate record call rewards validCall ∧
                                  record.input.rows = source.1.2 ∧
                                  record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                                  record.input.rewards = rewards ∧ record.input.time.val = s0 + (L0).length + n.val ∧
                                  cell.enabled = ReferenceActivePhysicalStep.collectionEnabled call.preLedger record.input.time ∧
                                  cell.reward = (fun a => ((rewards record.input.time a).val : ℝ) /
                                    (ConstructorDimensions.D p : ℝ)) ∧ cell.rate = out.payload.rate ∧
                                  (∀ a : Fin p.K,
                                    ReferenceCollectionRawBufferHistory.physicalQueueRecord head0.preLedger a record =
                                      (cell.enabled, RecordedQueueRun.quantizedArrival
                                        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)) ∧
                                  (0 < n.val → ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s0 record = some cell)) ∧
                              (∀ h, h ≤ out.ell → ∀ a : Fin p.K,
                                (out.window.take h).map (ReferenceCollectionRawBufferHistory.physicalQueueRecord head0.preLedger a) =
                                  ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (D0.take h)) ∧
                              out.ell = (ReferenceCollectionPhaseHistory.collectionWindow
                                (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)
                                (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
                                  (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)).length).length ∧
                              (∀ f : Fin (p.m - 1), c.preLedger.baseScore f =
                                (QueueReplay.replay (4 * rate.n) (0, 0)
                                  (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate (c.payload.assignment.assigned f) (Cells0 ++ D0))).1) ∧
                              (∀ a : Fin p.K, c.payload.queues a =
                                (QueueReplay.replay (4 * rate.n) (0, 0) (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells0 ++ D0))).2) ∧
                              (∃ (x : RoundInput p rate)
                                (dispatch : ReferenceFirstCollectionStreamEmptyDispatch.ActualNextDispatch
                                  x out.payload seedDispatch.ledger out.saved),
                                x = (ReferenceCompletePhysicalHistory.completeSuffixRecords
                                  rate source rewards C_star C_h)[b.val].input ∧
                                let input := collectionInput x out.payload seedDispatch.ledger
                                  (collectionClock out.payload seedDispatch.ledger out.saved dispatch.cutoffTime) dispatch.cutoffTime
                                let operationLedger := CoordinatorRoundDispatch.collectionOperationLedger input dispatch.core.payload_n_eq
                                ∃ consistent : LaterAssignmentStartOperation.LocalConsistency input.payload operationLedger,
                                ∃ output : LaterAssignmentStartOperation.SuccessfulStart input.payload operationLedger
                                  dispatch.instruction input.row,
                                ∃ hlocal : output.localConsistency = consistent,
                                ∃ clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output,
                                ∃ installed : CoordinatorAssignmentRegisterInstall.LaterInstallation output clockData,
                                ∃ selection : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
                                  dispatch.started dispatch.instruction.time installed.registers.complementWeights input.row,
                                  CoordinatorRoundDispatch.dispatchCollection input =
                                    .laterChosen dispatch.core consistent dispatch.started dispatch.startCheck
                                      dispatch.instruction dispatch.assignmentStart output hlocal clockData installed selection ∧
                                  installed = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
                                  c.payload = installed.registers.payload ∧
                                  c.preLedger.baseScore = installed.retainedBaseScore ∧
                                  (∀ a, AssignmentScoreReconstruction.sourceScore output.reconstruction a =
                                    (QueueReplay.replay (4 * rate.n) (0, 0) (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells0 ++ D0))).1 ∧
                                    AssignmentScoreReconstruction.initialQueue output.reconstruction a =
                                      (QueueReplay.replay (4 * rate.n) (0, 0) (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells0 ++ D0))).2) ∧
                                  (∀ a, installed.registers.payload.queues a =
                                    (QueueReplay.replay (4 * rate.n) (0, 0) (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells0 ++ D0))).2) ∧
                                  (∀ f : Fin (p.m - 1),
                                    installed.retainedBaseScore f =
                                      (QueueReplay.replay (4 * rate.n) (0, 0)
                                        (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate (installed.registers.payload.assignment.assigned f) (Cells0 ++ D0))).1 ∧
                                    (installed.registers.payload.downRecord f).val.q =
                                      (QueueReplay.replay (4 * rate.n) (0, 0)
                                        (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate (installed.registers.payload.assignment.assigned f) (Cells0 ++ D0))).2)) ∧
                              let Q_a := QueueReplay.replay cap (0, 0) (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells0 ++ D0))
                              let X0 := fun m => QueueReplay.replay cap (0, 0)
                                (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells0 ++ D0) ++ A.take m)
                              let Y0 := fun m => QueueReplay.replay cap (0, 0)
                                (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells0 ++ D0) ++ (A ++ H m))
                              (I.base i, M.val.q) = Q_a ∧
                              (∀ m, X m = X0 m) ∧ (∀ m, Y m = Y0 m) ∧
                              finished.cutoffRegisters a =
                                some ⟨(X0 N).1, (X0 N).2, (X0 N).1 - (X0 (N - 1)).1⟩ ∧
                              finished.currentRegisters a =
                                some ⟨(Y0 (n + 1)).2, (Y0 (n + 1)).1 - (Y0 n).1⟩ ∧
                              finished.increment a = (Y0 (n + 1)).1 - (X0 N).1 ∧
                              ((X0 N).1 + finished.increment a, (Y0 (n + 1)).2) = Y0 (n + 1) ∧
                              let Ledge := fun (j : ℕ) => endpointLedger seg.context.preLedger (seg.records.take j)
                              (∀ j : ℕ, n + 1 ≤ j → j ≤ seg.records.length →
                                ∃ suffixAccepted,
                                  CollectionCheckedExecution.checkedRounds done.final
                                    ((seg.inputs.drop (n + 1)).take (j - (n + 1))) =
                                      some (suffixAccepted, Ledge j) ∧
                                  (seg.records.take j).map (fun (r : RoundRecord (p := p) (rate := rate)) => r.input.time.val + 1) =
                                    List.range' u j ∧
                                  (Ledge j).cutoffRegisters a =
                                    some ⟨(X0 N).1, (X0 N).2, (X0 N).1 - (X0 (N - 1)).1⟩ ∧
                                  (Ledge j).currentRegisters a =
                                    some ⟨(Y0 j).2, (Y0 j).1 - (Y0 (j - 1)).1⟩ ∧
                                  (Ledge j).increment a =
                                    (QueueReplay.replay cap (0, U.val.q) (H j)).1 ∧
                                  (Ledge j).increment a = (Y0 j).1 - (X0 N).1 ∧
                                  ((X0 N).1 + (Ledge j).increment a, (Y0 j).2) = Y0 j ∧
                                  (Ledge j).assignment = I.assignment ∧
                                  (Ledge j).sigma = sigma ∧ (Ledge j).cutoff = u ∧
                                  (Ledge j).freezeAt = I.freezeAt) ∧
                              done.final = Ledge (n + 1) ∧
                              CollectionCheckedExecution.checkedRounds done.final [] =
                                some ([], done.final) ∧
                              ∃ suffixAccepted,
                                CollectionCheckedExecution.checkedRounds done.final
                                  ((seg.inputs.drop (n + 1)).take
                                    (seg.records.length - (n + 1))) =
                                      some (suffixAccepted, seg.final) ∧
                                seg.records.map (fun (r : RoundRecord (p := p) (rate := rate)) => r.input.time.val + 1) =
                                  List.range' u seg.records.length ∧
                                seg.final.cutoffRegisters a =
                                  some ⟨(X0 N).1, (X0 N).2, (X0 N).1 - (X0 (N - 1)).1⟩ ∧
                                seg.final.currentRegisters a = some ⟨
                                  (Y0 seg.records.length).2,
                                  (Y0 seg.records.length).1 - (Y0 (seg.records.length - 1)).1⟩ ∧
                                seg.final.increment a =
                                  (QueueReplay.replay cap (0, U.val.q) (H seg.records.length)).1 ∧
                                seg.final.increment a = (Y0 seg.records.length).1 - (X0 N).1 ∧
                                ((X0 N).1 + seg.final.increment a, (Y0 seg.records.length).2) =
                                  Y0 seg.records.length ∧
                                seg.final.assignment = I.assignment ∧
                                seg.final.sigma = sigma ∧ seg.final.cutoff = u ∧
                                seg.final.freezeAt = I.freezeAt) := by
  classical
  intro R
  obtain ⟨c, b, j, logged, after, cut, raw, scan, registers, lastService,
    hc, hbj, hjk, hbirth, hretained, hlogged, hdown, houtcome,
    hscan, hchecked, hq, hdpos, hdle, htimes, hLlen, v, ho,
    hselected, hprepared, hQ, hEd, hAlen, hAenabled, hregisters, hlastService,
    hz, hzk, terminal, terminalMemory, hterminalChoice, hterminalStatus,
    hterminalDown, hterminalRegisters, hterminalDelta, hUsigma,
    hUSterminal, hUdterminal, hUqterminal, hUNumerical, hUDNumerical, hledger⟩ :=
    ReferenceFirstReplacementAcceptedUpNumericalSeed.complete_accepted_up_first_replacement_numerical_seed
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
  let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  let o := u - (s + 1)
  let n := k.val - o
  obtain ⟨seg, done, c0, I, hok, hoR, hn, hsegment, hentry, hsegContext,
    hc0, hP0, hI, hIchecked, hIsigma, hIcutoff, hentryTime, hlive,
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
    hcurrentRegisters, hincrement, hcutoffRegisters, hcutoffTime, hnext,
    hH, hcutnum, hcurrentnum, hincreplay, hincnum, hfinishnum, hseedFull⟩ := hledger
  let B0 := I.base i
  let X := fun count => QueueReplay.replay cap (B0, M.val.q) (A.take count)
  let H := fun count => (seg.records.take count).map
    (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a)
  let Y := fun count => QueueReplay.replay cap (B0, M.val.q) (A ++ H count)
  let Ledge := fun count => endpointLedger seg.context.preLedger (seg.records.take count)
  have hsegmentRun : segmentAt
      (run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s (p.T - s) span active).records o = some seg := by
    rw [← hrun]
    exact hsegment
  have hextract : extractRound (seg.records[n]'hn) = some done := by
    rw [hrecord hn]
    exact hdone
  have hactualSuffix :=
    ReferenceCollectionAcceptedQueueContinuation.actual_accepted_up_physical_queue_suffix_continuation
      initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards s (p.T - s) span active hfirst o seg hsegmentRun
      n hn done hextract haccepted U hparsed i hsender
  obtain ⟨IA, hIA, _hcheckedStartA, _hwholeA, hprefixDataA⟩ := hactualSuffix
  obtain ⟨_prefixA, _hprefixRunA, _hprefixInitialA, _hprefixFinalA, hroundDataA⟩ :=
    hprefixDataA
  obtain ⟨_recordingA, _startedA, _decodedA, _bankA, finishedA,
    _hrecordingA, _hrecorderA, _hstartA, _hreceiveA, _hdecodeA, _hfinishA,
    hfinishedA, _hinputA, hhistoryA⟩ := hroundDataA
  obtain ⟨_hboundA, _lastIndexA, _hlastRoundA, _hlastIndexA, _hcursorA,
    _hassignmentA, hArmA, _hsigmaA, _hcutoffA, _hfreezeA, hbaseA,
    _hcutposA, _hcutcursorA, _hcursorTA, _hprefixUnknownA, _hstartedUnknownA,
    hpastDataA⟩ := hhistoryA
  obtain ⟨_pastA, _currentA, _hpastA, _hcurrentA, _hsuppliedA,
    _hpastPhysicalA, _hcurrentPhysicalA, _hpastCurrentA, _hphysicalAppendA,
    _hcurrentRegistersA, _hincrementA, hcutoffRegistersA, hcontinuationDataA⟩ :=
    hpastDataA
  have hforallA := hcontinuationDataA.1
  have hIAeq : IA = I := by
    apply Option.some.inj
    calc
      some IA = seg.context.initializer := hIA.symm
      _ = some I := by rw [hsegContext]; exact hI
  subst IA
  have hfinishedEq : finishedA = finished := hfinishedA.trans hfinished.symm
  have harm : I.assignment.arm i = a := congrFun hIarm i
  have htake : A.take N = A := List.take_of_length_le (Nat.le_of_eq hAlen)
  have hUReplay : QueueReplay.replay cap (0, M.val.q) A =
      (U.val.S, U.val.q) := hUNumerical.symm
  have hXN : X N = (B0 + U.val.S, U.val.q) := by
    dsimp only [X]
    rw [htake]
    have htranslate :=
      replay_score_origin cap B0 (0, M.val.q) A
    simpa only [Nat.add_zero, hUReplay] using htranslate
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
      replay_score_origin cap (B0 + U.val.S) (0, U.val.q) (H count)
  have hcutoffValue :
      (⟨I.base i + U.val.S, U.val.q, U.val.delta⟩ :
        CoordinatorCollectionLedger.CutoffRegister) =
        ⟨(X N).1, (X N).2, (X N).1 - (X (N - 1)).1⟩ := by
    apply Option.some.inj
    rw [hfinishedEq, ← hArmA, harm, hbaseA] at hcutoffRegistersA
    exact hcutoffRegistersA.symm.trans hcutnum
  have hcalendar (count : ℕ) (hcount : count ≤ seg.records.length) :
      (seg.records.take count).map (fun (r : RoundRecord (p := p) (rate := rate)) => r.input.time.val + 1) =
        List.range' u count := by
    have hlength : seg.records.length + seg.remaining.length = R.length - o := by
      have h := congrArg List.length hpartition
      simpa only [List.length_append, List.length_drop] using h
    have hprefixEq : seg.records.take count = (R.drop o).take count := by
      rw [← hpartition, List.take_append_of_le_length hcount]
    have hentryClock := ReferenceAssignmentFollowerMassSteps.complete_record_time
      rate rewards C_star C_h source ⟨o, hoR⟩
    have hstartTime : s + o + 1 = u := by
      have he := hentryTime
      rw [hentry hoR, hentryClock] at he
      exact he
    have hrunTimes := run_time_values initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards s (p.T - s) span active
    have hrunLength := run_record_count initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards s (p.T - s) span active
    rw [← hrun] at hrunTimes hrunLength
    have hcalendarR : R.map (fun (r : RoundRecord (p := p) (rate := rate)) =>
        r.input.time.val + 1) = List.range' (s + 1) R.length := by
      have h := congrArg (List.map (fun time : ℕ => time + 1)) hrunTimes
      simpa only [List.map_map, Function.comp_def, calendar,
        ← List.range'_succ_left, ← hrunLength, R] using h
    have hcountBound : count ≤ R.length - o := by
      rw [← hlength]
      exact hcount.trans (Nat.le_add_right _ _)
    rw [hprefixEq, List.map_take, List.map_drop, hcalendarR,
      List.drop_range', Nat.mul_one, List.take_range'_of_length_ge hcountBound]
    rw [Nat.add_right_comm s 1 o, hstartTime]

  have hcontinuation : ∀ count, n + 1 ≤ count → count ≤ seg.records.length →
      ∃ suffixAccepted,
        CollectionCheckedExecution.checkedRounds done.final
          ((seg.inputs.drop (n + 1)).take (count - (n + 1))) =
            some (suffixAccepted, Ledge count) ∧
        (seg.records.take count).map (fun (r : RoundRecord (p := p) (rate := rate)) => r.input.time.val + 1) =
          List.range' u count ∧
        (Ledge count).cutoffRegisters a =
          some ⟨(X N).1, (X N).2, (X N).1 - (X (N - 1)).1⟩ ∧
        (Ledge count).currentRegisters a =
          some ⟨(Y count).2, (Y count).1 - (Y (count - 1)).1⟩ ∧
        (Ledge count).increment a =
          (QueueReplay.replay cap (0, U.val.q) (H count)).1 ∧
        (Ledge count).increment a = (Y count).1 - (X N).1 ∧
        ((X N).1 + (Ledge count).increment a, (Y count).2) = Y count ∧
        (Ledge count).assignment = I.assignment ∧
        (Ledge count).sigma = sigma ∧ (Ledge count).cutoff = u ∧
        (Ledge count).freezeAt = I.freezeAt := by
    intro count hlower hupper
    obtain ⟨accepted, hfold, hcur, hinc, hcut, hassign, hsig, hcutTime, hfreeze⟩ :=
      hforallA count hlower hupper
    rw [harm] at hcur hinc hcut
    change (Ledge count).currentRegisters a =
      some ⟨(QueueReplay.replay cap (0, U.val.q) (H count)).2,
        (QueueReplay.replay cap (0, U.val.q) (H count)).1 -
          (QueueReplay.replay cap (0, U.val.q) (H (count - 1))).1⟩ at hcur
    change (Ledge count).increment a =
      (QueueReplay.replay cap (0, U.val.q) (H count)).1 at hinc
    refine ⟨accepted, hfold, hcalendar count hupper, ?_, ?_, hinc, ?_, ?_,
      hassign, hsig.trans hIsigma, hcutTime.trans hIcutoff, hfreeze⟩
    · rw [hcut, hcutoffValue]
    · rw [hcur, hY count, hY (count - 1)]
      simp only [Nat.add_sub_add_left]
    · rw [hY count, hinc]
      simp only [Nat.add_sub_cancel_left]
    · rw [hY count, hinc]
  have hacceptedEndpoint : done.final = Ledge (n + 1) := by
    obtain ⟨accepted, hfold, _⟩ := hcontinuation (n + 1) (by rfl) (Nat.succ_le_of_lt hn)
    simp only [Nat.sub_self, List.take_zero,
      CollectionCheckedExecution.checkedRounds] at hfold
    exact congrArg Prod.snd (Option.some.inj hfold)
  refine ⟨c, b, j, logged, after, cut, raw, scan, registers, lastService,
    hc, hbj, hjk, hbirth, hretained, hlogged, hdown, houtcome,
    hscan, hchecked, hq, hdpos, hdle, htimes, hLlen, v, ho,
    hselected, hprepared, hQ, hEd, hAlen, hAenabled, hregisters, hlastService,
    hz, hzk, terminal, terminalMemory, hterminalChoice, hterminalStatus,
    hterminalDown, hterminalRegisters, hterminalDelta, hUsigma,
    hUSterminal, hUdterminal, hUqterminal, hUNumerical, hUDNumerical,
    seg, done, c0, I, hok, hoR, hn, hsegment, hentry, hsegContext,
    hc0, hP0, hI, hIchecked, hIsigma, hIcutoff, hentryTime, hlive,
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
    hcurrentRegisters, hincrement, hcutoffRegisters, hcutoffTime, hnext,
    hH, hcutnum, hcurrentnum, hincreplay, hincnum, hfinishnum, ?_⟩
  intro hb
  obtain ⟨hcross, hspan, hshort, hepoch, seedDispatch, head0, initializer0,
    valid0, D0, hhead0, hpay0, hinit0, hchecked0, hDlen0, hzero0,
    hcells0, hprefix0, hell0, hseedBase, hseedQueue, hactual0,
    hseed, hX0, hY0, hseedCut, hseedCurrent, hseedIncrement, hseedPair⟩ := hseedFull hb
  let Cells0 := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate source rewards C_star C_h hcross (p.T - s) hspan
  let X0 := fun m => QueueReplay.replay cap (0, 0)
    (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells0 ++ D0) ++ A.take m)
  let Y0 := fun m => QueueReplay.replay cap (0, 0)
    (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells0 ++ D0) ++ (A ++ H m))
  change (∀ m, X m = X0 m) at hX0
  change (∀ m, Y m = Y0 m) at hY0
  refine ⟨hcross, hspan, hshort, hepoch, seedDispatch, head0, initializer0,
    valid0, D0, hhead0, hpay0, hinit0, hchecked0, hDlen0, hzero0,
    hcells0, hprefix0, hell0, hseedBase, hseedQueue, hactual0,
    hseed, hX0, hY0, hseedCut, hseedCurrent, hseedIncrement, hseedPair,
    ?_, hacceptedEndpoint, rfl, ?_⟩
  · intro count hlower hupper
    obtain ⟨accepted, hfold, hclock, hcut, hcur, hinc, hdiff, hpair,
      hassign, hsig, hcutTime, hfreeze⟩ := hcontinuation count hlower hupper
    exact ⟨accepted, hfold, hclock, by simpa only [hX0] using hcut,
      by simpa only [hY0] using hcur, hinc,
      by simpa only [hX0, hY0] using hdiff,
      by simpa only [hX0, hY0] using hpair, hassign, hsig, hcutTime, hfreeze⟩
  · obtain ⟨accepted, hfold, hclock, hcut, hcur, hinc, hdiff, hpair,
      hassign, hsig, hcutTime, hfreeze⟩ :=
        hcontinuation seg.records.length (Nat.succ_le_of_lt hn) (by rfl)
    have hfinalLedger : Ledge seg.records.length = seg.final := by
      dsimp only [Ledge, Segment.final]
      rw [List.take_length]
    rw [hfinalLedger] at hfold hcut hcur hinc hdiff hpair hassign hsig hcutTime hfreeze
    rw [List.take_length] at hclock
    exact ⟨accepted, hfold, hclock, by simpa only [hX0] using hcut,
      by simpa only [hY0] using hcur, hinc,
      by simpa only [hX0, hY0] using hdiff,
      by simpa only [hX0, hY0] using hpair, hassign, hsig, hcutTime, hfreeze⟩

end Bandits.Support.ReferenceFirstReplacementAcceptedUpKnownQueueNumericalSeed

end
