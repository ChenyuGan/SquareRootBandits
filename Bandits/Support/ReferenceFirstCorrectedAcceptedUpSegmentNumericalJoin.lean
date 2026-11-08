/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementAcceptedUpKnownQueueNumericalSeed
public import Bandits.Support.ReferenceFirstCorrectedReplacementCollectionBoundaryHistory

import Lean.Elab.Tactic.Omega

/-!
# Assigned-arm numerical values at the first corrected collection endpoint

Source evidence: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-174`.

The original corrected-cell run supplies whole-payload identity. Installation
chronology then identifies the accepted UP parent's birth and cutoff offsets
with this same extracted segment. Its actual initialized prefix and LIVE cells
seed the assigned arm's cutoff, current queue and accumulated increment at
`seg.final`. The two geometric localizers remain explicit implications.

This is an internal deterministic identity, with per-arm replay provenance.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstCorrectedAcceptedUpSegmentNumericalJoin

open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceCollectionSegmentExtraction

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- A real accepted UP in this segment supplies the initialized final values
of its assigned arm. Payload, birth offset and whole segment are identified
before the first-replacement parent's final equations are transported. -/
theorem firstCell_accepted_up_same_segment_numerical_values
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t)
    (e : ℕ) (seg : Segment rate)
    (hseg : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg)
    (hne : seg.records ≠ [])
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (hk : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val] ∈ seg.records)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input i U) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
    seg.context.payload.sigma.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z →
    FollowerCutoffScan.firstCutoff p rate.eta.val seg.context.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e + 1 →
    ∃ c : Choice rate, choice R[k.val].input = some c ∧ c.payload = seg.context.payload ∧
    ∃ I : Initializer p, seg.context.initializer = some I ∧
      I.checkedStart rate = .success seg.context.preLedger ∧
    let P := c.payload
    let a := P.assignment.assigned i
    let sigma := P.sigma.val + 1
    let uc := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)))
    let N := uc - sigma
    let L := (R.drop b).take N
    N = e - b ∧
    L.map (fun r => r.input.time.val + 1) = List.range' sigma N ∧
    ∃ (hLlen : L.length = N)
      (v : ∀ n : Fin N, Selection (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).input)
      (ho : ∀ n : Fin N, ReferenceLaterLiveNumericalReadout.preparedOrdinary
        (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm))),
      (∀ n, (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).output.preparation.coordinator.selection =
        some (v n) ∧ (v n).view.payload = P ∧ (v n).view.cutoff = none ∧
        CoordinatorLocalArmChoice.assignmentIsLive (v n).view.payload (v n).view.cutoff
          (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).input.time) ∧
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
    seg.final.cutoffRegisters a = some ⟨V.1, V.2, V.1 - Vprev.1⟩ ∧
    seg.final.currentRegisters a = some ⟨Q.2, Q.1 - Qprev.1⟩ ∧
    V.1 + seg.final.increment a = Q.1 := by
  classical
  intro R s b hsigma hcutoff
  have hpayAll :=
    (ReferenceFirstCorrectedReplacementCollectionBoundaryHistory.firstCell_collection_boundary_history
      rate rewards C_star C_h u t z hz e seg hseg hne hcut).2.2.1
  obtain ⟨c, bi, j, logged, after, cut, raw, scan, registers, lastService,
    hc, hbj, hjk, hbirth, hretained, hlogged, hdown, houtcome,
    hscan, hchecked, hq, hdpos, hdle, htimes, hLlen, v, ho,
    hselected, hprepared, hQ, hEd, hAlen, hAenabled, hregisters, hlastService,
    hz, hzk, terminal, terminalMemory, hterminalChoice, hterminalStatus,
    hterminalDown, hterminalRegisters, hterminalDelta, hUsigma,
    hUSterminal, hUdterminal, hUqterminal, hUNumerical, hUDNumerical, hledger⟩ :=
    ReferenceFirstReplacementAcceptedUpKnownQueueNumericalSeed.complete_accepted_up_first_replacement_known_queue_numerical_seed
      (rate := rate) rewards C_star C_h z k i U hacc
  have hp := hpayAll R[k.val] hk c hc
  have hbtime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[bi.val] c.payload hbirth
  have htime := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z bi
  have hbi : bi.val = b := by
    rw [hp, hsigma, htime] at hbtime
    change s + b = s + bi.val at hbtime
    omega
  let P := c.payload
  let cap := 4 * rate.n
  let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
    (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))
  let uc := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits
  let o := uc - (s + 1)
  have huc : uc = s + e + 1 := by simpa only [uc, bits, P, hp] using hcutoff
  have hoe : o = e := by dsimp only [o]; omega
  obtain ⟨segF, done, c0, I, hok, hoR, hn, hsegment, hentry, hsegContext,
    hc0, hP0, hI, hIchecked, hIsigma, hIcutoff, hentryTime, hlive,
    hrecord, hdone, hcontext, haccepted, hparsed, hsender, hprefix,
    hlabels, hpartition, hexit, hoffset, hIarm, hfreeze, hbase,
    initialF, spanF, activeF, hlaunchF, hfirstF, hrunF, hwhole,
    prefixExecution, hprefixRun, hprefixInitial, hprefixFinal,
    recording, started, decoded, bank, finished, hrecording, hrecorder,
    hstart, hreceive, hdecode, hfinish, hfinished, hinput,
    hbound, lastIndex, hlastRound, hlastIndex, hcursor, hassignment, hstartedSigma,
    hstartedCutoff, hstartedFreeze, hstartedBase, hcutpos, hcutcursor, hcursorT,
    hprefixUnknown, hstartedUnknown, past, current, hpast, hcurrent, hsupplied,
    hpastPhysical, hcurrentPhysical, hpastCurrent, hphysicalAppend,
    hcurrentRegisters, hincrement, hcutoffRegisters, hcutoffTime, hnext,
    hH, hcutnum, hcurrentnum, hincreplay, hincnum, hfinishnum, hseedFull⟩ := hledger
  change segmentAt R o = some segF at hsegment
  have hsegment' : segmentAt R e = some segF := by rw [← hoe]; exact hsegment
  have heq : segF = seg := Option.some.inj (hsegment'.symm.trans hseg)
  subst segF
  have hinitializer : seg.context.initializer = some I := by rw [hsegContext]; exact hI
  have hfirstBirth : bi.val =
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length +
        (ReferenceCollectionPhaseHistory.collectionWindow R
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length).length := hbi
  obtain ⟨hcross, hspan, hshort, hepoch, f, head0, initializer0,
    valid0, D0, hhead0, hpay0, hinit0, hchecked0, hDlen0, hzero0,
    hcells0, hprefix0, hell0, hseedBase, hseedQueue, hactual0,
    hseed, hX0, hY0, hseedCut, hseedCurrent, hseedIncrement, hseedPair,
    hcontinuation, hacceptedEndpoint, hemptyContinuation, suffixAccepted, hsuffix,
    hcalendar, hfinalCut, hfinalCurrent, hfinalIncReplay, hfinalInc, hfinalPair,
    hfinalAssignment, hfinalSigma, hfinalCutoff, hfinalFreeze⟩ := hseedFull hfirstBirth
  rw [← hbi]
  refine ⟨c, hc, hp, I, hinitializer, hIchecked, ?_⟩
  intro P' a' sigma' uc' N' L
  have hN : N' = e - bi.val := by
    change uc - (c.payload.sigma.val + 1) = e - bi.val
    rw [hp, hsigma]
    change uc - (s + b + 1) = e - bi.val
    omega
  refine ⟨hN, htimes, hLlen, v, ho, hselected, hprepared, ?_⟩
  intro Cells A
  refine ⟨hcross, hspan, hshort, f, head0, valid0, D0, hhead0, hpay0, hDlen0, ?_, hell0, ?_⟩
  · intro n
    obtain ⟨call, validCall, hcall, hpay, _, hcell, hrows, hJ, hrewards, htime, _⟩ := hcells0 n
    exact ⟨call, validCall, hcall, hpay, hcell, hrows, hJ, hrewards, htime⟩
  intro Cells0 E0 E H V Vprev Q Qprev
  change A.length = N' at hAlen
  let Xfull := QueueReplay.replay cap (0, 0) (E0 ++ A.take N')
  let Y := fun n => QueueReplay.replay cap (0, 0)
    (E0 ++ (A ++ (seg.records.take n).map
      (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a')))
  have hXfull : Xfull = V :=
    congrArg (fun words => QueueReplay.replay cap (0, 0) (E0 ++ words))
      (List.take_of_length_le (Nat.le_of_eq hAlen))
  have hwholeRecords : (seg.records.take seg.records.length).map
      (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a') = H :=
    congrArg (List.map (ReferenceCollectionRawBufferHistory.physicalQueueRecord
      seg.context.preLedger a')) (List.take_length (l := seg.records))
  have hYfull : Y seg.records.length = Q :=
    congrArg (QueueReplay.replay cap (0, 0))
      ((congrArg (fun words => E0 ++ (A ++ words)) hwholeRecords).trans
        (List.append_assoc E0 A H).symm)
  have hYprev : Y (seg.records.length - 1) = Qprev :=
    congrArg (QueueReplay.replay cap (0, 0))
      (List.append_assoc E0 A ((seg.records.take (seg.records.length - 1)).map
        (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a'))).symm
  change seg.final.cutoffRegisters a' =
    some ⟨Xfull.1, Xfull.2, Xfull.1 - Vprev.1⟩ at hfinalCut
  change seg.final.currentRegisters a' = some ⟨(Y seg.records.length).2,
    (Y seg.records.length).1 - (Y (seg.records.length - 1)).1⟩ at hfinalCurrent
  change (Xfull.1 + seg.final.increment a', (Y seg.records.length).2) =
    Y seg.records.length at hfinalPair
  rw [hXfull] at hfinalCut hfinalPair
  rw [hYfull, hYprev] at hfinalCurrent
  rw [hYfull] at hfinalPair
  exact ⟨hfinalCut, hfinalCurrent, congrArg Prod.fst hfinalPair⟩

end Bandits.Support.ReferenceFirstCorrectedAcceptedUpSegmentNumericalJoin
