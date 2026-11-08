/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedNextInstallationCalendarSeed
public import Bandits.Support.ReferenceCorrectedSuccessorAssignedNumericalStep

/-!
# Initialized assigned replay at the first corrected successor

The original corrected-cell execution constructs its actual first successor
installation and all-arm calendar seed. On an actual accepted-UP branch for
that installation, timestamp and payload uniqueness align the retained birth.
Both original-prefix initial equations are then discharged on that same
installation, DOWN, initializer and calendar before applying preservation.
The live and collection words retain their native meanings; this does not
assert a globally synchronized calendar for arbitrary successor cycles.

Sources: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-174`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstCorrectedNextAssignedCalendarReplay

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceCollectionSegmentExtraction CoordinatorPhaseClock CoordinatorRoundDispatch
open CoordinatorAssignmentRegisterInstall LaterAssignmentStartOperation RecordedQueueRun

variable {p : ConstructorDimensions.Parameters}

/-- If an actual accepted-UP timestamp selects an actual installation record,
the birth retained by the accepted-UP continuation is that same record and
payload. The proof uses installation timestamps and injectivity of the physical
suffix calendar. -/
theorem accepted_up_birth_matches_installation
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input i U)
    (q : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (installed : AssignmentStartPayload.Input p rate.eta)
    (hinstalled : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[q.val] installed)
    (hselector : U.val.sigma = installed.sigma.val + 1) :
    ∃ (c : ReferenceCollectionSegmentExtraction.Choice rate)
      (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length),
      ReferenceAssignmentPayloadPersistence.InstallationBirth
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[b.val] c.payload ∧
      b = q ∧ c.payload = installed := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  have hstep :=
    ReferenceCorrectedSuccessorAssignedNumericalStep.internal_complete_accepted_up_original_prefix_replay_of_initial_replay
      rewards C_star C_h source k i U hacc
  dsimp only [R] at hstep
  rcases hstep with ⟨c, b, j, logged, after, cut, raw, scan, registers, lastService,
    hc, hbj, hjk, hbirth, hretained, hlogged, hdown, houtcome,
    hscan, hchecked, _hq, hUsigma, _hdpos, _hdle, _htimes, _hrest⟩
  have htimeBirth := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    (R[b.val]'b.isLt) c.payload hbirth
  have htimeInstalled := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    (R[q.val]'q.isLt) installed hinstalled
  have hpayloadSigma : c.payload.sigma.val = installed.sigma.val := by
    exact Nat.add_right_cancel (hUsigma.symm.trans hselector)
  have htime : (R[b.val]'b.isLt).input.time.val =
      (R[q.val]'q.isLt).input.time.val := by
    calc
      (R[b.val]'b.isLt).input.time.val = c.payload.sigma.val := htimeBirth.symm
      _ = installed.sigma.val := hpayloadSigma
      _ = (R[q.val]'q.isLt).input.time.val := htimeInstalled
  have hnodup : (R.map (fun record => record.input.time.val)).Nodup := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values]
    exact List.nodup_range'
  have hindex : b = q := by
    apply Fin.ext
    apply (hnodup.getElem_inj_iff
      (hi := by simpa only [List.length_map] using b.isLt)
      (hj := by simpa only [List.length_map] using q.isLt)).mp
    simpa only [List.getElem_map] using htime
  cases hindex
  have hpayload := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
    (R[q.val]'q.isLt) c.payload installed hbirth hinstalled
  exact ⟨c, q, hbirth, rfl, hpayload⟩

/-- Literal output fields for an initialized actual accepted-UP application.
This only packages constructed witnesses and their equations, including the
same birth, DOWN, initializer, physical collection word and endpoint ledgers.
It is used only as a conclusion, never as an initialization assumption. -/
def initialized_assigned_replay
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (next : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (installed : AssignmentStartPayload.Input p rate.eta)
    (E : List (Bool × ℕ)) : Prop :=
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    ∃ (c : ReferenceCollectionSegmentExtraction.Choice rate)
      (b j : Fin R.length)
      (logged after : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
      (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
      (scan : FollowerCutoffScan.ScanResult p.T)
      (registers : ℕ × ℕ) (lastService : ℕ),
      b = next ∧ c.payload = installed ∧
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
      let o := u - (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + 1)
      let n := k.val - o
      let L := (R.drop b.val).take N
      let qp := ReferenceFirstLaunchNumericalCell.queueParameters rate
      ell = scan.endpoint ∧
      ActiveFollowerDownAcceptance.checkedRecovery p rate M logged ell =
        .ok ⟨registers, lastService⟩ ∧
      M.val.q = P.queues a ∧ U.val.sigma = sigma ∧ 0 < d ∧ d ≤ N ∧
      L.map (fun r : RoundRecord (p := p) (rate := rate) => r.input.time.val + 1) =
        List.range' sigma N ∧
      ∃ (hLlen : L.length = N)
        (v : ∀ x : Fin N, Selection
          (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)).input)
        (ho : ∀ x : Fin N, ReferenceLaterLiveNumericalReadout.preparedOrdinary
          (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm))),
        (∀ x, (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)).output.preparation.coordinator.selection =
            some (v x) ∧ (v x).view.payload = P ∧ (v x).view.cutoff = none ∧
            CoordinatorLocalArmChoice.assignmentIsLive (v x).view.payload
              (v x).view.cutoff (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)).input.time) ∧
        (∀ x f, (ReferenceFollowerFixedReply.actualChoice
            (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)) f).configuration =
          .ordinary
            (ReferenceLaterLiveNumericalReadout.preparedStates
              (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)) (ho x) f)
            (ReferenceLaterLiveNumericalReadout.preparedMemories
              (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)) (ho x) f)) ∧
        let Cells : Fin N → RecordedQueueRun.RoundInput p.K := fun x =>
          ReferenceFirstWindowNumericalStream.sourceCell
            (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)) (v x).view.payload
            (v x).view.pendingAtChoice
            (ReferenceLaterLiveNumericalReadout.preparedStates
              (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)) (ho x))
            (v x).view.complementWeights (v x).view.cutoff
            (ReferenceLaterLiveNumericalReadout.selection_choiceValid (v x))
        let A := List.ofFn (fun x : Fin N =>
          ((Cells x).enabled, RecordedQueueRun.quantizedArrival qp (Cells x) a))
        let V := fun count => QueueReplay.replay cap (0, M.val.q) (A.take count)
        let Ed := ((R.drop b.val).take d).map
          (fun r => (true, ReferenceFollowerSparseEmissionRecovery.emissionContribution M i r))
        let Q := ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged ell
        Q = Ed ∧ Ed = A.take d ∧ A.length = N ∧
        (∀ x ∈ A, x.1 = true) ∧ registers = V d ∧
        lastService = (V d).1 - (V (d - 1)).1 ∧
        ∃ (seg : Segment rate) (done : CompletedRound rate)
          (c0 : Choice rate) (I : Initializer p),
          o ≤ k.val ∧ o < R.length ∧ n < seg.records.length ∧
          segmentAt R o = some seg ∧
          (∀ ho : o < R.length, seg.entry = R[o]'ho) ∧
          seg.context = c0 ∧ choice seg.entry.input = some c0 ∧ c0.payload = P ∧
          c0.initializer = some I ∧ I.checkedStart rate = .success seg.context.preLedger ∧
          I.assignment.arm = P.assignment.assigned ∧ I.sigma = sigma ∧ I.cutoff = u ∧
          I.base = c.preLedger.baseScore ∧
          (match (R[b.val]'b.isLt).output.preparation.coordinator with
          | .first (.chosen installed _) => c.preLedger.baseScore = installed.followerBaseScore
          | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
              c.preLedger.baseScore = installed.retainedBaseScore
          | _ => False) ∧
          (∀ hn : n < seg.records.length, seg.records[n]'hn = R[k.val]'k.isLt) ∧
          extractRound (R[k.val]'k.isLt) = some done ∧ done.context = c ∧
          done.accepted = true ∧ done.input.parsed = some U ∧ done.input.selectedFollower = i ∧
          let H := fun count => (seg.records.take count).map
            (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a)
          let Ledge := fun count => endpointLedger seg.context.preLedger (seg.records.take count)
          done.final = Ledge (n + 1) ∧
          ∃ (recording : CoordinatorRecordingOperation.Output p)
            (started decoded : ReferenceActivePhysicalStep.Ledger rate)
            (bank : CoordinatorUpReception.UpDecoderBank p),
            (R[k.val]'k.isLt).output.coordinator.recording = some recording ∧
            CoordinatorCollectionLedger.startRound done.context.preLedger
              ((R[k.val]'k.isLt).input.time.val + 1)
              (ReferenceActivePhysicalStep.collectionEnabled done.context.preLedger
                (R[k.val]'k.isLt).input.time)
              (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                .success started ∧
            (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare (R[k.val]'k.isLt).input) started).result =
                .success (decoded, bank) ∧
            CoordinatorCollectionLedger.decodeUp started i (some U) = .success decoded ∧
            CoordinatorCollectionLedger.finishRound decoded = .success done.final ∧
            started.assignment = I.assignment ∧
            started.currentRegisters a = none ∧ started.gammaLoc a = 0 ∧
            decoded.gammaLoc a = 0 ∧ done.final.increment a = decoded.increment a ∧
            (∃ saved, (R[k.val]'k.isLt).output.next.coordinator =
              .collection P done.final saved) ∧
          M.val.q = (QueueReplay.replay cap (0, 0) E).2 ∧
          I.base i = (QueueReplay.replay cap (0, 0) E).1 ∧
          let Full := fun count => QueueReplay.replay cap (0, 0)
            (E ++ (A ++ H count))
          let Cut := QueueReplay.replay cap (0, 0) (E ++ A)
          let Prev := QueueReplay.replay cap (0, 0)
            (E ++ A.take (N - 1))
          (I.base i + registers.1, registers.2) =
            QueueReplay.replay cap (0, 0) (E ++ A.take d) ∧
          lastService =
            (QueueReplay.replay cap (0, 0) (E ++ A.take d)).1 -
              (QueueReplay.replay cap (0, 0) (E ++ A.take (d - 1))).1 ∧
          H (n + 1) = H n ++
            [ReferenceCollectionRawBufferHistory.physicalQueueRecord
              seg.context.preLedger a (R[k.val]'k.isLt)] ∧
          Cut = (I.base i + U.val.S, U.val.q) ∧
          U.val.delta = Cut.1 - Prev.1 ∧
          ∀ count, n + 1 ≤ count → count ≤ seg.records.length →
            ∃ suffixAccepted,
              CollectionCheckedExecution.checkedRounds done.final
                ((seg.inputs.drop (n + 1)).take (count - (n + 1))) =
                  some (suffixAccepted, Ledge count) ∧
              (seg.records.take count).map
                (fun r : RoundRecord (p := p) (rate := rate) => r.input.time.val + 1) =
                  List.range' u count ∧
              (Ledge count).cutoffRegisters a =
                some ⟨Cut.1, Cut.2, Cut.1 - Prev.1⟩ ∧
              (Ledge count).currentRegisters a =
                some ⟨(Full count).2, (Full count).1 - (Full (count - 1)).1⟩ ∧
              (Ledge count).increment a = (Full count).1 - Cut.1 ∧
              Cut.1 + (Ledge count).increment a = (Full count).1 ∧
              (Ledge count).assignment = I.assignment ∧
              (Ledge count).sigma = sigma ∧ (Ledge count).cutoff = u ∧
              (Ledge count).freezeAt = I.freezeAt

/-- Local composition of an actual installation's two numerical values with
one actual accepted-UP continuation. The original-source theorem below supplies
all installation and initialization inputs from its native first successor. -/
private theorem initialized_accepted_up
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input i U)
    (next : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (installed : AssignmentStartPayload.Input p rate.eta)
    (base : Fin (p.m - 1) → ℕ)
    (E : List (Bool × ℕ))
    (hinstalled : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[next.val] installed)
    (hbase : (match (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[next.val].output.preparation.coordinator with
      | .first (.chosen installation _) => some installation.followerBaseScore
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installation _) =>
          some installation.retainedBaseScore
      | _ => none) = some base)
    (hselector : U.val.sigma = installed.sigma.val + 1)
    (hqueue : (installed.downRecord i).val.q =
      (QueueReplay.replay (4 * rate.n) (0, 0) E).2)
    (hscore : base i = (QueueReplay.replay (4 * rate.n) (0, 0) E).1) :
    initialized_assigned_replay rewards C_star C_h source k i U next installed E := by
  classical
  unfold initialized_assigned_replay
  intro R
  obtain ⟨c, b, j, logged, after, cut, raw, scan, registers, lastService,
    hc, hbj, hjk, hbirth, hretained, hlogged, hdown, houtcome,
    hscan, hchecked, hq, hUsigma, hdpos, hdle, htimes, hLlen, v, ho,
    hselected, hprepared, hQ, hEd, hAlen, hAenabled, hregisters, hlastService,
    seg, done, c0, I, hok, hoR, hn, hsegment, hentry, hsegContext,
    hc0, hP0, hI, hIchecked, hIarm, hIsigma, hIcutoff, hIbase, hbaseProv,
    hrecord, hdone, hcontext, haccepted, hparsed, hsender,
    hacceptedEndpoint, recording, started, decoded, bank, hrecording, hstart,
    hreceive, hdecode, hfinish, hassignment, hunknownStarted,
    hgammaStarted, hgammaDecoded, hfinishIncrement, hnextActual, hcontinuation⟩ :=
    ReferenceCorrectedSuccessorAssignedNumericalStep.internal_complete_accepted_up_original_prefix_replay_of_initial_replay
      rewards C_star C_h source k i U hacc
  have htimeBirth := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    (R[b.val]'b.isLt) c.payload hbirth
  have htimeInstalled := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    (R[next.val]'next.isLt) installed hinstalled
  have hpayloadSigma : c.payload.sigma.val = installed.sigma.val :=
    Nat.add_right_cancel (hUsigma.symm.trans hselector)
  have htime : (R[b.val]'b.isLt).input.time.val =
      (R[next.val]'next.isLt).input.time.val :=
    htimeBirth.symm.trans (hpayloadSigma.trans htimeInstalled)
  have hnodup : (R.map (fun record => record.input.time.val)).Nodup := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values]
    exact List.nodup_range'
  have hindex : b = next := by
    apply Fin.ext
    apply (hnodup.getElem_inj_iff
      (hi := by simpa only [List.length_map] using b.isLt)
      (hj := by simpa only [List.length_map] using next.isLt)).mp
    simpa only [List.getElem_map] using htime
  subst b
  have hpayload := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
    (R[next.val]'next.isLt) c.payload installed hbirth hinstalled
  have hbaseRead : (match (R[next.val]'next.isLt).output.preparation.coordinator with
      | .first (.chosen installation _) => some installation.followerBaseScore
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installation _) =>
          some installation.retainedBaseScore
      | _ => none) = some c.preLedger.baseScore := by
    dsimp only [R]
    split at hbaseProv
    · rename_i heq
      rw [heq]
      exact congrArg some hbaseProv.symm
    · rename_i heq
      rw [heq]
      exact congrArg some hbaseProv.symm
    · exact False.elim hbaseProv
  have hbaseEq : c.preLedger.baseScore = base :=
    Option.some.inj (hbaseRead.symm.trans hbase)
  have hqueueE : (c.payload.downRecord i).val.q =
      (QueueReplay.replay (4 * rate.n) (0, 0) E).2 := by
    rw [hpayload]
    exact hqueue
  have hscoreE : I.base i = (QueueReplay.replay (4 * rate.n) (0, 0) E).1 := by
    rw [hIbase, hbaseEq]
    exact hscore
  have hinitialized := hcontinuation E hqueueE hscoreE
  refine ⟨c, next, j, logged, after, cut, raw, scan, registers, lastService,
    rfl, hpayload, hc, hbj, hjk, hbirth, hretained, hlogged, hdown, houtcome,
    hscan, hchecked, hq, hUsigma, hdpos, hdle, htimes, hLlen, v, ho,
    hselected, hprepared, hQ, hEd, hAlen, hAenabled, hregisters, hlastService,
    seg, done, c0, I, hok, hoR, hn, hsegment, hentry, hsegContext,
    hc0, hP0, hI, hIchecked, hIarm, hIsigma, hIcutoff, hIbase, hbaseProv,
    hrecord, hdone, hcontext, haccepted, hparsed, hsender,
    hacceptedEndpoint, recording, started, decoded, bank, hrecording, hstart,
    hreceive, hdecode, hfinish, hassignment, hunknownStarted,
    hgammaStarted, hgammaDecoded, hfinishIncrement, hnextActual,
    hqueueE, hscoreE, hinitialized⟩

/-- Apply the first successor's actual all-arm seed to each actual accepted UP
whose start selects that installation. The original corrected-cell source is
the only root premise. Horizon, dagger and non-later branches are preserved;
no existence of a future UP is asserted. The retained DOWN, cutoff and every
permitted post-UP physical prefix use one unchanged continuation witness. -/
theorem firstCell_next_installation_assigned_calendar_replay
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
                                        (∀ a : Fin p.K,
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
                                                  (U a q).1 - (U a (q - 1)).1))) ∧
                                        ∀ (k : Fin R.length) (i : Fin (p.m - 1))
                                          (reply : ReferenceCollectionPhaseHistory.UpRecord p rate),
                                          ReferenceCollectionPhaseHistory.AcceptedUp R[k.val].input i reply →
                                          reply.val.sigma = installation.registers.payload.sigma.val + 1 →
                                          let E := G.map (fun cell => (cell.enabled,
                                            quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                                              cell (installation.registers.payload.assignment.assigned i)))
                                          initialized_assigned_replay rewards C_star C_h z k i reply
                                            ⟨q, hv⟩ installation.registers.payload E)))
                )
    := by
  classical
  intro R s b Omega
  obtain ⟨L, c, birth, hL, hc, hprefix, hLb, htime, hb, ht,
    hrows, hselected, hrewards, henabled, hread, hcell0, hmode, hcont⟩ :=
    ReferenceFirstCorrectedNextInstallationCalendarSeed.firstCell_next_installation_calendar_seed
      rate rewards C_star C_h u t z hz
  refine ⟨L, c, birth, hL, hc, hprefix, hLb, htime, hb, ht,
    hrows, hselected, hrewards, henabled, hread, hcell0, hmode, ?_⟩
  intro rout qout beta hlive
  obtain ⟨hsigma, hcont⟩ := hcont rout qout beta hlive
  refine ⟨hsigma, ?_⟩
  intro hnextRound
  obtain ⟨hk, hstate, hlater, hBlen, heR, heT, hAlen, hAdate, hprefixA,
    rE, qE, hp, hstateE, hexit⟩ := hcont hnextRound
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z (b + 1)
  let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
    rewards C_star C_h z ⟨b + 1, hk⟩ rout qout beta hstate hlater
  let e := b + 1 + W.length
  let A := (L ++ [c]) ++ B
  refine ⟨hk, hstate, hlater, hBlen, heR, heT, hAlen, hAdate, hprefixA,
    rE, qE, hp, hstateE, ?_⟩
  rcases hexit with hhor | ⟨he, seg, I, l0, hseg, hentry, hpay, hpre,
    hI, hIdef, hchecked, harm, hIsigma, hIcut, hIscan, hfreeze, hbase,
    hcutchosen, hDuring, hpartition, dCells, hD, hG, hq, hT, hprefixG,
    hcoordinates, hdisabled, hunstopped, saved, hend, hcursor, hboundary⟩
  · exact Or.inl hhor
  · let q := e + seg.records.length
    let G := A ++ dCells
    let raw := fun (a : Fin p.K) (C : List (RecordedQueueRun.RoundInput p.K)) =>
      C.map (fun cell => (cell.enabled,
        quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a))
    let U := fun (a : Fin p.K) (h : ℕ) =>
      QueueReplay.replay (4 * rate.n) (0, 0) (raw a (G.take h))
    refine Or.inr ⟨he, seg, I, l0, hseg, hentry, hpay, hpre, hI, hIdef,
      hchecked, harm, hIsigma, hIcut, hIscan, hfreeze, hbase, hcutchosen,
      hDuring, hpartition, dCells, hD, hG, hq, hT, hprefixG, hcoordinates,
      hdisabled, hunstopped, saved, hend, hcursor, ?_⟩
    rcases hboundary with hhorQ | ⟨hv, hstateQ, hcoordQ, htimeQ, hdropQ, hchoiceQ⟩
    · exact Or.inl hhorQ
    · refine Or.inr ⟨hv, hstateQ, hcoordQ, htimeQ, hdropQ, ?_⟩
      rcases hchoiceQ with hnotLater | ⟨hlaterQ, hempty, haccepted, hnext⟩
      · exact Or.inl hnotLater
      · refine Or.inr ⟨hlaterQ, hempty, haccepted, ?_⟩
        obtain ⟨uNext, huNext, core, started, hstartNext, instruction, hassignment,
          htimeNext, hkind, consistent, output, hlocal, hcall, clockData, installation,
          selectedNext, hinstall, hresult, hdispatch, hpreparedNext, hrowsNext,
          hselectedNext, hrewardsNext, hpayload, hvector, hownVector, hreconstruction,
          hcorrected, hrenewal, hanchor, hweights, hprevious, hnoprevious,
          hselection, hvalues⟩ := hnext
        refine ⟨uNext, huNext, core, started, hstartNext, instruction, hassignment,
          htimeNext, hkind, consistent, output, hlocal, hcall, clockData, installation,
          selectedNext, hinstall, hresult, hdispatch, hpreparedNext, hrowsNext,
          hselectedNext, hrewardsNext, hpayload, hvector, hownVector, hreconstruction,
          hcorrected, hrenewal, hanchor, hweights, hprevious, hnoprevious,
          hselection, hvalues, ?_⟩
        intro k i V hacc hselector E
        have hnewBirth := ReferenceLaterInstallationProvenance.record_laterChosen_birth
          (R[q]'hv)
        rw [hpreparedNext] at hnewBirth
        obtain ⟨_, _, _, _, _, hassigned, _⟩ :=
          hvalues (installation.registers.payload.assignment.assigned i)
        obtain ⟨hbaseValue, hqueueValue⟩ := hassigned i rfl
        change installation.retainedBaseScore i =
          (U (installation.registers.payload.assignment.assigned i) q).1 at hbaseValue
        change (installation.registers.payload.downRecord i).val.q =
          (U (installation.registers.payload.assignment.assigned i) q).2 at hqueueValue
        have htake : G.take q = G := List.take_of_length_le (Nat.le_of_eq hG)
        exact initialized_accepted_up rewards C_star C_h z k i V hacc ⟨q, hv⟩
          installation.registers.payload installation.retainedBaseScore E hnewBirth
          (by rw [hpreparedNext]) hselector
          (by simpa only [U, raw, htake] using hqueueValue)
          (by simpa only [U, raw, htake] using hbaseValue)

end Bandits.Support.ReferenceFirstCorrectedNextAssignedCalendarReplay

end
