/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteAcceptedUpKnownQueueContinuation

/-!
# Original-prefix replay at an arbitrary accepted-UP assignment

An actual accepted UP supplies its own installation birth, retained DOWN,
cutoff initializer, accepted round, and every physical collection prefix.
Conditioned only on the assigned arm's two actual initial replay equalities,
this module translates those retained local numerical witnesses to the original
accumulated per-arm prefix.  It does not assume a common calendar word.

Source evidence: `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-174`, all under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCorrectedSuccessorAssignedNumericalStep

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceCollectionSegmentExtraction

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

private theorem replay_from_prefix (cap : ℕ) (E records : List (Bool × ℕ))
    (score backlog : ℕ)
    (hstate : QueueReplay.replay cap (0, 0) E = (score, backlog)) :
    QueueReplay.replay cap (score, backlog) records =
      QueueReplay.replay cap (0, 0) (E ++ records) := by
  calc
    QueueReplay.replay cap (score, backlog) records =
        QueueReplay.replay cap (QueueReplay.replay cap (0, 0) E) records := by
          rw [hstate]
    _ = QueueReplay.replay cap (0, 0) (E ++ records) :=
      (QueueReplay.replay_append cap (0, 0) E records).symm

/--
Normalize one arbitrary actual accepted-UP assigned arm to its original
accumulated replay.  The universal prefix E and its score/queue equations are
placed after the actual birth, retained DOWN, and collection segment have
been constructed. These are the two expanded local induction inputs; this
module does not construct them for a new cycle. The accepted first-successor
installation seed provides equations on its own installation witnesses;
matching that installation and instantiating its original prefix remain
separate application obligations.
-/
theorem internal_complete_accepted_up_original_prefix_replay_of_initial_replay
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
          ∀ (E : List (Bool × ℕ)),
            M.val.q = (QueueReplay.replay cap (0, 0) E).2 →
            I.base i = (QueueReplay.replay cap (0, 0) E).1 →
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
              (Ledge count).freezeAt = I.freezeAt := by
  classical
  intro R
  obtain ⟨c, b, j, logged, after, cut, raw, scan, registers, lastService,
    hc, hbj, hjk, hbirth, hretained, hlogged, hdown, houtcome,
    hscan, hchecked, hq, hdpos, hdle, htimes, hLlen, v, ho,
    hselected, hprepared, hQ, hEd, hAlen, hAenabled, hregisters, hlastService,
    hz, hzk, terminal, terminalMemory, hterminalChoice, hterminalStatus,
    hterminalDown, hterminalRegisters, hterminalDelta, hUsigma,
    hUSterminal, hUdterminal, hUqterminal, hUNumerical, hUDNumerical,
    hcollection⟩ :=
    ReferenceCompleteAcceptedUpKnownQueueContinuation.complete_accepted_up_known_queue_continuation
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
  let liveRecords := (R.drop b.val).take N
  let qp := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let Cells : Fin N → RecordedQueueRun.RoundInput p.K := fun x =>
    ReferenceFirstWindowNumericalStream.sourceCell
      (liveRecords[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)) (v x).view.payload
      (v x).view.pendingAtChoice
      (ReferenceLaterLiveNumericalReadout.preparedStates
        (liveRecords[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)) (ho x))
      (v x).view.complementWeights (v x).view.cutoff
      (ReferenceLaterLiveNumericalReadout.selection_choiceValid (v x))
  let A := List.ofFn (fun x : Fin N =>
    ((Cells x).enabled, RecordedQueueRun.quantizedArrival qp (Cells x) a))
  let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  let o := u - (s + 1)
  let n := k.val - o
  obtain ⟨seg, done, c0, I, hok, hoR, hn, hsegment, hentry, hsegContext,
    hc0, hP0, hI, hIchecked, hIsigma, hIcutoff, hentryTime, hlive,
    hrecord, hdone, hcontext, haccepted, hparsed, hsender, hprefix,
    hlabels, hpartition, hexit, hoffset, hIarm, hIfreeze, hIbase,
    initial, span, active, hlaunch, hfirst, hrun, hwhole,
    prefixExecution, hprefixRun, hprefixInitial, hprefixFinal,
    recording, started, decoded, bank, finished, hrecording, hrecorder,
    hstart, hreceive, hdecode, hfinish, hfinished, hinput,
    hbound, lastIndex, hlastRound, hlastIndex, hcursor, hassignment, hstartedSigma,
    hstartedCutoff, hstartedFreeze, hstartedBase, hcutpos, hcutcursor, hcursorT,
    hprefixUnknown, hstartedUnknown, past, current, hpast, hcurrent, hsupplied,
    hpastPhysical, hcurrentPhysical, hpastCurrent, hphysicalAppend,
    hcurrentRegisters, hincrement, hcutoffRegisters, hcutoffU, hnext, hnumeric,
    hcontinuation, hacceptedEndpoint, hcheckedEmpty, hfinal⟩ := hcollection
  have hprovenance :=
    ReferenceAssignmentRetainedBirthProvenance.complete_collection_choice_birth_provenance
      rate rewards C_star C_h source k c hc
  dsimp only at hprovenance
  obtain ⟨bProv, hbProvk, hbirthProv, _hProvAssignment, _hProvSigma,
    _hProvCutoff, hbaseProv⟩ := hprovenance
  have htimeProv := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    (R[bProv.val]'bProv.isLt) c.payload hbirthProv
  have htimeBirth := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    (R[b.val]'b.isLt) c.payload hbirth
  have htime : (R[bProv.val]'bProv.isLt).input.time.val =
      (R[b.val]'b.isLt).input.time.val := htimeProv.symm.trans htimeBirth
  have hnodup : (R.map (fun r => r.input.time.val)).Nodup := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values]
    exact List.nodup_range'
  have hindex : bProv = b := by
    apply Fin.ext
    apply (hnodup.getElem_inj_iff
      (hi := by simpa only [List.length_map] using bProv.isLt)
      (hj := by simpa only [List.length_map] using b.isLt)).mp
    simpa only [List.getElem_map] using htime
  subst bProv
  have harm : started.assignment.arm i = a := by
    rw [hassignment, hIarm]
  have hunknownStarted : started.currentRegisters a = none := by
    rw [← harm]
    exact hstartedUnknown
  have hunknownBefore : done.context.preLedger.currentRegisters a = none :=
    CollectionBufferProvenance.startRound_success_unknown_reflects
      _ _ _ _ _ a hstart hunknownStarted
  have hgammaStarted : started.gammaLoc a = 0 := by
    rw [CollectionCheckedExecution.startRound_success_candidate
      _ _ _ _ _ hstart]
    exact CoordinatorCollectionLedger.startRoundCandidate_unknown_zero
      _ _ _ _ a hunknownBefore
  have hgammaDecoded : decoded.gammaLoc a = 0 := by
    obtain ⟨_, _, _, _, _, _, _, _, hcandidate⟩ :=
      CollectionCheckedExecution.decodeUp_success_candidate started decoded i U hdecode
    rw [hcandidate]
    exact hgammaStarted
  have hfinishActual : CoordinatorCollectionLedger.finishRound decoded =
      .success done.final := by
    rw [← hfinished]
    exact hfinish
  have hfinishIncrement : done.final.increment a = decoded.increment a := by
    rw [← hfinished,
      CollectionCheckedExecution.finishRound_success_candidate decoded finished hfinish]
    change decoded.increment a + decoded.gammaLoc a = decoded.increment a
    rw [hgammaDecoded, Nat.add_zero]
  have hnextActual : ∃ saved, (R[k.val]'k.isLt).output.next.coordinator =
      .collection P done.final saved := by
    rw [← hfinished]
    exact hnext
  let B0 := I.base i
  let X := fun count => QueueReplay.replay cap (B0, M.val.q) (A.take count)
  let H := fun count => (seg.records.take count).map
    (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a)
  let Y := fun count => QueueReplay.replay cap (B0, M.val.q) (A ++ H count)
  let Ledge := fun count => endpointLedger seg.context.preLedger (seg.records.take count)
  let L := liveRecords
  obtain ⟨hH, hnumericCutoff, hnumericCurrent, hnumericIncrement,
    hnumericDifference, hnumericPair⟩ := hnumeric
  have htake : A.take N = A := List.take_of_length_le (Nat.le_of_eq hAlen)
  have hUReplay : QueueReplay.replay cap (0, M.val.q) A =
      (U.val.S, U.val.q) := hUNumerical.symm
  have hXN : X N = (B0 + U.val.S, U.val.q) := by
    dsimp only [X]
    rw [htake]
    have htranslate := replay_score_origin cap B0 (0, M.val.q) A
    simpa only [Nat.add_zero, hUReplay] using htranslate
  have hXprev : X (N - 1) =
      (B0 + (QueueReplay.replay cap (0, M.val.q) (A.take (N - 1))).1,
        (QueueReplay.replay cap (0, M.val.q) (A.take (N - 1))).2) := by
    dsimp only [X]
    exact replay_score_origin cap B0 (0, M.val.q) (A.take (N - 1))
  refine ⟨c, b, j, logged, after, cut, raw, scan, registers, lastService,
    hc, hbj, hjk, hbirth, hretained, hlogged, hdown, houtcome,
    ?_⟩
  dsimp only [P, M, a, sigma, cap, bits, u, ell, N, d, o, n, L, qp]
  refine ⟨hscan, hchecked, hq, hUsigma, hdpos, hdle, htimes, hLlen, v, ho,
    hselected, hprepared, hQ, hEd, hAlen, hAenabled, hregisters, hlastService,
    ?_⟩
  refine ⟨seg, done, c0, I, hok, hoR, hn, hsegment, hentry, hsegContext,
    hc0, hP0, hI, hIchecked, hIarm, hIsigma, hIcutoff, hIbase, hbaseProv,
    hrecord, hdone, hcontext, haccepted, hparsed, hsender,
    hacceptedEndpoint, recording, started, decoded, bank, hrecording, hstart,
    hreceive, hdecode, hfinishActual, hassignment, hunknownStarted,
    hgammaStarted, hgammaDecoded, hfinishIncrement, hnextActual, ?_⟩
  intro E hqE hbaseE
  let Full := fun count => QueueReplay.replay cap (0, 0)
    (E ++ (A ++ H count))
  let Cut := QueueReplay.replay cap (0, 0) (E ++ A)
  let Prev := QueueReplay.replay cap (0, 0) (E ++ A.take (N - 1))
  have hstate : QueueReplay.replay cap (0, 0) E = (B0, M.val.q) := by
    exact Prod.ext hbaseE.symm hqE.symm
  have hprefix (count : ℕ) :
      QueueReplay.replay cap (0, 0) (E ++ A.take count) =
        (B0 + (QueueReplay.replay cap (0, M.val.q) (A.take count)).1,
          (QueueReplay.replay cap (0, M.val.q) (A.take count)).2) := by
    calc
      _ = QueueReplay.replay cap (B0, M.val.q) (A.take count) :=
        (replay_from_prefix cap E (A.take count) B0 M.val.q hstate).symm
      _ = _ := by
        simpa only [Nat.add_zero] using
          replay_score_origin cap B0 (0, M.val.q) (A.take count)
  have hregistersReplay : registers =
      QueueReplay.replay cap (0, M.val.q) (A.take d) := hregisters
  have hdownNormalized : (I.base i + registers.1, registers.2) =
      QueueReplay.replay cap (0, 0) (E ++ A.take d) :=
    (congrArg (fun state : ℕ × ℕ => (B0 + state.1, state.2))
      hregistersReplay).trans (hprefix d).symm
  have hdownLastNormalized : lastService =
      (QueueReplay.replay cap (0, 0) (E ++ A.take d)).1 -
        (QueueReplay.replay cap (0, 0) (E ++ A.take (d - 1))).1 := by
    rw [hprefix d, hprefix (d - 1), Nat.add_sub_add_left]
    exact hlastService
  have hfull (count : ℕ) : Full count = Y count := by
    dsimp only [Full, Y, B0]
    exact (replay_from_prefix cap E (A ++ H count) (I.base i) M.val.q hstate).symm
  have hcut : Cut = X N := by
    dsimp only [Cut, X, B0]
    calc
      QueueReplay.replay cap (0, 0) (E ++ A) =
          QueueReplay.replay cap (I.base i, M.val.q) A :=
            (replay_from_prefix cap E A (I.base i) M.val.q hstate).symm
      _ = X N := by
        dsimp only [X]
        rw [htake]
  have hprev : Prev = X (N - 1) := by
    dsimp only [Prev, X, B0]
    calc
      QueueReplay.replay cap (0, 0) (E ++ A.take (N - 1)) =
          QueueReplay.replay cap (I.base i, M.val.q) (A.take (N - 1)) :=
            (replay_from_prefix cap E (A.take (N - 1)) (I.base i) M.val.q hstate).symm
      _ = X (N - 1) := rfl
  have hcutValue : Cut = (I.base i + U.val.S, U.val.q) := by
    rw [hcut, hXN]
  have hprevScore : Prev.1 = B0 +
      (QueueReplay.replay cap (0, M.val.q) (A.take (N - 1))).1 := by
    exact congrArg Prod.fst (hprev.trans hXprev)
  have hcutScore : Cut.1 = B0 + U.val.S := congrArg Prod.fst hcutValue
  have hrelativeScore :
      (QueueReplay.replay cap (0, M.val.q) A).1 = U.val.S :=
    congrArg Prod.fst hUReplay
  have hdelta : U.val.delta = Cut.1 - Prev.1 := by
    calc
      U.val.delta =
          (QueueReplay.replay cap (0, M.val.q) A).1 -
            (QueueReplay.replay cap (0, M.val.q) (A.take (N - 1))).1 := hUDNumerical
      _ = (B0 + (QueueReplay.replay cap (0, M.val.q) A).1) -
            (B0 + (QueueReplay.replay cap (0, M.val.q) (A.take (N - 1))).1) := by
              rw [Nat.add_sub_add_left]
      _ = Cut.1 - Prev.1 := by
        rw [hrelativeScore, ← hcutScore, ← hprevScore]
  have hacceptAppend : H (n + 1) = H n ++
      [ReferenceCollectionRawBufferHistory.physicalQueueRecord
        seg.context.preLedger a (R[k.val]'k.isLt)] := by
    exact hH
  refine ⟨hdownNormalized, hdownLastNormalized, hacceptAppend, hcutValue, hdelta, ?_⟩
  intro count hcountLower hcountUpper
  obtain ⟨suffixAccepted, hfold, hclock, hcutRegister, hcurrentRegister,
    hincrementRelative, hincrementDifference, haddPair, hassignment,
    hsigma, hcutoff, hfreeze⟩ := hcontinuation count hcountLower hcountUpper
  have hcurrentNormalized : (Ledge count).currentRegisters a =
      some ⟨(Full count).2, (Full count).1 - (Full (count - 1)).1⟩ := by
    rw [hfull count, hfull (count - 1)]
    exact hcurrentRegister
  have hcutoffNormalized : (Ledge count).cutoffRegisters a =
      some ⟨Cut.1, Cut.2, Cut.1 - Prev.1⟩ := by
    rw [hcut, hprev]
    exact hcutRegister
  have hincrementNormalized : (Ledge count).increment a =
      (Full count).1 - Cut.1 := by
    rw [hfull count, hcut]
    exact hincrementDifference
  have haddNormalized : Cut.1 + (Ledge count).increment a =
      (Full count).1 := by
    rw [hcut, hfull count]
    exact congrArg Prod.fst haddPair
  exact ⟨suffixAccepted, hfold, hclock, hcutoffNormalized,
    hcurrentNormalized, hincrementNormalized, haddNormalized,
    hassignment, hsigma, hcutoff, hfreeze⟩

end Bandits.Support.ReferenceCorrectedSuccessorAssignedNumericalStep

end
