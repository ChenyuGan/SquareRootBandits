/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteInstallationAssignedOriginReplay
public import Bandits.Support.ReferenceCompleteInstallationOutsideCalendarReplay

import Mathlib.Tactic

/-!
# Actual assigned-arm calendar replay for a later installation

An accepted UP at an actual later installation is aligned with its literal
whole source calendar, including the later known collection segment.

Source evidence: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-188`, under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteInstallationAssignedCalendarReplay

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceCollectionSegmentExtraction

variable {p : ConstructorDimensions.Parameters}

private theorem literal_replay_word_slots
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (P0 Cword Dword : List (RecordedQueueRun.RoundInput p.K)) (b e : ℕ)
    (hP0 : P0.length = b) (hP0C : (P0 ++ Cword).length = e)
    (hDlen : Dword.length = seg.records.length)
    (hpart : seg.records ++ seg.remaining = R.drop e)
    (hV : ((P0 ++ Cword) ++ Dword).length ≤ R.length)
    (hslots : ∀ x : Fin ((P0 ++ Cword) ++ Dword).length,
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
        (R[x.val]'(Nat.lt_of_lt_of_le x.isLt hV)) =
          some (((P0 ++ Cword) ++ Dword)[x.val]))
    (hraw : ∀ arm : Fin p.K,
      seg.records.map (ReferenceCollectionRawBufferHistory.physicalQueueRecord
        seg.context.preLedger arm) =
          ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm Dword) :
    (∀ x : Fin Cword.length,
      ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
        R[b + x.val]? = some r ∧
        ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some Cword[x.val]) ∧
    (∀ (arm : Fin p.K) (x : Fin seg.records.length),
      let d := Dword[x.val]'(Nat.lt_of_lt_of_eq x.isLt hDlen.symm)
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate seg.records[x.val] = some d ∧
      ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger
        arm seg.records[x.val] =
          (d.enabled, RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) d arm)) := by
  have htotal : ((P0 ++ Cword) ++ Dword).length = e + seg.records.length := by
    rw [List.length_append, hP0C, hDlen]
  have hP0C' : b + Cword.length = e := by
    simpa only [List.length_append, hP0] using hP0C
  constructor
  · intro x
    have hidx : b + x.val < ((P0 ++ Cword) ++ Dword).length := by omega
    have hR : b + x.val < R.length := Nat.lt_of_lt_of_le hidx hV
    refine ⟨R[b + x.val], List.getElem?_eq_getElem hR, ?_⟩
    have hh := hslots ⟨b + x.val, hidx⟩
    rw [List.getElem_append_left (by omega : b + x.val < (P0 ++ Cword).length),
      List.getElem_append_right (by omega : P0.length ≤ b + x.val)] at hh
    simpa only [hP0, Nat.add_sub_cancel_left] using hh
  · intro arm x
    dsimp only
    have hR : e + x.val < R.length := by omega
    have hrecord : seg.records[x.val] = R[e + x.val] := by
      have hh := congrArg (fun xs => xs[x.val]?) hpart
      rw [List.getElem?_append_left x.isLt, List.getElem?_drop] at hh
      simp only [List.getElem?_eq_getElem x.isLt,
        List.getElem?_eq_getElem hR] at hh
      exact Option.some.inj hh

    constructor
    · rw [hrecord]
      have hh := hslots ⟨e + x.val, by omega⟩
      rw [List.getElem_append_right (by omega : (P0 ++ Cword).length ≤ e + x.val)] at hh
      simpa only [hP0C, Nat.add_sub_cancel_left] using hh
    · have hh := congrArg (fun xs => xs[x.val]?) (hraw arm)
      simp only [ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar,
        List.getElem?_map, List.getElem?_eq_getElem x.isLt,
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_eq x.isLt hDlen.symm),
        Option.map_some] at hh
      exact Option.some.inj hh

private theorem continuing_excludes_accepted_up
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (reply : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hcontinue : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest r = true)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp r.input i reply) : False := by
  have hprep : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
    rw [r.output_eq]
    rfl
  unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest at hcontinue
  rw [hprep] at hcontinue
  obtain ⟨tail, recording, started, decoded, bank, ht, _⟩ := hacc
  unfold ReferenceCollectionPhaseHistory.executedTail at ht
  dsimp only at ht
  split at ht
  · contradiction
  · cases hc : (ReferenceActivePhysicalStep.prepare r.input).coordinator with
    | first outcome => simp only [hc, Bool.false_eq_true] at hcontinue
    | live registers owned base outcome =>
        cases outcome <;> simp only [hc] at ht hcontinue <;> contradiction
    | collection payload ledger clock cutoff outcome =>
        simp only [hc, Bool.false_eq_true] at hcontinue
    | invalidCollectionCutoff => simp only [hc, Bool.false_eq_true] at hcontinue
    | dagger => simp only [hc, Bool.false_eq_true] at hcontinue

/-- Numerical replay for an actual arbitrary later installation and an actual
accepted UP selected at its assigned arm.  The initial assigned queue and
score are derived from that installation's payload and retained base; the
accepted-UP replay is applied to the same literal calendar word through the
actual collection segment and its final ledger. The actual checked acceptance
round is replayed inclusively, and the same whole calendar supplies every later
known prefix through the segment's final ledger. -/
theorem actual_later_installation_assigned_arm_calendar_replay
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (reply : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input i reply)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true)
    (hselector : reply.val.sigma =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input.time.val + 1) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∃ (P0 : List (RecordedQueueRun.RoundInput p.K))
      (payload : AssignmentStartPayload.Input p rate.eta)
      (base : Fin (p.m - 1) → ℕ) (E : List (Bool × ℕ))
      (k0 : Fin R.length)
      (rb : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (qb : CoordinatorLiveServiceFinish.OwnedRegisters rb)
      (beta : Fin (p.m - 1) → ℕ)
      (cell : RecordedQueueRun.RoundInput p.K)
      (C : List (RecordedQueueRun.RoundInput p.K))
      (Cword Dword : List (RecordedQueueRun.RoundInput p.K)) (e : ℕ)
      (seg : ReferenceCollectionSegmentExtraction.Segment rate)
      (_hqueue : (payload.downRecord i).val.q =
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P0
          (payload.assignment.assigned i) P0.length).2)
      (_hscore : base i =
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P0
          (payload.assignment.assigned i) P0.length).1),
      ∃ (_hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth
          (R[b.val]'b.isLt) payload),
      ∃ (_hbase :
          (match (R[b.val]'b.isLt).output.preparation.coordinator with
          | .first (.chosen installed _) => some installed.followerBaseScore
          | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installation _) =>
              some installation.retainedBaseScore
          | _ => none) = some base)
        (_hselectorPayload : reply.val.sigma = payload.sigma.val + 1)
        (_hlater : s < payload.sigma.val)
        (_hP0 : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h (s + b.val) z = some P0)
        (_hscan : FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) = s + e + 1)
        (_hseg : ReferenceCollectionSegmentExtraction.segmentAt R e = some seg)
        (hClen : Cword.length = e - b.val)
        (hDlen : Dword.length = seg.records.length)
        (_hCslot : ∀ x : Fin Cword.length,
          ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
            R[b.val + x.val]? = some r ∧
            ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some Cword[x.val])
        (_hDslot : ∀ x : Fin seg.records.length,
          let c := Dword[x.val]'(Nat.lt_of_lt_of_eq x.isLt hDlen.symm)
          ReferenceFirstCollectionCurrentRetainedGate.cell0 rate seg.records[x.val] = some c ∧
          ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger
            (payload.assignment.assigned i) seg.records[x.val] =
            (c.enabled, RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
              (payload.assignment.assigned i))),
      ∃
      (choiceA : ReferenceCollectionSegmentExtraction.Choice rate)
      (birthA followerA : Fin R.length)
      (loggedA afterA : ReferencePrelaunchFollower.State p rate.eta)
      (cutA : ReferenceDownReception.ReferenceDownCutOutput p rate)
      (rawA : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
      (scanA : FollowerCutoffScan.ScanResult p.T)
      (registersA : ℕ × ℕ) (lastServiceA : ℕ)
      (segA : ReferenceCollectionSegmentExtraction.Segment rate)
      (doneA : ReferenceCollectionSegmentExtraction.CompletedRound rate)
      (choice0A : ReferenceCollectionSegmentExtraction.Choice rate)
      (initA : ReferenceCollectionSegmentExtraction.Initializer p)
      (recordingA : CoordinatorRecordingOperation.Output p)
      (startedA decodedA : ReferenceActivePhysicalStep.Ledger rate)
      (bankA : CoordinatorUpReception.UpDecoderBank p),
      let Pn := choiceA.payload
      let M := Pn.downRecord i
      let arm := Pn.assignment.assigned i
      let sigma := Pn.sigma.val + 1
      let cap := 4 * rate.n
      let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))
      let u := FollowerCutoffScan.firstCutoff p rate.eta.val Pn.sigma bits
      let ell := min u (R[followerA.val].input.time.val + 2)
      let d := ell - sigma
      let o := u - (s + 1)
      let n := k.val - o
      let V := fun count => QueueReplay.replay cap (0, M.val.q)
        ((ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm Cword).take count)
      let G := (P0 ++ Cword) ++ Dword
      let v := e + seg.records.length
      let U := ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G
      let Ledge := fun count => ReferenceCollectionSegmentExtraction.endpointLedger
        seg.context.preLedger (seg.records.take count)
      P0.length = b.val ∧
      E = ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate
        (payload.assignment.assigned i) P0 ∧
      (payload.downRecord i).val.q = (QueueReplay.replay cap (0, 0) E).2 ∧
      base i = (QueueReplay.replay cap (0, 0) E).1 ∧
      k0.val = b.val + 1 ∧
      (R[k0.val]'k0.isLt).input.state.coordinator = .live rb qb beta ∧
      (R[b.val]'b.isLt).output.next.coordinator = .live rb qb beta ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate (R[b.val]'b.isLt) = some cell ∧
      cell.enabled = true ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + (b.val + 1)) z = some (P0 ++ [cell]) ∧
      Cword = [cell] ++ C ∧
      Cword.length = e - b.val ∧
      Dword.length = seg.records.length ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth (R[b.val]'b.isLt) rb.payload ∧
      ReferenceCollectionSegmentExtraction.choice (R[k.val]'k.isLt).input = some choiceA ∧
      birthA.val = b.val ∧
      birthA.val ≤ followerA.val ∧ followerA.val < k.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth
        (R[birthA.val]'birthA.isLt) choiceA.payload ∧
      choiceA.payload = payload ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown R[followerA.val] i
        (choiceA.payload.downRecord i) ∧
      (R[followerA.val].output.followers i).downInput = some loggedA ∧
      (R[followerA.val].output.followers i).down = some cutA ∧
      cutA.outcome = .accepted loggedA afterA rawA (choiceA.payload.downRecord i)
        scanA registersA lastServiceA ∧
      ActiveFollowerDownAcceptance.checkedRecovery p rate M loggedA ell =
        .ok ⟨registersA, lastServiceA⟩ ∧
      M.val.q = Pn.queues arm ∧
      reply.val.sigma = sigma ∧
      registersA = V d ∧
      lastServiceA = (V d).1 - (V (d - 1)).1 ∧
      QueueReplay.replay cap (0, 0)
        (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm P0 ++
          ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm Cword) =
        (initA.base i + reply.val.S, reply.val.q) ∧
      reply.val.delta =
        (QueueReplay.replay cap (0, 0)
          (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm P0 ++
            ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm Cword)).1 -
        (QueueReplay.replay cap (0, 0)
          (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm P0 ++
            (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm Cword).take
              (Cword.length - 1))).1 ∧
      ReferenceCollectionSegmentExtraction.segmentAt R e = some seg ∧
      segA = seg ∧
      o = e ∧ e ≤ k.val ∧ n < seg.records.length ∧
      (∀ hn : n < seg.records.length, seg.records[n]'hn = R[k.val]'k.isLt) ∧
      seg.context = choice0A ∧ choice0A.payload = payload ∧
      choice0A.initializer = some initA ∧
      initA.checkedStart rate = .success seg.context.preLedger ∧
      initA.assignment.arm = payload.assignment.assigned ∧
      initA.sigma = payload.sigma.val + 1 ∧
      initA.cutoff = s + e + 1 ∧ initA.base = base ∧
      ReferenceCollectionSegmentExtraction.extractRound (R[k.val]'k.isLt) = some doneA ∧
      doneA.context = choiceA ∧ doneA.accepted = true ∧
      doneA.input.parsed = some reply ∧
      doneA.input.selectedFollower = i ∧
      doneA.final = Ledge (n + 1) ∧
      (R[k.val]'k.isLt).output.coordinator.recording = some recordingA ∧
      CoordinatorCollectionLedger.startRound doneA.context.preLedger
        ((R[k.val]'k.isLt).input.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled doneA.context.preLedger
          (R[k.val]'k.isLt).input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recordingA) =
          .success startedA ∧
      (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare (R[k.val]'k.isLt).input) startedA).result =
          .success (decodedA, bankA) ∧
      CoordinatorCollectionLedger.decodeUp startedA i (some reply) = .success decodedA ∧
      CoordinatorCollectionLedger.finishRound decodedA = .success doneA.final ∧
      (∃ saved, (R[k.val]'k.isLt).output.next.coordinator =
        .collection Pn doneA.final saved) ∧
      startedA.assignment = initA.assignment ∧
      startedA.currentRegisters arm = none ∧
      startedA.gammaLoc arm = 0 ∧
      decodedA.gammaLoc arm = 0 ∧
      doneA.final.increment arm = decodedA.increment arm ∧
      doneA.final.cutoffRegisters arm = some ⟨(U arm e).1, (U arm e).2,
        (U arm e).1 - (U arm (e - 1)).1⟩ ∧
      doneA.final.currentRegisters arm = some ⟨(U arm (k.val + 1)).2,
        (U arm (k.val + 1)).1 - (U arm k.val).1⟩ ∧
      (U arm e).1 + doneA.final.increment arm = (U arm (k.val + 1)).1 ∧
      Ledge seg.records.length = seg.final ∧
      (G.length = v ∧
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h (s + v) z = some G) ∧
      G.take e = P0 ++ Cword ∧
      seg.records ++ seg.remaining = R.drop e ∧
      R.take v = R.take e ++ seg.records ∧
      (R.take v).map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = G.map some ∧
      (∀ h, h ≤ v → ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + h) z = some (G.take h)) ∧
      (∀ count, (seg.records.take count).map
          (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger arm) =
          ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm (Dword.take count)) ∧
      (∀ count, n + 1 ≤ count → count ≤ seg.records.length →
        ∃ suffixAccepted, CollectionCheckedExecution.checkedRounds doneA.final
          ((seg.inputs.drop (n + 1)).take (count - (n + 1))) =
            some (suffixAccepted, Ledge count) ∧
        (Ledge count).cutoffRegisters arm = some ⟨(U arm e).1, (U arm e).2,
          (U arm e).1 - (U arm (e - 1)).1⟩ ∧
        (Ledge count).currentRegisters arm = some ⟨(U arm (e + count)).2,
          (U arm (e + count)).1 - (U arm (e + count - 1)).1⟩ ∧
        (U arm e).1 + (Ledge count).increment arm = (U arm (e + count)).1) ∧
      seg.final.cutoffRegisters arm = some ⟨(U arm e).1, (U arm e).2,
        (U arm e).1 - (U arm (e - 1)).1⟩ ∧
      seg.final.currentRegisters arm = some ⟨(U arm v).2,
        (U arm v).1 - (U arm (v - 1)).1⟩ ∧
      (U arm e).1 + seg.final.increment arm = (U arm v).1 := by
  classical
  intro R s
  obtain ⟨P0O, rb, qb, beta, cell, native,
    hP0lenO, hP0slotsO, hP0prefixO, hinitO, hpost,
    hbirthO, hstrictO, hbaseO, hcell, hnative, hnativePayload, henabled,
    hbirthPrefix, hbirthSlots, hcomplement, hassigned, hnext⟩ :=
    ReferenceCompleteInstallationOutsideCalendarReplay.actual_later_installation_complement_calendar_replay
      rate rewards C_star C_h z b hb
  obtain ⟨P0I, hP0lenI, hP0slotsI, hP0prefixI, hinitI,
    payload, base, E, hbirthI, hbaseI, hE, hqueuesI, hretainedI, happlication⟩ :=
    ReferenceCompleteInstallationAssignedOriginReplay.internal_complete_later_installation_assigned_origin_replay
      rewards C_star C_h z k i reply hacc b hb hselector
  have hP0Eq : P0O = P0I := by
    have hleft := hP0prefixO b le_rfl
    have hright := hP0prefixI b le_rfl
    rw [List.take_of_length_le (by omega : P0O.length ≤ b.val)] at hleft
    rw [List.take_of_length_le (by omega : P0I.length ≤ b.val)] at hright
    exact Option.some.inj (hleft.symm.trans hright)
  subst P0O
  let P0 := P0I
  have hP0Length : P0.length = b.val := hP0lenO
  have hpayload : payload = rb.payload :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      (R[b.val]'b.isLt) payload rb.payload hbirthI hbirthO
  have htimeBirth := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    (R[b.val]'b.isLt) payload hbirthI
  have hselectorPayload : reply.val.sigma = payload.sigma.val + 1 := by
    exact hselector.trans (congrArg Nat.succ htimeBirth.symm)
  have hlater : s < payload.sigma.val := by
    rw [hpayload]
    exact hstrictO
  have hP0 : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h (s + b.val) z = some P0 := by
    have hP0length : P0.length = b.val := by
      simpa only [P0] using hP0lenO
    have hh := hP0prefixO b le_rfl
    rw [List.take_of_length_le (by omega : P0.length ≤ b.val)] at hh
    simpa only [P0] using hh
  have hbk : b.val < k.val := by
    have happlication' := happlication
    dsimp only [ReferenceFirstCorrectedNextAssignedCalendarReplay.initialized_assigned_replay]
      at happlication'
    rcases happlication' with ⟨_choiceN, bN, _jN, _loggedN, _afterN, _cutN, _rawN,
      _scanN, _registersN, _lastServiceN, hbN, _hpayloadN, _hchoiceN, hbj, hjk, _⟩
    have hbNval : bN.val = b.val := congrArg Fin.val hbN
    exact Nat.lt_of_le_of_lt (by simpa only [hbNval] using hbj) hjk
  clear happlication
  have hbSucc : b.val + 1 < R.length := by
    have hle : b.val + 1 ≤ k.val := by
      simpa only [Nat.succ_eq_add_one] using Nat.succ_le_of_lt hbk
    exact Nat.lt_of_le_of_lt hle k.isLt
  rcases hnext with hnoSuccessor | ⟨k0, C, hk0, hstate0, hcontinuing⟩
  · omega
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z k0.val
  let e := k0.val + W.length
  have heIndex : e = k0.val + W.length := rfl
  let H := P0 ++ [cell] ++ C
  dsimp only [W, e, H] at hcontinuing
  rcases hcontinuing with ⟨hClen, hCreadouts, hCtimes, heR, heT, hHlen,
    hHprefix, hHslots, hHdisabled, hprefixRegs, rE, qE, hEndpointPayload,
    hEndpointLive, hEndpointInput, hEndpointRegisters, hsegment⟩
  rcases hsegment with hcutAtEnd | ⟨he, seg, I, l0, Dword, hseg, hentry,
    hsegPayload, hsegLedger, hsegInitializer, hIstate, hIchecked, hIarm,
    hIsigma, hIcutoff, hscanCutoff, hIfreeze, hIbase, hcutChosen, hne,
    hpartition, hexit, hrun, hDlen, hDreadout, hDqueues, hElen, hEtake,
    hvR, hvT, hRtake, hprefixAll, hslotsAll, hdisabledAll, hprefixLedger,
    hfinal⟩
  · have hk0le : k0.val ≤ k.val := by rw [hk0]; omega
    have hidx : k.val - k0.val < W.length := by
      change k0.val + W.length = R.length at hcutAtEnd
      exact Nat.sub_lt_left_of_lt_add hk0le (by rw [hcutAtEnd]; exact k.isLt)
    have hElem := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_index
      rewards C_star C_h z k0 (k.val - k0.val) hidx
    have htest := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_test
      rewards C_star C_h z k0 (k.val - k0.val) hidx
    have hindex : k0.val + (k.val - k0.val) = k.val := Nat.add_sub_of_le hk0le
    simp only [hindex] at hElem
    rw [hElem] at htest
    exact (continuing_excludes_accepted_up (R[k.val]'k.isLt) i reply htest hacc).elim
  have hbaseMatch :
      (match (R[b.val]'b.isLt).output.preparation.coordinator with
      | .first (.chosen installed _) => some installed.followerBaseScore
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installation _) =>
          some installation.retainedBaseScore
      | _ => none) = some base := hbaseI
  have hscan : FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) = s + e + 1 := by
    calc
      _ = FollowerCutoffScan.firstCutoff p rate.eta.val rb.payload.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
              (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) := by
              rw [hpayload]
      _ = I.cutoff := hscanCutoff.symm
      _ = s + e + 1 := hIcutoff
  let Cword : List (RecordedQueueRun.RoundInput p.K) := [cell] ++ C
  have hCword : Cword = [cell] ++ C := rfl
  change C.length = W.length at hClen
  have hbe : b.val ≤ e := by
    rw [heIndex, hk0, Nat.add_assoc]
    exact Nat.le_add_right _ _
  have hClenWord : Cword.length = e - b.val := by
    rw [hCword, List.length_append, List.length_singleton, hClen,
      heIndex, hk0, Nat.add_assoc, Nat.add_sub_cancel_left]
  have hP0C : (P0 ++ Cword).length = e := by
    rw [List.length_append, hP0Length, hClenWord, Nat.add_sub_of_le hbe]
  have hGlen : ((P0 ++ Cword) ++ Dword).length = e + seg.records.length := by
    rw [List.length_append, hP0C, hDlen]
  have hGle : ((P0 ++ Cword) ++ Dword).length ≤ R.length := by
    rw [hGlen]
    exact hvR
  have hHword : (P0 ++ [cell]) ++ C = P0 ++ Cword := by
    rw [hCword, List.append_assoc]
  have hGword : ((P0 ++ Cword) ++ Dword) = (((P0 ++ [cell]) ++ C) ++ Dword) := by
    exact congrArg (fun xs : List (RecordedQueueRun.RoundInput p.K) => xs ++ Dword)
      hHword.symm
  have hRtakeCanonical :
      (R.take (e + seg.records.length)).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) =
        (((P0 ++ Cword) ++ Dword).map some) := by
    change (R.take (e + seg.records.length)).map
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) =
        ((((P0 ++ [cell]) ++ C) ++ Dword).map some) at hslotsAll
    rw [hGword]
    exact hslotsAll
  have hfullSlots : ∀ x : Fin ((P0 ++ Cword) ++ Dword).length,
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
        (R[x.val]'(Nat.lt_of_lt_of_le x.isLt hGle)) =
          some (((P0 ++ Cword) ++ Dword)[x.val]) := by
    intro x
    have hx : x.val < e + seg.records.length := by omega
    have hslot := congrArg
      (fun xs : List (Option (RecordedQueueRun.RoundInput p.K)) => xs[x.val]?) hRtakeCanonical
    rw [List.getElem?_map, List.getElem?_take, List.getElem?_map] at hslot
    simp only [ite_eq_left hx] at hslot
    change Option.map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) R[x.val]? =
      Option.map some (((P0 ++ Cword) ++ Dword)[x.val]?) at hslot
    simp only [List.getElem?_eq_getElem (Nat.lt_of_lt_of_le x.isLt hGle),
      List.getElem?_eq_getElem x.isLt,
      Option.map_some] at hslot
    exact Option.some.inj hslot
  have hraw : ∀ arm : Fin p.K,
      seg.records.map (ReferenceCollectionRawBufferHistory.physicalQueueRecord
        seg.context.preLedger arm) =
          ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm Dword :=
    fun arm => by
      rw [hsegLedger]
      exact (hDqueues arm).2
  obtain ⟨hCslot, hDslot⟩ := literal_replay_word_slots rate R seg P0 Cword Dword
    b.val e hP0lenO hP0C hDlen hpartition hGle hfullSlots hraw
  have hqueue : (payload.downRecord i).val.q =
      (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P0
        (payload.assignment.assigned i) P0.length).2 :=
    (hretainedI i).2
  have hscore : base i =
      (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P0
        (payload.assignment.assigned i) P0.length).1 :=
    (hretainedI i).1
  have hscanPayload : reply.val.sigma = payload.sigma.val + 1 := hselectorPayload
  have hsegPayloadEq : payload = rb.payload := hpayload
  have hqueueRaw : (payload.downRecord i).val.q =
      (QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate
          (payload.assignment.assigned i) P0)).2 := by
    simpa only [ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay,
      List.take_length] using hqueue
  have hscoreRaw : base i =
      (QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate
          (payload.assignment.assigned i) P0)).1 := by
    simpa only [ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay,
      List.take_length] using hscore
  have hAligned :=
    ReferenceCompleteAssignedCalendarWordAlignment.complete_accepted_up_literal_calendar_replay
      rate rewards C_star C_h z k b i reply hacc payload base hbirthI hbaseMatch
      hscanPayload hlater P0 Cword Dword e seg hP0 hscan hseg hClenWord hDlen
      hCslot (hDslot (payload.assignment.assigned i)) hqueue hscore
  rcases hAligned with ⟨choiceA, birthA, followerA, loggedA, afterA, cutA,
    rawA, scanA, registersA, lastServiceA, hchoiceA, hbirthBoundA, hfollowBoundA,
    hbirthA, hretainedA, hloggedA, hdownA, houtcomeA, hscanA, hcheckedA,
    hqueueA, hreplySigmaA, hdposA, hdleA, htimesA, hLlenA, selectionsA,
    preparedA, hselectedA, hpreparedA, hQA, hEdA, hAlenA, hAenabledA,
    hregistersA, hlastServiceA, segA, doneA, choice0A, initA, hoA, hoRA,
    hnA, hsegmentA, hentryA, hsegContextA, hchoicePayloadA, hinitA,
    hentryChoiceA, hIcheckedA, hIarmA, hIsigmaA,
    hIcutoffA, hIbaseA, hbaseProvA, hrecordA,
    hdoneA, hcontextA, hacceptedA, hparsedA, hsenderA, hfinalA, recordingA,
    startedA, decodedA, bankA, hrecordingA, hstartA, hreceiveA, hdecodeA,
    hfinishA, hassignmentA, hstartedNoneA, hgammaStartedA, hgammaDecodedA,
    hfinishIncrementA, hnextA, hcontinuationA, hbirthIndexA, hpayloadEqA,
    hoffsetA, hsegEqA, hNlenA, hAwordA, hDwordA, hGlenA, hGprefixA,
    hLedgeA, hcalendarA⟩
  let Pn := choiceA.payload
  let M := Pn.downRecord i
  let arm := Pn.assignment.assigned i
  let sigma := Pn.sigma.val + 1
  let cap := 4 * rate.n
  let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
    (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))
  let u := FollowerCutoffScan.firstCutoff p rate.eta.val Pn.sigma bits
  let ell := min u (R[followerA.val].input.time.val + 2)
  let N := u - sigma
  let d := ell - sigma
  let o := u - (s + 1)
  let n := k.val - o
  let V := fun count => QueueReplay.replay cap (0, M.val.q)
    ((ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm Cword).take count)
  let G := (P0 ++ Cword) ++ Dword
  let v := e + seg.records.length
  let U := ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G
  let Ledge := fun count => ReferenceCollectionSegmentExtraction.endpointLedger
    seg.context.preLedger (seg.records.take count)
  have hNlen :
      N = Cword.length := by
    calc
      _ = e - b.val := hNlenA
      _ = Cword.length := hClenWord.symm
  have hbaseProvB := hbaseProvA
  rw [hbirthIndexA] at hbaseProvB
  have hbaseRead :
      (match (R[b.val]'b.isLt).output.preparation.coordinator with
      | .first (.chosen installed _) => some installed.followerBaseScore
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
          some installed.retainedBaseScore
      | _ => none) = some choiceA.preLedger.baseScore := by
    dsimp only [R]
    split at hbaseProvB
    · rename_i hcoord
      rw [hcoord]
      exact congrArg some hbaseProvB.symm
    · rename_i hcoord
      rw [hcoord]
      exact congrArg some hbaseProvB.symm
    · exact False.elim hbaseProvB
  have hbaseFunction : choiceA.preLedger.baseScore = base :=
    Option.some.inj (hbaseRead.symm.trans hbaseMatch)
  have hqueueRawA : M.val.q =
      (QueueReplay.replay cap (0, 0)
        (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm P0)).2 := by
    simpa only [M, Pn, arm, cap, hpayloadEqA] using hqueueRaw
  have hscoreRawA : initA.base i =
      (QueueReplay.replay cap (0, 0)
        (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm P0)).1 := by
    rw [hIbaseA, hbaseFunction]
    simpa only [arm, Pn, cap, hpayloadEqA] using hscoreRaw
  have hcontinuationActual := hcontinuationA
    (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm P0)
    hqueueRawA hscoreRawA
  rcases hcontinuationActual with ⟨hdownReplayA, hserviceReplayA,
    hHappendA, hCutValA, hdeltaA, hcontinueA⟩
  rw [hAwordA] at hCutValA hdeltaA hregistersA hlastServiceA
  have hCutValRaw :
      QueueReplay.replay cap (0, 0)
        (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm P0 ++
          ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm Cword) =
        (initA.base i + reply.val.S, reply.val.q) := hCutValA
  have hdeltaRaw :
      reply.val.delta =
        (QueueReplay.replay cap (0, 0)
          (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm P0 ++
            ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm Cword)).1 -
        (QueueReplay.replay cap (0, 0)
          (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm P0 ++
            (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm Cword).take
              (Cword.length - 1))).1 := by
    change reply.val.delta =
      (QueueReplay.replay cap (0, 0)
        (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm P0 ++
          ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm Cword)).1 -
      (QueueReplay.replay cap (0, 0)
        (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm P0 ++
          (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm Cword).take
            (N - 1))).1 at hdeltaA
    rw [hNlen] at hdeltaA
    exact hdeltaA
  have hregistersRaw : registersA = V d := hregistersA
  have hlastServiceRaw : lastServiceA = (V d).1 - (V (d - 1)).1 := hlastServiceA
  have hDwordRaw : ∀ count, (seg.records.take count).map
      (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger
        arm) =
      ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate
        arm (Dword.take count) := by
    intro count
    simpa only [hsegEqA] using hDwordA count
  have hcalendarRaw : ∀ count, n + 1 ≤ count → count ≤ seg.records.length →
      ∃ suffixAccepted, CollectionCheckedExecution.checkedRounds doneA.final
        ((seg.inputs.drop (n + 1)).take (count - (n + 1))) =
          some (suffixAccepted, Ledge count) ∧
      (Ledge count).cutoffRegisters arm = some ⟨(U arm e).1, (U arm e).2,
        (U arm e).1 - (U arm (e - 1)).1⟩ ∧
      (Ledge count).currentRegisters arm = some ⟨(U arm (e + count)).2,
        (U arm (e + count)).1 - (U arm (e + count - 1)).1⟩ ∧
      (U arm e).1 + (Ledge count).increment arm = (U arm (e + count)).1 := by
    intro count hlow hhigh
    obtain ⟨accepted, hchecked, _⟩ := hcontinueA count hlow
      (by simpa only [hsegEqA] using hhigh)
    refine ⟨accepted, ?_, ?_⟩
    · simpa only [hsegEqA] using hchecked
    · simpa only [hsegEqA] using hcalendarA count hlow hhigh
  have hfinalRaw : Ledge seg.records.length = seg.final := by
    simpa only [hsegEqA] using hLedgeA
  have hbirthValA : birthA.val = b.val := congrArg Fin.val hbirthIndexA
  have hdoneRaw : doneA.final = Ledge (n + 1) := by
    simpa only [hsegEqA] using hfinalA
  have hnBound : n + 1 ≤ seg.records.length := by
    have hh : n < seg.records.length := by simpa only [hsegEqA] using hnA
    omega
  obtain ⟨_acceptedFinal, _hcheckedFinal, hfinalCalendar⟩ :=
    hcalendarRaw seg.records.length hnBound le_rfl
  rw [hfinalRaw] at hfinalCalendar
  change seg.final.cutoffRegisters arm = _ ∧
    seg.final.currentRegisters arm = _ ∧ _ at hfinalCalendar
  have hsegmentIndex : e ≤ k.val := by simpa only [hoffsetA] using hoA
  have hoIndex : o = e := hoffsetA
  have hnIndex : e + n = k.val := by
    change e + (k.val - o) = k.val
    rw [hoIndex]
    exact Nat.add_sub_of_le hsegmentIndex
  have hcurrentIndex : e + (n + 1) = k.val + 1 := by
    rw [← Nat.add_assoc, hnIndex]
  have hpreviousIndex : e + (n + 1) - 1 = k.val := by
    rw [hcurrentIndex, Nat.add_sub_cancel]
  obtain ⟨_acceptedNow, _hcheckedNow, hinclusive⟩ :=
    hcalendarRaw (n + 1) le_rfl hnBound
  rw [← hdoneRaw, hpreviousIndex, hcurrentIndex] at hinclusive
  have hrecordRaw : ∀ hn : n < seg.records.length,
      seg.records[n]'hn = R[k.val]'k.isLt := by
    simpa only [hsegEqA] using hrecordA
  have hcontextRaw : seg.context = choice0A := by
    simpa only [hsegEqA] using hsegContextA
  have hcheckedStartRaw : initA.checkedStart rate = .success seg.context.preLedger := by
    simpa only [hsegEqA] using hIcheckedA
  have hcutoffRaw : initA.cutoff = s + e + 1 := by
    calc
      _ = u := hIcutoffA
      _ = s + e + 1 := by
        simpa only [u, bits, Pn, hpayloadEqA] using hscan
  have hprefixG : ∀ h, h ≤ v →
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + h) z = some (G.take h) := by
    intro h hh
    by_cases hbefore : h ≤ b.val
    · have hple : h ≤ P0.length := by rw [hP0Length]; exact hbefore
      have hprefix := hP0prefixO h hbefore
      simpa only [G, List.append_assoc, List.take_append_of_le_length hple] using hprefix
    · have hafter : k0.val ≤ h := by
        rw [hk0]
        exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hbefore)
      have hprefix := hprefixAll h hafter hh
      rw [← hGword] at hprefix
      exact hprefix
  have htakeG : G.take e = P0 ++ Cword := by
    change (((P0 ++ Cword) ++ Dword).take e) = P0 ++ Cword
    rw [← hP0C, List.take_append_length]
  refine ⟨P0, payload, base, E, k0, rb, qb, beta, cell, C, Cword,
    Dword, e, seg, hqueue, hscore, hbirthI, hbaseMatch, hselectorPayload,
    hlater, hP0, hscan, hseg, hClenWord, hDlen, hCslot,
    hDslot (payload.assignment.assigned i), choiceA, birthA, followerA,
    loggedA, afterA, cutA, rawA, scanA, registersA, lastServiceA, segA,
    doneA, choice0A, initA, recordingA, startedA, decodedA, bankA, ?_⟩
  refine ⟨hP0lenO, hE, ?_, ?_, hk0, hstate0, hpost, hcell, henabled,
    hbirthPrefix, hCword,
    hClenWord, hDlen, hbirthO, hchoiceA, hbirthValA, hbirthBoundA,
    hfollowBoundA, hbirthA, hpayloadEqA, hretainedA, hloggedA, hdownA,
    houtcomeA, hcheckedA, hqueueA, hreplySigmaA, hregistersRaw,
    hlastServiceRaw, hCutValRaw, hdeltaRaw, hseg, hsegEqA, hoffsetA, hsegmentIndex,
    Nat.lt_of_succ_le hnBound, hrecordRaw, hcontextRaw,
    hchoicePayloadA.trans hpayloadEqA, hinitA, hcheckedStartRaw,
    (by simpa only [Pn, hpayloadEqA] using hIarmA),
    (by simpa only [Pn, hpayloadEqA] using hIsigmaA), hcutoffRaw,
    hIbaseA.trans hbaseFunction, hdoneA, hcontextA, hacceptedA, hparsedA,
    hsenderA, hdoneRaw, hrecordingA, hstartA, hreceiveA, hdecodeA, hfinishA,
    hnextA, hassignmentA, hstartedNoneA, hgammaStartedA,
    hgammaDecodedA, hfinishIncrementA, hinclusive.1, hinclusive.2.1, hinclusive.2.2,
    hfinalRaw, ?_, htakeG,
    hpartition, hRtake, hRtakeCanonical, hprefixG, hDwordRaw,
    hcalendarRaw, hfinalCalendar⟩
  · calc
      (payload.downRecord i).val.q =
          (QueueReplay.replay (4 * rate.n) (0, 0)
            (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate
              (payload.assignment.assigned i) P0)).2 := hqueueRaw
      _ = (QueueReplay.replay (4 * rate.n) (0, 0) E).2 := by rw [← hE]
  · calc
      base i = (QueueReplay.replay (4 * rate.n) (0, 0)
          (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate
            (payload.assignment.assigned i) P0)).1 := hscoreRaw
      _ = (QueueReplay.replay (4 * rate.n) (0, 0) E).1 := by rw [← hE]
  · exact ⟨hGlenA, hGprefixA⟩

end Bandits.Support.ReferenceCompleteInstallationAssignedCalendarReplay

end
