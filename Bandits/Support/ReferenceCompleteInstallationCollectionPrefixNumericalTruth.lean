/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteInstallationCollectionPrefixInformation
public import Bandits.Support.ReferenceCompleteInstallationAssignedCalendarReplay

import Mathlib.Tactic

/-!
# Actual installation collection-prefix numerical truth

This module joins the actual-prefix ledger facts with the outside-arm and
accepted-assigned-arm calendar replays.  It keeps the literal calendar word,
physical segment, and zero-origin numerical prefix together.

Source evidence: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-188`, under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep

namespace Bandits.Support.ReferenceCompleteInstallationCollectionPrefixNumericalTruth

variable {p : ConstructorDimensions.Parameters}

private theorem replay_score_shift (capacity offset score queue : ℕ)
    (records : List (Bool × ℕ)) :
    QueueReplay.replay capacity (offset + score, queue) records =
      (offset + (QueueReplay.replay capacity (score, queue) records).1,
        (QueueReplay.replay capacity (score, queue) records).2) := by
  induction records generalizing score queue with
  | nil => rfl
  | cons record rest ih =>
      change QueueReplay.replay capacity
        (QueueReplay.transition capacity (offset + score, queue) record) rest =
        (offset + (QueueReplay.replay capacity
          (QueueReplay.transition capacity (score, queue) record) rest).1,
          (QueueReplay.replay capacity
            (QueueReplay.transition capacity (score, queue) record) rest).2)
      cases record with
      | mk enabled arrival =>
          cases enabled <;>
            simp [QueueReplay.transition, ih, Nat.add_assoc]

private theorem replayLastService_difference (capacity : ℕ) (initial : ℕ × ℕ)
    (retained : ℕ) (records : List (Bool × ℕ)) (hne : records ≠ []) :
    CollectionKnownQueueContinuation.replayLastService capacity initial retained records =
      (QueueReplay.replay capacity initial records).1 -
        (QueueReplay.replay capacity initial (records.take (records.length - 1))).1 := by
  rw [CollectionKnownQueueContinuation.replayLastService,
    List.getLast?_eq_getLast_of_ne_nil hne]
  have hsplit := List.dropLast_append_getLast hne
  have hfull : QueueReplay.replay capacity initial records =
      QueueReplay.transition capacity
        (QueueReplay.replay capacity initial records.dropLast) (records.getLast hne) := by
    conv_lhs => rw [← hsplit, QueueReplay.replay_append]
    rfl
  rw [hfull, List.dropLast_eq_take]

public theorem calendarReplay_append_registers
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (H D : List (RecordedQueueRun.RoundInput p.K)) (e count : ℕ)
    (a : Fin p.K) (hH : H.length = e) :
    let U := ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate (H ++ D)
    let Y := QueueReplay.replay (4 * rate.n)
      (0, (U a e).2)
      (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a (D.take count))
    U a (e + count) = ((U a e).1 + Y.1, Y.2) := by
  dsimp only
  have htake : (H ++ D).take (e + count) = H ++ D.take count := by
    rw [List.take_append]
    rw [List.take_of_length_le (by omega : H.length ≤ e + count)]
    rw [hH, Nat.add_sub_cancel_left]
  have hprefix : (H ++ D).take e = H := by
    rw [List.take_append]
    rw [List.take_of_length_le (by omega : H.length ≤ e)]
    rw [hH, Nat.sub_self, List.take_zero, List.append_nil]
  have hraw : ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a
      (H ++ D.take count) =
      ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a H ++
        ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a (D.take count) := by
    simp only [ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar, List.map_append]
  unfold ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
  rw [htake, hraw, QueueReplay.replay_append]
  rw [hprefix]
  cases hseed : QueueReplay.replay (4 * rate.n) (0, 0)
      (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a H) with
  | mk score queue =>
      change QueueReplay.replay (4 * rate.n) (score + 0, queue)
          (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a (D.take count)) =
        (score + (QueueReplay.replay (4 * rate.n) (0, queue)
          (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a (D.take count))).1,
          (QueueReplay.replay (4 * rate.n) (0, queue)
            (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a (D.take count))).2)
      exact replay_score_shift (4 * rate.n)
        score 0 queue
        (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a (D.take count))

public theorem calendarReplay_append_lastService
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (H D : List (RecordedQueueRun.RoundInput p.K)) (e count : ℕ)
    (a : Fin p.K) (hH : H.length = e) (hcount : count ≤ D.length) :
    let U := ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate (H ++ D)
    CollectionKnownQueueContinuation.replayLastService (4 * rate.n)
        (0, (U a e).2) ((U a e).1 - (U a (e - 1)).1)
        (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a (D.take count)) =
      (U a (e + count)).1 - (U a (e + count - 1)).1 := by
  dsimp only
  by_cases hzero : count = 0
  · subst count
    simp only [List.take_zero, ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar,
      List.map_nil, CollectionKnownQueueContinuation.replayLastService,
      List.getLast?_nil, Nat.add_zero]
  · have hpos : 0 < count := Nat.pos_of_ne_zero hzero
    let records := ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a
      (D.take count)
    have hlen : records.length = count := by
      simp only [records, ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar,
        List.length_map, List.length_take, Nat.min_eq_left hcount]
    have hne : records ≠ [] := by
      intro hnil
      have := congrArg List.length hnil
      simp only [hlen, List.length_nil] at this
      omega
    rw [replayLastService_difference _ _ _ records hne]
    have hfull := calendarReplay_append_registers rate H D e count a hH
    have hprior : count - 1 ≤ D.length := by omega
    have hprev := calendarReplay_append_registers rate H D e (count - 1) a hH
    have htakeRecords : records.take (records.length - 1) =
        ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a (D.take (count - 1)) := by
      rw [hlen]
      dsimp [records, ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar]
      rw [← List.map_take, List.take_take,
        Nat.min_eq_left (by omega : count - 1 ≤ count)]
    dsimp only at hfull hprev
    have hindex : e + count - 1 = e + (count - 1) := by omega
    rw [htakeRecords, hfull, hindex, hprev]
    exact (Nat.add_sub_add_left _ _ _).symm

/-- At an actual later installation, every complement arm's checked
collection-prefix registers are the literal zero-origin calendar registers.
The theorem retains the actual terminal, continuing-live, no-cutoff, and
segment branches. -/
public theorem actual_later_installation_outside_collection_prefix_numerical_truth
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∃ (P0 : List (RecordedQueueRun.RoundInput p.K))
      (rb : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (qb : CoordinatorLiveServiceFinish.OwnedRegisters rb)
      (beta : Fin (p.m - 1) → ℕ) (cell : RecordedQueueRun.RoundInput p.K)
      (native : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell (R[b.val]'b.isLt)),
      P0.length = b.val ∧
      (∀ h, h ≤ b.val → ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + h) z = some (P0.take h)) ∧
      (R[b.val]'b.isLt).output.next.coordinator = .live rb qb beta ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth (R[b.val]'b.isLt) rb.payload ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate (R[b.val]'b.isLt) = some cell ∧
      native.input = cell ∧ native.selected.view.payload = rb.payload ∧ cell.enabled = true ∧
      (∀ i : ActiveRoundActions.Follower p.m,
        (rb.payload.downRecord i).val.q =
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P0
            (rb.payload.assignment.assigned i) b.val).2 ∧
        beta i = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P0
          (rb.payload.assignment.assigned i) b.val).1) ∧
      (b.val + 1 = R.length ∨
        ∃ (k : Fin R.length) (C : List (RecordedQueueRun.RoundInput p.K)),
          k.val = b.val + 1 ∧
          (R[k.val]'k.isLt).input.state.coordinator = .live rb qb beta ∧
          let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
            rate rewards C_star C_h z k.val
          C.length = W.length ∧
          W.map (ReferenceLaterLiveNumericalReadout.laterLiveReadout s) = C.map some ∧
          W.map (fun r => r.input.time.val) = List.range' (s + k.val) W.length ∧
          ∃ (e : ℕ) (rE : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
            (qE : CoordinatorLiveServiceFinish.OwnedRegisters rE),
            e = k.val + W.length ∧ e ≤ R.length ∧ rE.payload = rb.payload ∧
            (e = R.length ∨
              ∃ (he : e < R.length) (seg : ReferenceCollectionSegmentExtraction.Segment rate)
                (I0 : ReferenceCollectionSegmentExtraction.Initializer p)
                (l0 : ReferenceActivePhysicalStep.Ledger rate)
                (Dword : List (RecordedQueueRun.RoundInput p.K)),
                ReferenceCollectionSegmentExtraction.segmentAt R e = some seg ∧
                seg.entry = (R[e]'he) ∧ seg.context.payload = rb.payload ∧
                seg.context.preLedger = l0 ∧ seg.context.initializer = some I0 ∧
                I0 = ReferenceCollectionSegmentExtraction.cutoffInitializer
                  (ReferenceActivePhysicalStep.liveRegistersAt rE (R[e]'he).input.time)
                  (ReferenceActivePhysicalStep.liveOwnedAt rE qE (R[e]'he).input.time)
                  beta (R[e]'he).input.time ∧
                I0.checkedStart rate = .success l0 ∧
                I0.assignment.arm = rb.payload.assignment.assigned ∧
                I0.sigma = rb.payload.sigma.val + 1 ∧ I0.cutoff = s + e + 1 ∧
                I0.freezeAt = rE.gridBoundary ∧ I0.base = beta ∧
                ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
                seg.records ++ seg.remaining = R.drop e ∧
                CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
                  (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
                  I0.assignment I0.sigma I0.cutoff I0.freezeAt I0.base I0.outside seg.inputs =
                    .success ⟨l0, seg.accepted, seg.final⟩ ∧
                Dword.length = seg.records.length ∧
                seg.records.map (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s) =
                  Dword.map some ∧
                (∀ a, CollectionKnownQueueContinuation.inputQueueRecords l0 a seg.inputs =
                    seg.records.map (ReferenceCollectionRawBufferHistory.physicalQueueRecord l0 a) ∧
                  seg.records.map (ReferenceCollectionRawBufferHistory.physicalQueueRecord l0 a) =
                    ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a Dword) ∧
                let H := P0 ++ [cell] ++ C
                let G := H ++ Dword
                let v := e + seg.records.length
                let U := ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G
                H.length = e ∧ G.length = v ∧ G.take e = H ∧ v ≤ R.length ∧
                R.take v = R.take e ++ seg.records ∧
                (∀ h, h ≤ v →
                  ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                    rate rewards C_star C_h (s + h) z = some (G.take h)) ∧
                (∀ count, count ≤ seg.records.length →
                  let ln := ReferenceCollectionSegmentExtraction.endpointLedger l0
                    (seg.records.take count)
                  ∀ j : CanonicalFastSampling.FastArm rb.payload.slowSet,
                    ln.cutoffRegisters j.val = some ⟨(U j.val e).1, (U j.val e).2,
                      (U j.val e).1 - (U j.val (e - 1)).1⟩ ∧
                    ln.currentRegisters j.val = some ⟨(U j.val (e + count)).2,
                      (U j.val (e + count)).1 - (U j.val (e + count - 1)).1⟩ ∧
                    (U j.val e).1 + ln.increment j.val = (U j.val (e + count)).1) ∧
                (∀ j : CanonicalFastSampling.FastArm rb.payload.slowSet,
                  seg.final.cutoffRegisters j.val =
                    some ⟨(U j.val e).1, (U j.val e).2,
                      (U j.val e).1 - (U j.val (e - 1)).1⟩ ∧
                  seg.final.currentRegisters j.val =
                    some ⟨(U j.val v).2, (U j.val v).1 - (U j.val (v - 1)).1⟩ ∧
                  (U j.val e).1 + seg.final.increment j.val = (U j.val v).1))) := by
  classical
  intro R s
  obtain ⟨P0, rb, qb, beta, cell, native, hPlen, _hPslots, hPprefix,
    _hinit, hpost, hbirth, _hstrict, _hbase, hcell, hnative, hnativePayload,
    henabled, _hbirthPrefix, _hbirthSlots, _hcomplement, hdown, hnext⟩ :=
    ReferenceCompleteInstallationOutsideCalendarReplay.actual_later_installation_complement_calendar_replay
      rate rewards C_star C_h z b hb
  have hdownB : ∀ i : ActiveRoundActions.Follower p.m,
      (rb.payload.downRecord i).val.q =
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P0
          (rb.payload.assignment.assigned i) b.val).2 ∧
      beta i = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P0
        (rb.payload.assignment.assigned i) b.val).1 := by
    intro i
    simpa only [hPlen] using hdown i
  dsimp only at hnext
  rcases hnext with hterminal | ⟨k, C, hk, hstate, hClen, hWmap, hWtime,
    _heR, _heT, _hHlen, _hprefix, _hslots, _hdisabled, _hprefixReplay,
    rE, qE, hrPayload, _hlast, _hin, _hvalues, hsegment⟩
  · exact ⟨P0, rb, qb, beta, cell, native, hPlen, hPprefix, hpost, hbirth,
      hcell, hnative, hnativePayload, henabled, hdownB, Or.inl hterminal⟩
  · let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z k.val
    let e := k.val + W.length
    rcases hsegment with hnoSegment | ⟨hbound, seg, I0, l0, Dword, hseg, hentry,
      hpay, hledger, hinitializer, hIeq, hstart, harm, hsigma, hcutoff, _hscan,
      hfreeze, hbase, hchosen, _hne, hpartition, _hexit, hrun, hDlen, hDmap,
      hqueues, hElen, hEtake, hvR, _hvT, hRtake, hprefixAll, _hcoordsAll,
      _hdisabledAll, hprefixRegs, hfinal⟩
    · exact ⟨P0, rb, qb, beta, cell, native, hPlen, hPprefix, hpost, hbirth,
        hcell, hnative, hnativePayload, henabled, hdownB,
        Or.inr ⟨k, C, hk, hstate, hClen, hWmap, hWtime,
          ⟨e, rE, qE, rfl, _heR, hrPayload, Or.inl hnoSegment⟩⟩⟩
    ·
      let H := P0 ++ [cell] ++ C
      let G := H ++ Dword
      let v := e + seg.records.length
      let U := ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G
      have hHlen : H.length = e := by simpa only [H, e, W] using _hHlen
      have hGlen : G.length = v := by simpa only [G, v, H] using hElen
      have hprefixEvery : ∀ h, h ≤ v →
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
            rate rewards C_star C_h (s + h) z = some (G.take h) := by
        intro h hh
        by_cases hkle : k.val ≤ h
        · have hh' : h ≤ v := hh
          simpa only [G, H, v] using hprefixAll h hkle hh'
        · have hlt : h ≤ b.val := by omega
          have hp := hPprefix h hlt
          have hGtake : G.take h = P0.take h := by
            change (((P0 ++ [cell]) ++ C) ++ Dword).take h = P0.take h
            rw [List.take_append_of_le_length (by
              simp only [List.length_append, List.length_cons, List.length_nil, hPlen]
              omega)]
            rw [List.take_append_of_le_length (by
              simp only [List.length_append, List.length_cons, List.length_nil, hPlen]
              omega)]
            rw [List.take_append_of_le_length (by simpa only [hPlen] using hlt)]
          rw [hGtake]
          exact hp
      have hcount : ∀ count, count ≤ seg.records.length →
          let ln := ReferenceCollectionSegmentExtraction.endpointLedger l0
            (seg.records.take count)
          ∀ j : CanonicalFastSampling.FastArm rb.payload.slowSet,
            ln.cutoffRegisters j.val = some ⟨(U j.val e).1, (U j.val e).2,
              (U j.val e).1 - (U j.val (e - 1)).1⟩ ∧
            ln.currentRegisters j.val = some ⟨(U j.val (e + count)).2,
              (U j.val (e + count)).1 - (U j.val (e + count - 1)).1⟩ ∧
            (U j.val e).1 + ln.increment j.val = (U j.val (e + count)).1 := by
        intro count hcount
        dsimp only
        intro j
        obtain ⟨_accepted, hchecked⟩ := hprefixRegs count hcount
        obtain ⟨_hfold, hsource⟩ := hchecked
        obtain ⟨hcut, hcurrent, hincrement⟩ := hsource j
        have hcountD : count ≤ Dword.length := by rw [hDlen]; exact hcount
        have hregs := calendarReplay_append_registers rate H Dword e count j.val hHlen
        have hservice := calendarReplay_append_lastService rate H Dword e count j.val
          hHlen hcountD
        have hqueue :
            (QueueReplay.replay (4 * rate.n) (0, (U j.val e).2)
              (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate j.val
                (Dword.take count))).2 = (U j.val (e + count)).2 := by
          exact (congrArg Prod.snd hregs).symm
        refine ⟨hcut, ?_, ?_⟩
        · rw [hcurrent, hqueue, hservice]
        · rw [hincrement]
          exact (congrArg Prod.fst hregs).symm
      have hfinal' : ∀ j : CanonicalFastSampling.FastArm rb.payload.slowSet,
          seg.final.cutoffRegisters j.val =
            some ⟨(U j.val e).1, (U j.val e).2,
              (U j.val e).1 - (U j.val (e - 1)).1⟩ ∧
          seg.final.currentRegisters j.val =
            some ⟨(U j.val v).2, (U j.val v).1 - (U j.val (v - 1)).1⟩ ∧
          (U j.val e).1 + seg.final.increment j.val = (U j.val v).1 := by
        simpa only [U, v, G, H] using hfinal
      refine ⟨P0, rb, qb, beta, cell, native, hPlen, hPprefix, hpost,
        hbirth, hcell, hnative, hnativePayload, henabled, hdownB,
        Or.inr ⟨k, C, hk, hstate, hClen, hWmap, hWtime,
          ⟨e, rE, qE, rfl, _heR, hrPayload, Or.inr ?_⟩⟩⟩
      exact ⟨hbound, seg, I0, l0, Dword, hseg, hentry, hpay, hledger,
        hinitializer, hIeq, hstart, harm, hsigma, hcutoff, hfreeze, hbase, hchosen,
        hpartition, hrun, hDlen, hDmap, hqueues, hHlen, hGlen, hEtake, hvR,
        hRtake, hprefixEvery, hcount, hfinal'⟩


/-- Align an actual accepted reply with an already fixed original segment and
calendar word. Acceptance and its selector are proof-local inputs to this join. -/
private theorem assigned_prefix_at_same_calendar
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true)
    (payload : AssignmentStartPayload.Input p rate.eta)
    (e count : ℕ) (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (G : List (RecordedQueueRun.RoundInput p.K))
    (i : Fin (p.m - 1)) (reply : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val] payload)
    (hscan : FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e + 1)
    (hseg : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)
      e = some seg)
    (hG : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
        (e + seg.records.length)) z = some G)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input i reply)
    (hselector : reply.val.sigma =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input.time.val + 1)
    (hke : e ≤ k.val) (hkc : k.val < e + count)
    (hcount : count ≤ seg.records.length) :
    let U := ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G
    let ln := ReferenceCollectionSegmentExtraction.endpointLedger seg.context.preLedger
      (seg.records.take count)
    let a := payload.assignment.assigned i
    ln.cutoffRegisters a = some ⟨(U a e).1, (U a e).2,
      (U a e).1 - (U a (e - 1)).1⟩ ∧
    ln.currentRegisters a = some ⟨(U a (e + count)).2,
      (U a (e + count)).1 - (U a (e + count - 1)).1⟩ ∧
    (U a e).1 + ln.increment a = (U a (e + count)).1 := by
  obtain ⟨P0A, payloadA, baseA, EA, k0A, rbA, qbA, betaA, cellA,
    CA, CwordA, DwordA, eA, segA, _hqueueA, _hscoreA, hbirthA, _hbaseA,
    _hselectorA, _hlaterA, _hP0A, hscanA, hsegA, _hClenA, _hDlenA,
    _hCslotA, _hDslotA, choiceA, birthA, followerA, loggedA, afterA,
    cutA, rawA, scanA, registersA, lastServiceA, segAA, doneA, choice0A,
    initA, recordingA, startedA, decodedA, bankA, hdata⟩ :=
    ReferenceCompleteInstallationAssignedCalendarReplay.actual_later_installation_assigned_arm_calendar_replay
      rate rewards C_star C_h z k b i reply hacc hb hselector
  dsimp only at hdata
  rcases hdata with ⟨_hPlen, _hEA, _hQA, _hBA, _hk0, _hstate, _hpost,
    _hcell, _henabled, _hbirthPrefix, _hCword, _hClen, _hDlen, _hbirthRb,
    _hchoice, _hbirthIndex, _hbf, _hfk, _hbirthChoice, hchoicePayload,
    _hretained, _hdownInput, _hdown, _houtcome, _hrecovery, _hMqueue,
    _hreplySigma, _hregisters, _hlast, _hreplay, _hdelta, _hsegment,
    _hsegAA, ho, _hek, _hn, _hrecord, _hcontext, _hchoice0Payload,
    _hinitializer, _hstart, _harm, _hsigma, _hcutoff, _hbase,
    _hextract, _hdoneContext, _haccepted, _hparsed, _hselected, _hfinal,
    _hrecording, _hstarted, _hreceived, _hdecoded, _hfinished, _hnext,
    _hstartedAssignment, _hunknown, _hgammaStarted, _hgammaDecoded,
    _hincrement, _hcutRegisters, _hcurrentRegisters, _hscore, _hfinalLedger,
    hword, _htake, _hpartition, _hRtake, _hslots, _hprefix, _hraw,
    hcontinuation, _hfinalCut, _hfinalCurrent, _hfinalScore⟩
  have hpayload : payloadA = payload :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      _ payloadA payload hbirthA hbirth
  have he : eA = e := by
    rw [hpayload] at hscanA
    omega
  rw [he] at hsegA hword hcontinuation ho
  have hsegment : segA = seg := Option.some.inj (hsegA.symm.trans hseg)
  rw [hsegment] at hword hcontinuation
  have hwordEq : (P0A ++ CwordA) ++ DwordA = G :=
    Option.some.inj (hword.2.symm.trans hG)
  rw [ho] at hcontinuation
  have hncount : k.val - e + 1 ≤ count := by omega
  obtain ⟨_suffixAccepted, _hchecked, hcut, hcurrent, hscore⟩ :=
    hcontinuation count hncount hcount
  dsimp only
  rw [hwordEq, hchoicePayload, hpayload] at hcut hcurrent hscore
  exact ⟨hcut, hcurrent, hscore⟩


private theorem outside_prefix_at_same_calendar
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true)
    (payload : AssignmentStartPayload.Input p rate.eta)
    (e : ℕ) (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (G : List (RecordedQueueRun.RoundInput p.K))
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val] payload)
    (hk : k.val = b.val + 1)
    (he : e = k.val + (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z k.val).length)
    (heR : e < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hseg : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)
      e = some seg)
    (hG : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
        (e + seg.records.length)) z = some G) :
    let U := ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G
    ∀ count, count ≤ seg.records.length →
      let ln := ReferenceCollectionSegmentExtraction.endpointLedger seg.context.preLedger
        (seg.records.take count)
      ∀ j : CanonicalFastSampling.FastArm payload.slowSet,
        ln.cutoffRegisters j.val = some ⟨(U j.val e).1, (U j.val e).2,
          (U j.val e).1 - (U j.val (e - 1)).1⟩ ∧
        ln.currentRegisters j.val = some ⟨(U j.val (e + count)).2,
          (U j.val (e + count)).1 - (U j.val (e + count - 1)).1⟩ ∧
        (U j.val e).1 + ln.increment j.val = (U j.val (e + count)).1 := by
  obtain ⟨P0O, rbO, qbO, betaO, cellO, nativeO, _hPlen, _hPprefix,
    _hpost, hbirthO, _hcell, _hnative, _hnativePayload, _henabled,
    _hdown, hbranch⟩ :=
    actual_later_installation_outside_collection_prefix_numerical_truth
      rate rewards C_star C_h z b hb
  rcases hbranch with hterminal | ⟨kO, CO, hkO, _hstate, _hClen,
    _hWmap, _hWtime, eO, rEO, qEO, heO, _heOR, _hpayloadEO, hsegment⟩
  · omega
  have hkEq : kO.val = k.val := hkO.trans hk.symm
  have heEq : eO = e := by rw [heO, hkEq, ← he]
  rw [heEq] at hsegment
  rcases hsegment with hterminal | ⟨_he, segO, IO, lO, DO, hsegO, _hentry,
    _hpay, hledgerO, _hinitializer, _hIeq, _hstart, _harm, _hsigma,
    _hcutoff, _hfreeze, _hbase, _hchosen, _hpartition, _hrun, _hDlen,
    _hDmap, _hqueues, _hHlen, hGlenO, _hGtake, _hvR, _hRtake,
    hprefixO, hcountO, _hfinalO⟩
  · omega
  have hsegEq : segO = seg := Option.some.inj (hsegO.symm.trans hseg)
  subst segO
  have hwordO := hprefixO (e + seg.records.length) le_rfl
  rw [List.take_of_length_le (by omega)] at hwordO
  have hwordEq : (P0O ++ [cellO] ++ CO) ++ DO = G :=
    Option.some.inj (hwordO.symm.trans hG)
  have hpayload : rbO.payload = payload :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      _ rbO.payload payload hbirthO hbirth
  dsimp only
  intro count hcount j
  let hj : CanonicalFastSampling.FastArm rbO.payload.slowSet :=
    ⟨j.val, by simpa only [hpayload] using j.property⟩
  have hh := hcountO count hcount hj
  rw [hwordEq] at hh
  rw [← hledgerO] at hh
  exact hh

/-- All-arm numerical and literal pending-buffer readouts at one common actual
birth and optional collection segment. No acceptance witness is a root input. -/
public theorem actual_later_installation_collection_prefix_numerical_truth
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∃ (P0 : List (RecordedQueueRun.RoundInput p.K))
      (rb : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (qb : CoordinatorLiveServiceFinish.OwnedRegisters rb)
      (beta : Fin (p.m - 1) → ℕ) (cell : RecordedQueueRun.RoundInput p.K)
      (native : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell (R[b.val]'b.isLt)),
      P0.length = b.val ∧
      (R.take b.val).map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) =
        P0.map some ∧
      (∀ h, h ≤ b.val →
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h (s + h) z = some (P0.take h)) ∧
      ReferenceFirstReplacementCalendarInitialization.initializes_calendar rate P0
        (R[b.val]'b.isLt) ∧
      (R[b.val]'b.isLt).output.next.coordinator = .live rb qb beta ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth (R[b.val]'b.isLt) rb.payload ∧
      s < rb.payload.sigma.val ∧
      ReferenceCompleteInstallationPredecessorInterval.installationBase?
        (R[b.val]'b.isLt).output.preparation.coordinator = some beta ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate (R[b.val]'b.isLt) = some cell ∧
      native.input = cell ∧ native.selected.view.payload = rb.payload ∧ cell.enabled = true ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + (b.val + 1)) z = some (P0 ++ [cell]) ∧
      (R.take (b.val + 1)).map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) =
        (P0 ++ [cell]).map some ∧
      (∀ i : Fin (p.m - 1),
        (rb.payload.downRecord i).val.q =
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P0
            (rb.payload.assignment.assigned i) P0.length).2 ∧
        beta i = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P0
          (rb.payload.assignment.assigned i) P0.length).1) ∧
      (b.val + 1 = R.length ∨
        ∃ (k : Fin R.length) (C : List (RecordedQueueRun.RoundInput p.K)),
          k.val = b.val + 1 ∧
          (R[k.val]'k.isLt).input.state.coordinator = .live rb qb beta ∧
          C.length = (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
            rate rewards C_star C_h z k.val).length ∧
          (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
            rate rewards C_star C_h z k.val).map
              (ReferenceLaterLiveNumericalReadout.laterLiveReadout s) = C.map some ∧
          (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
            rate rewards C_star C_h z k.val).map (fun r => r.input.time.val) =
              List.range' (s + k.val)
                (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
                  rate rewards C_star C_h z k.val).length ∧
          ∃ (e : ℕ),
            e = k.val + (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
              rate rewards C_star C_h z k.val).length ∧ e ≤ R.length ∧
            ∃ (rE : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
              (qE : CoordinatorLiveServiceFinish.OwnedRegisters rE),
              rE.payload = rb.payload ∧
              (e = R.length ∨
            ∃ (he : e < R.length) (seg : ReferenceCollectionSegmentExtraction.Segment rate)
              (I : ReferenceCollectionSegmentExtraction.Initializer p)
              (l0 : ReferenceActivePhysicalStep.Ledger rate)
              (Dword : List (RecordedQueueRun.RoundInput p.K)),
              ReferenceCollectionSegmentExtraction.segmentAt R e = some seg ∧
              seg.entry = (R[e]'he) ∧ seg.context.payload = rb.payload ∧
              seg.context.preLedger = l0 ∧ seg.context.initializer = some I ∧
              I = ReferenceCollectionSegmentExtraction.cutoffInitializer
                (ReferenceActivePhysicalStep.liveRegistersAt rE
                  (R[e]'he).input.time)
                (ReferenceActivePhysicalStep.liveOwnedAt rE qE
                  (R[e]'he).input.time) beta (R[e]'he).input.time ∧
              I.checkedStart rate = .success l0 ∧
              I.assignment.arm = rb.payload.assignment.assigned ∧
              I.sigma = rb.payload.sigma.val + 1 ∧ I.cutoff = s + e + 1 ∧
              I.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val rb.payload.sigma
                (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                  (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) ∧
              I.freezeAt = rE.gridBoundary ∧ I.base = beta ∧
              ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
              (∃ tail, seg.records = seg.entry :: tail) ∧
              seg.records ++ seg.remaining = R.drop e ∧
              CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
                (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
                I.assignment I.sigma I.cutoff I.freezeAt I.base I.outside seg.inputs =
                  .success ⟨l0, seg.accepted, seg.final⟩ ∧
              Dword.length = seg.records.length ∧
              seg.records.map (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s) =
                Dword.map some ∧
              (∀ a, CollectionKnownQueueContinuation.inputQueueRecords l0 a seg.inputs =
                seg.records.map (ReferenceCollectionRawBufferHistory.physicalQueueRecord l0 a) ∧
                seg.records.map (ReferenceCollectionRawBufferHistory.physicalQueueRecord l0 a) =
                  ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a Dword) ∧
              let H := P0 ++ [cell] ++ C
              let G := H ++ Dword
              let v := e + seg.records.length
              let U := ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G
              H.length = e ∧ G.length = v ∧ G.take e = H ∧ v ≤ R.length ∧
              (∀ h, h ≤ v →
                ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                  rate rewards C_star C_h (s + h) z = some (G.take h)) ∧
              R.take (e + seg.records.length) = R.take e ++ seg.records ∧
              (∀ h, k.val ≤ h → h ≤ e + seg.records.length →
                ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                  rate rewards C_star C_h (s + h) z =
                    some ((P0 ++ [cell] ++ C ++ Dword).take h)) ∧
              (∀ count, count ≤ seg.records.length →
                let ln := ReferenceCollectionSegmentExtraction.endpointLedger l0
                  (seg.records.take count)
                R.take (e + count) = R.take e ++ seg.records.take count ∧
                ln.pending = Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels
                  (seg.records.take count)).toFinset ∧
                (ReferenceCollectionPhaseHistory.acceptedLabels
                  (seg.records.take count)).Nodup ∧
                ∀ r ∈ seg.records.take count, ∀ i : Fin (p.m - 1),
                  ReferenceCollectionPhaseHistory.acceptedLabel r.input = some i →
                  ∃ (source : Fin R.length)
                    (reply : ReferenceCollectionPhaseHistory.UpRecord p rate),
                    e ≤ source.val ∧ source.val < e + count ∧
                    R[source.val] ∈ seg.records.take count ∧
                    ReferenceCollectionPhaseHistory.AcceptedUp R[source.val].input i reply ∧
                    reply.val.sigma = ln.sigma) ∧
              seg.final.pending = Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels
                seg.records).toFinset ∧
              (ReferenceCollectionPhaseHistory.acceptedLabels seg.records).Nodup ∧
              (∀ count, count ≤ seg.records.length →
                let ln := ReferenceCollectionSegmentExtraction.endpointLedger l0
                  (seg.records.take count)
                ∃ accepted,
                  CollectionCheckedExecution.checkedRounds l0 (seg.inputs.take count) =
                    some (accepted, ln) ∧
                  ln.phase = .ready ∧ ln.cursor = s + e + count + 1 ∧
                  (ln.assignment, ln.sigma, ln.cutoff, ln.freezeAt, ln.baseScore) =
                    (I.assignment, I.sigma, I.cutoff, I.freezeAt, I.base)) ∧
              rb.payload.sigma.val = (R[b.val]'b.isLt).input.time.val ∧
              (∀ count, count ≤ seg.records.length →
                let Q := seg.records.take count
                let ln := ReferenceCollectionSegmentExtraction.endpointLedger l0 Q
                CoordinatorCollectionLedger.validLedgerCheck ln = true ∧
                (∀ a, ¬ CoordinatorCollectionLedger.armPending ln a →
                  ln.cutoffRegisters a = some ⟨(U a e).1, (U a e).2,
                    (U a e).1 - (U a (e - 1)).1⟩ ∧
                  ln.currentRegisters a = some ⟨(U a (e + count)).2,
                    (U a (e + count)).1 - (U a (e + count - 1)).1⟩ ∧
                  (U a e).1 + ln.increment a = (U a (e + count)).1) ∧
                (∀ j : CanonicalFastSampling.FastArm rb.payload.slowSet,
                  ¬ CoordinatorCollectionLedger.armPending ln j.val) ∧
                (∀ i, CoordinatorCollectionLedger.armPending ln
                    (rb.payload.assignment.assigned i) ↔ i ∈ ln.pending) ∧
                (∀ i, i ∈ ln.pending →
                  let a := rb.payload.assignment.assigned i
                  ln.cutoffRegisters a = none ∧ ln.currentRegisters a = none ∧
                  ln.increment a = 0 ∧ ln.gammaLoc a = 0 ∧
                  ln.baseScore i = beta i ∧ beta i = (U a b.val).1 ∧
                  (∀ r amount, ln.rawBuffer a r = some amount ↔
                    ∃ record ∈ Q, record.input.time = r ∧ ∃ output,
                      record.output.coordinator.recording = some output ∧
                      output.gateArm = some a ∧ output.rawArrival = amount ∧
                      0 < amount ∧ r.val + 1 < l0.freezeAt) ∧
                  (∀ r, CoordinatorCollectionLedger.sourceRound r < I.cutoff →
                    ln.rawBuffer a r = none) ∧
                  (∀ r, I.freezeAt ≤ CoordinatorCollectionLedger.sourceRound r →
                    ln.rawBuffer a r = none) ∧
                  (∀ r, ln.cursor ≤ CoordinatorCollectionLedger.sourceRound r →
                    ln.rawBuffer a r = none)) ∧
                (∀ a, ¬ CoordinatorCollectionLedger.armPending ln a →
                  ∀ r, ln.rawBuffer a r = none) ∧
                (count = 0 → ∀ a r, ln.rawBuffer a r = none) ∧
                (count = seg.records.length → ln = seg.final) ∧
                (∀ record ∈ Q, ∃ done,
                  ReferenceCollectionSegmentExtraction.extractRound record = some done ∧
                  ln.enabledHistory done.input.round = some done.input.enabled) ∧
                (∀ left right, left ∈ Q → right ∈ Q →
                  left.input.time = right.input.time → left = right) ∧
                (∀ i ∈ ReferenceCollectionPhaseHistory.acceptedLabels Q,
                  ∃ (source : Fin R.length)
                    (reply : ReferenceCollectionPhaseHistory.UpRecord p rate),
                    e ≤ source.val ∧ source.val < e + count ∧
                    R[source.val] ∈ Q ∧
                    ReferenceCollectionPhaseHistory.AcceptedUp R[source.val].input i reply ∧
                    reply.val.sigma = ln.sigma ∧ ln.sigma = I.sigma ∧
                    I.sigma = rb.payload.sigma.val + 1 ∧
                    rb.payload.sigma.val + 1 = (R[b.val]'b.isLt).input.time.val + 1)) ∧
              (∀ a, ¬ CoordinatorCollectionLedger.armPending seg.final a →
                seg.final.cutoffRegisters a = some ⟨(U a e).1, (U a e).2,
                  (U a e).1 - (U a (e - 1)).1⟩ ∧
                seg.final.currentRegisters a = some ⟨(U a v).2,
                  (U a v).1 - (U a (v - 1)).1⟩ ∧
                (U a e).1 + seg.final.increment a = (U a v).1) ∧
              (∀ i, i ∈ seg.final.pending →
                let a := rb.payload.assignment.assigned i
                seg.final.cutoffRegisters a = none ∧
                seg.final.currentRegisters a = none ∧
                seg.final.increment a = 0 ∧ seg.final.gammaLoc a = 0 ∧
                seg.final.baseScore i = beta i ∧ beta i = (U a b.val).1))) := by
  classical
  intro R s
  obtain ⟨P0, rb, qb, beta, cell, native, hPlen, hPslots, hPprefix, hinit,
    hpost, hbirth, hstrict, hbase, hcell, hnative, hnativePayload, henabled,
    hbirthPrefix, hbirthSlots, hdown, hbranch⟩ :=
    ReferenceCompleteInstallationCollectionPrefixInformation.actual_later_installation_birth_calendar_data
      rate rewards C_star C_h z b hb
  refine ⟨P0, rb, qb, beta, cell, native, hPlen, hPslots, hPprefix, hinit,
    hpost, hbirth, hstrict, hbase, hcell, hnative, hnativePayload, henabled,
    hbirthPrefix, hbirthSlots, hdown, ?_⟩
  rcases hbranch with hterminal | ⟨k, C, hk, hstate, hClen, hWmap, hWtime,
    e, he, heR, rE, qE, hrPayload, hsegment⟩
  · exact Or.inl hterminal
  refine Or.inr ⟨k, C, hk, hstate, hClen, hWmap, hWtime,
    e, he, heR, rE, qE, hrPayload, ?_⟩
  rcases hsegment with hterminal | ⟨heLt, seg, I, l0, Dword, hseg, hentry,
    hpay, hledger, hinitializer, hIeq, hstart, harm, hsigma, hcutoff, hscan,
    hfreeze, hbaseI, hchosen, hne, hpart, hrun, hDlen, hDmap, hqueues,
    hRtake, hprefixAll, hlabels, hfinalPending, hfinalNodup, hchecked,
    hbirthTime, hinfo⟩
  · exact Or.inl hterminal
  let H := P0 ++ [cell] ++ C
  let G := H ++ Dword
  let v := e + seg.records.length
  let U := ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G
  have hHlen : H.length = e := by
    simp only [H, List.length_append, List.length_singleton, hPlen, hClen]
    omega
  have hGlen : G.length = v := by
    simp only [G, v, List.length_append, hHlen, hDlen]
  have hGtake : G.take e = H := by
    dsimp only [G]
    rw [← hHlen, List.take_left]
  have hvR : v ≤ R.length := by
    have hlen := congrArg List.length hpart
    simp only [List.length_append, List.length_drop] at hlen
    change seg.records.length + seg.remaining.length = R.length - e at hlen
    have heR' : e ≤ R.length := heR
    dsimp only [v]
    omega
  have hprefixEvery : ∀ h, h ≤ v →
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + h) z = some (G.take h) := by
    intro h hh
    by_cases hkh : k.val ≤ h
    · exact hprefixAll h hkh hh
    · have hhb : h ≤ b.val := by omega
      have htake : G.take h = P0.take h := by
        change (((P0 ++ [cell]) ++ C) ++ Dword).take h = P0.take h
        rw [List.take_append_of_le_length (by
          simp only [List.length_append, List.length_singleton, hPlen]; omega)]
        rw [List.take_append_of_le_length (by
          simp only [List.length_append, List.length_singleton, hPlen]; omega)]
        rw [List.take_append_of_le_length (by omega)]
      rw [htake]
      exact hPprefix h hhb
  have hGprefix : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h (s + v) z = some G := by
    simpa only [List.take_of_length_le (by omega : G.length ≤ v)] using
      hprefixEvery v le_rfl
  have hscan' : FollowerCutoffScan.firstCutoff p rate.eta.val rb.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) = s + e + 1 :=
    hscan.symm.trans hcutoff
  have houtside := outside_prefix_at_same_calendar rate rewards C_star C_h z
    b k hb rb.payload e seg G hbirth hk he heLt hseg hGprefix
  have hcontext (count : ℕ) (hc : count ≤ seg.records.length) :
      (ReferenceCollectionSegmentExtraction.endpointLedger l0
        (seg.records.take count)).assignment.arm = rb.payload.assignment.assigned := by
    obtain ⟨_accepted, _hfold, _hphase, _hcursor, hctx⟩ := hchecked count hc
    have hh := congrArg (fun x => x.1.arm) hctx
    exact hh.trans harm
  have hknown (count : ℕ) (hc : count ≤ seg.records.length) :
      let ln := ReferenceCollectionSegmentExtraction.endpointLedger l0
        (seg.records.take count)
      ∀ a, ¬ CoordinatorCollectionLedger.armPending ln a →
        ln.cutoffRegisters a = some ⟨(U a e).1, (U a e).2,
          (U a e).1 - (U a (e - 1)).1⟩ ∧
        ln.currentRegisters a = some ⟨(U a (e + count)).2,
          (U a (e + count)).1 - (U a (e + count - 1)).1⟩ ∧
        (U a e).1 + ln.increment a = (U a (e + count)).1 := by
    dsimp only
    intro a ha
    by_cases hassigned : ∃ i, rb.payload.assignment.assigned i = a
    · obtain ⟨i, rfl⟩ := hassigned
      have hinot : i ∉ (ReferenceCollectionSegmentExtraction.endpointLedger l0
          (seg.records.take count)).pending := by
        intro hi
        exact ha ⟨i, hi, congrFun (hcontext count hc) i⟩
      obtain ⟨_hRt, hpending, _hnodup, _hsources⟩ := hlabels count hc
      have hi : i ∈ ReferenceCollectionPhaseHistory.acceptedLabels
          (seg.records.take count) := by
        rw [hpending] at hinot
        by_contra hni
        exact hinot (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
          fun hmem => hni (List.mem_toFinset.mp hmem)⟩)
      obtain ⟨_hvalid, _hpendingInfo, _hcolumns, _hzero, _hfull,
        _henabledHistory, _hunique, hsources⟩ := hinfo count hc
      obtain ⟨source, reply, hse, hsc, _hmem, hacc, hsig, hsigI,
        hsigBirth, hsigTime⟩ := hsources i hi
      have hselector : reply.val.sigma = (R[b.val]'b.isLt).input.time.val + 1 :=
        hsig.trans (hsigI.trans (hsigBirth.trans hsigTime))
      have hh := assigned_prefix_at_same_calendar rate rewards C_star C_h z
        b source hb rb.payload e count seg G i reply hbirth hscan' hseg
        hGprefix hacc hselector hse hsc hc
      simpa only [hledger] using hh
    · have hj : a ∈ (Finset.univ : Finset (Fin p.K)) \ rb.payload.slowSet.val := by
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        intro hamem
        rw [← AssignmentStartPayload.Input.assignment_image rb.payload] at hamem
        obtain ⟨i, _hi, hia⟩ := Finset.mem_image.mp hamem
        exact hassigned ⟨i, hia⟩
      have hh := houtside count hc ⟨a, hj⟩
      simpa only [hledger] using hh
  have houtsideKnown (count : ℕ) (hc : count ≤ seg.records.length) :
      ∀ j : CanonicalFastSampling.FastArm rb.payload.slowSet,
        ¬ CoordinatorCollectionLedger.armPending
          (ReferenceCollectionSegmentExtraction.endpointLedger l0
            (seg.records.take count)) j.val := by
    intro j ⟨i, _hipending, hia⟩
    rw [congrFun (hcontext count hc) i] at hia
    have hi : rb.payload.assignment.assigned i ∈ rb.payload.slowSet.val := by
      rw [← AssignmentStartPayload.Input.assignment_image rb.payload]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    exact (Finset.mem_sdiff.mp j.property).2 (hia ▸ hi)
  have hpendingIff (count : ℕ) (hc : count ≤ seg.records.length)
      (i : Fin (p.m - 1)) :
      CoordinatorCollectionLedger.armPending
        (ReferenceCollectionSegmentExtraction.endpointLedger l0
          (seg.records.take count)) (rb.payload.assignment.assigned i) ↔
        i ∈ (ReferenceCollectionSegmentExtraction.endpointLedger l0
          (seg.records.take count)).pending := by
    constructor
    · rintro ⟨j, hj, hji⟩
      rw [congrFun (hcontext count hc) j] at hji
      have hji' := AssignmentStartPayload.Input.assignment_injective rb.payload hji
      exact hji' ▸ hj
    · intro hi
      exact ⟨i, hi, congrFun (hcontext count hc) i⟩
  have hbeta (i : Fin (p.m - 1)) :
      beta i = (U (rb.payload.assignment.assigned i) b.val).1 := by
    have ht : G.take b.val = P0 := by
      have hleft := hPprefix b.val le_rfl
      rw [List.take_of_length_le (by omega : P0.length ≤ b.val)] at hleft
      have hright := hprefixEvery b.val (by dsimp only [v]; omega)
      exact Option.some.inj (hright.symm.trans hleft)
    have hU : U (rb.payload.assignment.assigned i) b.val =
        ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P0
          (rb.payload.assignment.assigned i) P0.length := by
      dsimp only [U, ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay]
      rw [ht, List.take_length]
    rw [hU]
    exact (hdown i).2
  refine Or.inr ⟨heLt, seg, I, l0, Dword, hseg, hentry, hpay, hledger,
    hinitializer, hIeq, hstart, harm, hsigma, hcutoff, hscan, hfreeze, hbaseI,
    hchosen, hne, hpart, hrun, hDlen, hDmap, hqueues, hHlen, hGlen, hGtake,
    hvR, hprefixEvery, hRtake, hprefixAll, hlabels, hfinalPending, hfinalNodup,
    hchecked, hbirthTime, ?_, ?_, ?_⟩
  · intro count hc
    obtain ⟨hvalid, hpendingInfo, hcolumns, hzero, hfull, henabledHistory,
      hunique, hsources⟩ := hinfo count hc
    refine ⟨hvalid, hknown count hc, houtsideKnown count hc, hpendingIff count hc,
      ?_, hcolumns,
      hzero, hfull, henabledHistory, hunique, hsources⟩
    intro i hi
    have hh := hpendingInfo i hi
    dsimp only at hh ⊢
    rw [congrFun (hcontext count hc) i] at hh
    exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1,
      hh.2.2.2.2.1, hbeta i, hh.2.2.2.2.2⟩
  · intro a ha
    have hfull := (hinfo seg.records.length le_rfl).2.2.2.2.1 rfl
    have hh := hknown seg.records.length le_rfl a (by rw [hfull]; exact ha)
    simpa only [hfull] using hh
  · intro i hi
    obtain ⟨_hvalid, hpendingInfo, _hcolumns, _hzero, hfull, _henabledHistory,
      _hunique, _hsources⟩ := hinfo seg.records.length le_rfl
    have hfinalEq := hfull rfl
    have hh := hpendingInfo i (by rw [hfinalEq]; exact hi)
    dsimp only at hh ⊢
    rw [congrFun (hcontext seg.records.length le_rfl) i] at hh
    rw [hfinalEq] at hh
    exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1,
      hh.2.2.2.2.1, hbeta i⟩

end Bandits.Support.ReferenceCompleteInstallationCollectionPrefixNumericalTruth
