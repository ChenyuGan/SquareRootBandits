/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteInstallationOutsideCalendarReplay
public import Bandits.Support.ReferenceCompleteCollectionBoundaryHistory
public import Bandits.Support.ReferenceCompleteCollectionPrefixRawBufferHistory

import Mathlib.Tactic

/-!
# Actual installation collection-prefix information

This module keeps the actual later-installation replay and its terminal,
continuing-live, and collection-segment branches together.  The local helper
below records the checked-prefix context facts used when specializing an
actual segment.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep

namespace Bandits.Support.ReferenceCompleteInstallationCollectionPrefixInformation

variable {p : ConstructorDimensions.Parameters}

private theorem last_marked_prefix_length {α : Type} (test : α → Bool)
    (before before' : List α) (head head' : α) (tail tail' : List α)
    (h : before ++ head :: tail = before' ++ head' :: tail')
    (hh : test head = true) (hh' : test head' = true)
    (ht : ∀ r ∈ tail, test r = false) (ht' : ∀ r ∈ tail', test r = false) :
    before.length = before'.length := by
  induction before generalizing before' with
  | nil =>
      cases before' with
      | nil => rfl
      | cons r rs =>
          have he := (List.cons.inj h).2
          have hm : head' ∈ tail := by
            rw [he]
            exact List.mem_append_right _ List.mem_cons_self
          have hf := ht head' hm
          rw [hh'] at hf
          contradiction
  | cons r rs ih =>
      cases before' with
      | nil =>
          have he := (List.cons.inj h).2
          have hm : head ∈ tail' := by
            rw [← he]
            exact List.mem_append_right _ List.mem_cons_self
          have hf := ht' head hm
          rw [hh] at hf
          contradiction
      | cons r' rs' =>
          exact congrArg Nat.succ (ih rs' (List.cons.inj h).2)

private theorem connected_final_endpoint
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial final : ReferenceActivePhysicalStep.State p rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (h : ReferenceActivePhysicalHorizon.Connected initial records final) :
    final = ReferenceCollectionSegmentExtraction.endpointState initial records := by
  induction records generalizing initial final with
  | nil => simpa [ReferenceActivePhysicalHorizon.Connected,
      ReferenceCollectionSegmentExtraction.endpointState] using h
  | cons record rest ih =>
      rcases h with ⟨_, hrest⟩
      simpa [ReferenceCollectionSegmentExtraction.endpointState] using
        ih record.output.next final hrest

private theorem checked_prefix_context
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (initializer : ReferenceCollectionSegmentExtraction.Initializer p)
    (initial final : ReferenceActivePhysicalStep.Ledger rate)
    (inputs : List (CollectionCheckedExecution.RoundInput
      (p := p) (eta := rate.eta.val)))
    (accepted : List Bool)
    (hstart : initializer.checkedStart rate = .success initial)
    (hfold : CollectionCheckedExecution.checkedRounds initial inputs =
      some (accepted, final)) :
    final.phase = .ready ∧
      final.cursor = initial.cursor + inputs.length ∧
      (final.assignment, final.sigma, final.cutoff, final.freezeAt, final.baseScore) =
        (initializer.assignment, initializer.sigma, initializer.cutoff,
          initializer.freezeAt, initializer.base) := by
  have hready : initial.phase = .ready := by
    exact CollectionCheckedExecution.startCollectionChecked_success_ready
      p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
      initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
      initializer.base initializer.outside initial (by
        simpa only [ReferenceCollectionSegmentExtraction.Initializer.checkedStart] using hstart)
  have hchron := CollectionCheckedExecution.checkedRounds_success_chronology
    initial final hready inputs accepted hfold
  have hcontext := CollectionBufferProvenance.checkedRounds_success_preserves_context
    initial final inputs accepted hfold
  have hinitial := CollectionBufferProvenance.startCollectionChecked_success_context
    initializer.assignment initializer.sigma initializer.cutoff
    initializer.freezeAt initializer.base initializer.outside initial (by
      simpa only [ReferenceCollectionSegmentExtraction.Initializer.checkedStart] using hstart)
  have hinitialContext :
      (initial.assignment, initial.sigma, initial.cutoff, initial.freezeAt,
        initial.baseScore) =
        (initializer.assignment, initializer.sigma, initializer.cutoff,
          initializer.freezeAt, initializer.base) := by
    rcases hinitial with ⟨hassignment, hsigma, _, hcutoff, hfreeze, hbase⟩
    simp only [hassignment, hsigma, hcutoff, hfreeze, hbase]
  refine ⟨hchron.2, hchron.1, ?_⟩
  have hctx :
      (final.assignment, final.sigma, final.cutoff, final.freezeAt, final.baseScore) =
        (initial.assignment, initial.sigma, initial.cutoff, initial.freezeAt,
          initial.baseScore) := hcontext
  calc
    (final.assignment, final.sigma, final.cutoff, final.freezeAt, final.baseScore) =
        (initial.assignment, initial.sigma, initial.cutoff, initial.freezeAt,
          initial.baseScore) := hctx
    _ = (initializer.assignment, initializer.sigma, initializer.cutoff,
        initializer.freezeAt, initializer.base) := hinitialContext

/-- The accepted arbitrary-b installation fixes the original corrected
calendar, literal birth payload, and the same beta used to initialize its
assigned followers.  Every clipped collection prefix retains the literal physical
raw-buffer witnesses, including positive-arrival and pre-freeze guards;
terminal and continuing-live branches remain explicit. -/
public theorem actual_later_installation_birth_calendar_data
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
                (∀ i, i ∈ ln.pending →
                  let a := ln.assignment.arm i
                  ln.cutoffRegisters a = none ∧ ln.currentRegisters a = none ∧
                  ln.increment a = 0 ∧ ln.gammaLoc a = 0 ∧
                  ln.baseScore i = beta i ∧
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
                    rb.payload.sigma.val + 1 = (R[b.val]'b.isLt).input.time.val + 1)))) := by
  classical
  intro R s
  obtain ⟨P0, rb, qb, beta, cell, native, hPlen, hPslots, hPprefix, hinit,
    hpost, hbirth, hstrict, hbase, hcell, hnative, hnativePayload, henabled,
    hbirthPrefix, hbirthSlots, _hseed, hdown, hbranch⟩ :=
    ReferenceCompleteInstallationOutsideCalendarReplay.actual_later_installation_complement_calendar_replay
      rate rewards C_star C_h z b hb
  dsimp only at hbranch
  rcases hbranch with hterminal | ⟨k, C, hk, hstate, hClen, hWmap, hWtime,
    _heR, _heT, _hHlen, _hprefix, _hslots, _hdisabled, _hprefixReplay,
    rE, qE, hrPayload, _hlast, _hin, _hvalues, halt⟩
  · exact ⟨P0, rb, qb, beta, cell, native, hPlen, hPslots, hPprefix,
      hinit, hpost, hbirth, hstrict, hbase, hcell, hnative, hnativePayload,
      henabled, hbirthPrefix, hbirthSlots, hdown, Or.inl hterminal⟩
  · rcases halt with hnoSegment | ⟨he, seg, I, l0, Dword, hseg, hentry,
      hpay, hledger, _hinitializer, hIeq, hstart, harm, hsigma, hcutoff, hscan, hfreeze,
      hbaseI, hchosen, hne, hpart, _hexit, hfold, hDlen, hDmap, hsync,
      _hElen, _hEtake, hvR, hvT, hRtake, hprefixAll, _hcoordsAll,
      _hdisabledAll, hprefixChecked, _hfinal⟩
    · let e0 := k.val + (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z k.val).length
      exact ⟨P0, rb, qb, beta, cell, native, hPlen, hPslots, hPprefix,
        hinit, hpost, hbirth, hstrict, hbase, hcell, hnative, hnativePayload,
        henabled, hbirthPrefix, hbirthSlots, hdown,
        Or.inr ⟨k, C, hk, hstate, hClen, hWmap, hWtime,
          ⟨e0, rfl, _heR, rE, qE, hrPayload, Or.inl hnoSegment⟩⟩⟩
    ·
      let e0 := k.val + (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z k.val).length
      let ln (count : ℕ) := ReferenceCollectionSegmentExtraction.endpointLedger l0
        (seg.records.take count)
      have hnonempty : seg.records ≠ [] := by
        rcases hne with ⟨tail, hrecords⟩
        rw [hrecords]
        simp
      have hboundary :=
        ReferenceCompleteCollectionBoundaryHistory.internal_complete_collection_boundary_history
          rate rewards C_star C_h z e0 seg hseg hnonempty hchosen
      dsimp only at hboundary
      obtain ⟨saved, hsaved⟩ := hboundary.2.2.2
      have hhistory := hsaved.2.2
      rcases hhistory with ⟨duringBoundary, hrecordsBoundary, _hprefixBoundary,
        _hlaterBoundary, hnocutBoundary, hpending, hnodup, _, _⟩
      have hRnonempty : R ≠ [] := by
        intro hnil
        have hblt := b.isLt
        change b.val < R.length at hblt
        rw [hnil] at hblt
        simp at hblt
      have hlaunchNone : ReferenceCorrectedInitializationLaunch.correctedLaunch
          rate z rewards C_star C_h ≠ none := by
        intro hnone
        have hnil : R = [] := by
          simp [R, ReferenceCompletePhysicalHistory.completeSuffixRecords, hnone]
        exact hRnonempty hnil
      have hcross := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate z rewards C_star C_h).mp (Option.ne_none_iff_isSome.mp hlaunchNone)
      obtain ⟨initial, ⟨hlaunch, hfirst, _, _, _⟩, _⟩ :=
        ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
          rate z rewards C_star C_h hcross
      let hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
        rate z rewards C_star C_h initial hlaunch
      let total := p.T - s
      have hspanTotal : s + total ≤ p.T := by
        dsimp only [total, s]
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate z rewards C_star C_h
        omega
      have htotalLength : R.length = total := by
        simpa only [R, total, s] using
          ReferenceCompletePhysicalHistory.completeSuffixRecords_length
            rate z rewards C_star C_h
      have hvTotal : e0 + seg.records.length ≤ total := by
        rw [← htotalLength]
        simpa only [e0] using hvR
      let v0 := e0 + seg.records.length
      have hspanPrefix : s + v0 ≤ p.T := by
        dsimp only [v0]
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate z rewards C_star C_h
        omega
      let fullRun := ReferenceActivePhysicalHorizon.run initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s total hspanTotal hmode
      let prefixRun := ReferenceActivePhysicalHorizon.run initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s v0 hspanPrefix hmode
      have hRrun := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate z rewards C_star C_h initial hlaunch
      have hRrun' : R = fullRun.records := by
        simpa only [R, fullRun, total, hmode] using hRrun
      have hchainFull := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
        rate z rewards C_star C_h initial hlaunch
      have hchainFull' : ReferenceActivePhysicalHorizon.Connected initial R fullRun.finalState := by
        simpa only [R, fullRun, total, hmode] using hchainFull
      obtain ⟨suffix, happend⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
        initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
        s v0 (total - v0) (by omega) hmode
      have hsum : v0 + (total - v0) = total := Nat.add_sub_of_le hvTotal
      have happend' : fullRun.records = prefixRun.records ++ suffix := by
        simpa only [fullRun, prefixRun, hsum] using happend
      have hprefixRecords : fullRun.records.take v0 = prefixRun.records := by
        rw [happend', List.take_append_of_le_length (by
          rw [ReferenceActivePhysicalHorizon.run_record_count])]
        exact List.take_of_length_le (by
          rw [ReferenceActivePhysicalHorizon.run_record_count])
      have hRprefix : R.take v0 = prefixRun.records := by
        calc
          R.take v0 = fullRun.records.take v0 := by rw [hRrun']
          _ = prefixRun.records := hprefixRecords
      have hwindowFull : R.take v0 = R.take e0 ++ seg.records := by
        simpa only [v0, e0] using hRtake
      have hchainDrop := ReferenceCollectionSegmentExtraction.connected_drop
        R initial fullRun.finalState e0 hchainFull'
      rcases hne with ⟨tail, hrecords⟩
      have hdropEq : R.drop e0 = seg.entry :: (tail ++ seg.remaining) := by
        calc
          R.drop e0 = seg.records ++ seg.remaining := hpart.symm
          _ = seg.entry :: (tail ++ seg.remaining) := by rw [hrecords]; simp
      have hchainDropEntry := hchainDrop
      rw [hdropEq] at hchainDropEntry
      have hentryState : seg.entry.input.state =
          ReferenceCollectionSegmentExtraction.endpointState initial (R.take e0) :=
        hchainDropEntry.1
      have hprefixEndpoint := connected_final_endpoint initial prefixRun.finalState
        prefixRun.records prefixRun.connected
      have hprefixState : prefixRun.finalState =
          ReferenceCollectionSegmentExtraction.endpointState seg.entry.input.state seg.records := by
        calc
          prefixRun.finalState =
              ReferenceCollectionSegmentExtraction.endpointState initial prefixRun.records :=
            hprefixEndpoint
          _ = ReferenceCollectionSegmentExtraction.endpointState initial (R.take v0) := by
            rw [hRprefix]
          _ = ReferenceCollectionSegmentExtraction.endpointState initial
                (R.take e0 ++ seg.records) := by rw [hwindowFull]
          _ = ReferenceCollectionSegmentExtraction.endpointState
                (ReferenceCollectionSegmentExtraction.endpointState initial (R.take e0))
                seg.records := by
                  simp only [ReferenceCollectionSegmentExtraction.endpointState,
                    List.foldl_append]
          _ = ReferenceCollectionSegmentExtraction.endpointState seg.entry.input.state
                seg.records := by rw [← hentryState]
      have hcoordPrefix : prefixRun.finalState.coordinator =
          .collection seg.context.payload seg.final saved := by
        rw [hprefixState]
        exact hsaved.1
      have hsourceHistory := ReferenceCollectionPhaseHistory.run_history
        initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
        s v0 hspanPrefix hmode hfirst seg.context.payload seg.final saved hcoordPrefix
      rcases hsourceHistory with ⟨before, cutoffRecord, during, hdecomp,
        hcutoffHistory, _hlaterHistory, hduringHistory, _, _, hwitnesses⟩
      have hcomponents := CollectionBufferProvenance.startAndRunChecked_success_components
        I.assignment I.sigma I.cutoff I.freezeAt I.base I.outside seg.inputs
        ⟨l0, seg.accepted, seg.final⟩ hfold
      rcases hcomponents with ⟨acceptedFull, _, hcheckFull⟩
      have hfullContext := checked_prefix_context rate I l0 seg.final seg.inputs
        acceptedFull hstart hcheckFull
      rcases hfullContext with ⟨_, _, hfullPreserved⟩
      have hfullSigma : seg.final.sigma = I.sigma := by
        have hsigma := congrArg (fun context => context.2.1) hfullPreserved
        exact hsigma
      have htailEq : tail = duringBoundary := by
        have hcons := List.cons.inj (hrecords.symm.trans hrecordsBoundary)
        exact hcons.2
      have hdecomp' : R.take e0 ++ seg.entry :: tail =
          before ++ cutoffRecord :: during := by
        calc
          R.take e0 ++ seg.entry :: tail = R.take e0 ++ seg.records := by
            rw [hrecords]
          _ = prefixRun.records := hwindowFull.symm.trans hRprefix
          _ = before ++ cutoffRecord :: during := hdecomp
      have hnotcutTail : ∀ r ∈ tail,
          ReferenceCollectionPhaseHistory.cutoffChosen r.input = false := by
        intro r hr
        rw [htailEq] at hr
        exact (hnocutBoundary r hr).1
      have hbeforeLen : before.length = (R.take e0).length :=
        ReferenceCompleteInstallationCollectionPrefixInformation.last_marked_prefix_length
          (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
            ReferenceCollectionPhaseHistory.cutoffChosen r.input)
          (R.take e0) before seg.entry cutoffRecord tail during hdecomp'
          hchosen hcutoffHistory hnotcutTail
          (fun r hr => (hduringHistory r hr).1)
          |>.symm
      have he0le : e0 ≤ R.length := by omega
      have hleftLen : (R.take e0).length = e0 := by
        simp only [List.length_take, Nat.min_eq_left he0le]
      have hbeforeLen' : before.length = e0 := hbeforeLen.trans hleftLen
      have hwindowHistory : seg.records = cutoffRecord :: during := by
        calc
          seg.records = (R.take e0 ++ seg.records).drop (R.take e0).length :=
            List.drop_append_length.symm
          _ = (before ++ cutoffRecord :: during).drop before.length := by
            rw [hrecords, hdecomp', hleftLen, hbeforeLen']
          _ = cutoffRecord :: during := List.drop_append_length
      have hacceptedOnSegment : ∀ r ∈ seg.records, ∀ i : Fin (p.m - 1),
          ReferenceCollectionPhaseHistory.acceptedLabel r.input = some i →
          ∃ reply : ReferenceCollectionPhaseHistory.UpRecord p rate,
            ReferenceCollectionPhaseHistory.AcceptedUp r.input i reply ∧
              reply.val.sigma = seg.final.sigma := by
        intro r hr i hi
        have hr' : r ∈ cutoffRecord :: during := by
          rw [hwindowHistory] at hr
          exact hr
        obtain ⟨reply, haccepted, hreplySigma⟩ := hwitnesses r hr' i hi
        exact ⟨reply, haccepted, hreplySigma⟩
      have hinputLength : seg.inputs.length = seg.records.length :=
        ReferenceCollectionSegmentExtraction.segment_input_count (R.drop e0) seg
          (ReferenceCollectionSegmentExtraction.segmentAt_branch R e0 seg hseg).1
      have hprefixFacts : ∀ count, count ≤ seg.records.length →
          ∃ accepted,
            CollectionCheckedExecution.checkedRounds l0 (seg.inputs.take count) =
              some (accepted, ln count) ∧
            (ln count).phase = .ready ∧ (ln count).cursor = s + e0 + count + 1 ∧
            ((ln count).assignment, (ln count).sigma, (ln count).cutoff,
              (ln count).freezeAt, (ln count).baseScore) =
              (I.assignment, I.sigma, I.cutoff, I.freezeAt, I.base) := by
        intro count hcount
        obtain ⟨accepted, hcheck, _hknown⟩ := hprefixChecked count hcount
        have hcontext := checked_prefix_context rate I l0 (ln count)
          (seg.inputs.take count) accepted hstart hcheck
        have hlen : (seg.inputs.take count).length = count := by
          simp only [List.length_take, hinputLength]
          exact Nat.min_eq_left hcount
        have hinit := CollectionBufferProvenance.startCollectionChecked_success_context
          I.assignment I.sigma I.cutoff I.freezeAt I.base I.outside l0 (by
            simpa only [ReferenceCollectionSegmentExtraction.Initializer.checkedStart] using hstart)
        rcases hinit with ⟨_, _, hcursor, _, _, _⟩
        rcases hcontext with ⟨hready, hprefixCursor, hpreserved⟩
        have hcursor' : (ln count).cursor = s + e0 + count + 1 := by
          rw [hcursor, hcutoff] at hprefixCursor
          dsimp only [s, e0] at hprefixCursor ⊢
          omega
        exact ⟨accepted, hcheck, hready, hcursor', hpreserved⟩
      have hprefixWindows : ∀ count, count ≤ seg.records.length →
          R.take (e0 + count) = R.take e0 ++ seg.records.take count := by
        intro count hcount
        calc
          R.take (e0 + count) = R.take e0 ++ (R.drop e0).take count := by
            rw [List.take_add]
          _ = R.take e0 ++ (seg.records ++ seg.remaining).take count := by
            rw [hpart.symm]
          _ = R.take e0 ++ seg.records.take count := by
            congr 1
            exact List.take_append_of_le_length hcount
      have hstartPending : l0.pending = Finset.univ := by
        have hstart' : CoordinatorCollectionLedger.startCollectionChecked
            p rate.eta.val rate.eta.property
            (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
            I.assignment I.sigma I.cutoff I.freezeAt I.base I.outside = .success l0 := by
          simpa only [ReferenceCollectionSegmentExtraction.Initializer.checkedStart] using hstart
        unfold CoordinatorCollectionLedger.startCollectionChecked at hstart'
        repeat (first | split at hstart' | dsimp only at hstart')
        all_goals
          first
          | contradiction
          | (injection hstart' with heq; cases heq; rfl)
      have hgoodSegment := ReferenceCollectionSegmentExtraction.segment_all_completed
        (R.drop e0) seg (ReferenceCollectionSegmentExtraction.segmentAt_branch R e0 seg hseg).1
      have hprefixPendingFacts : ∀ count, count ≤ seg.records.length →
          let ln := ReferenceCollectionSegmentExtraction.endpointLedger l0
            (seg.records.take count)
          ln.pending = Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels
            (seg.records.take count)).toFinset ∧
          (ReferenceCollectionPhaseHistory.acceptedLabels
            (seg.records.take count)).Nodup := by
        intro count hcount
        dsimp only
        by_cases hzero : count = 0
        · subst count
          constructor
          · simp [ReferenceCollectionSegmentExtraction.endpointLedger,
              ReferenceCollectionSegmentExtraction.completed,
              ReferenceCollectionPhaseHistory.acceptedLabels, hstartPending]
          · simp [ReferenceCollectionPhaseHistory.acceptedLabels]
        · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
          have hQnonempty : seg.records.take (n + 1) ≠ [] := by
            rw [hrecords]
            simp
          have hgoodQ : ∀ record ∈ seg.records.take (n + 1),
              (ReferenceCollectionSegmentExtraction.extractRound record).isSome = true := by
            intro record hrecord
            exact hgoodSegment record (List.mem_of_mem_take hrecord)
          obtain ⟨payload, proposal, hendpoint⟩ :=
            ReferenceCollectionSegmentExtraction.completed_endpoint
              (seg.records.take (n + 1)) seg.entry.input.state l0 hQnonempty hgoodQ
          let vCount := e0 + (n + 1)
          have hvCount : vCount ≤ total := by
            dsimp only [vCount]
            omega
          have hspanCount : s + vCount ≤ p.T := by
            dsimp only [vCount]
            have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
              rate z rewards C_star C_h
            omega
          let runCount := ReferenceActivePhysicalHorizon.run initial z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s vCount
            hspanCount hmode
          obtain ⟨suffixCount, happendCount⟩ :=
            ReferenceCollectionPhaseHistory.run_records_prefix initial z.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s vCount
              (total - vCount) (by omega) hmode
          have hsumCount : vCount + (total - vCount) = total :=
            Nat.add_sub_of_le hvCount
          have happendCount' : fullRun.records = runCount.records ++ suffixCount := by
            simpa only [fullRun, runCount, hsumCount] using happendCount
          have hrecordsCount : fullRun.records.take vCount = runCount.records := by
            rw [happendCount', List.take_append_of_le_length (by
              rw [ReferenceActivePhysicalHorizon.run_record_count])]
            exact List.take_of_length_le (by
              rw [ReferenceActivePhysicalHorizon.run_record_count])
          have hRrecordsCount : R.take vCount = runCount.records := by
            calc
              R.take vCount = fullRun.records.take vCount := by rw [hRrun']
              _ = runCount.records := hrecordsCount
          have hstateCount : runCount.finalState =
              ReferenceCollectionSegmentExtraction.endpointState seg.entry.input.state
                (seg.records.take (n + 1)) := by
            have hendpointRun := connected_final_endpoint initial runCount.finalState
              runCount.records runCount.connected
            calc
              runCount.finalState =
                  ReferenceCollectionSegmentExtraction.endpointState initial runCount.records :=
                hendpointRun
              _ = ReferenceCollectionSegmentExtraction.endpointState initial (R.take vCount) := by
                rw [hRrecordsCount]
              _ = ReferenceCollectionSegmentExtraction.endpointState initial
                    (R.take e0 ++ seg.records.take (n + 1)) := by
                rw [hprefixWindows (n + 1) (by omega)]
              _ = ReferenceCollectionSegmentExtraction.endpointState
                    (ReferenceCollectionSegmentExtraction.endpointState initial (R.take e0))
                    (seg.records.take (n + 1)) := by
                simp only [ReferenceCollectionSegmentExtraction.endpointState,
                  List.foldl_append]
              _ = ReferenceCollectionSegmentExtraction.endpointState seg.entry.input.state
                    (seg.records.take (n + 1)) := by rw [← hentryState]
          have hcoordCount : runCount.finalState.coordinator =
              .collection payload (ln (n + 1)) proposal := by
            rw [hstateCount]
            simpa only [ln, ReferenceCollectionSegmentExtraction.endpointLedger] using hendpoint
          have hphaseHistory := ReferenceCollectionPhaseHistory.run_history
            initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
            s vCount hspanCount hmode hfirst
          have hhistoryCount := hphaseHistory payload (ln (n + 1)) proposal hcoordCount
          rcases hhistoryCount with ⟨before, cutoffRecord, during, hdecompCount,
            hcutoffCount, _hlaterCount, hduringCount, hpendingCount, hnodupCount, _⟩
          let tailCount := tail.take n
          have hQshape : seg.records.take (n + 1) = seg.entry :: tailCount := by
            simp [tailCount, hrecords]
          have hdecompCount' : R.take e0 ++ seg.entry :: tailCount =
              before ++ cutoffRecord :: during := by
            calc
              R.take e0 ++ seg.entry :: tailCount =
                  R.take e0 ++ seg.records.take (n + 1) := by rw [hQshape]
              _ = R.take (e0 + (n + 1)) := (hprefixWindows (n + 1) (by omega)).symm
              _ = runCount.records := by simpa only [vCount] using hRrecordsCount
              _ = before ++ cutoffRecord :: during := hdecompCount
          have hnotcutTailCount : ∀ r ∈ tailCount,
              ReferenceCollectionPhaseHistory.cutoffChosen r.input = false := by
            intro r hr
            exact hnotcutTail r (List.mem_of_mem_take hr)
          have hbeforeCount : before.length = (R.take e0).length := by
            apply (last_marked_prefix_length
              (fun r : ReferenceActivePhysicalHorizon.RoundRecord
                (p := p) (rate := rate) => ReferenceCollectionPhaseHistory.cutoffChosen r.input)
              (R.take e0) before seg.entry cutoffRecord tailCount during hdecompCount'
              hchosen hcutoffCount hnotcutTailCount
              (fun r hr => (hduringCount r hr).1)).symm
          have hbeforeCount' : before.length = e0 := by
            rw [hleftLen] at hbeforeCount
            exact hbeforeCount
          have hwindowHistoryCount : seg.records.take (n + 1) = cutoffRecord :: during := by
            calc
              seg.records.take (n + 1) =
                  (R.take e0 ++ seg.records.take (n + 1)).drop (R.take e0).length :=
                    List.drop_append_length.symm
              _ = (before ++ cutoffRecord :: during).drop before.length := by
                rw [hQshape, hdecompCount', hleftLen, hbeforeCount']
              _ = cutoffRecord :: during := List.drop_append_length
          constructor
          · rw [← hwindowHistoryCount] at hpendingCount
            exact hpendingCount
          · rw [hwindowHistoryCount]
            exact hnodupCount
      have hacceptedPrefixes : ∀ count, count ≤ seg.records.length →
          let ln := ReferenceCollectionSegmentExtraction.endpointLedger l0
            (seg.records.take count)
          R.take (e0 + count) = R.take e0 ++ seg.records.take count ∧
          ln.pending = Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels
            (seg.records.take count)).toFinset ∧
          (ReferenceCollectionPhaseHistory.acceptedLabels
            (seg.records.take count)).Nodup ∧
          ∀ r ∈ seg.records.take count, ∀ i : Fin (p.m - 1),
            ReferenceCollectionPhaseHistory.acceptedLabel r.input = some i →
            ∃ (source : Fin R.length)
              (reply : ReferenceCollectionPhaseHistory.UpRecord p rate),
              e0 ≤ source.val ∧ source.val < e0 + count ∧
              R[source.val] ∈ seg.records.take count ∧
              ReferenceCollectionPhaseHistory.AcceptedUp R[source.val].input i reply ∧
              reply.val.sigma = ln.sigma := by
        intro count hcount
        dsimp only
        refine ⟨hprefixWindows count hcount, (hprefixPendingFacts count hcount).1,
          (hprefixPendingFacts count hcount).2, ?_⟩
        intro r hr i hi
        obtain ⟨reply, haccepted, hreplySigma⟩ :=
          hacceptedOnSegment r (List.mem_of_mem_take hr) i hi
        obtain ⟨accepted, hcheck, hready, hcursor, hpreserved⟩ :=
          hprefixFacts count hcount
        have hlnSigma : (ln count).sigma = I.sigma := by
          exact congrArg (fun context => context.2.1) hpreserved
        have hreplyAtPrefix : reply.val.sigma = (ln count).sigma := by
          calc
            reply.val.sigma = seg.final.sigma := hreplySigma
            _ = I.sigma := hfullSigma
            _ = (ln count).sigma := hlnSigma.symm
        have hQlen : (seg.records.take count).length = count := by
          simp only [List.length_take]
          exact Nat.min_eq_left hcount
        obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hr
        have hjCount : j < count := by simpa only [hQlen] using hj
        have hjSeg : j < seg.records.length := by omega
        have hgetQ : (seg.records.take count)[j]? = some r := by
          simp only [List.getElem?_eq_getElem hj, hget]
        have hgetSeg : seg.records[j]? = some r := by
          simpa only [List.getElem?_take_of_lt hjCount] using hgetQ
        have hk : e0 + j < R.length := by omega
        have hpartIndex : (seg.records ++ seg.remaining)[j]? = (R.drop e0)[j]? :=
          congrArg (fun records => records[j]?) hpart
        have hrecord : R[e0 + j]'hk = r := by
          simpa only [List.getElem?_append_left hjSeg, hgetSeg,
            List.getElem?_drop, List.getElem?_eq_getElem hk,
            Option.some.injEq] using hpartIndex.symm
        let source : Fin R.length := ⟨e0 + j, hk⟩
        have hsourceInPrefix : R[source.val] ∈ seg.records.take count := by
          change R[e0 + j] ∈ seg.records.take count
          rw [hrecord]
          exact hr
        have hsourceAccepted :
            ReferenceCollectionPhaseHistory.AcceptedUp R[source.val].input i reply := by
          change ReferenceCollectionPhaseHistory.AcceptedUp R[e0 + j].input i reply
          rw [hrecord]
          exact haccepted
        exact ⟨source, reply, by change e0 ≤ e0 + j; omega,
          by change e0 + j < e0 + count; omega,
          hsourceInPrefix, hsourceAccepted, hreplyAtPrefix⟩
      have hbirthTime : rb.payload.sigma.val = (R[b.val]'b.isLt).input.time.val := by
        unfold ReferenceAssignmentPayloadPersistence.InstallationBirth at hbirth
        split at hbirth <;> first | exact hbirth.2 | contradiction
      have hstartContext := CollectionBufferProvenance.startCollectionChecked_success_context
        I.assignment I.sigma I.cutoff I.freezeAt I.base I.outside l0 (by
          simpa only [ReferenceCollectionSegmentExtraction.Initializer.checkedStart] using hstart)
      have hpreCutoff : l0.cursor = I.cutoff := hstartContext.2.2.1
      have hpreFreeze : l0.freezeAt = I.freezeAt := hstartContext.2.2.2.2.1
      have hrawPrefixes := fun count hcount =>
        ReferenceCompleteCollectionPrefixRawBufferHistory.run_segment_prefix_raw_buffer_history
          rewards C_star C_h z e0 seg hseg hnonempty hchosen count hcount
      have hrawJoined : ∀ count, count ≤ seg.records.length →
                let Q := seg.records.take count
                let ln := ReferenceCollectionSegmentExtraction.endpointLedger l0 Q
                CoordinatorCollectionLedger.validLedgerCheck ln = true ∧
                (∀ i, i ∈ ln.pending →
                  let a := ln.assignment.arm i
                  ln.cutoffRegisters a = none ∧ ln.currentRegisters a = none ∧
                  ln.increment a = 0 ∧ ln.gammaLoc a = 0 ∧
                  ln.baseScore i = beta i ∧
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
                    e0 ≤ source.val ∧ source.val < e0 + count ∧
                    R[source.val] ∈ Q ∧
                    ReferenceCollectionPhaseHistory.AcceptedUp R[source.val].input i reply ∧
                    reply.val.sigma = ln.sigma ∧ ln.sigma = I.sigma ∧
                    I.sigma = rb.payload.sigma.val + 1 ∧
                    rb.payload.sigma.val + 1 = (R[b.val]'b.isLt).input.time.val + 1) := by
        intro count hcount
        dsimp only
        obtain ⟨I', hI', _hstart', accepted', hchecked', _hready', _hcursor',
          _hassignment', hsig', _hcutoff', _hfreeze', _hbase', hvalid,
          hpendingRaw, hnonpendingRaw, hzeroRaw, hfullRaw, henabledRaw, htimeRaw⟩ :=
          hrawPrefixes count hcount
        have hII : I' = I := Option.some.inj (hI'.symm.trans _hinitializer)
        subst I'
        rw [hledger] at hchecked' hsig' hvalid hpendingRaw hnonpendingRaw hzeroRaw hfullRaw henabledRaw
        refine ⟨hvalid, ?_, hnonpendingRaw, hzeroRaw, hfullRaw, henabledRaw, htimeRaw, ?_⟩
        · intro i hi
          have h := hpendingRaw i hi
          simpa only [hbaseI, hpreCutoff, hpreFreeze] using h
        · intro i hi
          obtain ⟨r, hr, haccept⟩ := List.mem_filterMap.mp hi
          obtain ⟨source, reply, hlow, hupp, hmem, hreply, hreplySigma⟩ :=
            (hacceptedPrefixes count hcount).2.2.2 r hr i haccept
          exact ⟨source, reply, hlow, hupp, hmem, hreply, hreplySigma,
            hsig', hsigma, congrArg (fun t => t + 1) hbirthTime⟩
      exact ⟨P0, rb, qb, beta, cell, native, hPlen, hPslots, hPprefix,
        hinit, hpost, hbirth, hstrict, hbase, hcell, hnative, hnativePayload,
        henabled, hbirthPrefix, hbirthSlots, hdown,
        Or.inr ⟨k, C, hk, hstate, hClen, hWmap, hWtime,
          ⟨e0, rfl, _heR, rE, qE, hrPayload,
          Or.inr ⟨he, seg, I, l0, Dword, hseg, hentry, hpay, hledger,
            _hinitializer, hIeq, hstart, harm, hsigma, hcutoff, hscan, hfreeze, hbaseI, hchosen,
            ⟨tail, hrecords⟩, hpart, hfold, hDlen, hDmap, hsync, hRtake,
            hprefixAll, hacceptedPrefixes, hpending, hnodup, hprefixFacts, hbirthTime, hrawJoined⟩⟩⟩⟩

end Bandits.Support.ReferenceCompleteInstallationCollectionPrefixInformation

end
