/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteInstallationCalendarInitializationInduction

import Mathlib.Tactic

/-!
# Actual later-installation outside calendar replay

At an arbitrary actual later installation, join its accepted original-index
calendar initialization to the birth service transition and apply the
conditional outside-live calendar replay with its source inputs derived from
that same transition.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon

namespace Bandits.Support.ReferenceCompleteInstallationOutsideCalendarReplay

variable {p : ConstructorDimensions.Parameters}

private theorem actual_live_cell0
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (s : ℕ)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : RecordedQueueRun.RoundInput p.K)
    (hread : ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some c) :
    ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
  classical
  obtain ⟨selected, ho, hselection, hbase, hliveState, hcell⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_some s r c hread
  have hz : 0 < selected.view.payload.sigma.val := by omega
  have hzero : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c := by
    unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
    simp only [hselection, hz, hliveState, and_self, ite_true, dite_eq_left ho]
    exact congrArg some hcell.symm
  have hcollection : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = none := by
    cases hc : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r with
    | none => rfl
    | some d =>
        exact False.elim (ReferenceCompleteNumericalBranchObservation.readouts_disjoint
          rate 0 r ⟨by rw [hzero]; rfl, by rw [hc]; rfl⟩)
  simp [ReferenceFirstCollectionCurrentRetainedGate.cell0, hcollection, hzero]

private theorem calendarReplay_append_enabled_birth
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (P : List (RecordedQueueRun.RoundInput p.K))
    (cell : RecordedQueueRun.RoundInput p.K) (arm : Fin p.K)
    (henabled : cell.enabled = true) :
    ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate (P ++ [cell]) arm
        (P.length + 1) =
      QueueReplay.transition (4 * rate.n)
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P arm P.length)
        (true, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm) := by
  have htake : (P ++ [cell]).take (P.length + 1) = P ++ [cell] := by simp
  unfold ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
  rw [htake]
  have hraw :
      ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm (P ++ [cell]) =
        ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm P ++
          [(true, RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm)] := by
    simp only [ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar,
      List.map_append, List.map_cons, List.map_nil, henabled]
  rw [hraw, QueueReplay.replay_append]
  simp only [QueueReplay.replay, List.foldl_cons, List.foldl_nil]
  rw [List.take_length]

private theorem actual_installation_birth_join
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (P0 : List (RecordedQueueRun.RoundInput p.K))
    (hinit : ReferenceFirstReplacementCalendarInitialization.initializes_calendar rate P0
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val]) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∃ (rb : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (qb : CoordinatorLiveServiceFinish.OwnedRegisters rb)
      (beta : Fin (p.m - 1) → ℕ) (cell : RecordedQueueRun.RoundInput p.K),
      R[b.val].output.next.coordinator = .live rb qb beta ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] rb.payload ∧
      s < rb.payload.sigma.val ∧
      ReferenceCompleteInstallationPredecessorInterval.installationBase?
        R[b.val].output.preparation.coordinator = some beta ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate R[b.val] = some cell ∧
      (∀ j : CanonicalFastSampling.FastArm rb.payload.slowSet,
        (rb.complementScores j, qb.queue j) =
          ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate (P0 ++ [cell])
            j.val (P0 ++ [cell]).length) ∧
      (∀ j : CanonicalFastSampling.FastArm rb.payload.slowSet,
        qb.previousService j =
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate
            (P0 ++ [cell]) j.val (P0 ++ [cell]).length).1 -
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate
            (P0 ++ [cell]) j.val ((P0 ++ [cell]).length - 1)).1) ∧
      (∀ i : Fin (p.m - 1),
        (rb.payload.downRecord i).val.q =
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P0
            (rb.payload.assignment.assigned i) P0.length).2 ∧
        beta i = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P0
          (rb.payload.assignment.assigned i) P0.length).1) ∧
      ∃ native : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell R[b.val],
        native.input = cell ∧ native.selected.view.payload = rb.payload ∧
        cell.enabled = true ∧
        ReferenceLaterLiveNumericalReadout.laterLiveReadout s R[b.val] = some cell := by
  classical
  intro R s
  rcases hinit with ⟨old, ledger, proposal, uA, hstateA, hpendingA, huA,
    coreA, startedA, hstartA, instructionA, hassignmentA, htimeA,
    consistentA, outputA, hlocalA, clockDataA, installedA, selectedA,
    hinstallA, hsuccessA, hdispatchA, hpreparedA,
    hpayloadA, hsigmaA, hvectorA, hrecA, hnumA, hretainedA,
    hcomplementA, hcorrectedA, hrenewalA⟩
  have hstep :=
    ReferenceCompleteEmptyInstallationNumericalStep.complete_empty_installation_current_numerical_step
      rate rewards C_star C_h z b
  dsimp only at hstep
  rw [hstateA] at hstep
  dsimp only at hstep
  rcases hstep hpendingA with ⟨u, hu, core, started, hstart, instruction,
    hassignment, htime, hkind, consistent, output, hlocal, hsuccess, clockData,
    installed, selected, hinstall, hresult, hdispatch, hprepared,
    hpayload, hvector, hassignmentVector, hbaseNew, hqueues, hanchor,
    v, hselection, hvpayload, hvcutoff, hlive, hstrict, cell, ho, actualCell,
    hreadout, hcell, hcellSelected, hstates, hmemories, hunoccupied,
    henabled, hrate, hreward, hmarker, hrows, hselectedRow, hrewards,
    harrival, hcontribution, hoccupiedArrival, howner,
    recording, serviced, pending, finished, hrecording, hrecorded,
    hservicedRecording, hrawAll, hservice, hconfirmation, hfinish, hpost,
    hcoordinator, hnext, hupBank⟩
  have huEq : uA = u := Fin.ext (by omega)
  cases huEq
  have hstartedEq : startedA = started := Except.ok.inj (hstartA.symm.trans hstart)
  cases hstartedEq
  have hinstructionEq : instructionA = instruction :=
    Option.some.inj (hassignmentA.symm.trans hassignment)
  cases hinstructionEq
  have hpreparedEq := hpreparedA.symm.trans hprepared
  have houtputEq : outputA = output := by
    cases hpreparedEq
    rfl
  subst outputA
  have hnum : ∀ arm : Fin p.K,
      AssignmentScoreReconstruction.sourceScore output.reconstruction arm =
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P0 arm P0.length).1 ∧
      AssignmentScoreReconstruction.initialQueue output.reconstruction arm =
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P0 arm P0.length).2 := by
    intro arm
    exact ⟨(hnumA arm).1, (hnumA arm).2.1⟩
  let rb : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta :=
    { payload := installed.registers.payload
      priorClock := finished.clock
      pendingAtChoice := finished.pending
      time := R[b.val].input.time
      gridBoundary := finished.clock.g
      complementScores := serviced.score }
  let qb : CoordinatorLiveServiceFinish.OwnedRegisters rb :=
    { queue := serviced.queue, previousService := serviced.previousService }
  have hseed : ∀ j : CanonicalFastSampling.FastArm rb.payload.slowSet,
      (rb.complementScores j, qb.queue j) =
        ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate (P0 ++ [cell])
          j.val (P0 ++ [cell]).length := by
    intro j
    have htransition := (hservice j).2.1
    have hinitial :
        (AssignmentScoreReconstruction.sourceScore output.reconstruction j.val,
          AssignmentScoreReconstruction.initialQueue output.reconstruction j.val) =
          ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P0 j.val P0.length :=
      Prod.ext (hnum j.val).1 (hnum j.val).2
    rw [hinitial] at htransition
    have happend := calendarReplay_append_enabled_birth rate P0 cell j.val henabled
    have hjoined := htransition.trans happend.symm
    simpa only [rb, qb, List.length_append, List.length_singleton] using hjoined
  refine ⟨rb, qb, installed.retainedBaseScore, cell, ?_, ?_, hstrict, ?_,
    actual_live_cell0 rate s R[b.val] cell hreadout, hseed, ?_, ?_, ?_⟩
  · rw [hpost] at hnext
    simpa only [rb, qb] using hnext
  · rw [ReferenceAssignmentPayloadPersistence.InstallationBirth, hprepared]
    exact ⟨rfl, by
      change installed.registers.payload.sigma.val = R[b.val].input.time.val
      rw [hpayload, output.payload_start, htime]⟩
  · rw [hprepared]
    rfl
  · intro j
    change serviced.previousService j = _
    rw [(hservice j).2.2, (hnum j.val).1, ← hseed j]
    have htake : (P0 ++ [cell]).take ((P0 ++ [cell]).length - 1) = P0 := by
      simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel,
        List.take_left]
    congr 1
    simp only [ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay, htake,
      List.take_length]
  · intro i
    exact ⟨(AssignmentStartPayload.Input.downRecord_initialQueue _ i).trans
        ((hqueues _).trans (hnum _).2),
      hbaseNew i |>.trans (hnum _).1⟩

  · exact ⟨actualCell, hcell, by rw [hcellSelected]; exact hvpayload,
      henabled, hreadout⟩

/-- Actual collection prefixes use the same physical endpoint ledgers, including
both the empty prefix and the full segment. -/
private theorem actual_segment_prefix_checked
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (e : ℕ) (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hseg : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)
      e = some seg) (hne : seg.records ≠ []) (n : ℕ) (hn : n ≤ seg.records.length) :
    ∃ accepted, CollectionCheckedExecution.checkedRounds seg.context.preLedger
      (seg.inputs.take n) = some (accepted,
        ReferenceCollectionSegmentExtraction.endpointLedger seg.context.preLedger
          (seg.records.take n)) := by
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      have hnil : ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h = [] := by
        simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hl, dite_true]
      have hpart := ReferenceCollectionSegmentExtraction.segmentAt_partition _ e seg hseg
      rw [hnil, List.drop_nil] at hpart
      exact False.elim (hne (List.append_eq_nil_iff.mp hpart).1)
  | some initial =>
      have hrun := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate z rewards C_star C_h initial hl
      rw [hrun] at hseg
      exact ReferenceCollectionPrefixLedgerHistory.run_segment_prefix_checked
        initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
        _ _ _ _ e seg hseg n hn

/-- At any actual later installation, derive the birth seed internally and apply
the accepted outside replay to its actual successor. The result retains the
native source word and physical collection endpoint, without requiring a future
installation or an empty pending set. -/
public theorem actual_later_installation_complement_calendar_replay
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
    let capacity : ℕ := 4 * ActiveFollowerDownAcceptance.RateInput.n rate
    ∃ (P0 : List (RecordedQueueRun.RoundInput p.K))
      (rb : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (qb : CoordinatorLiveServiceFinish.OwnedRegisters rb)
      (beta : Fin (p.m - 1) → ℕ) (cell : RecordedQueueRun.RoundInput p.K)
      (native : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell (R[b.val]'b.isLt)),
      P0.length = b.val ∧
      (R.take b.val).map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = P0.map some ∧
      (∀ h, h ≤ b.val → ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + h) z = some (P0.take h)) ∧
      ReferenceFirstReplacementCalendarInitialization.initializes_calendar rate P0 (R[b.val]'b.isLt) ∧
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
      (∀ j : CanonicalFastSampling.FastArm rb.payload.slowSet,
        (rb.complementScores j, qb.queue j) =
          ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate (P0 ++ [cell])
            j.val (P0 ++ [cell]).length ∧
        qb.previousService j =
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate
            (P0 ++ [cell]) j.val (P0 ++ [cell]).length).1 -
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate
            (P0 ++ [cell]) j.val b.val).1) ∧
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
      let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z k.val
      let e := k.val + W.length
      let H := P0 ++ [cell] ++ C
      C.length = W.length ∧
      W.map (ReferenceLaterLiveNumericalReadout.laterLiveReadout s) = C.map some ∧
      W.map (fun r => r.input.time.val) = List.range' (s + k.val) W.length ∧
      e ≤ R.length ∧ s + e ≤ p.T ∧ H.length = e ∧
      (∀ h, k.val ≤ h → h ≤ e →
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h (s + h) z = some (H.take h)) ∧
      (R.take e).map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = H.map some ∧
      (∀ c ∈ H, c.enabled = false → c.recordedArm = none ∧ ∀ a,
        RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) ∧
      (∀ (count : ℕ) (_hcount : count ≤ W.length),
        ∃ (rn : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (qn : CoordinatorLiveServiceFinish.OwnedRegisters rn),
          rn.payload = rb.payload ∧
          (∀ _hpos : 0 < count, (W[count - 1]?).map (fun r => r.output.next.coordinator) = some (.live rn qn beta)) ∧
          (∀ _hnext : k.val + count < R.length,
            (R[k.val + count]?).map (fun r => r.input.state.coordinator) = some (.live rn qn beta)) ∧
          ∀ j : CanonicalFastSampling.FastArm rb.payload.slowSet,
            ∃ jn : CanonicalFastSampling.FastArm rn.payload.slowSet,
            jn.val = j.val ∧
            (rn.complementScores jn, qn.queue jn) = (QueueReplay.replay capacity (rb.complementScores j, qb.queue j)
                (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate j.val (C.take count))) ∧
            qn.previousService jn =
              if count = 0 then qb.previousService j else ((QueueReplay.replay capacity (rb.complementScores j, qb.queue j)
                (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate j.val (C.take count)))).1 - ((QueueReplay.replay capacity (rb.complementScores j, qb.queue j)
                (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate j.val (C.take (count - 1))))).1) ∧
      ∃ (rE : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (qE : CoordinatorLiveServiceFinish.OwnedRegisters rE),
        rE.payload = rb.payload ∧
        (∀ _hpos : 0 < W.length,
          (W[W.length - 1]?).map (fun r => r.output.next.coordinator) = some (.live rE qE beta)) ∧
        (∀ _he : e < R.length, (R[e]?).map (fun r => r.input.state.coordinator) = some (.live rE qE beta)) ∧
        (∀ j : CanonicalFastSampling.FastArm rb.payload.slowSet,
          ∃ jE : CanonicalFastSampling.FastArm rE.payload.slowSet,
          jE.val = j.val ∧
          (rE.complementScores jE, qE.queue jE) =
            ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate H j.val e ∧
          qE.previousService jE =
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate H j.val e).1 -
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate H j.val (e - 1)).1) ∧
        (e = R.length ∨
        ∃ (he : e < R.length) (seg : ReferenceCollectionSegmentExtraction.Segment rate)
          (I : ReferenceCollectionSegmentExtraction.Initializer p)
          (l0 : ReferenceActivePhysicalStep.Ledger rate)
          (Dword : List (RecordedQueueRun.RoundInput p.K)),
          ReferenceCollectionSegmentExtraction.segmentAt R e = some seg ∧
          seg.entry = (R[e]'he) ∧ seg.context.payload = rb.payload ∧
          seg.context.preLedger = l0 ∧ seg.context.initializer = some I ∧
          I = ReferenceCollectionSegmentExtraction.cutoffInitializer
            (liveRegistersAt rE (R[e]'he).input.time) (liveOwnedAt rE qE (R[e]'he).input.time) beta (R[e]'he).input.time ∧
          I.checkedStart rate = .success l0 ∧
          I.assignment.arm = rb.payload.assignment.assigned ∧ I.sigma = rb.payload.sigma.val + 1 ∧
          I.cutoff = s + e + 1 ∧
          I.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val rb.payload.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
              (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) ∧
          I.freezeAt = rE.gridBoundary ∧ I.base = beta ∧
          ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
          (∃ tail, seg.records = seg.entry :: tail) ∧
          seg.records ++ seg.remaining = R.drop e ∧
          seg.exit = ReferenceCollectionSegmentExtraction.exitOf seg.remaining ∧
          CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
            (ReferenceUpReception.sourceCap_forLedger rate) (ActiveFollowerDownAcceptance.RateInput.n rate) rate.n_scale
            I.assignment I.sigma I.cutoff I.freezeAt I.base I.outside seg.inputs =
              .success ⟨l0, seg.accepted, seg.final⟩ ∧
          Dword.length = seg.records.length ∧
          seg.records.map (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s) = Dword.map some ∧
          (∀ a, CollectionKnownQueueContinuation.inputQueueRecords l0 a seg.inputs =
              seg.records.map (ReferenceCollectionRawBufferHistory.physicalQueueRecord l0 a) ∧
            seg.records.map (ReferenceCollectionRawBufferHistory.physicalQueueRecord l0 a) =
              ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a Dword) ∧
          let E := H ++ Dword
          let v := e + seg.records.length
          let U := ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate E
          E.length = v ∧ E.take e = H ∧ v ≤ R.length ∧ s + v ≤ p.T ∧
          R.take v = R.take e ++ seg.records ∧
          (∀ h, k.val ≤ h → h ≤ v →
            ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
              rate rewards C_star C_h (s + h) z = some (E.take h)) ∧
          (R.take v).map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = E.map some ∧
          (∀ c ∈ E, c.enabled = false → c.recordedArm = none ∧ ∀ a,
            RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) ∧
          (∀ count, count ≤ seg.records.length →
            let ln := ReferenceCollectionSegmentExtraction.endpointLedger l0 (seg.records.take count)
            ∃ accepted, CollectionCheckedExecution.checkedRounds l0 (seg.inputs.take count) =
              some (accepted, ln) ∧
            ∀ j : CanonicalFastSampling.FastArm rb.payload.slowSet,
              let d := (U j.val e).1 - (U j.val (e - 1)).1
              let records := ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate j.val (Dword.take count)
              let Y := QueueReplay.replay capacity (0, (U j.val e).2) records
              ln.cutoffRegisters j.val = some ⟨(U j.val e).1, (U j.val e).2, d⟩ ∧
              ln.currentRegisters j.val = some ⟨Y.2,
                CollectionKnownQueueContinuation.replayLastService capacity
                  (0, (U j.val e).2) d records⟩ ∧
              ln.increment j.val = Y.1) ∧
          (∀ j : CanonicalFastSampling.FastArm rb.payload.slowSet,
            seg.final.cutoffRegisters j.val =
              some ⟨(U j.val e).1, (U j.val e).2, (U j.val e).1 - (U j.val (e - 1)).1⟩ ∧
            seg.final.currentRegisters j.val =
              some ⟨(U j.val v).2, (U j.val v).1 - (U j.val (v - 1)).1⟩ ∧
            (U j.val e).1 + seg.final.increment j.val = (U j.val v).1))) := by
  classical
  intro R s capacity
  obtain ⟨P0, hPlen, hPslots, hPprefix, hinit⟩ :=
    ReferenceCompleteInstallationCalendarInitializationInduction.internal_complete_later_installation_calendar_initialization
      rate rewards C_star C_h z b hb
  obtain ⟨rb, qb, beta, cell, hpost, hbirth, hstrict, hbase, hcell,
    hseed, hpreviousBirth, hdown, native, hnative, hnativePay, henabled, hreadout⟩ :=
    actual_installation_birth_join rate rewards C_star C_h z b P0 hinit
  have hP0 : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h (s + b.val) z = some P0 := by
    simpa only [List.take_of_length_le (by omega : P0.length ≤ b.val)] using
      hPprefix b.val le_rfl
  have hindex : s + b.val -
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
        rate rewards C_star C_h z = b.val := by
    dsimp [s, ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart]
    omega
  have hlookup :
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
        rate rewards C_star C_h z)[s + b.val -
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
            rate rewards C_star C_h z]? = some (R[b.val]'b.isLt) := by
    change R[s + b.val -
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
        rate rewards C_star C_h z]? = some (R[b.val]'b.isLt)
    rw [hindex]
    exact List.getElem?_eq_getElem b.isLt
  have happend :=
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_append_one
      rate rewards C_star C_h (s + b.val) z P0 hP0
      (R[b.val]'b.isLt) cell hlookup hcell
  have hPbirth : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h (s + (b.val + 1)) z = some (P0 ++ [cell]) := by
    simpa only [Nat.add_assoc] using happend
  have hbirthSlots : (R.take (b.val + 1)).map
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = (P0 ++ [cell]).map some := by
    rw [List.take_add_one, List.getElem?_eq_getElem b.isLt,
      Option.toList_some, List.map_append, hPslots]
    simp only [List.map_cons, List.map_nil, hcell, List.map_append]
  refine ⟨P0, rb, qb, beta, cell, native, hPlen, hPslots, hPprefix, hinit,
    hpost, hbirth, hstrict, hbase, hcell, hnative, hnativePay, henabled,
    hPbirth, hbirthSlots, ?_, hdown, ?_⟩
  · intro j
    refine ⟨hseed j, ?_⟩
    simpa only [List.length_append, List.length_singleton, Nat.add_sub_cancel, hPlen] using
      hpreviousBirth j
  by_cases hk : b.val + 1 < R.length
  · let k : Fin R.length := ⟨b.val + 1, hk⟩
    have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
      (rate := rate) rewards C_star C_h z b.val hk
    have hstate : R[k.val].input.state.coordinator = .live rb qb beta :=
      (congrArg (fun state : ReferenceActivePhysicalStep.State p rate => state.coordinator)
        hadj).trans hpost
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z k.val
    let C := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
      rewards C_star C_h z k rb qb beta hstate hstrict
    let e := k.val + W.length
    let H := P0 ++ [cell] ++ C
    have hprevious : W.length = 0 →
        ∀ j : CanonicalFastSampling.FastArm rb.payload.slowSet,
          qb.previousService j =
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate
              (P0 ++ [cell]) j.val (P0 ++ [cell]).length).1 -
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate
              (P0 ++ [cell]) j.val (k.val - 1)).1 := by
      intro _ j
      simpa only [List.length_append, List.length_singleton, hPlen, k] using hpreviousBirth j
    have houtside :=
      ReferenceCompleteInitializedOutsideCalendarReplay.complete_later_live_initialized_outside_calendar_replay
        rate rewards C_star C_h z k rb qb beta hstate hstrict (P0 ++ [cell]) hPbirth
        hseed hprevious
    dsimp only at houtside
    obtain ⟨_, hClen, heR, heT, hHlen, _hHtake, hprefix, _hrawSlots,
      hcoords, hdisabled, rE, qE, hp, hlast, hin, hvalues, halt⟩ := houtside
    change H.length = e at hHlen
    change e ≤ R.length at heR
    change C.length = W.length at hClen
    have hslots : (R.take e).map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) =
        H.map some := by
      apply List.ext_getElem
      · simp only [List.length_map, List.length_take, hHlen, Nat.min_eq_left heR]
      · intro i hi hi'
        have hiE : i < e := by simpa only [List.length_map, hHlen] using hi'
        simpa only [List.getElem_map, List.getElem_take] using (hcoords heR hHlen ⟨i, hiE⟩).1
    refine Or.inr ⟨k, C, rfl, hstate, hClen,
      ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_map
        rewards C_star C_h z k rb qb beta hstate hstrict,
      ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_times rewards C_star C_h z k,
      heR, heT, hHlen, hprefix, hslots, hdisabled, ?_, rE, qE, hp,
      ?_, ?_, ?_, ?_⟩
    · intro count hn
      obtain ⟨rn, qn, hpn, houtn, hinn, hnum⟩ :=
        ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_replay
          rewards C_star C_h z k rb qb beta hstate hstrict count hn
      refine ⟨rn, qn, hpn, ?_, ?_, ?_⟩
      · intro hpos
        rw [List.getElem?_eq_getElem (Nat.lt_of_lt_of_le
          (Nat.sub_lt hpos Nat.zero_lt_one) hn)]
        exact congrArg some (houtn hpos)
      · intro hnext
        rw [List.getElem?_eq_getElem hnext]
        exact congrArg some (hinn hnext)
      · intro j
        refine ⟨⟨j.val, by simpa only [hpn] using j.property⟩, rfl, ?_⟩
        exact hnum j
    · intro hpos
      rw [List.getElem?_eq_getElem (Nat.sub_lt hpos Nat.zero_lt_one)]
      exact congrArg some (hlast hpos)
    · intro he
      rw [List.getElem?_eq_getElem he]
      exact congrArg some (hin he)
    · intro j
      refine ⟨⟨j.val, by simpa only [hp] using j.property⟩, rfl, ?_⟩
      simpa only [ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay,
        List.take_of_length_le (by omega : H.length ≤ e)] using hvalues j
    rcases halt with hterminal | ⟨he, seg, I, l0, Dword, hat, hentry, hpay, hledger,
      hI, hIeq, hchecked, harm, hsigma, hcutoff, hscan, hfreeze, hbaseI,
      hchosen, hne, hpart, hexit, hfold, hDlen, hDmap, hsync,
      hElen, hEtake, _hEtakeP, hvR, hvT, hRtake, hprefixAll,
      hcoordsAll, _hCenabled, _hDdisabled, hdisabledAll, hfinal⟩
    · exact Or.inl hterminal
    · change (H ++ Dword).length = e + seg.records.length at hElen
      change (H ++ Dword).take e = H at hEtake
      change e + seg.records.length ≤ R.length at hvR
      refine Or.inr ⟨he, seg, I, l0, Dword, hat, hentry, hpay, hledger,
        hI, hIeq, hchecked, harm, hsigma, hcutoff, hscan, hfreeze, hbaseI,
        hchosen, hne, hpart, hexit, hfold, hDlen, hDmap, hsync,
        hElen, hEtake, hvR, hvT, hRtake, hprefixAll, ?_, hdisabledAll, ?_, hfinal⟩
      · change (R.take (e + seg.records.length)).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = (H ++ Dword).map some
        apply List.ext_getElem
        · simp only [List.length_map, List.length_take, hElen, Nat.min_eq_left hvR]
        · intro i hi hi'
          have hiV : i < e + seg.records.length := by
            simpa only [List.length_map, hElen] using hi'
          simpa only [List.getElem_map, List.getElem_take] using
            (hcoordsAll hvR hElen ⟨i, hiV⟩).1
      · intro count hn
        obtain ⟨accepted, hprefixChecked⟩ := actual_segment_prefix_checked
          rate rewards C_star C_h z e seg hat (by
            obtain ⟨tail, ht⟩ := hne
            rw [ht]
            exact List.cons_ne_nil _ _) count hn
        rw [hledger] at hprefixChecked
        refine ⟨accepted, hprefixChecked, ?_⟩
        intro j
        -- The initializer supplies the actual known cutoff register. Its
        -- score/queue/last-service are identified by the actual LIVE endpoint.
        have hinitFields : l0.cutoffRegisters = I.outside ∧
            l0.currentRegisters = (fun a => (I.outside a).map
              (fun q => ⟨q.queue, q.lastService⟩)) ∧ l0.increment = fun _ => 0 := by
          unfold ReferenceCollectionSegmentExtraction.Initializer.checkedStart
            CoordinatorCollectionLedger.startCollectionChecked at hchecked
          split at hchecked
          · dsimp only at hchecked
            split at hchecked
            · cases hchecked
              exact ⟨rfl, rfl, rfl⟩
            · contradiction
          · contradiction
        let jE : CanonicalFastSampling.FastArm rE.payload.slowSet :=
          ⟨j.val, (congrArg (fun payload =>
                j.val ∈ CanonicalFastSampling.fastArmFinset payload.slowSet) hp).mpr j.property⟩
        have hout : I.outside j.val = some
            ⟨rE.complementScores jE, qE.queue jE, qE.previousService jE⟩ := by
          have hj : j.val ∈ CanonicalFastSampling.fastArmFinset rE.payload.slowSet := jE.property
          rw [hIeq]
          simp only [ReferenceCollectionSegmentExtraction.cutoffInitializer,
            CoordinatorStartRoundCutoffDispatch.outsideRegisters, liveRegistersAt,
            liveOwnedAt, hj, ↓reduceDIte]
          rfl
        have hpair := (hvalues j).1
        have hlastService := (hvalues j).2
        change (rE.complementScores jE, qE.queue jE) =
          ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate H j.val e at hpair
        change qE.previousService jE =
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate H j.val e).1 -
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate H j.val (e - 1)).1 at hlastService
        have hglobal :
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate
              (H ++ Dword) j.val e) =
            ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate H j.val e := by
          simp only [ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay, hEtake,
            List.take_of_length_le (by omega : H.length ≤ e)]
        have hglobalPrev :
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate
              (H ++ Dword) j.val (e - 1)) =
            ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate H j.val (e - 1) := by
          unfold ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
          rw [List.take_append_of_le_length (by omega : e - 1 ≤ H.length)]
        have houtNumerical : I.outside j.val = some
            ⟨(ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate
                (H ++ Dword) j.val e).1,
             (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate
                (H ++ Dword) j.val e).2,
             (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate
                (H ++ Dword) j.val e).1 -
             (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate
                (H ++ Dword) j.val (e - 1)).1⟩ := by
          rw [hglobal, hglobalPrev, hout]
          have hscore : rE.complementScores jE =
              (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate H j.val e).1 := by
            exact congrArg Prod.fst hpair
          have hqueue : qE.queue jE =
              (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate H j.val e).2 := by
            exact congrArg Prod.snd hpair
          have hlastGlobal : qE.previousService jE =
              (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate H j.val e).1 -
              (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate H j.val (e - 1)).1 := by
            exact hlastService
          rw [hscore, hqueue, hlastGlobal]
        have hknown := congrFun hinitFields.2.1 j.val
        rw [houtNumerical] at hknown
        have hcontinued := CollectionKnownQueueContinuation.checkedRounds_known_queue_continuation
          l0 (ReferenceCollectionSegmentExtraction.endpointLedger l0 (seg.records.take count))
          j.val _ (seg.inputs.take count) accepted hknown hprefixChecked
        have hrawPrefix : CollectionKnownQueueContinuation.inputQueueRecords l0 j.val
            (seg.inputs.take count) = ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar
              rate j.val (Dword.take count) := by
          have hs := (hsync j.val).1.trans (hsync j.val).2
          have ht := congrArg (List.take count) hs
          simpa only [CollectionKnownQueueContinuation.inputQueueRecords,
            ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar, List.map_take] using ht
        dsimp only at hcontinued
        rw [hrawPrefix, congrFun hinitFields.2.2 j.val] at hcontinued
        refine ⟨?_, hcontinued.1, hcontinued.2.1⟩
        exact hcontinued.2.2.2.2.2.2.trans
          ((congrFun hinitFields.1 j.val).trans houtNumerical)
  · exact Or.inl (by have hbR : b.val < R.length := b.isLt; omega)

end Bandits.Support.ReferenceCompleteInstallationOutsideCalendarReplay

end
