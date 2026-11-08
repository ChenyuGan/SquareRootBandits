/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteInstallationCollectionPrefixNumericalTruth
public import Bandits.Support.ReferenceFirstCorrectedCollectionKnownQueueOverflowCover

import Mathlib.Tactic

/-!
# Actual later-installation collection known-queue sites

This module aligns actual collection register sites with the original calendar
prefix at later installations. It records only queues that are present at the
literal site and keeps the first excluded candidate separate from the retained
collection segment.

Source evidence: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`04_slow_fast_learner.tex:157-188,218-254`, and
`06_interruptions.tex:192-233,246-299,391-426`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceCollectionSegmentExtraction
open ReferenceFirstCorrectedCollectionKnownQueueSource
open ReferenceLaterCollectionArrivalReadout
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix (sourceRecords sourceStart)
open scoped Classical

namespace Bandits.Support.ReferenceCompleteInstallationCollectionKnownQueueSource

variable {p : ConstructorDimensions.Parameters}

private theorem calendar_append_one_queue
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (G : List (RecordedQueueRun.RoundInput p.K))
    (d : RecordedQueueRun.RoundInput p.K) (a : Fin p.K) :
    (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
      rate (G ++ [d]) a (G ++ [d]).length).2 =
      (QueueReplay.transition (4 * rate.n)
        (0, (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a G.length).2)
        (d.enabled, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) d a)).2 := by
  simp only [ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay,
    ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar, List.take_length,
    List.map_append, List.map_cons, List.map_nil, QueueReplay.replay_append]
  simp only [QueueReplay.replay, List.foldl_cons, List.foldl_nil]
  cases d.enabled <;> simp only [QueueReplay.transition,
    Bool.false_eq_true, ite_false, ite_true]

private theorem calendar_take
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (G : List (RecordedQueueRun.RoundInput p.K)) (a : Fin p.K) (h : ℕ) :
    ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate (G.take h) a
        (G.take h).length =
      ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a h := by
  simp only [ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay, List.take_length]

private theorem actual_candidate_calendar
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (call : Choice rate) (d : RecordedQueueRun.RoundInput p.K)
    (hread : laterCollectionReadout 0 record = some d)
    (hcall : laterCollectionCall 0 record =
      some ⟨call.payload, call.preLedger, call.started, call.weights⟩)
    (G : List (RecordedQueueRun.RoundInput p.K))
    (hqueues : ∀ a current, call.preLedger.currentRegisters a = some current →
      current.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a G.length).2)
    (out : CoordinatorRecordingOperation.Output p)
    (hout : record.coordinatorDiagnostics.recording = some out)
    (candidate : ReferenceActivePhysicalStep.Ledger rate)
    (hreached : reachedStageOneCandidate? call.preLedger record.input.time
      (ReferenceActivePhysicalStep.collectionEnabled call.preLedger record.input.time)
      out = some candidate) :
    (∀ a current, candidate.currentRegisters a = some current →
      current.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
        rate (G ++ [d]) a (G ++ [d]).length).2) ∧
    candidate.cutoffRegisters = call.preLedger.cutoffRegisters := by
  obtain ⟨payload, ledger, clock, weights, out', hcall', _htail, _hrun,
    _henabled, _hclock, _hrate, _hreward, hout', _hgate, harr⟩ :=
    laterCollectionReadout_call 0 record d hread
  have hargs := Option.some.inj (hcall'.symm.trans hcall)
  cases hargs
  have heq : out' = out := Option.some.inj (hout'.symm.trans hout)
  subst out'
  obtain ⟨_hv, _hp, _hc, _hpos, _hbound, _hdomain, _hslot, hcandidate⟩ :=
    reachedStageOneCandidate_guard_values _ _ _ _ _ hreached
  rw [hcandidate]
  refine ⟨?_, rfl⟩
  intro a current hcurrent
  cases hknown : call.preLedger.currentRegisters a with
  | none => simp only [CoordinatorCollectionLedger.startRoundCandidate, hknown,
      reduceCtorEq] at hcurrent
  | some before =>
      have ht := CoordinatorCollectionLedger.startRoundCandidate_known_transition
        call.preLedger record.input.time
        (ReferenceActivePhysicalStep.collectionEnabled call.preLedger record.input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out)
        a before hknown
      have hcurrentEq := Option.some.inj (hcurrent.symm.trans ht)
      have hqueue := congrArg CoordinatorCollectionLedger.CurrentRegister.queue hcurrentEq
      dsimp only at hqueue
      rw [calendar_append_one_queue, hqueue, hqueues a before hknown]
      rw [← _henabled]
      cases he : d.enabled with
      | false =>
          simp [CoordinatorCollectionLedger.localQueueRecord, QueueReplay.transition]
      | true =>
          have hce : collectionEnabled call.preLedger record.input.time = true := by
            rw [← _henabled, he]
          have hfreeze : record.input.time.val + 1 < call.preLedger.freezeAt := by
            unfold ReferenceActivePhysicalStep.collectionEnabled at hce
            simp only [decide_eq_true_eq] at hce
            exact hce.2.2
          simp [CoordinatorCollectionLedger.localQueueRecord,
            CoordinatorCollectionLedger.sourceRound, hfreeze, harr,
            ReferenceFirstLaunchNumericalCell.queueParameters, QueueReplay.transition]

private theorem not_pending_of_current_present
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (a : Fin p.K)
    (current : CoordinatorCollectionLedger.CurrentRegister)
    (hvalid : CoordinatorCollectionLedger.validLedgerCheck ledger = true)
    (hcurrent : ledger.currentRegisters a = some current) :
    ¬ CoordinatorCollectionLedger.armPending ledger a := by
  have hchecks : CoordinatorCollectionLedger.allFin p.K (fun x =>
      (ledger.currentRegisters x).isNone == CoordinatorCollectionLedger.armPendingCheck ledger x) = true := by
    have hh := hvalid
    simp only [CoordinatorCollectionLedger.validLedgerCheck, Bool.and_eq_true] at hh
    tauto
  have hforall : ∀ x ∈ List.ofFn (fun x : Fin p.K =>
      (ledger.currentRegisters x).isNone == CoordinatorCollectionLedger.armPendingCheck ledger x),
      x = true := by
    simpa only [CoordinatorCollectionLedger.allFin, List.all_eq_true, id_eq] using hchecks
  have hentry := hforall ((ledger.currentRegisters a).isNone ==
      CoordinatorCollectionLedger.armPendingCheck ledger a)
      (List.mem_ofFn.mpr ⟨a, rfl⟩)
  rw [hcurrent] at hentry
  have hcheck : CoordinatorCollectionLedger.armPendingCheck ledger a = false := by
    cases hc : CoordinatorCollectionLedger.armPendingCheck ledger a with
    | false => rfl
    | true => simp [Option.isNone_some, hc] at hentry
  intro hpending
  have htrue : CoordinatorCollectionLedger.armPendingCheck ledger a = true := by
    change CoordinatorCollectionLedger.anyFin (p.m - 1) _ = true
    unfold CoordinatorCollectionLedger.anyFin
    rw [List.any_eq_true]
    rcases hpending with ⟨i, hi, harm⟩
    exact ⟨true, List.mem_ofFn.mpr ⟨i, by simp [hi, harm]⟩, rfl⟩
  rw [hcheck] at htrue
  cases htrue

private theorem not_pending_of_cutoff_present
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (a : Fin p.K)
    (cutoff : CoordinatorCollectionLedger.CutoffRegister)
    (hvalid : CoordinatorCollectionLedger.validLedgerCheck ledger = true)
    (hcutoff : ledger.cutoffRegisters a = some cutoff) :
    ¬ CoordinatorCollectionLedger.armPending ledger a := by
  have hchecks : CoordinatorCollectionLedger.allFin p.K (fun x =>
      (ledger.cutoffRegisters x).isNone == CoordinatorCollectionLedger.armPendingCheck ledger x) = true := by
    have hh := hvalid
    simp only [CoordinatorCollectionLedger.validLedgerCheck, Bool.and_eq_true] at hh
    tauto
  have hforall : ∀ x ∈ List.ofFn (fun x : Fin p.K =>
      (ledger.cutoffRegisters x).isNone == CoordinatorCollectionLedger.armPendingCheck ledger x),
      x = true := by
    simpa only [CoordinatorCollectionLedger.allFin, List.all_eq_true, id_eq] using hchecks
  have hentry := hforall ((ledger.cutoffRegisters a).isNone ==
      CoordinatorCollectionLedger.armPendingCheck ledger a)
      (List.mem_ofFn.mpr ⟨a, rfl⟩)
  rw [hcutoff] at hentry
  have hcheck : CoordinatorCollectionLedger.armPendingCheck ledger a = false := by
    cases hc : CoordinatorCollectionLedger.armPendingCheck ledger a with
    | false => rfl
    | true => simp [Option.isNone_some, hc] at hentry
  intro hpending
  have htrue : CoordinatorCollectionLedger.armPendingCheck ledger a = true := by
    change CoordinatorCollectionLedger.anyFin (p.m - 1) _ = true
    unfold CoordinatorCollectionLedger.anyFin
    rw [List.any_eq_true]
    rcases hpending with ⟨i, hi, harm⟩
    exact ⟨true, List.mem_ofFn.mpr ⟨i, by simp [hi, harm]⟩, rfl⟩
  rw [hcheck] at htrue
  cases htrue

private theorem actual_segment_run
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (e : ℕ) (seg : Segment rate)
    (hseg : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg) :
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∃ (initial : ReferenceActivePhysicalStep.State p rate)
      (span : s + (p.T - s) ≤ p.T) (active : allActiveAtStart initial s),
      initial.coordinator = .first ∧
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h =
        (run initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
          rewards s (p.T - s) span active).records := by
  intro s
  have hlaunchNe : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h ≠ none := by
    intro hnone
    have hnil : ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h = [] := by
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hnone, dite_true]
    rw [hnil] at hseg
    simp only [segmentAt, List.drop_nil, ReferenceCollectionSegmentExtraction.segment] at hseg
    contradiction
  have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h).isSome = true := by
    cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h with
    | none => exact False.elim (hlaunchNe hl)
    | some initial => rfl
  have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate z rewards C_star C_h).mp hsome
  obtain ⟨initial, hlaunch, hfirst, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
      rate z rewards C_star C_h hc
  have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  exact ⟨initial, by dsimp only [s]; omega,
    ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
      rate z rewards C_star C_h initial hlaunch, hfirst,
    ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h initial hlaunch⟩

private theorem actual_collection_choice_payload
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool)) (call : Choice rate)
    (hstate : record.input.state.coordinator = .collection payload ledger proposal)
    (hchoice : choice record.input = some call) :
    call.payload = payload := by
  unfold choice at hchoice
  split at hchoice
  · contradiction
  next =>
    change choiceOfCut (ReferenceActivePhysicalStep.dispatch record.input) = some call at hchoice
    simp only [ReferenceActivePhysicalStep.dispatch, hstate] at hchoice
    split at hchoice
    next hcut =>
      let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
      let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
      change choiceOfCut (.collection payload ledger clock cutoff
        (CoordinatorRoundDispatch.dispatchCollection
          (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff))) =
            some call at hchoice
      cases ho : CoordinatorRoundDispatch.dispatchCollection
          (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff) <;>
        simp only [choiceOfCut, ho] at hchoice
      all_goals first
        | contradiction
        | exact (congrArg Choice.payload (Option.some.inj hchoice)).symm
    · simp only [choiceOfCut, reduceCtorEq] at hchoice

variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem completed_payload
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (done : CompletedRound rate)
    (h : extractRound record = some done) :
    ∃ saved, record.output.next.coordinator = .collection done.context.payload done.final saved := by
  obtain ⟨hc, _, _, P, saved, hn⟩ := actual_collection_round_checked record done h
  have ht : record.output.coordinator = collectionPostChoice (prepare record.input)
      done.context.payload done.context.preLedger done.context.started done.context.weights := by
    rw [record.output_eq]
    exact choice_tail record.input done.context hc
  have hf := ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
    (prepare record.input) done.context.payload done.context.preLedger
      done.context.started done.context.weights
  have hs : record.output.coordinator.configuration = .collection P done.final saved := by
    rw [record.output_eq] at hn ⊢
    exact hn
  rw [← ht, hs] at hf
  simp only [ReferenceAssignmentPayloadPersistence.storedPayload_collection,
    reduceCtorEq, false_or] at hf
  have hp := Option.some.inj hf
  exact ⟨saved, hp ▸ hn⟩

private theorem choice_selection (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (ctx : Choice rate) (hchoice : choice r.input = some ctx) :
    ∃ v : Selection r.input,
      r.output.preparation.coordinator.selection = some v ∧ v.view.payload = ctx.payload := by
  classical
  unfold choice at hchoice
  split at hchoice
  next => contradiction
  next hn =>
    have hprep : (prepare r.input).coordinator = r.output.preparation.coordinator := by
      rw [r.output_eq]; rfl
    rw [hprep] at hchoice hn
    cases hc : r.output.preparation.coordinator with
    | first outcome => cases outcome <;> simp [hc, choiceOfCut] at hchoice
    | invalidCollectionCutoff => simp [hc, choiceOfCut] at hchoice
    | dagger => simp [hc, choiceOfCut] at hchoice
    | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simp only [hc, choiceOfCut] at hchoice
      all_goals try contradiction
      next core snapshot hboundary hchecked =>
        rw [← Option.some.inj hchoice]
        exact ⟨_, rfl, rfl⟩
    | live registers owned base outcome =>
      cases outcome <;> simp only [hc, choiceOfCut] at hchoice
      all_goals try contradiction
      next dispatched hs ledger hi he hd hclock hp hn selected =>
        rw [← Option.some.inj hchoice]
        simp only [DispatchCut.selection, selectionAt, dite_true]
        exact ⟨_, rfl, rfl⟩

private theorem preparedFollowersUnoccupied_of_actual_selection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (selected : ReferenceActivePhysicalStep.Selection
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input)
    (hselection : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).output.preparation.coordinator.selection =
        some selected)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hpayload : selected.view.payload = payload)
    (hcut : FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input.row) ≤
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.time.val + 1) :
    ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let record := R[k.val]'k.isLt
  obtain ⟨states, memories, hstates, hdown, _hinputFields, _houtputFields⟩ :=
    ReferenceCompletePayloadChoiceChronology.complete_selected_payload_choice_fields
      (rate := rate) rewards C_star C_h source k selected hselection
  intro i
  change match (ReferenceFollowerFixedReply.actualChoice record i).configuration with
    | .ordinary state _ => state.status = .unoccupied
    | .dagger => False
  rw [hstates i]
  by_contra hbusy
  have hcurrent := hdown i hbusy
  rw [hpayload] at hcurrent
  obtain ⟨before, memory, choice, hbefore, _hdomain, hstart, hchoice,
      _hchoiceDomain, _hoperationDomain⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
      (rate := rate) rewards C_star C_h source k i
  have hchoiceEq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hchoice.symm.trans (hstates i))
  have hchoiceDown : choice.lastDown = some (payload.downRecord i) := by
    rw [hchoiceEq.1]
    exact hcurrent
  have hbeforeDown : before.lastDown = some (payload.downRecord i) :=
    (ActiveFollowerLifecycle.startRound_frame rate.eta record.input.time before
      choice memory memory hstart).1.symm.trans hchoiceDown
  have hphase := ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_phase
    rate rewards C_star C_h source k i before memory hbefore
      (payload.downRecord i) hbeforeDown
  have htoken : before.status ≠ .unoccupied → ∃ stamp : Fin p.T,
      stamp.val + 1 = record.input.time.val ∧
        memory.lastProposalRead = some ⟨stamp,
          FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row stamp⟩ := by
    intro hoccupied
    exact ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_token
      rate rewards C_star C_h source k i before memory hbefore hoccupied
  have hstatus := ReferenceAssignmentFollowerMassSteps.start_round_cutoff_status
    (rate := rate) record.input.time record.input.row before choice memory memory
      (payload.downRecord i) hbeforeDown hphase htoken hstart
  have hstartPayload : ActiveFollowerDownAcceptance.downStart p rate
      (payload.downRecord i) = payload.sigma := by
    apply Fin.ext
    have hval := ActiveFollowerDownAcceptance.downStart_val_add_one p rate
      (payload.downRecord i)
    rw [payload.downRecord_fields i] at hval
    exact Nat.add_right_cancel hval
  have hchoiceUnoccupied : choice.status = .unoccupied :=
    hstatus.mpr (by rw [hstartPayload]; exact hcut)
  exact hbusy (hchoiceEq.1 ▸ hchoiceUnoccupied)

/-- Actual collection CHOICE after its true cutoff supplies the canonical
cell before START, decoding, finishing, or clock success is tested. -/
private theorem actual_choice_readout
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (call : Choice rate)
    (hchoice : choice (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input = some call)
    (hlater : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h < call.payload.sigma.val)
    (hcut : FollowerCutoffScan.firstCutoff p rate.eta.val call.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input.row) ≤
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input.time.val + 1) :
    ∃ d, laterCollectionReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] = some d ∧
      laterCollectionReadout 0
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] = some d ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] = some d ∧
      laterCollectionCall 0
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] =
        some ⟨call.payload, call.preLedger, call.started, call.weights⟩ := by
  classical
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
  obtain ⟨selected, hselected, hpay⟩ := choice_selection record call hchoice
  have ho := preparedFollowersUnoccupied_of_actual_selection rate rewards C_star C_h z k
    selected hselected call.payload hpay hcut
  change preparedFollowersUnoccupied record at ho
  have hp : (prepare record.input).coordinator = record.output.preparation.coordinator := by
    rw [record.output_eq]; rfl
  have hch := hchoice
  unfold choice at hch
  split at hch
  · contradiction
  next hn =>
    rw [hp] at hch
    have hdom : (match record.output.preparation.coordinator with
      | .collection _ _ _ _ (.continuing ..) => True
      | .live r _ _ (.cutoffChosen ..) =>
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h < r.payload.sigma.val
      | _ => False) := by
      cases hc : record.output.preparation.coordinator with
      | first outcome => cases outcome <;> simp [hc, choiceOfCut] at hch
      | invalidCollectionCutoff => simp [hc, choiceOfCut] at hch
      | dagger => simp [hc, choiceOfCut] at hch
      | collection payload ledger clock cutoff outcome =>
          cases outcome <;> simp only [hc, choiceOfCut] at hch
          all_goals first | contradiction | trivial
      | live registers owned base outcome =>
          cases outcome <;> simp only [hc, choiceOfCut] at hch
          all_goals first | contradiction | (have heq := congrArg Choice.payload (Option.some.inj hch); change registers.payload = call.payload at heq; simpa only [← heq] using hlater)
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp
      ((laterCollectionReadout_domain _ record).mpr ⟨ho, hdom⟩)
    have hzero : laterCollectionReadout 0 record = some d := by
      cases hc : record.output.preparation.coordinator with
      | first outcome => simp only [hc] at hdom
      | invalidCollectionCutoff => simp only [hc] at hdom
      | dagger => simp only [hc] at hdom
      | collection payload ledger clock cutoff outcome =>
          cases outcome <;> simp only [hc] at hdom
          simpa only [laterCollectionReadout, dite_eq_left ho, hc] using hd
      | live registers owned base outcome =>
          cases outcome <;> simp only [hc] at hdom
          have hpos : 0 < registers.payload.sigma.val := by omega
          simpa only [laterCollectionReadout, dite_eq_left ho, hc, dite_eq_left hdom,
            dite_eq_left hpos] using hd
    have hlive : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = none := by
      cases hh : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record with
      | none => rfl
      | some c => exact False.elim (ReferenceCompleteNumericalBranchObservation.readouts_disjoint rate 0 record
          ⟨by rw [hh]; rfl, by rw [hzero]; rfl⟩)
    refine ⟨d, hd, hzero, ?_, ?_⟩
    · change ReferenceFirstCollectionCurrentRetainedGate.cell0 rate record = some d
      simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hlive, Option.none_or, hzero]
    · unfold laterCollectionCall
      rw [ite_eq_left ho]
      cases hc : record.output.preparation.coordinator with
      | first outcome => cases outcome <;> simp [hc, choiceOfCut] at hch
      | invalidCollectionCutoff => simp [hc, choiceOfCut] at hch
      | dagger => simp [hc, choiceOfCut] at hch
      | collection payload ledger clock cutoff outcome =>
          cases outcome <;> simp only [hc, choiceOfCut] at hch
          all_goals first | contradiction | (rw [← Option.some.inj hch])
      | live registers owned base outcome =>
          cases outcome <;> simp only [hc, choiceOfCut] at hch
          all_goals try contradiction
          simp only [hc] at hdom
          have hpos : 0 < registers.payload.sigma.val := by omega
          rw [← Option.some.inj hch]
          simp only [ite_eq_left hpos]

private theorem source_record_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (k : ℕ)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : (sourceRecords rate rewards C_star C_h z)[k]? = some record) :
    record.input.time.val = sourceStart rate rewards C_star C_h z + k := by
  obtain ⟨hk, hkr⟩ := List.getElem?_eq_some_iff.mp hr
  have ht := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values rate z rewards C_star C_h
  change (sourceRecords rate rewards C_star C_h z).map (fun r => r.input.time.val) =
    List.range' (sourceStart rate rewards C_star C_h z)
      (p.T - sourceStart rate rewards C_star C_h z) at ht
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  have hk' : k < p.T - sourceStart rate rewards C_star C_h z := by
    change (sourceRecords rate rewards C_star C_h z).length = p.T - sourceStart rate rewards C_star C_h z at hlen
    omega
  have hh := congrArg (fun xs => xs[k]?) ht
  rw [List.getElem?_map, hr, Option.map_some,
    List.getElem?_eq_getElem (by simpa only [List.length_range'] using hk')] at hh
  exact (Option.some.inj hh).trans (List.getElem_range'_1 k _)

private theorem retained_original_index
    (R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (e : ℕ) (seg : Segment rate) (hseg : segmentAt R e = some seg)
    (v : ℕ) (hv : v < seg.records.length) :
    R[e + v]? = some seg.records[v] := by
  have hp := congrArg (fun xs => xs[v]?) (segmentAt_partition R e seg hseg)
  rw [List.getElem?_append_left hv, List.getElem?_eq_getElem hv,
    List.getElem?_drop] at hp
  exact hp.symm

/-! The root telescope is used to select the actual optional retained segment;
no caller-supplied segment or run is introduced. -/

/-- Literal known-register sites at an actual later installation, with N's
common birth, continuation and optional collection witnesses. Retained INPUT,
CHOICE, decoded, OUTPUT and observed stage-(1) candidates use the same original
calendar. A first excluded CHOICE constructs its cell before later checks;
its observed candidate uses the appended calendar. Missing registers and
candidates remain absent, and the first cutoff's LIVE INPUT is not identified
with the initialized collection CHOICE ledger. -/
theorem actual_later_installation_retained_completed_round_source
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
              H.length = e ∧ G.length = e + seg.records.length ∧ G.take e = H ∧
              (∀ h, h ≤ e + seg.records.length →
                ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                  rate rewards C_star C_h (s + h) z = some (G.take h)) ∧
          (∀ j : Fin seg.records.length, ∃ done,
            R[e + j.val]? = some seg.records[j.val] ∧
            seg.records[j.val].input.time.val = s + (e + j.val) ∧
            extractRound seg.records[j.val] = some done ∧
            choice seg.records[j.val].input = some done.context ∧
            done.context.preLedger = endpointLedger seg.context.preLedger (seg.records.take j.val) ∧
            done.final = endpointLedger seg.context.preLedger (seg.records.take (j.val + 1)) ∧
            (∀ payload ledger proposal,
              seg.records[j.val].input.state.coordinator = .collection payload ledger proposal →
              ledger = done.context.preLedger ∧
              (∀ a current, ledger.currentRegisters a = some current →
                current.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
                  rate G a (e + j.val)).2) ∧
              (∀ a cutoff, ledger.cutoffRegisters a = some cutoff →
                cutoff.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
                  rate G a e).2) ∧
              (∀ a field q, knownSiteQueue? ledger a field = some q →
                ReferenceFirstCorrectedCollectionKnownQueueOverflowCover.KnownQueueSourceSite rate seg a field q)) ∧
            (∀ a current, done.context.preLedger.currentRegisters a = some current →
              current.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
                rate G a (e + j.val)).2) ∧
            (∀ a cutoff, done.context.preLedger.cutoffRegisters a = some cutoff →
              cutoff.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
                rate G a e).2) ∧
            (∀ a current, done.final.currentRegisters a = some current →
              current.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
                rate G a (e + j.val + 1)).2) ∧
            (∀ a cutoff, done.final.cutoffRegisters a = some cutoff →
              cutoff.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
                rate G a e).2) ∧
            ∃ out started decoded bank,
              seg.records[j.val].output.coordinator.recording = some out ∧
              CoordinatorRecorderComplementBridge.run
                (collectionRecordingInput (prepare seg.records[j.val].input)
                  done.context.payload done.context.started done.context.weights) = some out ∧
              CoordinatorCollectionLedger.startRound done.context.preLedger
                (seg.records[j.val].input.time.val + 1)
                (collectionEnabled done.context.preLedger seg.records[j.val].input.time)
                (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) =
                  .success started ∧
              (receiveUp (prepare seg.records[j.val].input) started).result =
                (if done.accepted then .success (decoded, bank) else .rejected (decoded, bank)) ∧
              CoordinatorCollectionLedger.finishRound decoded = .success done.final ∧
              (∀ a current, decoded.currentRegisters a = some current →
                current.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
                  rate G a (e + j.val + 1)).2) ∧
              (∀ a cutoff, decoded.cutoffRegisters a = some cutoff →
                cutoff.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
                  rate G a e).2) ∧
              (∀ a field q, knownSiteQueue? decoded a field = some q →
                ReferenceFirstCorrectedCollectionKnownQueueOverflowCover.KnownQueueSourceSite rate seg a field q) ∧
              done.context.payload = seg.context.payload ∧
              (∀ a field q, knownSiteQueue? done.context.preLedger a field = some q →
                ReferenceFirstCorrectedCollectionKnownQueueOverflowCover.KnownQueueSourceSite rate seg a field q) ∧
              (∃ proposal,
                seg.records[j.val].output.next.coordinator =
                  .collection seg.context.payload done.final proposal ∧
                ∀ a field q, knownSiteQueue? done.final a field = some q →
                  ReferenceFirstCorrectedCollectionKnownQueueOverflowCover.KnownQueueSourceSite rate seg a field q) ∧
              (∀ out' candidate,
                seg.records[j.val].coordinatorDiagnostics.recording = some out' →
                reachedStageOneCandidate? done.context.preLedger seg.records[j.val].input.time
                  (collectionEnabled done.context.preLedger seg.records[j.val].input.time)
                  out' = some candidate →
                CoordinatorRecorderComplementBridge.run
                  (collectionRecordingInput (prepare seg.records[j.val].input)
                    done.context.payload done.context.started done.context.weights) = some out' ∧
                (∀ a current, candidate.currentRegisters a = some current →
                  current.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
                    rate G a (e + j.val + 1)).2) ∧
                (∀ a cutoff, candidate.cutoffRegisters a = some cutoff →
                  cutoff.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
                    rate G a e).2) ∧
                (∀ a field q, knownSiteQueue? candidate a field = some q →
                  ReferenceFirstCorrectedCollectionKnownQueueOverflowCover.KnownQueueSourceSite rate seg a field q))) ∧
          let v := e + seg.records.length
          v ≤ R.length ∧
          (∀ r, seg.remaining.head? = some r →
            ∃ proposal, R[v]? = some r ∧ r.input.time.val = s + v ∧
              r.input.state.coordinator = .collection seg.context.payload seg.final proposal ∧
              (∀ a current, seg.final.currentRegisters a = some current →
                current.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
                  rate G a v).2) ∧
              (∀ a cutoff, seg.final.cutoffRegisters a = some cutoff →
                cutoff.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
                  rate G a e).2) ∧
              (∀ a current, seg.final.currentRegisters a = some current →
                ReferenceFirstCorrectedCollectionKnownQueueOverflowCover.KnownQueueSourceSite
                  rate seg a .current current.queue) ∧
              (∀ a cutoff, seg.final.cutoffRegisters a = some cutoff →
                ReferenceFirstCorrectedCollectionKnownQueueOverflowCover.KnownQueueSourceSite
                  rate seg a .cutoff cutoff.queue) ∧
              (∀ call, choice r.input = some call →
                call.payload = seg.context.payload ∧ call.preLedger = seg.final ∧
                call.initializer = none ∧
                (∀ a current, call.preLedger.currentRegisters a = some current →
                  current.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
                    rate G a v).2) ∧
                (∀ a cutoff, call.preLedger.cutoffRegisters a = some cutoff →
                  cutoff.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
                    rate G a e).2) ∧
                (∀ a current, call.preLedger.currentRegisters a = some current →
                  ReferenceFirstCorrectedCollectionKnownQueueOverflowCover.KnownQueueSourceSite
                    rate seg a .current current.queue) ∧
                (∀ a cutoff, call.preLedger.cutoffRegisters a = some cutoff →
                  ReferenceFirstCorrectedCollectionKnownQueueOverflowCover.KnownQueueSourceSite
                    rate seg a .cutoff cutoff.queue) ∧
                ∃ d, laterCollectionReadout s r = some d ∧
                  laterCollectionReadout 0 r = some d ∧
                  ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some d ∧
                  laterCollectionCall 0 r =
                    some ⟨call.payload, call.preLedger, call.started, call.weights⟩ ∧
                  ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                    rate rewards C_star C_h (s + v + 1) z = some (G ++ [d]) ∧
                  ∀ out candidate, r.coordinatorDiagnostics.recording = some out →
                    reachedStageOneCandidate? call.preLedger r.input.time
                      (collectionEnabled call.preLedger r.input.time) out = some candidate →
                    (∀ a current, candidate.currentRegisters a = some current →
                      current.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
                        rate (G ++ [d]) a (v + 1)).2) ∧
                    (∀ a cutoff, candidate.cutoffRegisters a = some cutoff →
                      cutoff.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
                        rate G a e).2))) )) := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hroot := ReferenceCompleteInstallationCollectionPrefixNumericalTruth.actual_later_installation_collection_prefix_numerical_truth
    rate rewards C_star C_h z b hb
  rcases hroot with ⟨P0, rb, qb, beta, cell, native, hPlen, hPslots, hPprefix,
    hinit, hpost, hbirth, hstrict, hbase, hcell, hnative, hnativePayload,
    henabled, hbirthPrefix, hbirthSlots, hdown, hbranch⟩
  rcases hbranch with hterminal | ⟨k, C, hk, hstate, hClen, hWmap, hWtime,
    e, he, heR, rE, qE, hrPayload, hsegment⟩
  · exact ⟨P0, rb, qb, beta, cell, native, hPlen, hPslots, hPprefix,
      hinit, hpost, hbirth, hstrict, hbase, hcell, hnative, hnativePayload,
      henabled, hbirthPrefix, hbirthSlots, hdown, Or.inl hterminal⟩
  · rcases hsegment with hsegmentTerminal | ⟨heLt, seg, I, l0, Dword,
      hseg, hentry, hpay, hledger, hinitializer, hIeq, hstart, harm, hsigma,
      hcutoff, hscan, hfreeze, hbaseI, hchosen, hne, hpart, hrun, hDlen,
      hDmap, hqueues, hHlen, hGlen, hGtake, hvR, hprefixEvery, hRtake,
      hprefixAll, hlabels, hfinalPending, hfinalNodup, hchecked, hbirthTime,
      hinfo⟩
    · exact ⟨P0, rb, qb, beta, cell, native, hPlen, hPslots, hPprefix,
        hinit, hpost, hbirth, hstrict, hbase, hcell, hnative, hnativePayload,
        henabled, hbirthPrefix, hbirthSlots, hdown, Or.inr
          ⟨k, C, hk, hstate, hClen, hWmap, hWtime, e, he, heR, rE, qE,
            hrPayload, Or.inl hsegmentTerminal⟩⟩
    · let G := (P0 ++ [cell] ++ C) ++ Dword
      rcases hinfo with ⟨hinfoCount, hinfoFinalKnown, hinfoFinalPending⟩
      have hGlen' : G.length = e + seg.records.length := by
        dsimp only [G]
        exact hGlen
      have hboundary := ReferenceCompleteCollectionBoundaryHistory.internal_complete_collection_boundary_history
        rate rewards C_star C_h z e seg hseg
        (by rcases hne with ⟨tail, htail⟩; rw [htail]; simp) hchosen
      have hfields := hboundary.2.1
      have hpayloads := hboundary.2.2.1
      refine ⟨P0, rb, qb, beta, cell, native, hPlen, hPslots, hPprefix,
        hinit, hpost, hbirth, hstrict, hbase, hcell, hnative, hnativePayload,
        henabled, hbirthPrefix, hbirthSlots, hdown, Or.inr
          ⟨k, C, hk, hstate, hClen, hWmap, hWtime, e, he, heR, rE, qE,
            hrPayload, Or.inr ⟨heLt, seg, I, l0, Dword, hseg, hentry, hpay,
              hledger, hinitializer, hIeq, hstart, harm, hsigma, hcutoff, hscan,
              hfreeze, hbaseI, hchosen, hne, hpart, hrun, hDlen, hDmap, hqueues,
              hHlen, hGlen', hGtake, ?_, ?_, ?_⟩⟩⟩
      · intro h hh
        exact hprefixEvery h hh
      · intro j
        have hj : j.val < seg.records.length := j.isLt
        have hgood := segment_all_completed _ seg (segmentAt_branch R e seg hseg).1
        obtain ⟨done, hdone⟩ : ∃ done, extractRound seg.records[j.val] = some done := by
          cases hh : extractRound seg.records[j.val] with
          | none => have hg := hgood _ (List.getElem_mem hj); simp only [hh] at hg; contradiction
          | some done => exact ⟨done, rfl⟩
        obtain ⟨initial, span, active, _hfirst, hrunActual⟩ :=
          actual_segment_run rate rewards C_star C_h z e seg hseg
        have hsegRun : segmentAt
            (ReferenceActivePhysicalHorizon.run initial z.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s
              (p.T - s) span active).records e = some seg := by
          rw [← hrunActual]
          exact hseg
        have hbefore := ReferenceCollectionPrefixLedgerHistory.retained_completed_preledger
          initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
          rewards s (p.T - s) span active e seg hsegRun j.val hj done hdone
        have hbeforeL0 : done.context.preLedger =
            endpointLedger l0 (seg.records.take j.val) := by
          rw [hbefore, hledger]
        have hafter := (ReferenceFirstCorrectedCollectionKnownQueueSource.retained_final_endpoint
          seg.context.preLedger seg.records j.val hj done hdone).symm
        have hafterL0 : done.final =
            endpointLedger l0 (seg.records.take (j.val + 1)) := by
          rw [hafter, hledger]
        have hactual := actual_collection_round_checked seg.records[j.val] done hdone
        have hdataPre := hinfoCount j.val (Nat.le_of_lt hj)
        rcases hdataPre with ⟨hvalidPre, hknownPre, _, _, _, _, _, _, _, _, _⟩
        have hpreCurrent : ∀ a current,
            done.context.preLedger.currentRegisters a = some current →
            current.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
              rate G a (e + j.val)).2 := by
          intro a current hcurrent
          have hreg : (endpointLedger l0 (seg.records.take j.val)).currentRegisters a = some current := by
            rw [← hbeforeL0]
            exact hcurrent
          have hnot := not_pending_of_current_present _ a current hvalidPre hreg
          have hqueues := hknownPre a hnot
          have hsame := Option.some.inj (hreg.symm.trans hqueues.2.1)
          exact congrArg CoordinatorCollectionLedger.CurrentRegister.queue hsame
        have hpreCutoff : ∀ a cutoff,
            done.context.preLedger.cutoffRegisters a = some cutoff →
            cutoff.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
              rate G a e).2 := by
          intro a cutoff hcutReg
          have hreg : (endpointLedger l0 (seg.records.take j.val)).cutoffRegisters a = some cutoff := by
            rw [← hbeforeL0]
            exact hcutReg
          have hnot := not_pending_of_cutoff_present _ a cutoff hvalidPre hreg
          have hqueues := hknownPre a hnot
          have hsame := Option.some.inj (hreg.symm.trans hqueues.1)
          exact congrArg CoordinatorCollectionLedger.CutoffRegister.queue hsame
        have hdataPost := hinfoCount (j.val + 1) (by omega)
        rcases hdataPost with ⟨hvalidPost, hknownPost, _, _, _, _, _, _, _, _, _⟩
        have hpostCurrent : ∀ a current,
            done.final.currentRegisters a = some current →
            current.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
              rate G a (e + j.val + 1)).2 := by
          intro a current hcurrent
          have hreg : (endpointLedger l0 (seg.records.take (j.val + 1))).currentRegisters a = some current := by
            rw [← hafterL0]
            exact hcurrent
          have hnot := not_pending_of_current_present _ a current hvalidPost hreg
          have hqueues := hknownPost a hnot
          have hsame := Option.some.inj (hreg.symm.trans hqueues.2.1)
          simpa only [Nat.add_assoc] using congrArg CoordinatorCollectionLedger.CurrentRegister.queue hsame
        have hpostCutoff : ∀ a cutoff,
            done.final.cutoffRegisters a = some cutoff →
            cutoff.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
              rate G a e).2 := by
          intro a cutoff hcutReg
          have hreg : (endpointLedger l0 (seg.records.take (j.val + 1))).cutoffRegisters a = some cutoff := by
            rw [← hafterL0]
            exact hcutReg
          have hnot := not_pending_of_cutoff_present _ a cutoff hvalidPost hreg
          have hqueues := hknownPost a hnot
          have hsame := Option.some.inj (hreg.symm.trans hqueues.1)
          exact congrArg CoordinatorCollectionLedger.CutoffRegister.queue hsame
        have hindex := retained_original_index R e seg hseg j.val hj
        have htime := source_record_time rate rewards C_star C_h z
          (e + j.val) seg.records[j.val] hindex
        refine ⟨done, hindex, htime, hdone, hactual.1, hbefore, hafter, ?_, hpreCurrent,
          hpreCutoff, hpostCurrent, hpostCutoff, ?_⟩
        · intro payload ledger proposal hinput
          have hledger := ReferenceFirstCorrectedCollectionKnownQueueSource.collection_input_ledger
            seg.records[j.val] done.context hactual.1 payload ledger proposal hinput
          refine ⟨hledger, ?_, ?_, ?_⟩
          · intro a current hcur
            rw [hledger] at hcur
            exact hpreCurrent a current hcur
          · intro a cutoff hcutReg
            rw [hledger] at hcutReg
            exact hpreCutoff a cutoff hcutReg
          · intro a field q hq
            have hpayDone := hpayloads _ (List.getElem_mem hj) done.context hactual.1
            have hpayInput := actual_collection_choice_payload seg.records[j.val]
              payload ledger proposal done.context hinput hactual.1
            have hinput' : seg.records[j.val].input.state.coordinator =
                .collection seg.context.payload ledger proposal := by
              rw [hinput, ← hpayDone, hpayInput]
            exact .retainedInput j.val hj ledger proposal hinput' hq
        · obtain ⟨out, started, decoded, bank, hout, hrunOut, hstartOut,
            hreceive, hfinish, hdecodeCurrent, hdecodeCutoff⟩ :=
            ReferenceFirstCorrectedCollectionKnownQueueSource.completed_decode_registers
              seg.records[j.val] done hdone
          refine ⟨out, started, decoded, bank, hout, hrunOut, hstartOut,
            hreceive, hfinish, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro a current hcurrent
            have hfinal : done.final.currentRegisters a = some current := by
              rw [← hdecodeCurrent]
              exact hcurrent
            exact hpostCurrent a current hfinal
          · intro a cutoff hcutReg
            have hfinal : done.final.cutoffRegisters a = some cutoff := by
              rw [← hdecodeCutoff]
              exact hcutReg
            exact hpostCutoff a cutoff hfinal
          · intro a field q hq
            exact .retainedDecoded j.val hj done hdone hactual.1
              (hpayloads _ (List.getElem_mem hj) done.context hactual.1)
              out hout hrunOut started decoded bank hstartOut hreceive hfinish hq
          · exact hpayloads _ (List.getElem_mem hj) done.context hactual.1
          · intro a field q hq
            exact .retainedChoice j.val hj done.context hactual.1
              (hpayloads _ (List.getElem_mem hj) done.context hactual.1) hq
          · obtain ⟨proposal, houtput⟩ := completed_payload seg.records[j.val] done hdone
            have hpayDone := hpayloads _ (List.getElem_mem hj) done.context hactual.1
            rw [hpayDone] at houtput
            refine ⟨proposal, houtput, ?_⟩
            intro a field q hq
            exact .retainedOutput j.val hj done hdone hpayDone proposal houtput hq
          · intro out' candidate hdiagnostic hreached
            obtain ⟨hkR, hrecord⟩ := List.getElem?_eq_some_iff.mp hindex
            have hrR : seg.records[j.val] ∈ R := by
              rw [← hrecord]; exact List.getElem_mem hkR
            have hrow : seg.records[j.val].input.row =
                z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
              change seg.records[j.val].input.rows seg.records[j.val].input.selected = _
              rw [(hfields _ hrR).1, (hfields _ hrR).2.1]
            have hpayDone := hpayloads _ (List.getElem_mem hj) done.context hactual.1
            change seg.records[j.val].input.time.val = s + (e + j.val) at htime
            have hcutNow : FollowerCutoffScan.firstCutoff p rate.eta.val done.context.payload.sigma
                (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                  seg.records[j.val].input.row) ≤ seg.records[j.val].input.time.val + 1 := by
              rw [hpayDone, hpay, hrow, ← hscan, hcutoff, htime]
              omega
            obtain ⟨d, hread, hzero, hcellD, hcallD⟩ := actual_choice_readout rate rewards
              C_star C_h z ⟨e + j.val, hkR⟩ done.context
              (by rw [hrecord]; exact hactual.1)
              (by rw [hpayDone, hpay]; exact hstrict)
              (by rw [hrecord]; exact hcutNow)
            rw [hrecord] at hread hzero hcellD hcallD
            obtain ⟨_, _, _, _, outD, hcallD', _, hrunD, _, _, _, _, hdiagD, _, _⟩ :=
              laterCollectionReadout_call 0 seg.records[j.val] d hzero
            have hargs := Option.some.inj (hcallD'.symm.trans hcallD)
            cases hargs
            have houtEq : outD = out' := Option.some.inj (hdiagD.symm.trans hdiagnostic)
            subst outD
            have hprep : seg.records[j.val].output.preparation =
                prepare seg.records[j.val].input := by
              rw [seg.records[j.val].output_eq]; rfl
            rw [hprep] at hrunD
            have happend := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_append_one
              rate rewards C_star C_h (s + (e + j.val)) z (G.take (e + j.val))
              (hprefixEvery _ (by omega)) seg.records[j.val] d
              (by simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
                ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart,
                s, R, Nat.add_sub_cancel_left] using hindex) hcellD
            have hnext := hprefixEvery (e + j.val + 1) (by omega)
            have hword : G.take (e + j.val) ++ [d] = G.take (e + j.val + 1) := by
              have hdate : s + (e + j.val) + 1 = s + (e + j.val + 1) := by omega
              rw [hdate, hnext] at happend
              exact (Option.some.inj happend).symm
            have hcand := actual_candidate_calendar rate seg.records[j.val] done.context d
              hzero hcallD (G.take (e + j.val))
              (by intro a current hcurrent; rw [calendar_take]; exact hpreCurrent a current hcurrent)
              out' hdiagnostic candidate hreached
            refine ⟨hrunD, ?_, ?_, ?_⟩
            · intro a current hcurrent
              have hq := hcand.1 a current hcurrent
              rw [hword, calendar_take] at hq
              exact hq
            · intro a cutoff hcutReg
              rw [hcand.2] at hcutReg
              exact hpreCutoff a cutoff hcutReg
            · intro a field q hq
              exact .reachedStageOneCandidate j.val hj done.context hactual.1
                hpayDone out' hdiagnostic hrunD candidate hreached hq
      · let v := e + seg.records.length
        obtain ⟨hvR, _, _, saved, _hboundaryCoord, _hcursor, during,
          _hrecords, _htake, _hlaterEntry, _hduring, _hpending, _hnodup,
          _haccepted, hendpoint⟩ := hboundary
        have hfinalData := hinfoCount seg.records.length (Nat.le_refl _)
        rcases hfinalData with ⟨hvalidFinal, _, _, _, _, _, _, hlnFinal, _, _, _⟩
        have hln : endpointLedger l0 (seg.records.take seg.records.length) = seg.final := by
          simpa only [List.take_length] using hlnFinal (Eq.refl seg.records.length)
        have hvalidSeg : CoordinatorCollectionLedger.validLedgerCheck seg.final = true := by
          rw [← hln]
          exact hvalidFinal
        have hfinalCurrent : ∀ a current, seg.final.currentRegisters a = some current →
            current.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
              rate G a v).2 := by
          intro a current hcurrent
          have hnot := not_pending_of_current_present seg.final a current hvalidSeg hcurrent
          have hqueues := hinfoFinalKnown a hnot
          have hsame := Option.some.inj (hcurrent.symm.trans hqueues.2.1)
          simpa only [Nat.add_assoc] using
            congrArg CoordinatorCollectionLedger.CurrentRegister.queue hsame
        have hfinalCutoff : ∀ a cutoff, seg.final.cutoffRegisters a = some cutoff →
            cutoff.queue = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
              rate G a e).2 := by
          intro a cutoff hcutReg
          have hnot := not_pending_of_cutoff_present seg.final a cutoff hvalidSeg hcutReg
          have hqueues := hinfoFinalKnown a hnot
          have hsame := Option.some.inj (hcutReg.symm.trans hqueues.1)
          exact congrArg CoordinatorCollectionLedger.CutoffRegister.queue hsame
        refine ⟨hvR, ?_⟩
        intro r hhead
        have hindex := ReferenceFirstCorrectedCollectionKnownQueueSource.first_excluded_original_index
          R e seg hseg r hhead
        rcases hendpoint with hvEnd | ⟨hv, hstate, hcoord, htime, hdrop, _hlater⟩
        · have hlen := congrArg List.length hpart
          simp only [List.length_append, List.length_drop] at hlen
          have hnil : seg.remaining = [] := by
            apply List.eq_nil_iff_length_eq_zero.mpr
            omega
          rw [hnil] at hhead
          simp at hhead
        · obtain ⟨hvFin, hrec⟩ := List.getElem?_eq_some_iff.mp hindex
          have hcoordRecord : r.input.state.coordinator =
              .collection seg.context.payload seg.final saved := by
            rw [← hrec]
            exact hcoord
          refine ⟨saved, hindex, ?_, hcoordRecord, hfinalCurrent,
            hfinalCutoff, ?_, ?_, ?_⟩
          · rw [← hrec]
            exact htime
          · intro a current hcurrent
            refine .firstExcludedInput r hhead saved hcoordRecord ?_
            rw [knownSiteQueue?_current]
            simp [hcurrent]
          · intro a cutoff hcutReg
            refine .firstExcludedInput r hhead saved hcoordRecord ?_
            rw [knownSiteQueue?_cutoff]
            simp [hcutReg]
          · intro call hchoice
            have hcall := ReferenceCollectionSegmentExtraction.choice_collection_pre
              r.input seg.context.payload seg.final saved call hcoordRecord hchoice
            have hcallPayload := actual_collection_choice_payload r seg.context.payload
              seg.final saved call hcoordRecord hchoice
            refine ⟨hcallPayload, hcall.1, hcall.2, ?_, ?_, ?_, ?_, ?_⟩
            · intro a current hcurrent
              have hreg : seg.final.currentRegisters a = some current := by
                simpa only [hcall.1] using hcurrent
              exact hfinalCurrent a current hreg
            · intro a cutoff hcutReg
              have hreg : seg.final.cutoffRegisters a = some cutoff := by
                simpa only [hcall.1] using hcutReg
              exact hfinalCutoff a cutoff hreg
            · intro a current hcurrent
              refine .firstExcludedChoice r hhead call hchoice
                ⟨hcallPayload, hcall.1, hcall.2⟩ ?_
              rw [knownSiteQueue?_current]
              simp [hcurrent]
            · intro a cutoff hcutReg
              refine .firstExcludedChoice r hhead call hchoice
                ⟨hcallPayload, hcall.1, hcall.2⟩ ?_
              rw [knownSiteQueue?_cutoff]
              simp [hcutReg]
            · have hspan := ReferenceCompleteCollectionIncrementSpan.complete_collection_input_increment_span
                rate rewards C_star C_h z ⟨v, hvFin⟩ seg.context.payload seg.final saved
                (by rw [hrec]; exact hcoordRecord)
              obtain ⟨_b, _hbk, _hbirth, _hbase, _hassign, _hstart,
                htruecut, _hfreeze, _hpos, _horder, _hT, hcutCursor, hcursor, _hspan⟩ := hspan
              have hrR : r ∈ R := by rw [← hrec]; exact List.getElem_mem hvFin
              have hrow : r.input.row = z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
                change r.input.rows r.input.selected = _
                rw [(hfields r hrR).1, (hfields r hrR).2.1]
              have hcutNow : FollowerCutoffScan.firstCutoff p rate.eta.val call.payload.sigma
                  (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row) ≤
                  r.input.time.val + 1 := by
                rw [hcallPayload, hrow, ← htruecut]
                rw [hrec] at hcursor
                omega
              obtain ⟨d, hread, hzero, hcellD, hcallD⟩ := actual_choice_readout rate rewards
                C_star C_h z ⟨v, hvFin⟩ call
                (by rw [hrec]; exact hchoice)
                (by rw [hcallPayload, hpay]; exact hstrict)
                (by rw [hrec]; exact hcutNow)
              rw [hrec] at hread hzero hcellD hcallD
              have hfull : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                  rate rewards C_star C_h (s + v) z = some G := by
                have hh := hprefixEvery v (Nat.le_refl _)
                have htake : G.take v = G := by
                  rw [← show G.length = v from hGlen', List.take_length]
                change ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                  rate rewards C_star C_h (s + v) z = some (G.take v) at hh
                simpa only [htake] using hh
              have happend := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_append_one
                rate rewards C_star C_h (s + v) z G hfull r d
                (by simpa only [sourceRecords, sourceStart, s, R, Nat.add_sub_cancel_left] using hindex)
                hcellD
              refine ⟨d, hread, hzero, hcellD, hcallD, happend, ?_⟩
              intro out candidate hdiagnostic hreached
              have hcand := actual_candidate_calendar rate r call d hzero hcallD G
                (by intro a current hcurrent; rw [hGlen']; apply hfinalCurrent a current;
                    rw [← hcall.1]; exact hcurrent)
                out hdiagnostic candidate hreached
              refine ⟨?_, ?_⟩
              · intro a current hcurrent
                have hq := hcand.1 a current hcurrent
                simpa only [List.length_append, List.length_singleton, hGlen'] using hq
              · intro a cutoff hcutReg
                rw [hcand.2, hcall.1] at hcutReg
                exact hfinalCutoff a cutoff hcutReg

end Bandits.Support.ReferenceCompleteInstallationCollectionKnownQueueSource

end
