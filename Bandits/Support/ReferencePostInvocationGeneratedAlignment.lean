/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostInvocationNoncallGeometry

import Mathlib.Tactic

/-!
# Generated post-invocation alignment on the original physical source

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`08_main_theorem.tex:78-109`.

The existing installation/calendar recursion aligns both native LIVE seeds
and physical complements. Its collection queries belong to the installed
cutoff segment with the all-arm old-anchor envelope on enabled, PRE-clear
dates. Disabled dates advance the complete word with frozen registers.
No probability law or manuscript closure is asserted.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstNextInstallationTransitionLaw
open ReferenceFirstNextInstallationCellFactors
open ReferenceFirstCollectionLogicalNumericalAlignment
open ReferencePostInvocationNoncallGeometry
open ReferenceActualCollectionHiddenRefreshPath (actualOriginalWord)
open ReferenceFirstLaunchNumericalCell (queueParameters)
open ReferenceCompletePhysicalHistory (physicalStart completeSuffixRecords)
open ReferenceFirstCollectionLogicalPrefixExtension (extendedPast noCallAt)

open RecordedQueueRun (RoundInput RunState run scoreWeight)
open ReferenceActivePhysicalStep (Payload Ledger)
open ReferenceCollectionSegmentExtraction
  (Segment Initializer segmentAt segmentAt_branch continuing choice choiceOfCut choice_collection_pre extractRound)
open ReferenceCompleteLaterLiveComplementPrefixReplay (continuingTest continuingPrefix)
open CanonicalFastSampling (FastArm)
open ReferenceAssignmentPayloadPersistence (InstallationBirth storedPayload storedPayload_live)
open ReferenceFirstCorrectedNextCalendarWordJoin (calendarReplay rawCalendar)
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix (prefixInputs)
open ContinuousLearningRows (TimeControl)
open ReferenceLaterCollectionArrivalReadout
  (laterCollectionReadout laterCollectionReadout_domain laterCollectionReadout_call laterCollectionCall)
open CoordinatorLiveChoiceRecorderStep (Registers unchangedLiveClockFrame cutoffFromClock)
open ReferenceCoordinatorClockDomains (clockAt)
open ReferenceSourcePrefixHistoryFiltration (actualRecord)
open FollowerCutoffScan (gridBoundary completeRowProposalBit)
open ReferenceFirstCollectionCurrentRetainedGate (cell0)
open ReferenceCorrectedInitializationLaunch (correctedLaunch correctedLaunch_isSome_iff_crossing)
open ReferenceCompletePhysicalHistory (completeSuffixRecords_length completeSuffixRecords_time_values physicalStart_le_T)
open ReferenceActualCollectionHiddenRefreshPath (actualOriginalWord_length actualOriginalWord_spec actualOriginalWord_prefix actualOriginalWord_numericalPrefix)

namespace Bandits.Support.ReferencePostInvocationGeneratedAlignment

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

local notation "PhysicalControl" => ContinuousLearningRows.TimeControl p
local notation "PhysicalRecord" => ReferenceFirstLiveChronologicalPrefixFoundation.Record rate
local notation "Q" => queueParameters rate
local notation "start " z:max => physicalStart rate z rewards C_star C_h
local notation "records " z:max => completeSuffixRecords rate z rewards C_star C_h

local notation "FirstSource" => FirstInvocationSource rate rewards C_star C_h
local notation "LiveSource" => ContinuingLiveSource rate rewards C_star C_h
local notation "CollectionSource" => CollectionDateSource rate rewards C_star C_h
local notation "firstCell" => firstSourceCell rate rewards C_star C_h
local notation "birthRecord" => firstRecord rate rewards C_star C_h
local notation "liveCell" => continuingSourceCell rate rewards C_star C_h
local notation "liveRecord" => continuingRecord rate rewards C_star C_h
local notation "collectionRecordAt" => collectionRecord rate rewards C_star C_h
local notation "collectionArgs" => collectionArguments rate rewards C_star C_h
local notation "collectionPRE" => collectionBefore rate rewards C_star C_h
local notation "collectionWord" => collectionNumericalWord rate rewards C_star C_h
local notation "livePRE" => continuingBefore rate rewards C_star C_h
local notation "originalWord" => actualOriginalWord rate rewards C_star C_h
local notation "sourceRecord" => actualRecord rate rewards C_star C_h
local notation "CallFree" => NoCallBetween rate rewards C_star C_h
local notation "postPrefix" => postInvocationPrefix rate rewards C_star C_h
local notation "noncallRun" => noncallCalendar rate rewards C_star C_h
local notation "liveDomain" => ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h
local notation "collectionDomain" => collectionDateDomain rate rewards C_star C_h
local notation "numericalPrefix" => prefixInputs rate rewards C_star C_h

/-- The invocation installs its native selected payload and actual POST registers. -/
theorem firstInvocation_installation (t : Fin p.T) (z : FirstSource t) :
    ∃ (b : Fin (records z.val).length) (rb : Registers p rate.eta)
      (qb : CoordinatorLiveServiceFinish.OwnedRegisters rb) (beta : Fin (p.m - 1) → ℕ),
      sourceRecord t z.val = some (records z.val)[b.val] ∧
      (records z.val)[b.val] = birthRecord t z ∧
      ReferenceCollectionPhaseHistory.laterChosen (records z.val)[b.val].input = true ∧
      (records z.val)[b.val].output.next.coordinator = .live rb qb beta ∧
      InstallationBirth (records z.val)[b.val] rb.payload ∧
      rb.payload = (firstCell t z).selected.view.payload := by
  obtain ⟨b, hr, _ht, hb⟩ := ReferenceRankInstallationRecorderFoundation.installationEvent_chosen
      rate rewards C_star C_h 0 t z.val z.property
  have heq : (records z.val)[b.val] = birthRecord t z :=
    Option.some.inj (hr.symm.trans (firstSourceCell_spec rate rewards C_star C_h t z).1)
  obtain ⟨_P0, rb, qb, beta, _cell, native, _hlen, _hmap, _hprefix, _hinit,
      hnext, hbirth, _hsigma, _hbase, _hcell, _hinput, hpayload, _⟩ :=
    ReferenceCompleteInstallationCollectionPrefixNumericalTruth.actual_later_installation_collection_prefix_numerical_truth
        rate rewards C_star C_h z.val b hb
  have hselected :
      ((records z.val)[b.val].output.preparation.coordinator.selection).map
        (fun s => s.view.payload) = some rb.payload := by
    rw [native.selection_actual, Option.map_some, hpayload]
  rw [heq, (firstCell t z).selection_actual, Option.map_some] at hselected
  exact ⟨b, rb, qb, beta, hr, heq, hb, hnext, hbirth, (Option.some.inj hselected).symm⟩

/-- A surviving successor performs the original append after checking no call. -/
theorem noncallCalendar_some_succ (t q : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (initial s : SlowSet p × List (LogicalCell p rate)) (htq : t.val < q.val)
    (hs : noncallRun t z a initial (q.val + 1) = some s) :
    ∃ prev, noncallRun t z a initial q.val = some prev ∧ noCallAt rate rewards C_star C_h q z ∧
      s = appendNoncallDate rate rewards C_star C_h q z a prev := by
  rw [noncallCalendar] at hs
  cases hp : noncallRun t z a initial q.val with
  | none => rw [hp, Option.bind_none] at hs; cases hs
  | some prev =>
      rw [hp, Option.bind_some, dite_eq_left ⟨htq, q.isLt⟩] at hs
      split_ifs at hs with hc
      · exact ⟨prev, rfl, hc, (Option.some.inj hs).symm⟩

/-- A surviving result supplies its actual killed interval. -/
theorem postInvocationPrefix_some_noCall (t : Fin p.T) (n : Fin (p.T + 1)) (d : TransitionData rate t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) (s : SlowSet p × List (LogicalCell p rate))
    (hs : postPrefix t n d a = some s) :
    CallFree t n (insertedPhysicalSource rate d) := by
  apply (noncallCalendar_isSome rate rewards C_star C_h t n
    (insertedPhysicalSource rate d) a (postSeed rate d, postHistory d)).mp
  rw [← postInvocationPrefix, hs]
  rfl

/-- The source record fixes its original zero-origin suffix index. -/
theorem actualRecord_index (q : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) (r : PhysicalRecord)
    (hr : sourceRecord q z = some r) :
    ∃ k : Fin (records z).length, k.val = q.val - start z ∧ (records z)[k.val] = r ∧ start z ≤ q.val := by
  unfold actualRecord at hr
  split at hr
  next hstart =>
    obtain ⟨hk, heq⟩ := List.getElem?_eq_some_iff.mp hr
    exact ⟨⟨q.val - start z, hk⟩, rfl, heq, hstart⟩
  · cases hr

/-- The actual run supplies its clock and saved proposal stamp. -/
theorem actualRecord_clock (q : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) (r : PhysicalRecord)
    (hr : sourceRecord q z = some r) :
    clockAt r.input.rows r.input.selected r.input.time.val r.input.state ∧
    clockAt r.input.rows r.input.selected (r.input.time.val + 1) r.output.next := by
  obtain ⟨k, _hk, hrecord, _hs⟩ := actualRecord_index rate rewards C_star C_h q z r hr
  cases hl : correctedLaunch rate z rewards C_star C_h with
  | none =>
      have hnil := (ReferenceCompleteOriginalCalendarCellPresence.no_launch_complete_original_calendar_cell_presence
        rate rewards C_star C_h z hl).1
      have hk := k.isLt
      have hlen : (records z).length = 0 := congrArg List.length hnil
      omega
  | some active =>
      have hc := (correctedLaunch_isSome_iff_crossing rate z rewards C_star C_h).mp (by rw [hl]; rfl)
      obtain ⟨first, hlaunch, hfirst, _⟩ :=
        ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance rate z rewards C_star C_h hc
      have heq : first = active := Option.some.inj (hlaunch.symm.trans hl)
      subst first
      have hseed : clockAt z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) (start z) active := by
        simp only [clockAt, hfirst]
      have hspan : start z + (p.T - start z) ≤ p.T := by
        have := physicalStart_le_T rate z rewards C_star C_h
        omega
      have hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
        rate z rewards C_star C_h active hl
      have hrun := ReferenceRunClockPreservation.run_clockAt active z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
        (start z) (p.T - start z) hspan hmode hseed
      have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate z rewards C_star C_h active hl
      have hmem : r ∈ (ReferenceActivePhysicalHorizon.run active z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
          (start z) (p.T - start z) hspan hmode).records := by
        rw [← hrecords, ← hrecord]
        exact List.getElem_mem k.isLt
      have h := hrun.2.2.2 r hmem
      simpa only [h.2.2.1, h.2.2.2.1] using And.intro h.1 h.2.1

private theorem collectionCall_projections (r : PhysicalRecord) (hc : (laterCollectionCall 0 r).isSome = true) :
    (laterCollectionReadout 0 r).isSome = true ∧ (choice r.input).isSome = true := by
  have hprep : (ReferenceActivePhysicalStep.prepare r.input).coordinator =
      r.output.preparation.coordinator := by rw [r.output_eq]; rfl
  unfold laterCollectionCall at hc
  rw [laterCollectionReadout_domain]
  split at hc
  next ho =>
    cases hp : r.output.preparation.coordinator with
    | first outcome => cases outcome <;> simp only [hp, Option.isSome_none, Bool.false_eq_true] at hc
    | live regs owned base outcome =>
        cases outcome <;> simp only [hp, Option.isSome_none, Bool.false_eq_true] at hc
        split_ifs at hc with hs
        · refine ⟨⟨ho, hs⟩, ?_⟩
          simp [choice, hprep, hp, ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.selectionAt, choiceOfCut]
        · cases hc
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;> simp only [hp, Option.isSome_none, Bool.false_eq_true] at hc
        refine ⟨⟨ho, trivial⟩, ?_⟩
        simp [choice, hprep, hp, ReferenceActivePhysicalStep.DispatchCut.selection, choiceOfCut]
    | invalidCollectionCutoff => simp only [hp, Option.isSome_none, Bool.false_eq_true] at hc
    | dagger => simp only [hp, Option.isSome_none, Bool.false_eq_true] at hc
  · cases hc

/-- The canonical collection input is its actual collection readout. -/
theorem collectionInput_readout (q : Fin p.T) (z : CollectionSource q) :
    laterCollectionReadout 0 (collectionRecordAt q z) = some (collectionInput rate rewards C_star C_h q z) := by
  let r := collectionRecordAt q z
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp
    (collectionCall_projections rate r (collectionRecord_spec rate rewards C_star C_h q z).2.2).1
  have hlive : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = none := by
    cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r with
    | none => rfl
    | some d =>
        exact (ReferenceCompleteNumericalBranchObservation.readouts_disjoint rate 0 r
          ⟨by rw [hl]; rfl, by rw [hc]; rfl⟩).elim
  have hnum : cell0 rate r = some c := by
    rw [cell0, hlive, Option.none_or, hc]
  have hc' : c = collectionInput rate rewards C_star C_h q z :=
    Option.some.inj (hnum.symm.trans (Option.some_get _).symm)
  exact hc.trans (congrArg some hc')

/-- Actual canonical rates and old-clock enablement, including disabled dates. -/
theorem collectionInput_parameters (q : Fin p.T) (z : CollectionSource q) :
    let c := collectionInput rate rewards C_star C_h q z
    let args := collectionArgs q z
    c.rate = args.1.rate ∧ args.1.rate = CanonicalRecordingRates.xi p rate.eta.val args.1.anchor ∧
      c.enabled = decide (q.val + 1 < args.2.2.1.clock.g) ∧
      (∀ j, 0 < args.1.anchor j) := by
  dsimp only
  let r := collectionRecordAt q z
  have hr := (collectionRecord_spec rate rewards C_star C_h q z).1
  obtain ⟨whole, past, k, payload, ledger, started, weights, _hmap, _hpast,
      _hprefix, _hrecord, _hnum, hcall, hrate, henabled, _⟩ :=
    ReferenceFirstCollectionWeightEnvelope.actual_collection_readout_source_prefix
      rewards C_star C_h z.val q r hr _ (collectionInput_readout rate rewards C_star C_h q z)
  have hargs := Option.some.inj (hcall.symm.trans (collectionArguments_spec rate rewards C_star C_h q z))
  have hpayload := congrArg Sigma.fst hargs
  have hstarted := congrArg (fun args => args.2.2.1) hargs
  dsimp only at hstarted
  have htime := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q z.val r hr).2.2.1
  refine ⟨?_, ?_, ?_, (collectionArgs q z).1.anchor_pos⟩
  · exact hrate.trans (congrArg (fun P => P.rate) hpayload)
  · rfl
  · rw [henabled, htime, hstarted]

private theorem live_dispatch_frame (x : CoordinatorRoundDispatch.LiveInput p) :
    match CoordinatorRoundDispatch.dispatchLive x with
    | .continuingChosen dispatched _ _ _ =>
        CoordinatorLocalArmChoice.assignmentIsLive x.registers.payload
          (cutoffFromClock p dispatched.startResult.clock.u)
          x.registers.time ∧
        unchangedLiveClockFrame x.registers dispatched.startResult ∧
        x.registers.priorClock.sigma = some x.registers.payload.sigma
    | _ => True := by
  generalize hcomputed : CoordinatorRoundDispatch.dispatchLive x = outcome
  unfold CoordinatorRoundDispatch.dispatchLive at hcomputed
  repeat' first
    | (split at hcomputed)
    | (extract_lets at hcomputed)
    | (subst outcome; trivial)
  all_goals
    dsimp +zetaDelta only at hcomputed
    split at hcomputed
    · contradiction
    · subst outcome
      trivial

/-- Continuing LIVE uses its actual incoming registers and unchanged old clock. -/
theorem continuingRecord_frame (q : Fin p.T) (z : LiveSource q) :
    let r := liveRecord q z
    let c := liveCell q z
    ∃ (regs : Registers p rate.eta) (owned : CoordinatorLiveServiceFinish.OwnedRegisters regs)
      (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p),
      r.input.state.coordinator = .live regs owned base ∧
      continuingTest r = true ∧
      c.selected.view.payload = regs.payload ∧
      CoordinatorPhaseClock.startRound p rate.eta.val r.input.time regs.priorClock
        regs.clockPending = .ok started ∧ started.clock = regs.priorClock ∧
      c.selected.view =
        { payload := regs.payload
          pendingAtChoice := started.pending
          cutoff := cutoffFromClock p started.clock.u
          complementWeights := regs.complementWeights } := by
  dsimp only
  let r := liveRecord q z
  let c := liveCell q z
  obtain ⟨r0, hr0, ⟨regs, owned, base, hin⟩, _hread⟩ := z.property
  have heq : r0 = r := Option.some.inj (hr0.symm.trans (continuingSourceCell_spec rate rewards C_star C_h q z).1)
  have hin' : r.input.state.coordinator = .live regs owned base := by
    simpa only [heq] using hin
  have hp : r.output.preparation.coordinator = .live regs owned base
      (CoordinatorRoundDispatch.dispatchLive (ReferenceActivePhysicalStep.liveInput r.input regs owned base)) := by
    rw [r.output_eq]
    exact ReferenceLiveDispatchMeasurability.canonicalDispatch_live_reconstruction r.input regs owned base hin'
  have hsel := c.selection_actual
  have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames r
  have hlocal := live_dispatch_frame (ReferenceActivePhysicalStep.liveInput r.input regs owned base)
  rw [hp] at hsel hframes
  cases hd : CoordinatorRoundDispatch.dispatchLive
      (ReferenceActivePhysicalStep.liveInput r.input regs owned base) with
  | continuingChosen dispatched hstart continuation selected =>
      rw [hd] at hsel hlocal
      change ReferenceActivePhysicalStep.selectionAt r.input regs.payload dispatched.startResult
        r.input.time (ReferenceActivePhysicalStep.liveRegistersAt regs r.input.time).complementWeights
        selected = some c.selected at hsel
      rw [ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq
        r.input regs.payload dispatched.startResult r.input.time
        (ReferenceActivePhysicalStep.liveRegistersAt regs r.input.time).complementWeights selected rfl] at hsel
      have hpayload : c.selected.view.payload = regs.payload :=
        (congrArg (fun s => s.view.payload) (Option.some.inj hsel)).symm
      refine ⟨regs, owned, base, dispatched.startResult, hin', ?_, hpayload, hstart, hlocal.2.1.1, ?_⟩
      · rw [continuingTest, hp, hd]
      · exact congrArg (fun s => s.view) (Option.some.inj hsel).symm
  | cutoffChosen dispatched hstart ledger hinit hledger hvalid hclock hpending hnone selected =>
      rw [hd] at hsel hframes
      change ReferenceActivePhysicalStep.selectionAt r.input regs.payload dispatched.startResult
        r.input.time (ReferenceActivePhysicalStep.liveRegistersAt regs r.input.time).complementWeights
        selected = some c.selected at hsel
      rw [ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq
        r.input regs.payload dispatched.startResult r.input.time
        (ReferenceActivePhysicalStep.liveRegistersAt regs r.input.time).complementWeights selected rfl] at hsel
      apply False.elim
      apply hframes.1
      have hactive := c.assignment_live
      change CoordinatorLocalArmChoice.assignmentIsLive c.selected.view.payload
        c.selected.view.cutoff r.input.time at hactive
      rw [← Option.some.inj hsel] at hactive
      exact hactive
  | clockFailure failure he => rw [hd] at hsel; cases hsel
  | initializerFailure dispatched hstart checked he => rw [hd] at hsel; cases hsel
  | localFailure dispatched hstart reason => rw [hd] at hsel; cases hsel

private theorem detectCutoff_of_true (clock : CoordinatorPhaseClock.ClockRegisters p)
    (time sigma : Fin p.T) (hsigma : clock.sigma = some sigma) (hu : clock.u = none)
    (hsaved : CoordinatorPhaseClock.savedPriorProposal clock time = .ok true) :
    CoordinatorPhaseClock.detectCutoff clock time = .ok (.cutoff sigma hsigma) := by
  rcases clock with ⟨s, u, g, token⟩
  change s = some sigma at hsigma
  change u = none at hu
  subst s
  subst u
  simp [CoordinatorPhaseClock.detectCutoff, hsaved, Bind.bind, Except.bind]

/-- The actual saved proposal preceding a continuing-LIVE date is false. -/
theorem continuing_previous_proposal_false (q : Fin p.T) (z : LiveSource q)
    (v : Fin p.T) (hvq : v.val + 1 = q.val) :
    completeRowProposalBit p rate.eta.val
      (z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val)) v = false := by
  let r := liveRecord q z
  have hr := (continuingSourceCell_spec rate rewards C_star C_h q z).1
  obtain ⟨regs, owned, base, started, hin, _htest, _hpayload, hstart, hframe, _hview⟩ :=
    continuingRecord_frame rate rewards C_star C_h q z
  change r.input.state.coordinator = .live regs owned base at hin
  change CoordinatorPhaseClock.startRound p rate.eta.val r.input.time regs.priorClock
    regs.clockPending = .ok started at hstart
  have hclock := (actualRecord_clock rate rewards C_star C_h q z.val r hr).1
  simp only [clockAt, hin] at hclock
  obtain ⟨hstamped, hvalid, hsigma, hu, _hgrid, _hsigtime, _hbefore, hproposal⟩ := hclock
  have hfields := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q z.val r hr
  have htime : regs.time = v := Fin.ext (by rw [hfields.2.2.1] at hstamped; omega)
  have hbit : completeRowProposalBit p rate.eta.val r.input.row regs.time = false := by
    cases hb : completeRowProposalBit p rate.eta.val r.input.row regs.time with
    | false => rfl
    | true =>
        have hproposal' : regs.priorClock.lastProposal = some (regs.time, true) := by
          change regs.priorClock.lastProposal = some (regs.time,
            completeRowProposalBit p rate.eta.val r.input.row regs.time) at hproposal
          exact hproposal.trans (congrArg (fun bit => some (regs.time, bit)) hb)
        have hstamp : regs.time.val + 1 = r.input.time.val := hstamped
        have hsaved := CoordinatorPhaseClock.savedPriorProposal_correct
          regs.priorClock r.input.time regs.time true hproposal' hstamp
        have hdetect := detectCutoff_of_true regs.priorClock r.input.time regs.payload.sigma hsigma hu hsaved
        have hparam := ReferenceCoordinatorClockDomains.proposalParameterValid_of_rate rate
        have htimeValid : CoordinatorPhaseClock.startRoundTimeValid p r.input.time regs.priorClock := by
          simp only [CoordinatorPhaseClock.startRoundTimeValid, hsigma, hu, FollowerCutoffScan.calendarRound]
          exact ⟨_hsigtime, by omega⟩
        obtain ⟨cut, hcut, hcutclock, _⟩ := CoordinatorPhaseClock.startRound_cutoff_effect
          p rate.eta.val r.input.time regs.payload.sigma regs.priorClock regs.clockPending
          hparam hvalid htimeValid hsigma hdetect
        have hcutEq : cut = started := Except.ok.inj (hcut.symm.trans hstart)
        have heq := congrArg CoordinatorPhaseClock.ClockRegisters.u (hframe.symm.trans (hcutEq ▸ hcutclock))
        simp only [hu] at heq
        cases heq
  rw [htime, ReferenceActivePhysicalStep.RoundInput.row, hfields.1, hfields.2.1] at hbit
  exact hbit

private theorem previous_record_proposal_false (v q : Fin p.T) (hvq : v.val + 1 = q.val)
    (z : LiveSource q) (r : PhysicalRecord) (hr : sourceRecord v z.val = some r) :
    completeRowProposalBit p rate.eta.val r.input.row r.input.time = false := by
  have hb := continuing_previous_proposal_false rate rewards C_star C_h q z v hvq
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields rate rewards C_star C_h v z.val r hr
  simpa only [ReferenceActivePhysicalStep.RoundInput.row, hf.1, hf.2.1, hf.2.2.1] using hb

/-- Actual adjacent calendar readouts retain the connected physical state. -/
theorem actualRecord_adjacent (v q : Fin p.T) (hvq : v.val + 1 = q.val)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (rv rq : PhysicalRecord) (hv : sourceRecord v z = some rv)
    (hq : sourceRecord q z = some rq) :
    rq.input.state = rv.output.next := by
  obtain ⟨i, hi, hri, hs⟩ := actualRecord_index rate rewards C_star C_h v z rv hv
  obtain ⟨k, hk, hrk, _⟩ := actualRecord_index rate rewards C_star C_h q z rq hq
  have hik : i.val + 1 = k.val := by omega
  have hbound : i.val + 1 < (records z).length := by rw [hik]; exact k.isLt
  have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
    (rate := rate) rewards C_star C_h z i.val hbound
  have hget : (records z)[i.val + 1] = rq := by simpa only [hik] using hrk
  calc rq.input.state = (records z)[i.val + 1].input.state := congrArg (fun r => r.input.state) hget.symm
    _ = (records z)[i.val].output.next := hadj
    _ = rv.output.next := congrArg (fun r => r.output.next) hri

/-- Actual collection readouts end in collection, also after overflow or freeze. -/
theorem collectionRecord_output (q : Fin p.T) (z : CollectionSource q) :
    ∃ (ledger : Ledger rate) (saved : Option (Fin p.T × Bool)),
      (collectionRecordAt q z).output.next.coordinator = .collection (collectionArgs q z).1 ledger saved := by
  let r := collectionRecordAt q z
  have hr := (collectionRecord_spec rate rewards C_star C_h q z).1
  obtain ⟨k, _hk, hrecord, _hs⟩ := actualRecord_index rate rewards C_star C_h q z.val r hr
  have hread := collectionInput_readout rate rewards C_star C_h q z
  have hread' : laterCollectionReadout 0
      (records z.val)[k.val] = some (collectionInput rate rewards C_star C_h q z) := by
    simpa only [hrecord] using hread
  obtain ⟨payload, ledger, started, weights, _hbranch, hcall, _hrate, _henabled, recording, startedLedger,
      decoded, finished, bank, clockFinished, _hrecording, _hstart, _hreceive,
      _hfinish, _hclock, _hss, _hsc, _hsf, _hds, _hdc, _hdf,
      _hfs, _hfc, _hff, hpost⟩ :=
    ReferenceCollectionOldEpisodeOperationPreservation.complete_suffix_collectionReadout_operation_frames
      (rate := rate) rewards C_star C_h z.val k _ hread'
  rw [hrecord] at hcall hpost
  have hpayload : payload = (collectionArgs q z).1 := congrArg Sigma.fst (Option.some.inj
      (hcall.symm.trans (collectionArguments_spec rate rewards C_star C_h q z)))
  obtain ⟨_P, _l, _s, _w, _o, hc, hdiagnostics, _⟩ := laterCollectionReadout_call 0 r _ hread
  have hargs := Option.some.inj (hc.symm.trans hcall)
  cases hargs
  dsimp only [ReferenceActivePhysicalHorizon.RoundRecord.coordinatorDiagnostics] at hdiagnostics
  have hnext : r.output.next.coordinator = r.output.coordinator.configuration := by
    rw [r.output_eq]
    exact (ReferenceActivePhysicalStep.step_next_fields r.input).1
  rw [hdiagnostics, hpost] at hnext
  exact ⟨finished, clockFinished.clock.lastProposal, by simpa only [hpayload] using hnext⟩

/-- A noncall preceding continuing LIVE is itself continuing LIVE. -/
theorem continuing_previous_domain (v q : Fin p.T) (hvq : v.val + 1 = q.val) (z : LiveSource q)
    (hsv : start z.val < v.val) (hnocall : noCallAt rate rewards C_star C_h v z.val) :
    z.val ∈ liveDomain v := by
  rcases noncall_phase_coverage rate rewards C_star C_h v z.val hsv hnocall with hlive | hc
  · exact hlive
  · let cz : CollectionSource v := ⟨z.val, hc⟩
    obtain ⟨ledger, saved, hout⟩ := collectionRecord_output rate rewards C_star C_h v cz
    obtain ⟨regs, owned, base, _started, hin, _⟩ := continuingRecord_frame rate rewards C_star C_h q z
    have hadj := actualRecord_adjacent rate rewards C_star C_h v q hvq z.val
      (collectionRecordAt v cz) (liveRecord q z)
      (collectionRecord_spec rate rewards C_star C_h v cz).1
      (continuingSourceCell_spec rate rewards C_star C_h q z).1
    have heq := (congrArg ReferenceActivePhysicalStep.State.coordinator hadj).symm.trans hin
    rw [hout] at heq
    cases heq

private theorem continuing_not_birth (r : PhysicalRecord) (htest : continuingTest r = true) (P : Payload rate) :
    ¬ InstallationBirth r P := by
  intro hbirth
  cases hp : r.output.preparation.coordinator <;>
    simp_all only [continuingTest, InstallationBirth, Bool.false_eq_true]

private theorem collection_not_birth (r : PhysicalRecord) (c : RoundInput p.K)
    (hc : laterCollectionReadout 0 r = some c) (P : Payload rate) :
    ¬ InstallationBirth r P := by
  intro hbirth
  have hphase := ((laterCollectionReadout_domain 0 r).mp (by rw [hc]; rfl)).2
  cases hp : r.output.preparation.coordinator with
  | first outcome => cases outcome <;> simp only [hp] at hphase
  | live regs owned base outcome =>
      simp only [InstallationBirth, hp] at hbirth
  | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simp only [hp, InstallationBirth] at hphase hbirth
  | invalidCollectionCutoff => simp only [hp] at hphase
  | dagger => simp only [hp] at hphase

/-- Actual POST-t payload retention through the PRE boundary, and no births strictly before it. -/
theorem firstInvocation_retained_interval (t : Fin p.T) (n : Fin (p.T + 1)) (z : FirstSource t)
    (hcall : CallFree t n z.val) :
    (∀ v : Fin p.T, t.val < v.val → v.val ≤ n.val → ∀ r : PhysicalRecord, sourceRecord v z.val = some r →
        storedPayload r.input.state.coordinator = some (firstCell t z).selected.view.payload) ∧
    (∀ v : Fin p.T, t.val < v.val → v.val < n.val → ∀ r : PhysicalRecord, sourceRecord v z.val = some r →
        ∀ fresh, ¬ InstallationBirth r fresh) := by
  obtain ⟨b, rb, _qb, _beta, hr, _heq, _hb, hnext, _hbirth, hpay⟩ :=
    firstInvocation_installation rate rewards C_star C_h t z
  have hst := (actualRecord_index rate rewards C_star C_h t z.val _ hr).choose_spec.2.2
  constructor
  · intro v htv hvn r hrecord
    have hp := noCallBetween_payload rate rewards C_star C_h t n z.val hst hcall v htv hvn
    rw [ReferenceFirstCollectionOldRecorderFoundation.incomingPayload?, hrecord,
      Option.bind_some, hr, Option.bind_some, hnext,
      storedPayload_live, hpay] at hp
    exact hp
  · intro v htv hvn r hrecord fresh
    rcases noncall_phase_coverage rate rewards C_star C_h v z.val (by omega)
      (hcall v htv hvn) with hlive | hcollection
    · have heq : r = liveRecord v ⟨z.val, hlive⟩ :=
        Option.some.inj (hrecord.symm.trans (continuingSourceCell_spec rate rewards C_star C_h v ⟨z.val, hlive⟩).1)
      rw [heq]
      exact continuing_not_birth rate _
        (continuingRecord_frame rate rewards C_star C_h v ⟨z.val, hlive⟩).choose_spec.choose_spec.choose_spec.choose_spec.2.1 fresh
    · have heq : r = collectionRecordAt v ⟨z.val, hcollection⟩ :=
        Option.some.inj (hrecord.symm.trans (collectionRecord_spec rate rewards C_star C_h v ⟨z.val, hcollection⟩).1)
      rw [heq]
      exact collection_not_birth rate _ _
        (collectionInput_readout rate rewards C_star C_h v ⟨z.val, hcollection⟩) fresh

/-- Actual collection retains the installed POST-t payload, with an evolving logical set. -/
theorem firstInvocation_collectionPayload (t q : Fin p.T) (z : FirstSource t) (htq : t.val < q.val)
    (hcall : CallFree t q.castSucc z.val) (hc : z.val ∈ collectionDomain q) :
    (collectionArgs q ⟨z.val, hc⟩).1 = (firstCell t z).selected.view.payload := by
  have hr := (collectionRecord_spec rate rewards C_star C_h q ⟨z.val, hc⟩).1
  have hp := (firstInvocation_retained_interval rate rewards C_star C_h t q.castSucc z hcall).1 q htq le_rfl _ hr
  have hi := collectionArguments_incoming rate rewards C_star C_h q ⟨z.val, hc⟩
  rw [ReferenceFirstCollectionOldRecorderFoundation.incomingPayload?, hr, Option.bind_some] at hi
  exact Option.some.inj (hi.symm.trans hp)

/-- The selected LIVE payload retains its actual installation origin. -/
theorem firstInvocation_continuingPayload (t q : Fin p.T) (z : FirstSource t) (htq : t.val < q.val)
    (hcall : CallFree t q.castSucc z.val) (hlive : z.val ∈ liveDomain q) :
    (liveCell q ⟨z.val, hlive⟩).selected.view.payload = (firstCell t z).selected.view.payload := by
  obtain ⟨regs, owned, base, _started, hin, _htest, hpay, _⟩ :=
    continuingRecord_frame rate rewards C_star C_h q ⟨z.val, hlive⟩
  have hp := (firstInvocation_retained_interval rate rewards C_star C_h t q.castSucc z hcall).1
    q htq le_rfl _ (continuingSourceCell_spec rate rewards C_star C_h q ⟨z.val, hlive⟩).1
  rw [hin, storedPayload_live] at hp
  exact hpay.trans (Option.some.inj hp)

private theorem prefix_clear_mono (W : List (RoundInput p.K)) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ W.length)
    (hclear : (run Q (W.take j)).overflow = false) :
    (run Q (W.take i)).overflow = false := by
  cases hi : (run Q (W.take i)).overflow with
  | false => rfl
  | true =>
      have hfirst := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
        Q W i (hij.trans hj)).mp hi
      have hlate := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
        Q W j hj).mpr (hfirst.trans hij)
      rw [hclear] at hlate
      cases hlate

private theorem appendLogicalCell_next_of_noProposal (r : PhysicalRecord)
    (c : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r) (S : RunState p.K)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) (hclear : S.overflow = false)
    (hbit : completeRowProposalBit p rate.eta.val r.input.row r.input.time = false) :
    (appendLogicalCell r c S a).nextSlowSet = c.selected.view.payload.slowSet := by
  simp only [appendLogicalCell, hclear, hbit, Bool.not_false, Bool.true_and, Bool.false_eq_true, ite_false]

/-- The produced residual seed agrees with actual LIVE before overflow, including at t+1. -/
theorem firstInvocation_generated_live_seed (control0 : PhysicalControl) (u t q : Fin p.T) (z : FirstSource t)
    (hz : z.val ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t) (htq : t.val < q.val)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (x : ContinuousControlSlice.Scalar) (s : SlowSet p × List (LogicalCell p rate))
    (hs : noncallRun t z.val a ((actualFirstCell rate rewards C_star C_h control0 t z x).nextSlowSet,
        extendedPast rate rewards C_star C_h t.castSucc (z.val, a) ++
          [actualFirstCell rate rewards C_star C_h control0 t z x]) q.val = some s)
    (hlive : z.val ∈ liveDomain q) (hclear : (run Q ((originalWord z.val
        (firstCall_launch rate rewards C_star C_h u t z.val hz)).take (q.val - start z.val))).overflow = false) :
    s.1 = (liveCell q ⟨z.val, hlive⟩).selected.view.payload.slowSet := by
  let W := originalWord z.val (firstCall_launch rate rewards C_star C_h u t z.val hz)
  have hd := firstCall_dates rate rewards C_star C_h u t z.val hz
  have hst : start z.val ≤ t.val := hd.1.trans hd.2.1.le
  have hWlen : W.length = p.T - start z.val := by
    rw [actualOriginalWord_length, completeSuffixRecords_length]
  have hqW : q.val - start z.val ≤ W.length := by rw [hWlen]; omega
  have hcall : CallFree t q.castSucc z.val := by
    apply (noncallCalendar_isSome rate rewards C_star C_h t q.castSucc z.val a
      ((actualFirstCell rate rewards C_star C_h control0 t z x).nextSlowSet,
        extendedPast rate rewards C_star C_h t.castSucc (z.val, a) ++
          [actualFirstCell rate rewards C_star C_h control0 t z x])).mp
    change (noncallRun t z.val a _ q.val).isSome = true
    rw [hs]
    rfl
  have hpay := firstInvocation_continuingPayload rate rewards C_star C_h t q z htq hcall hlive
  by_cases hfirst : q.val = t.val + 1
  · have hinit := noncallCalendar_initial rate rewards C_star C_h t z.val a
      ((actualFirstCell rate rewards C_star C_h control0 t z x).nextSlowSet,
        extendedPast rate rewards C_star C_h t.castSucc (z.val, a) ++
          [actualFirstCell rate rewards C_star C_h control0 t z x]) q.val (by omega)
    have heq := Option.some.inj (hs.symm.trans hinit)
    rw [heq]
    have hc := actualFirstCell_originalWord rate rewards C_star C_h control0 u t z hz x
    have hbefore : (firstBefore rate rewards C_star C_h control0 t z).overflow = false := by
      change (actualFirstCell rate rewards C_star C_h control0 t z x).before.overflow = false
      rw [hc.2.1]
      exact prefix_clear_mono rate W (t.val - start z.val) (q.val - start z.val) (by omega) hqW hclear
    have hbit := previous_record_proposal_false rate rewards C_star C_h t q hfirst.symm
      ⟨z.val, hlive⟩ (birthRecord t z) (firstSourceCell_spec rate rewards C_star C_h t z).1
    exact (appendLogicalCell_next_of_noProposal rate _ _ _ _ hbefore hbit).trans
      (congrArg (fun P => P.slowSet) hpay.symm)
  · let v : Fin p.T := ⟨q.val - 1, by omega⟩
    have hvq : v.val + 1 = q.val := by dsimp only [v]; omega
    have htv : t.val < v.val := by dsimp only [v]; omega
    have hs' : noncallRun t z.val a ((actualFirstCell rate rewards C_star C_h control0 t z x).nextSlowSet,
          extendedPast rate rewards C_star C_h t.castSucc (z.val, a) ++
            [actualFirstCell rate rewards C_star C_h control0 t z x]) (v.val + 1) = some s := by
      simpa only [hvq] using hs
    obtain ⟨prev, _hprev, hnocall, happend⟩ :=
      noncallCalendar_some_succ rate rewards C_star C_h t v z.val a _ s htv hs'
    have hvLive := continuing_previous_domain rate rewards C_star C_h v q hvq ⟨z.val, hlive⟩
      (by change start z.val < v.val; omega) hnocall
    have hcell : noncallDateCell rate rewards C_star C_h v z.val a prev.1 =
        some (continuingLogicalCell rate rewards C_star C_h v ⟨z.val, hvLive⟩ a) := by
      rw [noncallDateCell, dite_eq_left hvLive]
    rw [happend, appendNoncallDate, hcell]
    have hvclear : (livePRE v ⟨z.val, hvLive⟩).overflow = false :=
      prefix_clear_mono rate W (v.val - start z.val) (q.val - start z.val) (by omega) hqW hclear
    have hbit := previous_record_proposal_false rate rewards C_star C_h v q hvq
      ⟨z.val, hlive⟩ (liveRecord v ⟨z.val, hvLive⟩)
      (continuingSourceCell_spec rate rewards C_star C_h v ⟨z.val, hvLive⟩).1
    have hcallv : CallFree t v.castSucc z.val := by
      intro r htr hrv
      exact hcall r htr (by
        change r.val < q.val
        change r.val < v.val at hrv
        omega)
    have hpayv := firstInvocation_continuingPayload rate rewards C_star C_h t v z htv hcallv hvLive
    exact (appendLogicalCell_next_of_noProposal rate _ _ _ a hvclear hbit).trans
      (congrArg (fun P => P.slowSet) (hpayv.trans hpay.symm))

private theorem startRound_valid (time : Fin p.T) (clock : CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (Fin (p.m - 1))) (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val time clock pending = .ok started) :
    CoordinatorPhaseClock.clockRegistersValid p rate.eta.val clock ∧
      CoordinatorPhaseClock.startRoundTimeValid p time clock := by
  unfold CoordinatorPhaseClock.startRound at hstart
  split at hstart
  · split at hstart
    · split at hstart
      · exact ⟨‹_›, ‹_›⟩
      · contradiction
    · contradiction
  · contradiction

private theorem collectionCall_grid (r : PhysicalRecord) (args : (payload : Payload rate) ×
      Ledger rate × CoordinatorPhaseClock.StartRoundResult p ×
      (FastArm payload.slowSet → ℝ))
    (hc : laterCollectionCall 0 r = some args) :
    args.2.2.1.clock.g = gridBoundary p rate.eta.val args.1.sigma := by
  unfold laterCollectionCall at hc
  split at hc
  next ho =>
    cases hp : r.output.preparation.coordinator with
    | first outcome => cases outcome <;> simp only [hp] at hc <;> cases hc
    | dagger => simp only [hp] at hc; cases hc
    | invalidCollectionCutoff => simp only [hp] at hc; cases hc
    | live regs owned base outcome =>
        cases outcome with
        | cutoffChosen dispatched hstart ledger hinit hledger hvalid hclock hpending hnone selected =>
            simp only [hp] at hc
            split_ifs at hc with hsigma
            have hargs := Option.some.inj hc
            cases hargs
            have hvalidClock := (startRound_valid rate _ _ _ _ hstart).1.1
            have hsigmaClock := hvalid.1
            change regs.priorClock.sigma = some regs.payload.sigma at hsigmaClock
            change regs.priorClock.g = CoordinatorPhaseClock.boundaryFromSigma
              p rate.eta.val regs.priorClock.sigma at hvalidClock
            rw [hsigmaClock] at hvalidClock
            change dispatched.startResult.clock.g = gridBoundary p rate.eta.val regs.payload.sigma
            exact (congrArg CoordinatorPhaseClock.ClockRegisters.g hclock).trans hvalidClock
        | _ => simp only [hp] at hc; cases hc
    | collection payload ledger clock cutoff outcome =>
        cases outcome with
        | continuing core snapshot boundary scores =>
            simp only [hp] at hc
            have hargs := Option.some.inj hc
            cases hargs
            have hvalidClock := snapshot.inputsValid.clock_registers_valid.1
            rw [snapshot.inputsValid.clock_sigma_eq] at hvalidClock
            change snapshot.clockStarted.clock.g = gridBoundary p rate.eta.val payload.sigma
            exact (congrArg CoordinatorPhaseClock.ClockRegisters.g snapshot.clockStarted_frame.1).trans hvalidClock
        | _ => simp only [hp] at hc; cases hc
  · cases hc

private theorem initialized_choice_grid (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (c : ReferenceCollectionSegmentExtraction.Choice rate) (I : Initializer p)
    (hc : choice x = some c) (hI : c.initializer = some I) :
    I.freezeAt = gridBoundary p rate.eta.val c.payload.sigma := by
  unfold choice at hc
  split at hc
  · cases hc
  · cases hp : (ReferenceActivePhysicalStep.prepare x).coordinator with
    | live regs owned base outcome =>
        cases outcome <;> simp only [hp, choiceOfCut] at hc
        all_goals try contradiction
        next dispatched hstart ledger hinit hledger hvalid hclock hpending hnone selected =>
          cases Option.some.inj hc
          cases Option.some.inj hI
          have hg := (startRound_valid rate _ _ _ _ hstart).1.1
          change regs.priorClock.g = CoordinatorPhaseClock.boundaryFromSigma
            p rate.eta.val regs.priorClock.sigma at hg
          have hsigma : regs.priorClock.sigma = some regs.payload.sigma := hvalid.1
          rw [hsigma] at hg
          exact hvalid.2.1.trans hg
    | first outcome => cases outcome <;> simp only [hp, choiceOfCut] at hc <;> cases hc
    | collection P ledger clock cutoff outcome =>
        cases outcome <;> simp only [hp, choiceOfCut] at hc
        all_goals first | contradiction | (cases Option.some.inj hc; cases hI)
    | invalidCollectionCutoff => simp only [hp, choiceOfCut] at hc; cases hc
    | dagger => simp only [hp, choiceOfCut] at hc; cases hc

private theorem segment_choice (R : List PhysicalRecord) (e : ℕ) (seg : Segment rate)
    (hs : segmentAt R e = some seg) : choice seg.entry.input = some seg.context := by
  have hb := (segmentAt_branch R e seg hs).1
  cases hd : R.drop e with
  | nil => simp only [hd, ReferenceCollectionSegmentExtraction.segment] at hb; cases hb
  | cons entry rest =>
      rw [hd, ReferenceCollectionSegmentExtraction.segment] at hb
      cases hc : choice entry.input with
      | none => simp only [hc, Option.map_none] at hb; cases hb
      | some c =>
          simp only [hc, Option.map_some] at hb
          split at hb <;> cases Option.some.inj hb <;> exact hc

/-- Literal old-grid enablement on the one-based clock, without a clarity premise. -/
theorem collectionInput_oldGrid (q : Fin p.T) (z : CollectionSource q) :
    let args := collectionArgs q z
    args.2.2.1.clock.g = gridBoundary p rate.eta.val args.1.sigma ∧
      (collectionInput rate rewards C_star C_h q z).enabled =
        decide (q.val + 1 < gridBoundary p rate.eta.val args.1.sigma) := by
  dsimp only
  have hg := collectionCall_grid rate _ _ (collectionArguments_spec rate rewards C_star C_h q z)
  exact ⟨hg, (collectionInput_parameters rate rewards C_star C_h q z).2.2.1.trans
    (congrArg (fun g => decide (q.val + 1 < g)) hg)⟩

/-- Disabled dates advance the complete word with frozen registers and a false zero record. -/
theorem collection_disabled_word_step (q : Fin p.T) (z : CollectionSource q)
    (hboundary : gridBoundary p rate.eta.val (collectionArgs q z).1.sigma ≤ q.val + 1) :
    let W := collectionWord q z
    let S := collectionPRE q z
    let S' := run Q (W.take (q.val + 1 - start z.val))
    (collectionInput rate rewards C_star C_h q z).enabled = false ∧
      ∀ j : Fin p.K, S'.registers j = S.registers j ∧ S'.records j = S.records j ++ [(false, 0)] := by
  dsimp only
  have henabled : (collectionInput rate rewards C_star C_h q z).enabled = false := by
    rw [(collectionInput_oldGrid rate rewards C_star C_h q z).2, decide_eq_false (Nat.not_lt.mpr hboundary)]
  obtain ⟨hk, hsq, hc⟩ := collectionInput_word rate rewards C_star C_h q z
  have hstep : run Q ((collectionWord q z).take (q.val + 1 - start z.val)) =
      RecordedQueueRun.step Q (collectionPRE q z) (collectionInput rate rewards C_star C_h q z) := by
    rw [collectionBefore, hc, Nat.sub_add_comm hsq, ← List.take_append_getElem hk,
      RecordedSlowRefresh.run_append_singleton]
  refine ⟨henabled, ?_⟩
  intro j
  rw [hstep]
  refine ⟨(RecordedQueueRun.step_disabled_preserves Q _ _ henabled j).1, ?_⟩
  change _ ++ [RecordedQueueRun.acceptedRecord Q _ _ j] = _
  have hr : RecordedQueueRun.acceptedRecord Q (collectionPRE q z)
      (collectionInput rate rewards C_star C_h q z) j = (false, 0) := by
    unfold RecordedQueueRun.acceptedRecord
    split <;> simp only [henabled, Bool.false_eq_true, ite_false]
  rw [hr]

/-- Every intervening noncall before a continuing-LIVE query is continuing LIVE. -/
theorem firstInvocation_live_interval (t q : Fin p.T) (z : FirstSource t) (hcall : CallFree t q.castSucc z.val)
    (hlive : z.val ∈ liveDomain q) :
    ∀ v : Fin p.T, t.val < v.val → v.val ≤ q.val → z.val ∈ liveDomain v := by
  have hst := (actualRecord_index rate rewards C_star C_h t z.val _
    (firstSourceCell_spec rate rewards C_star C_h t z).1).choose_spec.2.2
  have h : ∀ k : ℕ, ∀ v : Fin p.T, v.val + k = q.val → t.val < v.val → z.val ∈ liveDomain v := by
    intro k
    induction k with
    | zero =>
        intro v hv _htv
        have heq : v = q := Fin.ext (by omega)
        subst v
        exact hlive
    | succ k ih =>
        intro v hv htv
        let next : Fin p.T := ⟨v.val + 1, by omega⟩
        have hnext := ih next (by dsimp only [next]; omega) (by dsimp only [next]; omega)
        exact continuing_previous_domain rate rewards C_star C_h v next rfl ⟨z.val, hnext⟩
          (by change start z.val < v.val; omega)
          (hcall v htv (by change v.val < q.val; omega))
  intro v htv hvq
  exact h (q.val - v.val) v (by omega) htv

/-- The LIVE query belongs to this installation's maximal continuing prefix. -/
theorem firstInvocation_live_prefix_index (t q : Fin p.T) (z : FirstSource t) (htq : t.val < q.val)
    (hcall : CallFree t q.castSucc z.val) (hlive : z.val ∈ liveDomain q) :
    q.val - start z.val < t.val + 1 - start z.val + (continuingPrefix
        rate rewards C_star C_h z.val (t.val + 1 - start z.val)).length := by
  let R := records z.val
  let k := t.val + 1 - start z.val
  let L := R.drop k
  let n := q.val - start z.val - k + 1
  have hst := (actualRecord_index rate rewards C_star C_h t z.val _
    (firstSourceCell_spec rate rewards C_star C_h t z).1).choose_spec.2.2
  have hRlen : R.length = p.T - start z.val := completeSuffixRecords_length rate z.val rewards C_star C_h
  have hn : n ≤ L.length := by
    dsimp only [n, L, k]
    rw [List.length_drop, hRlen]
    omega
  have htest : ∀ r ∈ L.take n, continuingTest r = true := by
    intro r hr
    obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.mp hr
    have hin : i < n := hi.trans_le (List.length_take_le n L)
    have hiL : i < L.length := by omega
    have hiR : k + i < R.length := by dsimp only [L] at hiL; rw [List.length_drop] at hiL; omega
    have hrecord : R[k + i] = r := by
      simpa only [List.getElem_take, L, List.getElem_drop] using hir
    let v : Fin p.T := ⟨start z.val + (k + i), by rw [hRlen] at hiR; omega⟩
    have htv : t.val < v.val := by dsimp only [v, k]; omega
    have hvq : v.val ≤ q.val := by dsimp only [v, n, k] at *; omega
    have hvLive := firstInvocation_live_interval rate rewards C_star C_h t q z hcall hlive v htv hvq
    have hlookup : sourceRecord v z.val = some r := by
      rw [actualRecord, ite_eq_left (by dsimp only [v]; omega : start z.val ≤ v.val)]
      change R[(start z.val + (k + i)) - start z.val]? = some r
      rw [Nat.add_sub_cancel_left, List.getElem?_eq_getElem hiR, hrecord]
    have heq : r = liveRecord v ⟨z.val, hvLive⟩ :=
      Option.some.inj (hlookup.symm.trans (continuingSourceCell_spec rate rewards C_star C_h v ⟨z.val, hvLive⟩).1)
    rw [heq]
    exact (continuingRecord_frame rate rewards C_star C_h v ⟨z.val, hvLive⟩).choose_spec.choose_spec.choose_spec.choose_spec.2.1
  have htake : L.takeWhile continuingTest = L.take n ++ (L.drop n).takeWhile continuingTest := by
    conv_lhs => rw [← List.take_append_drop n L]
    exact List.takeWhile_append_of_pos htest
  have hlen := congrArg List.length htake
  rw [List.length_append, List.length_take, Nat.min_eq_left hn] at hlen
  change q.val - start z.val < k + (L.takeWhile continuingTest).length
  dsimp only [n, k] at hlen ⊢
  omega

private theorem originalWord_weight_of_clear (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hl : ∃ active, correctedLaunch rate z rewards C_star C_h = some active)
    (n : ℕ) (hn : n ≤ (originalWord z hl).length) (hc : (run Q ((originalWord z hl).take n)).overflow = false) :
    scoreWeight Q (run Q ((originalWord z hl).take n)) =
      (fun j => AssignmentScoreReconstruction.sourceWeightBase p ^
        (calendarReplay rate (originalWord z hl) j n).1) := by
  have hpre : n ≤ UnstoppedRecordedQueueComparison.firstOverflowPrefix Q (originalWord z hl) := by
    by_contra hnot
    have hf := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
      Q (originalWord z hl) n hn).mpr (by omega)
    rw [hc] at hf
    cases hf
  have hw := (actualOriginalWord_numericalPrefix rate rewards C_star C_h z hl n hn).2.1
  simpa only [Nat.min_eq_left hpre] using hw

/-- At a clear LIVE PRE state the physical complement equals the all-arm numerical restriction. -/
theorem firstInvocation_live_complement (t q : Fin p.T) (z : FirstSource t) (htq : t.val < q.val)
    (hcall : CallFree t q.castSucc z.val) (hlive : z.val ∈ liveDomain q)
    (hclear : (livePRE q ⟨z.val, hlive⟩).overflow = false) :
    ∀ j : FastArm (liveCell q ⟨z.val, hlive⟩).selected.view.payload.slowSet,
      (liveCell q ⟨z.val, hlive⟩).selected.view.complementWeights j =
        scoreWeight Q (livePRE q ⟨z.val, hlive⟩) j.val := by
  let R := records z.val
  let r := liveRecord q ⟨z.val, hlive⟩
  let W := continuingNumericalWord rate rewards C_star C_h q ⟨z.val, hlive⟩
  let h := q.val - start z.val
  obtain ⟨_b0, _rb0, _qb0, _beta0, _hr0, heq0, hb0, _⟩ := firstInvocation_installation rate rewards C_star C_h t z
  obtain ⟨b, hbindex, hbrec, hst⟩ := actualRecord_index rate rewards C_star C_h t z.val _
    (firstSourceCell_spec rate rewards C_star C_h t z).1
  have hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true := by
    rw [hbrec, ← heq0]
    exact hb0
  obtain ⟨iq, hiq, hqrec, _hsq⟩ := actualRecord_index rate rewards C_star C_h q z.val r
    (continuingSourceCell_spec rate rewards C_star C_h q ⟨z.val, hlive⟩).1
  have hhR : h < R.length := by dsimp only [h]; rw [← hiq]; exact iq.isLt
  have hWlen : W.length = R.length := actualOriginalWord_length rate rewards C_star C_h z.val _
  obtain ⟨P0, rb, qb, beta, cell, _native, hP0len, _hP0map, _hP0prefix, _hinit,
      _hnext, _hbirth, _hstrict, _hbase, _hcell, _hninput, _hnpayload, _henabled,
      _hbirthPrefix, _hbirthSlots, hseed, _hdown, hbranch⟩ :=
    ReferenceCompleteInstallationOutsideCalendarReplay.actual_later_installation_complement_calendar_replay
      rate rewards C_star C_h z.val b hb
  rcases hbranch with hterminal | ⟨k, C, hk, _hstate, _hClen, _hCmap, _hCtimes,
    heR, _heT, _hHlen, hprefix, _hslots, _hdisabled, hcounts, htail⟩
  · omega
  clear htail
  have hkvalue : k.val = t.val + 1 - start z.val :=
    hk.trans ((congrArg (fun n => n + 1) hbindex).trans (Nat.sub_add_comm hst).symm)
  have hqin := firstInvocation_live_prefix_index rate rewards C_star C_h t q z htq hcall hlive
  rw [← hkvalue] at hqin
  let count := h - k.val
  have hkh : k.val ≤ h := by dsimp only [h]; omega
  have hcount : count ≤ (continuingPrefix
      rate rewards C_star C_h z.val k.val).length := by dsimp only [count, h]; omega
  have hsum : k.val + count = h := by dsimp only [count]; omega
  obtain ⟨rn, qn, hpn, _houtn, hinn, hnum⟩ := hcounts count hcount
  have hrecord : R[k.val + count] = r := by simpa only [hsum, hiq] using hqrec
  have hinoption := hinn (by change k.val + count < R.length; omega)
  rw [List.getElem?_eq_getElem (by change k.val + count < R.length; omega), Option.map_some, hrecord] at hinoption
  have hinrn : r.input.state.coordinator = .live rn qn beta := Option.some.inj hinoption
  let H := P0 ++ [cell] ++ C
  have hprefixH := hprefix h hkh (by dsimp only [h]; omega)
  have hcalendar := (originalWord_calendar_prefix rate rewards C_star C_h z.val
    (continuing_launch rate rewards C_star C_h q ⟨z.val, hlive⟩) q.castSucc (by change start z.val ≤ q.val; omega)).2.2
  have hdate : start z.val + h = q.val := by
    dsimp only [h]
    omega
  rw [hdate] at hprefixH
  have htake : H.take h = W.take h := Option.some.inj (hprefixH.symm.trans hcalendar)
  have hbirthLength : (P0 ++ [cell]).length = k.val := by
    rw [List.length_append, List.length_singleton, hP0len]
    exact hk.symm
  have htakeH : H.take h = (P0 ++ [cell]) ++ C.take count := by
    change ((P0 ++ [cell]) ++ C).take h = _
    rw [List.take_append, List.take_of_length_le (by omega : (P0 ++ [cell]).length ≤ h), hbirthLength]
  have hreplay (j : FastArm rb.payload.slowSet) :
      QueueReplay.replay (4 * rate.n) (rb.complementScores j, qb.queue j) (rawCalendar rate j.val (C.take count)) =
      calendarReplay rate W j.val h := by
    rw [(hseed j).1]
    unfold calendarReplay
    rw [List.take_length, ← QueueReplay.replay_append, ← htake, htakeH]
    simp only [rawCalendar, List.map_append]
  have hregisters (j : FastArm rn.payload.slowSet) :
      rn.complementScores j = (calendarReplay rate W j.val h).1 := by
    let j0 : FastArm rb.payload.slowSet := ⟨j.val, by simpa only [← hpn] using j.property⟩
    obtain ⟨j1, hj1, hvalue, _hservice⟩ := hnum j0
    have hjeq : j1 = j := Subtype.ext hj1
    subst j1
    exact (congrArg Prod.fst hvalue).trans (congrArg Prod.fst (hreplay j0))
  have hweight := originalWord_weight_of_clear rate rewards C_star C_h z.val
    (continuing_launch rate rewards C_star C_h q ⟨z.val, hlive⟩) h
    (by change h ≤ W.length; omega) hclear
  change scoreWeight Q (run Q (W.take h)) =
    (fun j => AssignmentScoreReconstruction.sourceWeightBase p ^ (calendarReplay rate W j h).1) at hweight
  obtain ⟨regs, owned, base, started, hin, _htest, _hpayload, _hstart, _hframe, hview⟩ :=
    continuingRecord_frame rate rewards C_star C_h q ⟨z.val, hlive⟩
  change r.input.state.coordinator = .live regs owned base at hin
  have hregs : regs = rn := Option.some.inj (congrArg (fun configuration => match configuration with
      | .live registers _ _ => some registers
      | _ => none) (hin.symm.trans hinrn))
  subst regs
  let property := fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
    ∀ j : FastArm view.payload.slowSet, view.complementWeights j = scoreWeight Q (livePRE q ⟨z.val, hlive⟩) j.val
  apply Eq.mpr (congrArg property hview)
  intro j
  change rn.complementWeights j = scoreWeight Q (run Q (W.take h)) j.val
  rw [hweight]
  change AssignmentScoreReconstruction.sourceWeightBase p ^ rn.complementScores j = _
  rw [hregisters j]

/-- A real first invocation supplies its own corrected launch. -/
theorem firstInvocation_launch (t : Fin p.T) (z : FirstSource t) :
    ∃ active, correctedLaunch rate z.val rewards C_star C_h = some active := by
  cases hl : correctedLaunch rate z.val rewards C_star C_h with
  | some active => exact ⟨active, rfl⟩
  | none =>
      obtain ⟨b, _⟩ := firstInvocation_installation rate rewards C_star C_h t z
      have hnil := (ReferenceCompleteOriginalCalendarCellPresence.no_launch_complete_original_calendar_cell_presence
        rate rewards C_star C_h z.val hl).1
      have hlen : (records z.val).length = 0 := congrArg List.length hnil
      have := b.isLt
      omega

/-- The installed old anchor is its actual episode-origin weight vector on the complete word. -/
theorem firstInvocation_episode_anchor (t : Fin p.T) (z : FirstSource t) :
    let R := records z.val
    let P := (firstCell t z).selected.view.payload
    let W := originalWord z.val (firstInvocation_launch rate rewards C_star C_h t z)
    ∃ (b rho : Fin R.length) (P_rho : Payload rate), sourceRecord t z.val = some R[b.val] ∧
      InstallationBirth R[b.val] P ∧
      rho.val ≤ b.val ∧ InstallationBirth R[rho.val] P_rho ∧
      ReferenceCompleteEpisodeAnchorOrigin.IsEpisodeAnchorBirth R[rho.val] ∧
      P.anchor = P_rho.anchor ∧
      (∀ j, P_rho.anchor j = AssignmentScoreReconstruction.sourceWeightBase p ^
        (calendarReplay rate W j rho.val).1) ∧
      R[rho.val].input.time = P_rho.sigma ∧ P_rho.sigma.val ≤ P.sigma.val ∧
      gridBoundary p rate.eta.val P_rho.sigma = gridBoundary p rate.eta.val P.sigma := by
  dsimp only
  obtain ⟨b, rb, _qb, _beta, hr, _heq, _hb, _hnext, hbirth, hpay⟩ :=
    firstInvocation_installation rate rewards C_star C_h t z
  rw [hpay] at hbirth
  have hrestore := ReferenceCompleteOriginalCalendarWeightMarginalRestoration.complete_original_installation_weight_marginal_restoration
    rate rewards C_star C_h z.val
  rw [Classical.choose_spec (firstInvocation_launch rate rewards C_star C_h t z)] at hrestore
  obtain ⟨whole, _hlen, _hprefix, hfull, _hunique, hbirths, _hbranches, _hweights⟩ := hrestore
  have hwhole : whole = originalWord z.val (firstInvocation_launch rate rewards C_star C_h t z) :=
    Option.some.inj (hfull.symm.trans (actualOriginalWord_spec rate rewards C_star C_h z.val _))
  obtain ⟨rho, P_rho, hrho, hroot, hepisode, _hcurrent, _horigin, hanchor,
    hpow, htime, htimeOrder, hgrid, _hspan⟩ := hbirths b _ hbirth
  exact ⟨b, rho, P_rho, hr, hbirth, hrho, hroot, hepisode, hanchor,
    by simpa only [hwhole] using hpow, htime, htimeOrder, hgrid⟩

private theorem noncallCalendar_chronology (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hl : ∃ active, correctedLaunch rate z rewards C_star C_h = some active)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) (initial : SlowSet p × List (LogicalCell p rate))
    (hpair : initial.2.Pairwise (fun e f => e.time.val < f.time.val))
    (htime : ∀ e ∈ initial.2, e.time.val ≤ t.val) (k : ℕ) (s : SlowSet p × List (LogicalCell p rate))
    (hs : noncallRun t z a initial k = some s) :
    initial.2 <+: s.2 ∧ s.2.Pairwise (fun e f => e.time.val < f.time.val) ∧
      ∀ e ∈ s.2, e.time.val < max (t.val + 1) k := by
  induction k generalizing s with
  | zero =>
      cases Option.some.inj hs
      exact ⟨List.prefix_refl _, hpair, fun e he => by have := htime e he; omega⟩
  | succ k ih =>
      rw [noncallCalendar] at hs
      cases hp : noncallRun t z a initial k with
      | none => rw [hp, Option.bind_none] at hs; cases hs
      | some prev =>
          rw [hp, Option.bind_some] at hs
          obtain ⟨hprefix, hprev, hprevtime⟩ := ih prev hp
          have hretain : initial.2 <+: prev.2 ∧ prev.2.Pairwise (fun e f => e.time.val < f.time.val) ∧
              ∀ e ∈ prev.2, e.time.val < max (t.val + 1) (k + 1) :=
            ⟨hprefix, hprev, fun e he => by have := hprevtime e he; omega⟩
          split at hs
          next hactive =>
            split_ifs at hs with hnocall
            have heq := Option.some.inj hs
            rw [← heq]
            unfold appendNoncallDate
            split
            · exact hretain
            next c hc =>
              have hct := (noncallDateCell_actualWord rate rewards C_star C_h ⟨k, hactive.2⟩ z hl a prev.1 c hc).1
              have hct' : c.time.val = k := congrArg Fin.val hct
              refine ⟨hprefix.trans (List.prefix_append _ _), ?_, ?_⟩
              · rw [List.pairwise_append]
                refine ⟨hprev, List.pairwise_singleton _ _, ?_⟩
                intro e he f hf
                have hf' : f = c := List.mem_singleton.mp hf
                subst f
                have := hprevtime e he
                omega
              · intro e he
                rcases List.mem_append.mp he with he | he
                · exact hretain.2.2 e he
                · have heq : e = c := List.mem_singleton.mp he
                  subst e
                  omega
          · cases Option.some.inj hs
            exact hretain

/-- The entire produced history and every retained noncall cell remain chronological. -/
theorem firstInvocation_generated_chronology (control0 : PhysicalControl) (u t : Fin p.T) (z : FirstSource t)
    (hz : z.val ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (x : ContinuousControlSlice.Scalar) (n : Fin (p.T + 1))
    (s : SlowSet p × List (LogicalCell p rate)) (htn : t.val < n.val)
    (hs : noncallRun t z.val a ((actualFirstCell rate rewards C_star C_h control0 t z x).nextSlowSet,
        extendedPast rate rewards C_star C_h t.castSucc (z.val, a) ++
          [actualFirstCell rate rewards C_star C_h control0 t z x]) n.val = some s) :
    (extendedPast rate rewards C_star C_h t.castSucc (z.val, a) ++
      [actualFirstCell rate rewards C_star C_h control0 t z x]) <+: s.2 ∧
      s.2.Pairwise (fun e f => e.time.val < f.time.val) ∧ ∀ e ∈ s.2, e.time.val < n.val := by
  have hpast := firstCall_generatedPast_chronology rate rewards C_star C_h u t z.val hz a t.castSucc le_rfl
  have hcelltime := actualFirstCell_time rate rewards C_star C_h control0 t z x
  have hinitial : (extendedPast rate rewards C_star C_h t.castSucc (z.val, a) ++
      [actualFirstCell rate rewards C_star C_h control0 t z x]).Pairwise (fun e f => e.time.val < f.time.val) := by
    rw [List.pairwise_append]
    refine ⟨hpast.1, List.pairwise_singleton _ _, ?_⟩
    intro e he f hf
    have hf' := List.mem_singleton.mp hf
    subst f
    rw [hcelltime]
    exact (hpast.2.1 e he).2
  have hbound : ∀ e ∈ (extendedPast rate rewards C_star C_h t.castSucc (z.val, a) ++
      [actualFirstCell rate rewards C_star C_h control0 t z x]), e.time.val ≤ t.val := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact (hpast.2.1 e he).2.le
    · rw [List.mem_singleton.mp he, hcelltime]
  have h := noncallCalendar_chronology rate rewards C_star C_h t z.val
    (firstCall_launch rate rewards C_star C_h u t z.val hz) a _ hinitial hbound n.val s hs
  simpa only [Nat.max_eq_right (Nat.succ_le_of_lt htn)] using h

private theorem collectionRecord_continuing (q : Fin p.T) (z : CollectionSource q)
    (P : Payload rate) (ledger : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hin : (collectionRecordAt q z).input.state.coordinator = .collection P ledger saved) :
    continuing (collectionRecordAt q z) = true := by
  let r := collectionRecordAt q z
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp
    (collectionCall_projections rate r (collectionRecord_spec rate rewards C_star C_h q z).2.2).2
  obtain ⟨final, proposal, hpost⟩ := collectionRecord_output rate rewards C_star C_h q z
  obtain ⟨done, hd⟩ := ReferenceCollectionSegmentExtraction.actual_collection_round_complete
    r c _ final proposal hc hpost
  have hcontext : done.context = c := Option.some.inj
    ((ReferenceCollectionSegmentExtraction.actual_collection_round_checked r done hd).1.symm.trans hc)
  have hi := (choice_collection_pre r.input P ledger saved c hin hc).2
  change continuing r = true
  simp only [continuing, hd, hcontext, hi, Option.isNone_none]

private theorem collection_not_continuing (r : PhysicalRecord) (hc : (laterCollectionCall 0 r).isSome = true) :
    continuingTest r = false := by
  unfold laterCollectionCall at hc
  split at hc
  · cases hp : r.output.preparation.coordinator with
    | first outcome => cases outcome <;> simp only [hp, Option.isSome_none, Bool.false_eq_true] at hc
    | live regs owned base outcome =>
        cases outcome <;> simp only [hp, Option.isSome_none, Bool.false_eq_true] at hc
        simp only [continuingTest, hp]
    | collection payload ledger clock cutoff outcome =>
        simp only [continuingTest, hp]
    | invalidCollectionCutoff => simp only [hp, Option.isSome_none, Bool.false_eq_true] at hc
    | dagger => simp only [hp, Option.isSome_none, Bool.false_eq_true] at hc
  · cases hc

private theorem takeWhile_boundary {α : Type*} (f : α → Bool) (L : List α)
    (h : (L.takeWhile f).length < L.length) :
    f (L[(L.takeWhile f).length]'h) = false := by
  induction L with
  | nil => simp only [List.takeWhile_nil, List.length_nil, Nat.lt_irrefl] at h
  | cons a L ih =>
      cases hf : f a with
      | false => simp only [List.takeWhile_cons, hf, Bool.false_eq_true, ite_false,
          List.length_nil, List.getElem_cons_zero]
      | true =>
          have ht : (L.takeWhile f).length < L.length := by
            simpa only [List.takeWhile_cons, hf, ite_true, List.length_cons, Nat.add_lt_add_iff_right] using h
          simpa only [List.takeWhile_cons, hf, ite_true, List.length_cons, List.getElem_cons_succ] using ih ht

private theorem segment_boundary_not_continuing (R : List (PhysicalRecord)) (e : ℕ) (seg : Segment rate)
    (hs : segmentAt R e = some seg) (hne : seg.records ≠ []) (hv : e + seg.records.length < R.length) :
    continuing R[e + seg.records.length] = false := by
  have hs' := (segmentAt_branch R e seg hs).1
  cases hdrop : R.drop e with
  | nil => simp only [hdrop, ReferenceCollectionSegmentExtraction.segment] at hs'; cases hs'
  | cons entry rest =>
      rw [hdrop, ReferenceCollectionSegmentExtraction.segment] at hs'
      cases hc : choice entry.input with
      | none => simp only [hc, Option.map_none] at hs'; cases hs'
      | some c =>
          simp only [hc, Option.map_some] at hs'
          split at hs'
          · cases Option.some.inj hs'
            have hlen : (rest.takeWhile continuing).length < rest.length := by
              have hl := congrArg List.length hdrop
              simp only [List.length_drop, List.length_cons] at hl hv
              omega
            have heq : R[e + (entry :: rest.takeWhile continuing).length] =
                rest[(rest.takeWhile continuing).length] := by
              rw [List.getElem_drop' hv]
              simp only [hdrop, List.length_cons, List.getElem_cons_succ]
            rw [heq]
            exact takeWhile_boundary _ rest hlen
          · cases Option.some.inj hs'
            exact (hne rfl).elim

private theorem complete_record_time
    (z : BootstrapPrivateRoundStreams.SourceInput p) (b : Fin (records z).length) :
    (records z)[b.val].input.time.val = start z + b.val := by
  have ht := completeSuffixRecords_time_values rate z rewards C_star C_h
  have hl := completeSuffixRecords_length rate z rewards C_star C_h
  have hb : b.val < p.T - start z := by omega
  have hg := congrArg (fun xs : List ℕ => xs[b.val]?) ht
  simpa only [List.getElem?_map, List.getElem?_eq_getElem b.isLt,
    Option.map_some, ReferenceActivePhysicalHorizon.calendar,
    List.getElem?_range', hb, ite_true, one_mul, Option.some.injEq] using hg

/-- All-arm OLD-anchor bounds on enabled collection, from the actual episode
birth with its arbitrary incoming score and backlog. -/
theorem firstInvocation_collection_envelope (t q : Fin p.T) (z : FirstSource t) (htq : t.val < q.val)
    (hcall : CallFree t q.castSucc z.val) (hc : z.val ∈ collectionDomain q)
    (hboundary : q.val + 1 < gridBoundary p rate.eta.val (collectionArgs q ⟨z.val, hc⟩).1.sigma)
    (hclear : (collectionPRE q ⟨z.val, hc⟩).overflow = false) :
    ∀ j : Fin p.K, (collectionArgs q ⟨z.val, hc⟩).1.anchor j ≤ scoreWeight Q (collectionPRE q ⟨z.val, hc⟩) j ∧
      scoreWeight Q (collectionPRE q ⟨z.val, hc⟩) j ≤ 2 * (collectionArgs q ⟨z.val, hc⟩).1.anchor j := by
  let W := collectionWord q ⟨z.val, hc⟩
  let h := q.val - start z.val
  have hpay := firstInvocation_collectionPayload rate rewards C_star C_h t q z htq hcall hc
  obtain ⟨b, rho, P, hb, _hbirth, hrhob, _hroot, _hepisode, ha, hpow,
      htime, _horder, hg⟩ := firstInvocation_episode_anchor rate rewards C_star C_h t z
  have hbt := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h t z.val (records z.val)[b.val] hb).2.2.1
  have hbt' := complete_record_time rate rewards C_star C_h z.val b
  have hbh : rho.val ≤ h := by dsimp only [h]; omega
  have hWlen : W.length = (records z.val).length := actualOriginalWord_length rate rewards C_star C_h z.val _
  have hlenR := completeSuffixRecords_length rate z.val rewards C_star C_h
  have hhW : h ≤ W.length := by dsimp only [h]; omega
  have hrhoW : rho.val ≤ W.length := hbh.trans hhW
  have hclearR := prefix_clear_mono rate W rho.val h hbh hhW hclear
  have hweights := originalWord_weight_of_clear rate rewards C_star C_h z.val
    (collection_launch rate rewards C_star C_h q ⟨z.val, hc⟩) rho.val hrhoW hclearR
  change scoreWeight Q (run Q (W.take rho.val)) =
    (fun j => AssignmentScoreReconstruction.sourceWeightBase p ^ (calendarReplay rate W j rho.val).1) at hweights
  have hanchor : (collectionArgs q ⟨z.val, hc⟩).1.anchor = scoreWeight Q (run Q (W.take rho.val)) := by
    rw [hpay, ha, hweights]
    funext j
    exact hpow j
  have htimeR := complete_record_time rate rewards C_star C_h z.val rho
  have hsig : P.sigma.val = start z.val + rho.val := (congrArg Fin.val htime).symm.trans htimeR
  let H := ReplayWeightStability.episodeHorizon rate.eta.val
  have hgrid : gridBoundary p rate.eta.val P.sigma ≤ P.sigma.val + 1 + H := by
    have hd := Nat.mod_add_div (P.sigma.val + 1) H
    have hm : H * ((P.sigma.val + 1) / H + 1) ≤ P.sigma.val + 1 + H := by
      rw [Nat.mul_succ]
      omega
    exact (Nat.min_le_right _ _).trans hm
  have hshort : h - rho.val ≤ H := by
    rw [hpay, ← hg] at hboundary
    dsimp only [h]
    omega
  intro j
  have he := RecordedEpisodeStability.execute_source_weight_envelope Q
    (run Q (W.take rho.val)) ((W.drop rho.val).take (h - rho.val)) j
    ((List.length_take_le _ _).trans hshort)
  rw [← RecordedEpisodeStability.run_take_eq_execute_drop Q W rho.val h hbh] at he
  rw [hanchor]
  exact ⟨he.1, he.2.1.le⟩

private theorem complete_record_lookup
    (z : BootstrapPrivateRoundStreams.SourceInput p) (k : Fin (records z).length) :
    sourceRecord (records z)[k.val].input.time z = some (records z)[k.val] := by
  have ht := complete_record_time rate rewards C_star C_h z k
  unfold actualRecord
  rw [ite_eq_left (by omega : start z ≤ (records z)[k.val].input.time.val), ht,
    Nat.add_sub_cancel_left, List.getElem?_eq_getElem k.isLt]

/-- Actual query containment and its zero-origin prefix in the same complete
word, including open collection segments with no next invocation. -/
theorem firstInvocation_collection_prefix (t q : Fin p.T) (z : FirstSource t) (htq : t.val < q.val)
    (hcall : CallFree t q.castSucc z.val) (hc : z.val ∈ collectionDomain q) :
    let W := collectionWord q ⟨z.val, hc⟩
    let args := collectionArgs q ⟨z.val, hc⟩
    ∃ (e : ℕ) (seg : Segment rate) (I : Initializer p) (i : Fin seg.records.length) (G : List (RoundInput p.K)),
      segmentAt (records z.val) e = some seg ∧
      e + i.val = q.val - start z.val ∧
      seg.records[i.val] = collectionRecordAt q ⟨z.val, hc⟩ ∧
      seg.context.payload = args.1 ∧
      args.1 = (firstCell t z).selected.view.payload ∧
      seg.context.initializer = some I ∧ I.checkedStart rate = .success seg.context.preLedger ∧
      I.assignment.arm = args.1.assignment.assigned ∧ I.sigma = args.1.sigma.val + 1 ∧
      I.cutoff = start z.val + e + 1 ∧ I.freezeAt = gridBoundary p rate.eta.val args.1.sigma ∧
      ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
      G.length = e + seg.records.length ∧ G = W.take G.length ∧
      (∀ n, n ≤ G.length → numericalPrefix (start z.val + n) z.val = some (G.take n)) := by
  dsimp only
  let R := records z.val
  let h := q.val - start z.val
  obtain ⟨iq, hiq, hqr, hsq⟩ := actualRecord_index rate rewards C_star C_h q z.val _
    (collectionRecord_spec rate rewards C_star C_h q ⟨z.val, hc⟩).1
  have hh : h < R.length := by dsimp only [h]; rw [← hiq]; exact iq.isLt
  have hqrec : R[h] = collectionRecordAt q ⟨z.val, hc⟩ := by
    simpa only [hiq] using hqr
  obtain ⟨b, rb0, _qb0, _beta0, hb, _heq, hchosenB, hpost0, _hbirth0, hpay0⟩ :=
    firstInvocation_installation rate rewards C_star C_h t z
  obtain ⟨P0, rb, _qb, _beta, cell, _native, _hP0len, _hP0map, _hP0pre, _hinit,
      hpost, _hbirth, _hstrict, _hbase, _hcell, _hnative, _hnpayload, _henabled,
      _hbirthPrefix, _hbirthSlots, _hdown, hbranch⟩ :=
    ReferenceCompleteInstallationCollectionPrefixNumericalTruth.actual_later_installation_collection_prefix_numerical_truth
      rate rewards C_star C_h z.val b hchosenB
  have hpayB : rb.payload = (firstCell t z).selected.view.payload := by
    have hp := congrArg storedPayload (hpost.symm.trans hpost0)
    simp only [ReferenceAssignmentPayloadPersistence.storedPayload_live, Option.some.injEq] at hp
    exact hp.trans hpay0
  have hbt := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h t z.val (records z.val)[b.val] hb).2.2.1
  have hbt' := complete_record_time rate rewards C_star C_h z.val b
  rcases hbranch with hterminal | ⟨k, C, hk, _hstate, hClen, _hCmap, _hCtime,
    e, he, heR, _rE, _qE, _hrPayload, hsegment⟩
  · dsimp only [h, R] at hh
    omega
  have hkh : k.val ≤ h := by dsimp only [h]; omega
  have heh : e ≤ h := by
    by_contra hnot
    have hi : h - k.val < (continuingPrefix rate rewards C_star C_h z.val k.val).length := by omega
    have hp := (List.takeWhile_prefix continuingTest (l := R.drop k.val)).getElem hi
    have hm := List.mem_takeWhile_imp (List.getElem_mem hi)
    change continuingTest ((R.drop k.val).takeWhile continuingTest)[h - k.val] = true at hm
    rw [hp, List.getElem_drop] at hm
    have hm' : continuingTest R[h] = true := by
      simpa only [Nat.add_sub_of_le hkh] using hm
    rw [hqrec, collection_not_continuing rate _
      (collectionRecord_spec rate rewards C_star C_h q ⟨z.val, hc⟩).2.2] at hm'
    cases hm'
  rcases hsegment with hterminal | ⟨_heLt, seg, I, l0, Dword, hseg, _hentry,
    hsegPay, hledger, hinit, _hIeq, hstart, harm, hsigma, hcutoff, _hscan,
    _hfreeze, _hbaseI, hchosen, hne, hpart, _hrun, hDlen, _hDmap, _hqueues,
    _hHlen, hGlen, _hGtake, hvR, hprefix, _hRtake, _hpref, _hrest⟩
  · change e = R.length at hterminal
    omega
  have hnonempty : seg.records ≠ [] := by obtain ⟨tail, heq⟩ := hne; rw [heq]; exact List.cons_ne_nil _ _
  have hhseg : h < e + seg.records.length := by
    by_contra hnot
    have hv : e + seg.records.length < R.length := by omega
    have hf := segment_boundary_not_continuing rate R e seg hseg hnonempty hv
    obtain ⟨_hle, _hfields, _hchoices, saved, _hend, _hcursor, _during, _hshape,
        _hpre, _hnotlater, _hduring, _hpending, _hnodup, _hw, hboundary⟩ :=
      ReferenceCompleteCollectionBoundaryHistory.internal_complete_collection_boundary_history
        rate rewards C_star C_h z.val e seg hseg hnonempty hchosen
    rcases hboundary with hend | ⟨hv', _hstate, hcoord, htime, _hdrop, _hlater⟩
    · change e + seg.records.length = R.length at hend
      omega
    let v : Fin R.length := ⟨e + seg.records.length, hv⟩
    let date := R[v.val].input.time
    have hdate : date.val = start z.val + (e + seg.records.length) := htime
    have htdate : t.val < date.val := by omega
    have hdateq : date.val ≤ q.val := by dsimp only [h] at hnot; omega
    have hlookup := complete_record_lookup rate rewards C_star C_h z.val v
    have hcollection : z.val ∈ collectionDomain date := by
      by_cases heq : date = q
      · simpa only [heq] using hc
      · have hnocall := hcall date htdate (by change date.val < q.val; exact lt_of_le_of_ne hdateq (fun he => heq (Fin.ext he)))
        rcases noncall_phase_coverage rate rewards C_star C_h date z.val (by omega) hnocall with hlive | hcol
        · obtain ⟨regs, owned, base, _started, hin, _⟩ :=
            continuingRecord_frame rate rewards C_star C_h date ⟨z.val, hlive⟩
          have hr : liveRecord date ⟨z.val, hlive⟩ = R[v.val] :=
            Option.some.inj ((continuingSourceCell_spec rate rewards C_star C_h date ⟨z.val, hlive⟩).1.symm.trans hlookup)
          rw [hr, hcoord] at hin
          cases hin
        · exact hcol
    have hr : R[v.val] = collectionRecordAt date ⟨z.val, hcollection⟩ :=
      Option.some.inj (hlookup.symm.trans (collectionRecord_spec rate rewards C_star C_h date ⟨z.val, hcollection⟩).1)
    have ht := collectionRecord_continuing rate rewards C_star C_h date ⟨z.val, hcollection⟩
      seg.context.payload seg.final saved (by rw [← hr]; exact hcoord)
    rw [← hr] at ht
    rw [hf] at ht
    cases ht
  let i : Fin seg.records.length := ⟨h - e, by omega⟩
  have hi : e + i.val = h := by dsimp only [i]; omega
  have hget : seg.records[i.val] = collectionRecordAt q ⟨z.val, hc⟩ := by
    have hp : seg.records <+: R.drop e := ⟨seg.remaining, hpart⟩
    have hid : i.val < (R.drop e).length := i.isLt.trans_le hp.length_le
    calc seg.records[i.val] = (R.drop e)[i.val] := hp.getElem i.isLt
      _ = R[e + i.val] := by rw [List.getElem_drop]
      _ = R[h] := by congr 1
      _ = collectionRecordAt q ⟨z.val, hc⟩ := hqrec
  let G := P0 ++ [cell] ++ C ++ Dword
  have hG : G = (collectionWord q ⟨z.val, hc⟩).take G.length := by
    have hp := hprefix G.length (by dsimp only [G]; omega)
    rw [List.take_length] at hp
    have hw := actualOriginalWord_prefix
      rate rewards C_star C_h z.val (collection_launch rate rewards C_star C_h q ⟨z.val, hc⟩)
      G.length (by dsimp only [G]; omega)
    exact Option.some.inj (hp.symm.trans hw)
  have hpayq := firstInvocation_collectionPayload rate rewards C_star C_h t q z htq hcall hc
  refine ⟨e, seg, I, i, G, hseg, hi, hget, hsegPay.trans (hpayB.trans hpayq.symm), hpayq,
    hinit, ?_, ?_, ?_, hcutoff, ?_, hchosen, hGlen, hG, ?_⟩
  · simpa only [hledger] using hstart
  · simpa only [hpayq, ← hpayB] using harm
  · simpa only [hpayq, ← hpayB] using hsigma
  · have hg := initialized_choice_grid rate seg.entry.input seg.context I (segment_choice rate R e seg hseg) hinit
    simpa only [hsegPay, hpayB, ← hpayq] using hg
  · intro n hn
    exact hprefix n (by dsimp only [G] at hn; omega)

/-- The all-arm envelope supplies the native FAST law for every evolved logical set. -/
theorem firstInvocation_collection_fastLaw (t q : Fin p.T) (z : FirstSource t) (htq : t.val < q.val)
    (hcall : CallFree t q.castSucc z.val) (hc : z.val ∈ collectionDomain q)
    (hboundary : q.val + 1 < gridBoundary p rate.eta.val (collectionArgs q ⟨z.val, hc⟩).1.sigma)
    (hclear : (collectionPRE q ⟨z.val, hc⟩).overflow = false) :
    let P := (collectionArgs q ⟨z.val, hc⟩).1
    let weight := scoreWeight Q (collectionPRE q ⟨z.val, hc⟩)
    ∃ (hlo : ∀ j, P.anchor j ≤ weight j) (hhi : ∀ j, weight j ≤ 2 * P.anchor j), ∀ (U : SlowSet p) (j : FastArm U),
        collectionFastMass rate P.anchor weight P.anchor_pos (RecordedSlowRefresh.scoreWeight_pos Q _) U j =
          CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property rate.sourceCap
            P.anchor weight P.anchor_pos (RecordedSlowRefresh.scoreWeight_pos Q _) hlo hhi U j := by
  have henv := firstInvocation_collection_envelope rate rewards C_star C_h t q z htq hcall hc hboundary hclear
  exact ⟨fun j => (henv j).1, fun j => (henv j).2,
    collectionFastMass_eq_qGamma rate _ _ _ _ (fun j => (henv j).1) (fun j => (henv j).2)⟩

/-- Surviving nonrenewed prefixes retain their actual source, complete word,
produced history, LIVE seed and installed collection payload. -/
theorem nonrenewed_generated_alignment (control0 : PhysicalControl) (u t q : Fin p.T) (htq : t.val < q.val)
    (wv : (ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t ×
      ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) ×
      AssignmentParameterFibreKernel.AssignmentVector p) :
    let d := nonrenewedTransition rate rewards C_star C_h control0 u t wv
    let z := nonrenewedFirstSource rate rewards C_star C_h t u wv.1.1 wv.2
    let hz := firstCall_insertVector_mem rate rewards C_star C_h u t wv.1.1.val wv.1.1.property.1 wv.2
    let hl := firstCall_launch rate rewards C_star C_h u t z.val hz
    let W := originalWord z.val hl
    let S := run Q (W.take (q.val - start z.val))
    match postPrefix t q.castSucc d wv.1.2 with
    | none => True
    | some s =>
        CallFree t q.castSucc z.val ∧
        prefixNumerical rate rewards C_star C_h q.castSucc z.val = some S ∧
        (records z.val).map (cell0 rate) = W.map some ∧
        postHistory d <+: s.2 ∧
        (s.2.Pairwise (fun e f => e.time.val < f.time.val) ∧ ∀ e ∈ s.2, e.time.val < q.val) ∧
        (∀ hlive : z.val ∈ liveDomain q, S.overflow = false →
          s.1 = (liveCell q ⟨z.val, hlive⟩).selected.view.payload.slowSet ∧
          ∀ j : FastArm (liveCell q ⟨z.val, hlive⟩).selected.view.payload.slowSet,
            (liveCell q ⟨z.val, hlive⟩).selected.view.complementWeights j = scoreWeight Q S j.val) ∧
        (∀ hc : z.val ∈ collectionDomain q,
          let P := (collectionArgs q ⟨z.val, hc⟩).1
          let weight := scoreWeight Q S
          P = (firstCell t z).selected.view.payload ∧
          (∃ (e : ℕ) (seg : Segment rate) (i : Fin seg.records.length), segmentAt (records z.val) e = some seg ∧
            e + i.val = q.val - start z.val ∧
            seg.records[i.val] = collectionRecordAt q ⟨z.val, hc⟩ ∧
            seg.context.payload = P) ∧
          (q.val + 1 < gridBoundary p rate.eta.val P.sigma → S.overflow = false →
            ∃ (hlo : ∀ j, P.anchor j ≤ weight j) (hhi : ∀ j, weight j ≤ 2 * P.anchor j),
              ∀ (U : SlowSet p) (j : FastArm U),
                collectionFastMass rate P.anchor weight P.anchor_pos (RecordedSlowRefresh.scoreWeight_pos Q _) U j =
                  CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property rate.sourceCap
                    P.anchor weight P.anchor_pos (RecordedSlowRefresh.scoreWeight_pos Q _) hlo hhi U j)) := by
  dsimp only
  let d := nonrenewedTransition rate rewards C_star C_h control0 u t wv
  let z := nonrenewedFirstSource rate rewards C_star C_h t u wv.1.1 wv.2
  have hz := firstCall_insertVector_mem rate rewards C_star C_h u t wv.1.1.val wv.1.1.property.1 wv.2
  have hl := firstCall_launch rate rewards C_star C_h u t z.val hz
  have hi := nonrenewed_initialization rate rewards C_star C_h control0 u t wv
  cases hp : postPrefix t q.castSucc d wv.1.2 with
  | none => trivial
  | some s =>
      have hcall := postInvocationPrefix_some_noCall rate rewards C_star C_h t q.castSucc d wv.1.2 s hp
      have hd := firstCall_dates rate rewards C_star C_h u t z.val hz
      have hst : start z.val ≤ q.val := hd.1.trans (hd.2.1.trans htq).le
      have hcal : noncallRun t z.val wv.1.2 (postSeed rate d, postHistory d) q.val = some s := hp
      have hcal' := hcal
      rw [hi.2.1] at hcal'
      have hchron := firstInvocation_generated_chronology rate rewards C_star C_h control0 u t z hz
        wv.1.2 _ q.castSucc s htq hcal'
      refine ⟨hcall, prefixNumerical_actualWord rate rewards C_star C_h q.castSucc z.val hl hst,
        originalWord_record_map rate rewards C_star C_h z.val hl, ?_, hchron.2, ?_, ?_⟩
      · rw [hi.2.1]
        exact hchron.1
      · intro hlive hclear
        exact ⟨firstInvocation_generated_live_seed rate rewards C_star C_h control0 u t q z hz htq
          wv.1.2 (wv.1.2 (t, 1)) s hcal' hlive hclear,
          firstInvocation_live_complement rate rewards C_star C_h t q z htq hcall hlive hclear⟩
      · intro hc
        obtain ⟨e, seg, I, i, G, hseg, hi, hrecord, hpay, hpost, _⟩ :=
          firstInvocation_collection_prefix rate rewards C_star C_h t q z htq hcall hc
        exact ⟨hpost, ⟨e, seg, i, hseg, hi, hrecord, hpay⟩,
          firstInvocation_collection_fastLaw rate rewards C_star C_h t q z htq hcall hc⟩

/-- The same deterministic alignment on the literal renewal lift. Its
produced residual consumes `(t,0)` after the distinct initial `(t,1)` draw. -/
theorem renewed_generated_alignment (control0 : PhysicalControl) (u t q : Fin p.T) (htq : t.val < q.val)
    (wv : ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift rate rewards C_star C_h u t) :
    let d := renewedTransition rate rewards C_star C_h control0 u t wv
    let source := (ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t wv).2
    let z := renewedFirstSource rate rewards C_star C_h t u source
    let hl := firstCall_launch rate rewards C_star C_h u t z.val source.property.1
    let W := originalWord z.val hl
    let S := run Q (W.take (q.val - start z.val))
    match postPrefix t q.castSucc d wv.1.2 with
    | none => True
    | some s =>
        CallFree t q.castSucc z.val ∧
        prefixNumerical rate rewards C_star C_h q.castSucc z.val = some S ∧
        (records z.val).map (cell0 rate) = W.map some ∧
        postHistory d <+: s.2 ∧
        (s.2.Pairwise (fun e f => e.time.val < f.time.val) ∧ ∀ e ∈ s.2, e.time.val < q.val) ∧
        (∀ hlive : z.val ∈ liveDomain q, S.overflow = false →
          s.1 = (liveCell q ⟨z.val, hlive⟩).selected.view.payload.slowSet ∧
          ∀ j : FastArm (liveCell q ⟨z.val, hlive⟩).selected.view.payload.slowSet,
            (liveCell q ⟨z.val, hlive⟩).selected.view.complementWeights j = scoreWeight Q S j.val) ∧
        (∀ hc : z.val ∈ collectionDomain q,
          let P := (collectionArgs q ⟨z.val, hc⟩).1
          let weight := scoreWeight Q S
          P = (firstCell t z).selected.view.payload ∧
          (∃ (e : ℕ) (seg : Segment rate) (i : Fin seg.records.length), segmentAt (records z.val) e = some seg ∧
            e + i.val = q.val - start z.val ∧
            seg.records[i.val] = collectionRecordAt q ⟨z.val, hc⟩ ∧
            seg.context.payload = P) ∧
          (q.val + 1 < gridBoundary p rate.eta.val P.sigma → S.overflow = false →
            ∃ (hlo : ∀ j, P.anchor j ≤ weight j) (hhi : ∀ j, weight j ≤ 2 * P.anchor j),
              ∀ (U : SlowSet p) (j : FastArm U),
                collectionFastMass rate P.anchor weight P.anchor_pos (RecordedSlowRefresh.scoreWeight_pos Q _) U j =
                  CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property rate.sourceCap
                    P.anchor weight P.anchor_pos (RecordedSlowRefresh.scoreWeight_pos Q _) hlo hhi U j)) := by
  dsimp only
  let d := renewedTransition rate rewards C_star C_h control0 u t wv
  let source := (ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t wv).2
  let z := renewedFirstSource rate rewards C_star C_h t u source
  have hz := source.property.1
  have hl := firstCall_launch rate rewards C_star C_h u t z.val hz
  have hi := renewed_initialization rate rewards C_star C_h control0 u t wv
  cases hp : postPrefix t q.castSucc d wv.1.2 with
  | none => trivial
  | some s =>
      have hcall := postInvocationPrefix_some_noCall rate rewards C_star C_h t q.castSucc d wv.1.2 s hp
      have hd := firstCall_dates rate rewards C_star C_h u t z.val hz
      have hst : start z.val ≤ q.val := hd.1.trans (hd.2.1.trans htq).le
      have hcal : noncallRun t z.val wv.1.2 (postSeed rate d, postHistory d) q.val = some s := hp
      have hcal' := hcal
      rw [hi.2.1] at hcal'
      have hchron := firstInvocation_generated_chronology rate rewards C_star C_h control0 u t z hz
        wv.1.2 _ q.castSucc s htq hcal'
      refine ⟨hcall, prefixNumerical_actualWord rate rewards C_star C_h q.castSucc z.val hl hst,
        originalWord_record_map rate rewards C_star C_h z.val hl, ?_, hchron.2, ?_, ?_⟩
      · rw [hi.2.1]
        exact hchron.1
      · intro hlive hclear
        exact ⟨firstInvocation_generated_live_seed rate rewards C_star C_h control0 u t q z hz htq
          wv.1.2 (wv.1.2 (t, 0)) s hcal' hlive hclear,
          firstInvocation_live_complement rate rewards C_star C_h t q z htq hcall hlive hclear⟩
      · intro hc
        obtain ⟨e, seg, I, i, G, hseg, hi, hrecord, hpay, hpost, _⟩ :=
          firstInvocation_collection_prefix rate rewards C_star C_h t q z htq hcall hc
        exact ⟨hpost, ⟨e, seg, i, hseg, hi, hrecord, hpay⟩,
          firstInvocation_collection_fastLaw rate rewards C_star C_h t q z htq hcall hc⟩


end Bandits.Support.ReferencePostInvocationGeneratedAlignment
