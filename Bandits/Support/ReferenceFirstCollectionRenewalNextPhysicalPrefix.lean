/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix
public import Bandits.Support.ReferenceFirstReplacementNextFollowerStep
public import Bandits.Support.ReferenceFirstReplacementCutoffPreparedBoundary

import Mathlib.Tactic

/-!
# The first physical date after the first renewal

The original complete suffix supplies the next date, including absent readouts.
The numerical queue run is the analytical stopped run; no equality with the
physical queues or the coordinator's scores is asserted.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-290`,
`sources/zip4/manuscript/06_interruptions.tex:9-70,246-295,355-426`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section
noncomputable section

open scoped Classical
open Bandits.Support ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix

open ReferenceFirstCollectionRenewalIncomingQueuePrefix
open ReferenceCompleteFirstPhaseObservationRecovery
open ReferenceCompleteObservationPrefixInformation
open ReferenceCompleteNumericalBranchObservation
open ReferenceFirstCollectionRenewalSourceCurrentPrefix

abbrev Source {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalSourceCurrentPrefix.Source rate rewards C_star C_h u t

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

local notation "Z" => Source rate rewards C_star C_h u t

/-- The full numerical prefix, including the actual renewal round. -/
def currentCells (z : Z) : List (RecordedQueueRun.RoundInput p.K) :=
  pastCells rate rewards C_star C_h u t z ++
    [ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell rate rewards C_star C_h u t z]

/-- The same stopped queue state after the complete current prefix. -/
def currentState (z : Z) : RecordedQueueRun.RunState p.K :=
  RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (currentCells rate rewards C_star C_h u t z)

/-- The next calendar position exists precisely when the action horizon continues. -/
def nextIndex (z : Z) (hq : t.val + 1 < p.T) :
    Fin (sourceRecords rate rewards C_star C_h u t z).length :=
  ⟨t.val - start rate rewards C_star C_h u t z + 1, by
    rw [sourceRecords_length]
    have hb := actual_boundaries rate rewards C_star C_h u t z
    omega⟩

/-- The first next record, never a search for the next successful readout. -/
def nextRecord (z : Z) (hq : t.val + 1 < p.T) :=
  (sourceRecords rate rewards C_star C_h u t z).get
    (nextIndex rate rewards C_star C_h u t z hq)

theorem nextRecord_lookup (z : Z) (hq : t.val + 1 < p.T) :
    (sourceRecords rate rewards C_star C_h u t z)[
      t.val - start rate rewards C_star C_h u t z + 1]? =
        some (nextRecord rate rewards C_star C_h u t z hq) :=
  List.getElem?_eq_getElem (nextIndex rate rewards C_star C_h u t z hq).isLt

/-- Calendar date and all original physical input fields come from the run. -/
theorem nextRecord_fields (z : Z) (hq : t.val + 1 < p.T) :
    let r := nextRecord rate rewards C_star C_h u t z hq
    r.input.time = (⟨t.val + 1, hq⟩ : Fin p.T) ∧
      r.input.rows = z.val.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z.val ∧
      r.input.rewards = rewards := by
  obtain ⟨_, _, hr⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z.val (nextIndex rate rewards C_star C_h u t z hq)
  change nextRecord rate rewards C_star C_h u t z hq = _ at hr
  dsimp only
  rw [hr]
  refine ⟨Fin.ext ?_, rfl, rfl, rfl⟩
  have hb := actual_boundaries rate rewards C_star C_h u t z
  change start rate rewards C_star C_h u t z +
    (t.val - start rate rewards C_star C_h u t z + 1) = t.val + 1
  omega

/-- Adjacent records share the actual output/input boundary. -/
theorem nextRecord_state (z : Z) (hq : t.val + 1 < p.T) :
    (nextRecord rate rewards C_star C_h u t z hq).input.state =
      (callRecord rate rewards C_star C_h u t z).output.next := by
  let k := t.val - start rate rewards C_star C_h u t z
  obtain ⟨_, _, h0⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z.val
    ⟨k, call_index_lt rate rewards C_star C_h u t z⟩
  obtain ⟨_, _, h1⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z.val (nextIndex rate rewards C_star C_h u t z hq)
  change callRecord rate rewards C_star C_h u t z = _ at h0
  change nextRecord rate rewards C_star C_h u t z hq = _ at h1
  rw [h0, h1]
  exact ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
    _ z.val.1.2 _ rewards _ k _ _

private theorem actual_birth (z : Z) :
    ReferenceCollectionPhaseHistory.laterChosen
      (callRecord rate rewards C_star C_h u t z).input = true := by
  obtain ⟨d, consistent, output, hlocal, _hstart, _hvector, _hreconstruction,
    _hslow, _hslowSet, _hinstalledPayload, _hinstalledVector, _hinstalledReconstruction,
    _hanchor, _hqueues, _hretained, selection, _hchoice, hdispatch, hprep, hcoord,
    _harm, _hpost⟩ :=
    ReferenceFirstCollectionRenewalSampleInstallation.actual_renewal_call_installation
      rate rewards C_star C_h u t z
  have heq := actual_call_record_eq rate rewards C_star C_h u t z d
  rw [← heq]
  unfold ReferenceCollectionPhaseHistory.laterChosen
  rw [← hprep, hcoord, hdispatch]

/-- The first-replacement index is the original renewal date's suffix index. -/
theorem firstReplacementIndex_eq (z : Z) :
    let R := sourceRecords rate rewards C_star C_h u t z
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length =
      t.val - start rate rewards C_star C_h u t z := by
  obtain ⟨d⟩ := ReferenceFirstCollectionRenewalAuxiliaryLaw.actual_renewal_call_parameters
    rate rewards C_star C_h u t z
  have heq := actual_call_record_eq rate rewards C_star C_h u t z d
  have hchosen := actual_birth rate rewards C_star C_h u t z
  rw [← heq] at hchosen
  have hrecord := ReferenceFirstCollectionRenewalRecordingFeedback.actual_call_first_replacement_record
    rate rewards C_star C_h u t z d hchosen
  have htime := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate z.val rewards C_star C_h _ d.record hrecord
  rw [d.time_eq] at htime
  dsimp only at htime ⊢
  change t.val = start rate rewards C_star C_h u t z + _ at htime
  unfold sourceRecords
  omega

private theorem birth_shape (z : Z) :
    match (callRecord rate rewards C_star C_h u t z).output.preparation.coordinator with
    | .collection _ _ _ _ (.laterChosen ..) => True
    | _ => False := by
  have hb := actual_birth rate rewards C_star C_h u t z
  unfold ReferenceCollectionPhaseHistory.laterChosen at hb
  have hp : (callRecord rate rewards C_star C_h u t z).output.preparation =
      ReferenceActivePhysicalStep.prepare (callRecord rate rewards C_star C_h u t z).input := by
    rw [(callRecord rate rewards C_star C_h u t z).output_eq]
    rfl
  rw [← hp] at hb
  cases h : (callRecord rate rewards C_star C_h u t z).output.preparation.coordinator
    <;> simp only [h] at hb ⊢ <;> try contradiction
  rename_i outcome
  cases outcome <;> simp_all

/-- The two actual next readouts. Absence is retained at this exact date. -/
def nextLive (z : Z) (hq : t.val + 1 < p.T) :=
  ReferenceLaterLiveNumericalReadout.laterLiveReadout
    (start rate rewards C_star C_h u t z) (nextRecord rate rewards C_star C_h u t z hq)

def nextCollection (z : Z) (hq : t.val + 1 < p.T) :=
  ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
    (start rate rewards C_star C_h u t z) (nextRecord rate rewards C_star C_h u t z hq)

/-- Literal union of the disjoint numerical projections, with no completion. -/
def nextCell (z : Z) (hq : t.val + 1 < p.T) :=
  (nextLive rate rewards C_star C_h u t z hq).or
    (nextCollection rate rewards C_star C_h u t z hq)

/-- The admitted next-follower producer is applied at the actual first next
record, on its continuing constructor, with the same installed assignment. -/
theorem next_continuing_present (z : Z) (hq : t.val + 1 < p.T) :
    match (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator with
    | .live _ _ _ (.continuingChosen ..) =>
        (nextLive rate rewards C_star C_h u t z hq).isSome = true
    | _ => True := by
  have hn := ReferenceFirstReplacementNextFollowerStep.complete_first_replacement_next_continuing_readout
    rate z.val rewards C_star C_h
  have hi := firstReplacementIndex_eq rate rewards C_star C_h u t z
  dsimp only [sourceRecords] at hi
  dsimp only at hn
  have h0 : (sourceRecords rate rewards C_star C_h u t z)[
      t.val - start rate rewards C_star C_h u t z]? =
        some (callRecord rate rewards C_star C_h u t z) :=
    List.getElem?_eq_getElem (call_index_lt rate rewards C_star C_h u t z)
  dsimp only [sourceRecords] at h0
  simp only [hi, h0] at hn
  have hb := birth_shape rate rewards C_star C_h u t z
  cases hbirth : (callRecord rate rewards C_star C_h u t z).output.preparation.coordinator
    <;> simp only [hbirth] at hb hn
  rename_i outcome
  cases outcome <;> try contradiction
  have h1 := nextRecord_lookup rate rewards C_star C_h u t z hq
  dsimp only [sourceRecords] at h1
  simp only [h1] at hn
  cases hnext : (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator
    <;> try trivial
  rename_i outcome
  cases outcome <;> try trivial
  simp only [hnext] at hn
  obtain ⟨_selected, _hselected, _hpayload, _hsigma, _hlive, _hfollowers,
    cell, hread, _hcellPayload, _harrival, _howner⟩ := hn
  change (ReferenceLaterLiveNumericalReadout.laterLiveReadout
    (start rate rewards C_star C_h u t z) (nextRecord rate rewards C_star C_h u t z hq)).isSome = true
  change ReferenceLaterLiveNumericalReadout.laterLiveReadout
    (start rate rewards C_star C_h u t z) (nextRecord rate rewards C_star C_h u t z hq) =
      some cell.input at hread
  rw [hread]
  rfl

/-- At an immediate cutoff the continuing tail is empty. The admitted cutoff
boundary therefore supplies the actual next PREPARE states. -/
theorem next_cutoff_present (z : Z) (hq : t.val + 1 < p.T) :
    match (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator with
    | .live _ _ _ (.cutoffChosen ..) =>
        (nextCollection rate rewards C_star C_h u t z hq).isSome = true
    | _ => True := by
  have hbnd := ReferenceFirstReplacementCutoffPreparedBoundary.complete_first_replacement_cutoff_follower_boundary
    rate z.val rewards C_star C_h
  have hi := firstReplacementIndex_eq rate rewards C_star C_h u t z
  dsimp only [sourceRecords] at hi
  dsimp only at hbnd
  have h0 : (sourceRecords rate rewards C_star C_h u t z)[
      t.val - start rate rewards C_star C_h u t z]? =
        some (callRecord rate rewards C_star C_h u t z) :=
    List.getElem?_eq_getElem (call_index_lt rate rewards C_star C_h u t z)
  dsimp only [sourceRecords] at h0
  simp only [hi, h0] at hbnd
  have hb := birth_shape rate rewards C_star C_h u t z
  cases hbirth : (callRecord rate rewards C_star C_h u t z).output.preparation.coordinator
    <;> simp only [hbirth] at hb hbnd
  rename_i outcome
  cases outcome <;> try contradiction
  cases hnext : (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator
    <;> try trivial
  rename_i registers owned base outcome
  cases outcome <;> try trivial
  have htail : ReferenceFirstReplacementLiveFollowerPrefix.continuingTail
      (sourceRecords rate rewards C_star C_h u t z)
      (t.val - start rate rewards C_star C_h u t z) = [] := by
    apply List.takeWhile_eq_nil_iff.mpr
    intro hlen
    have hget : ((sourceRecords rate rewards C_star C_h u t z).drop
        (t.val - start rate rewards C_star C_h u t z + 1)).get ⟨0, hlen⟩ =
          nextRecord rate rewards C_star C_h u t z hq := by
      have he := List.getElem?_eq_getElem hlen
      simp only [List.getElem?_drop, Nat.add_zero,
        nextRecord_lookup rate rewards C_star C_h u t z hq] at he
      exact (Option.some.inj he).symm
    rw [hget]
    simp only [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hnext,
      Bool.false_eq_true, not_false_eq_true]
  have h1 := nextRecord_lookup rate rewards C_star C_h u t z hq
  dsimp only [sourceRecords] at htail h1
  simp only [htail, List.length_nil, Nat.add_zero, h1] at hbnd
  simp only [hnext] at hbnd
  obtain ⟨_hnoncontinuing, hregisters, _htime, _hindex, _hrows, _hselected,
    _hrewards, _hsigma, hbase, _hcutoff, _hgrid, _htrigger,
    selected, _hselection, _hpayload, _hpending, _hselectedCutoff, hfollowers⟩ := hbnd
  apply (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain
    (start rate rewards C_star C_h u t z) (nextRecord rate rewards C_star C_h u t z hq)).2
  constructor
  · intro i
    obtain ⟨old, memory, _hinput, _hdomain, _hbound, _hzero, _haccepted,
      _hoccupied, _hdecision, _hstart, hprepared, _⟩ := hfollowers i
    simp only [hprepared]
  · simp only [hnext]
    rw [hregisters]
    exact hbase

private theorem livePostChoice_phase
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
    match (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).configuration with
    | .live .. => True
    | .dagger => True
    | _ => False := by
  cases hrecording : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared registers started) with
  | none => simp [ReferenceActivePhysicalStep.livePostChoice, hrecording,
      ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
    cases hservice : CoordinatorLiveServiceFinish.servicePass registers owned recording with
    | error reason => simp [ReferenceActivePhysicalStep.livePostChoice, hrecording,
        hservice, ReferenceActivePhysicalStep.coordinatorFailure]
    | ok serviced =>
      cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate registers.payload started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          x.time x.row prepared.coordinatorObservation with
      | none => simp [ReferenceActivePhysicalStep.livePostChoice, hrecording,
          hservice, hconfirmation, ReferenceActivePhysicalStep.coordinatorFailure]
      | some pending =>
        cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock pending x.row
          <;> simp [ReferenceActivePhysicalStep.livePostChoice, hrecording, hservice,
            hconfirmation, hfinish, ReferenceActivePhysicalStep.coordinatorFailure]

/-- Checked tails may kill the coordinator, but cannot turn the newly
installed live assignment into a first call or a collection state. -/
theorem nextRecord_input_phase (z : Z) (hq : t.val + 1 < p.T) :
    match (nextRecord rate rewards C_star C_h u t z hq).input.state.coordinator with
    | .live .. => True
    | .dagger => True
    | _ => False := by
  obtain ⟨d, _consistent, _output, _hlocal, _hstart, _hvector, _hreconstruction,
    _hslow, _hslowSet, _hinstalledPayload, _hinstalledVector, _hinstalledReconstruction,
    _hanchor, _hqueues, _hretained, _selection, _hchoice, _hdispatch, _hprep, _hcoord,
    _harm, _hcoordinator, hnext⟩ :=
    ReferenceFirstCollectionRenewalSampleInstallation.actual_renewal_call_installation
      rate rewards C_star C_h u t z
  rw [nextRecord_state, ← actual_call_record_eq rate rewards C_star C_h u t z d, hnext]
  exact livePostChoice_phase rate _ _ _ _ _

/-- This is the exhaustive actual next phase cut, before any success test. -/
theorem nextRecord_dispatch_phase (z : Z) (hq : t.val + 1 < p.T) :
    match (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator with
    | .live .. => True
    | .dagger => True
    | _ => False := by
  let r := nextRecord rate rewards C_star C_h u t z hq
  have hphase := nextRecord_input_phase rate rewards C_star C_h u t z hq
  have hp : r.output.preparation.coordinator = ReferenceActivePhysicalStep.dispatch r.input := by
    rw [r.output_eq]
    rfl
  dsimp only [r] at hp
  rw [hp]
  unfold ReferenceActivePhysicalStep.dispatch
  cases hs : (nextRecord rate rewards C_star C_h u t z hq).input.state.coordinator
    <;> simp only [hs] at hphase
  · simp only [CoordinatorRoundDispatch.dispatch]
    cases CoordinatorRoundDispatch.dispatchLive _ <;> trivial
  · trivial

private theorem dispatch_live_origin (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    match ReferenceActivePhysicalStep.dispatch x with
    | .live registers owned base _ => x.state.coordinator = .live registers owned base
    | _ => True := by
  unfold ReferenceActivePhysicalStep.dispatch
  cases hs : x.state.coordinator with
  | first => trivial
  | live registers owned base =>
    simp only [CoordinatorRoundDispatch.dispatch]
    cases CoordinatorRoundDispatch.dispatchLive _ <;> rfl
  | collection payload ledger saved =>
    by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
    · simp only [dite_eq_left hc, CoordinatorRoundDispatch.dispatch]
      cases CoordinatorRoundDispatch.dispatchCollection _ <;> trivial
    · simp only [dite_eq_right hc]
  | dagger => trivial

/-- Actual run clocks rule out the clock-failure constructor, without
claiming follower, queue, or later-tail success. -/
theorem nextRecord_no_clockFailure (z : Z) (hq : t.val + 1 < p.T) :
    match (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator with
    | .live _ _ _ (.clockFailure ..) => False
    | _ => True := by
  have hclock := ReferenceFirstReplacementNextFollowerStep.complete_suffix_record_clock
    rate z.val rewards C_star C_h (nextIndex rate rewards C_star C_h u t z hq)
  have horigin := dispatch_live_origin rate (nextRecord rate rewards C_star C_h u t z hq).input
  have hd : ReferenceActivePhysicalStep.dispatch
      (nextRecord rate rewards C_star C_h u t z hq).input =
        (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator := by
    rw [(nextRecord rate rewards C_star C_h u t z hq).output_eq]
    rfl
  rw [hd] at horigin
  cases hnext : (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator
    <;> try trivial
  rename_i registers owned base outcome
  cases outcome <;> try trivial
  rename_i failure hfailure
  simp only [hnext] at horigin
  exact ReferenceCoordinatorClockDomains.live_dispatch_no_clockFailure
    registers owned base horigin hclock failure hfailure

/-- A surviving next live dispatch retains the exact installation in the
actual renewal record, including its queues, rates, vector, and anchor. -/
theorem nextRecord_installed_payload (z : Z) (hq : t.val + 1 < p.T) :
    match (callRecord rate rewards C_star C_h u t z).output.preparation.coordinator with
    | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
      match (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator with
      | .live registers _ _ _ => registers.payload = installed.registers.payload
      | _ => True
    | _ => False := by
  have hb := birth_shape rate rewards C_star C_h u t z
  cases hbirth : (callRecord rate rewards C_star C_h u t z).output.preparation.coordinator
    <;> simp only [hbirth] at hb ⊢
  rename_i payload ledger clock cutoff outcome
  cases outcome <;> try contradiction
  rename_i core consistent started hstart instruction hinstruction output hlocal clockData installed selection
  have hselected := wholeCell_numerical rate rewards C_star C_h u t z
  obtain ⟨_henabled, selected0, hsel0, _hreward, _hrate⟩ := hselected
  have hnext0 : (callRecord rate rewards C_star C_h u t z).output.next.coordinator =
      (ReferenceActivePhysicalStep.livePostChoice
        (callRecord rate rewards C_star C_h u t z).output.preparation
        installed.registers installed.ownedRegisters installed.retainedBaseScore started).configuration := by
    have he : (callRecord rate rewards C_star C_h u t z).output.next.coordinator =
        (callRecord rate rewards C_star C_h u t z).output.preparation.observeCoordinator.configuration := by
      rw [(callRecord rate rewards C_star C_h u t z).output_eq]
      rfl
    rw [he]
    unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator
    rw [dite_eq_right (by rw [hsel0]; exact Option.some_ne_none _), hbirth]
  have hframe := ReferenceAssignmentPayloadPersistence.livePostChoice_payload_frame
    (callRecord rate rewards C_star C_h u t z).output.preparation
    installed.registers installed.ownedRegisters installed.retainedBaseScore started
  rw [← hnext0] at hframe
  have horigin := dispatch_live_origin rate (nextRecord rate rewards C_star C_h u t z hq).input
  have hd : ReferenceActivePhysicalStep.dispatch
      (nextRecord rate rewards C_star C_h u t z hq).input =
        (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator := by
    rw [(nextRecord rate rewards C_star C_h u t z hq).output_eq]
    rfl
  rw [hd] at horigin
  cases hnext : (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator
    <;> try trivial
  rename_i registers owned base outcome
  simp only [hnext] at horigin
  have hstored : ReferenceAssignmentPayloadPersistence.storedPayload
      (callRecord rate rewards C_star C_h u t z).output.next.coordinator =
        some registers.payload := by
    rw [← nextRecord_state rate rewards C_star C_h u t z hq, horigin]
    rfl
  rcases hframe with hnone | hsame
  · rw [hstored] at hnone
    cases hnone
  · exact Option.some.inj (hstored.symm.trans hsame)

private theorem live_baseline_zero
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (s : ℕ) (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some c) :
    ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c := by
  obtain ⟨selected, ho, hselection, hbase, hlive, hcell⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_some s r c hc
  have hz : 0 < selected.view.payload.sigma.val := by omega
  unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
  simp only [hselection, hz, hlive, and_self, ite_true, dite_eq_left ho]
  exact congrArg some hcell.symm

private theorem collection_baseline_zero
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (s : ℕ) (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s r = some c) :
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c := by
  have hd := (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain s r).mp
    (by rw [hc]; rfl)
  unfold ReferenceLaterCollectionArrivalReadout.laterCollectionReadout at hc ⊢
  simp only [dite_eq_left hd.1] at hc ⊢
  cases hcut : r.output.preparation.coordinator <;> simp only [hcut] at hd hc ⊢ <;> try contradiction
  · rename_i outcome
    cases outcome <;> simp_all
    omega
  · rename_i outcome
    cases outcome <;> simp_all

private theorem collection_none_of_live
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (b : ℕ) (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceLaterLiveNumericalReadout.laterLiveReadout b r = some c) :
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout b r = none := by
  cases hh : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout b r with
  | none => rfl
  | some other =>
    exact False.elim (readouts_disjoint rate b r ⟨by rw [hc]; rfl, by rw [hh]; rfl⟩)

private theorem live_none_of_collection
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (b : ℕ) (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout b r = some c) :
    ReferenceLaterLiveNumericalReadout.laterLiveReadout b r = none := by
  cases hh : ReferenceLaterLiveNumericalReadout.laterLiveReadout b r with
  | none => rfl
  | some other =>
    exact False.elim (readouts_disjoint rate b r ⟨by rw [hh]; rfl, by rw [hc]; rfl⟩)

/-- The actual next dispatch determines its canonical cell. The complementary
readout is absent at both baselines; failures have two absent readouts. -/
theorem nextDate_readouts (z : Z) (hq : t.val + 1 < p.T) :
    let r := nextRecord rate rewards C_star C_h u t z hq
    match r.output.preparation.coordinator with
    | .live _ _ _ (.continuingChosen ..) =>
        ∃ c, nextLive rate rewards C_star C_h u t z hq = some c ∧
          ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c ∧
          nextCollection rate rewards C_star C_h u t z hq = none ∧
          ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = none
    | .live _ _ _ (.cutoffChosen ..) =>
        ∃ c, nextCollection rate rewards C_star C_h u t z hq = some c ∧
          ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c ∧
          nextLive rate rewards C_star C_h u t z hq = none ∧
          ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = none
    | _ =>
        nextLive rate rewards C_star C_h u t z hq = none ∧
          ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = none ∧
          nextCollection rate rewards C_star C_h u t z hq = none ∧
          ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = none := by
  dsimp only
  have hphase := nextRecord_dispatch_phase rate rewards C_star C_h u t z hq
  have hcont := next_continuing_present rate rewards C_star C_h u t z hq
  have hcut := next_cutoff_present rate rewards C_star C_h u t z hq
  cases hnext : (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator
    <;> simp only [hnext] at hphase hcont hcut ⊢
  · rename_i outcome
    cases outcome
    case continuingChosen =>
      cases hread : nextLive rate rewards C_star C_h u t z hq with
      | none => simp only [hread, Option.isSome_none, Bool.false_eq_true] at hcont
      | some c =>
        have hz := live_baseline_zero rate _ _ c hread
        exact ⟨c, rfl, hz, collection_none_of_live rate _ _ c hread,
          collection_none_of_live rate _ 0 c hz⟩
    case cutoffChosen =>
      cases hread : nextCollection rate rewards C_star C_h u t z hq with
      | none => simp only [hread, Option.isSome_none, Bool.false_eq_true] at hcut
      | some c =>
        have hz := collection_baseline_zero rate _ _ c hread
        exact ⟨c, rfl, hz, live_none_of_collection rate _ _ c hread,
          live_none_of_collection rate _ 0 c hz⟩
    all_goals simp [nextLive, nextCollection,
      ReferenceLaterLiveNumericalReadout.laterLiveReadout,
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
      hnext, ReferenceActivePhysicalStep.DispatchCut.selection]
  · simp [nextLive, nextCollection,
      ReferenceLaterLiveNumericalReadout.laterLiveReadout,
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
      hnext, ReferenceActivePhysicalStep.DispatchCut.selection]

/-- Both baselines read the identical actual next input, or the identical
absence. The baseline is only an assignment-start guard. -/
theorem next_baseline_readouts (z : Z) (hq : t.val + 1 < p.T) :
    ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
        (nextRecord rate rewards C_star C_h u t z hq) =
      nextLive rate rewards C_star C_h u t z hq ∧
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
        (nextRecord rate rewards C_star C_h u t z hq) =
      nextCollection rate rewards C_star C_h u t z hq := by
  have hr := nextDate_readouts rate rewards C_star C_h u t z hq
  dsimp only at hr
  cases hnext : (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator
    <;> simp only [hnext] at hr
    <;> try exact ⟨hr.2.1.trans hr.1.symm, hr.2.2.2.trans hr.2.2.1.symm⟩
  rename_i outcome
  cases outcome <;> simp only at hr
    <;> try exact ⟨hr.2.1.trans hr.1.symm, hr.2.2.2.trans hr.2.2.1.symm⟩
  · obtain ⟨c, hc, hz, hl, hlz⟩ := hr
    exact ⟨hlz.trans hl.symm, hz.trans hc.symm⟩
  · obtain ⟨c, hc, hz, hl, hlz⟩ := hr
    exact ⟨hz.trans hc.symm, hlz.trans hl.symm⟩

/-- On the actual next continuing branch, every arm has its unique physical
owner and literal numerical arrival. Unoccupied followers contribute their
saved current observation, rather than a coordinator-only projection. -/
theorem next_continuing_physical (z : Z) (hq : t.val + 1 < p.T) :
    let r := nextRecord rate rewards C_star C_h u t z hq
    match r.output.preparation.coordinator with
    | .live _ _ _ (.continuingChosen ..) =>
      ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r,
        nextLive rate rewards C_star C_h u t z hq = some cell.input ∧
        nextCollection rate rewards C_star C_h u t z hq = none ∧
        cell.input.enabled = true ∧
        cell.input.reward = (fun a => ((rewards ⟨t.val + 1, hq⟩ a).val : ℝ) / (D p : ℝ)) ∧
        cell.input.rate = cell.selected.view.payload.rate ∧
        cell.input.recordedArm = ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
          r cell.selected.view.payload true ∧
        (∀ a, cell.input.recordedArm = some a → ∃ owner : Fin p.m,
          SnapshotRecordingKernel.owns p (.live cell.selected.view.payload.assignment
            (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) owner a ∧
          (∀ other, SnapshotRecordingKernel.owns p (.live cell.selected.view.payload.assignment
            (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) other a → other = owner) ∧
          r.output.preparation.arms.actions owner = a ∧
          r.gridFeedback owner = rewards r.input.time a ∧
          (r.output.ownEntries owner).2.val.val =
            ((rewards r.input.time a).val : ℝ) / (D p : ℝ)) ∧
        ∀ a, (∃! owner : Fin p.m,
          SnapshotRecordingKernel.owns p (.live cell.selected.view.payload.assignment
            (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) owner a) ∧
          ((a ∉ cell.selected.view.payload.slowSet.1 ∧ ∃ out,
            r.output.coordinator.recording = some out ∧
            ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
              (ReferenceActiveHorizonMeasurability.roundRecordCode r) a =
                some (RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a)) ∨
            ∃ i : Fin (p.m - 1), cell.selected.view.payload.assignment.assigned i = a ∧
              (∀ j, cell.selected.view.payload.assignment.assigned j = a → j = i) ∧
              (if (cell.states i).status = .unoccupied then
                ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution
                  r cell.selected.view.payload i
              else ActiveFollowerQueueOperation.rawArrival rate.eta i r.input.row r.input.time
                (cell.selected.view.payload.downRecord i)
                (r.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2) =
                  RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a)
    | _ => True := by
  dsimp only
  have hr := nextDate_readouts rate rewards C_star C_h u t z hq
  dsimp only at hr
  cases hnext : (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator
    <;> try trivial
  rename_i outcome
  cases outcome <;> try trivial
  simp only [hnext] at hr
  obtain ⟨c, hread, _hzero, hnone, _hzeroNone⟩ := hr
  have hphysical := ReferenceLaterLiveNumericalReadout.laterLiveReadout_physical
    rate rewards C_star C_h z.val (nextIndex rate rewards C_star C_h u t z hq) c hread
  obtain ⟨cell, hinput, _henabled, _hlive, _htraceEnabled, _hrows, _hselected,
    _hrewards, hmarker, _hdown, howner, hoccupied, hunoccupied, _hlogging,
    hcoordinator, _hbirth⟩ := hphysical
  have hfields := nextRecord_fields rate rewards C_star C_h u t z hq
  refine ⟨cell, ?_, hnone, cell.enabled, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hinput]
    exact hread
  · rw [cell.input_eq]
    change (fun a => (((nextRecord rate rewards C_star C_h u t z hq).input.rewards
      (nextRecord rate rewards C_star C_h u t z hq).input.time a).val : ℝ) / (D p : ℝ)) = _
    rw [hfields.2.2.2, hfields.1]
  · rw [cell.input_eq]
    rfl
  · rw [hinput]
    exact hmarker
  · intro a ha
    rw [hinput] at ha
    exact howner a ha
  · intro a
    constructor
    · obtain ⟨owner, howns⟩ := SnapshotRecordingKernel.exists_ownerSource p
        (.live cell.selected.view.payload.assignment
          (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) a
      exact ⟨owner, howns, fun other hother =>
        SnapshotRecordingKernel.owns_unique p _ a other owner hother howns⟩
    · by_cases ha : a ∈ cell.selected.view.payload.slowSet.1
      · rw [← cell.selected.view.payload.assignment_image] at ha
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
        refine Or.inr ⟨i, hi, ?_, ?_⟩
        · intro j hj
          exact cell.selected.view.payload.assignment.injective (hj.trans hi.symm)
        · split_ifs with hu
          · simpa only [nextRecord, sourceRecords, hinput, hi] using hunoccupied i hu
          · simpa only [nextRecord, sourceRecords, hinput, hi] using (hoccupied i hu).2
      · obtain ⟨out, hout, hraw⟩ := hcoordinator
        refine Or.inl ⟨ha, out, hout, ?_⟩
        rw [hinput]
        exact hraw a ha

/-- The immediate cutoff uses the actual collection recorder and reward.
Its cell remains present at the grid boundary, where its service bit is false. -/
theorem next_cutoff_physical (z : Z) (hq : t.val + 1 < p.T) :
    let r := nextRecord rate rewards C_star C_h u t z hq
    match r.output.preparation.coordinator with
    | .live _ _ _ (.cutoffChosen ..) =>
      ∃ (c : RecordedQueueRun.RoundInput p.K)
        (payload : ReferenceActivePhysicalStep.Payload rate)
        (ledger : ReferenceActivePhysicalStep.Ledger rate)
        (started : CoordinatorPhaseClock.StartRoundResult p)
        (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
        (out : CoordinatorRecordingOperation.Output p),
        nextCollection rate rewards C_star C_h u t z hq = some c ∧
        nextLive rate rewards C_star C_h u t z hq = none ∧
        ReferenceLaterCollectionArrivalReadout.laterCollectionCall
          (start rate rewards C_star C_h u t z) r = some ⟨payload, ledger, started, weights⟩ ∧
        c.enabled = decide (t.val + 2 < started.clock.g) ∧
        c.rate = payload.rate ∧
        c.reward = (fun a => ((rewards ⟨t.val + 1, hq⟩ a).val : ℝ) / (D p : ℝ)) ∧
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput
            r.output.preparation payload started weights) = some out ∧
        r.coordinatorDiagnostics.recording = some out ∧ out.gateArm = c.recordedArm ∧
        (∀ a, CoordinatorCollectionLedger.localArrival
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a =
          RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) ∧
        (∀ a, ∃! owner : Fin p.m, SnapshotRecordingKernel.owns p .collection owner a) ∧
        ∀ a, c.recordedArm = some a →
          let input := CoordinatorRecorderComplementBridge.recorderInput
            (ReferenceActivePhysicalStep.collectionRecordingInput r.output.preparation payload started weights)
          ∃ valid : CoordinatorRecordingOperation.InputsValid input,
            CoordinatorRecordingOperation.selectedSlot input = PublicDiscreteDraws.dataSlot ∧
            CoordinatorRecordingOperation.selectedRecorder input = ActiveRoundActions.coordinator p.two_le_m ∧
            ¬ CoordinatorRecordingOperation.isFrozen input ∧
            SnapshotRecordingKernel.owns p .collection (ActiveRoundActions.coordinator p.two_le_m) a ∧
            r.actions (ActiveRoundActions.coordinator p.two_le_m) = a ∧
            CanonicalRecordingSlice.recordingMask (K_pos p) (ActiveRoundActions.coordinator p.two_le_m) a
              (ContinuousLearningRows.sliceAt r.input.time r.input.row.2) ∧
            (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
              (ContinuousLearningRows.sliceAt r.input.time r.input.row.2)).val ≤
                CoordinatorRecordingOperation.coordinatorThreshold input valid ∧
            r.gridFeedback (ActiveRoundActions.coordinator p.two_le_m) = rewards r.input.time a ∧
            out.rawArrival = Nat.floor ((D p : ℝ) * rate.eta.val *
              (((rewards r.input.time a).val : ℝ) / (D p : ℝ)) / payload.rate a)
    | _ => True := by
  dsimp only
  have hr := nextDate_readouts rate rewards C_star C_h u t z hq
  dsimp only at hr
  cases hnext : (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator
    <;> try trivial
  rename_i outcome
  cases outcome <;> try trivial
  simp only [hnext] at hr
  obtain ⟨c, hread, _hzero, hnone, _hzeroNone⟩ := hr
  obtain ⟨payload, ledger, started, weights, out, hcall, hrun, hdiag, hgate,
      harrival, hrate, hreward, howner⟩ :=
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_physical
      rate rewards C_star C_h z.val (nextIndex rate rewards C_star C_h u t z hq) c hread
  obtain ⟨payload', ledger', started', weights', _out', hcall', _hpost, _hrun',
      _henabled, hclockEnabled, _⟩ :=
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call
      (start rate rewards C_star C_h u t z)
      (nextRecord rate rewards C_star C_h u t z hq) c hread
  change ReferenceLaterCollectionArrivalReadout.laterCollectionCall
    (start rate rewards C_star C_h u t z) (nextRecord rate rewards C_star C_h u t z hq) =
      some ⟨payload, ledger, started, weights⟩ at hcall
  have hstarted : started' = started := congrArg (fun args => args.2.2.1)
    (Option.some.inj (hcall'.symm.trans hcall))
  rw [hstarted, (nextRecord_fields rate rewards C_star C_h u t z hq).1] at hclockEnabled
  have hreward' : c.reward =
      (fun a => ((rewards ⟨t.val + 1, hq⟩ a).val : ℝ) / (D p : ℝ)) := by
    change c.reward = (fun a => ((rewards
      (nextRecord rate rewards C_star C_h u t z hq).input.time a).val : ℝ) / (D p : ℝ)) at hreward
    rw [(nextRecord_fields rate rewards C_star C_h u t z hq).1] at hreward
    exact hreward
  refine ⟨c, payload, ledger, started, weights, out, hread, hnone, hcall,
    hclockEnabled, hrate, hreward', hrun, hdiag, hgate, harrival, ?_, howner⟩
  intro a
  obtain ⟨owner, howns⟩ := SnapshotRecordingKernel.exists_ownerSource p .collection a
  exact ⟨owner, howns, fun other hother =>
    SnapshotRecordingKernel.owns_unique p .collection a other owner hother howns⟩

private theorem rawLive_prefix_take (z : Z) (n : ℕ) (hn : n ≤ p.T) :
    rawLiveNumericalDecoder rate (datePrefix rate n
      (completeObservation rate rewards C_star C_h u t z)) =
      (rawLiveNumericalDecoder rate (completeObservation rate rewards C_star C_h u t z)).take
        (n - start rate rewards C_star C_h u t z) := by
  unfold completeObservation
  rw [datePrefix_eq_take rate rewards C_star C_h n hn]
  exact List.map_take

private theorem rawCollection_prefix_take (z : Z) (n : ℕ) (hn : n ≤ p.T) :
    rawCollectionNumericalDecoder rate (datePrefix rate n
      (completeObservation rate rewards C_star C_h u t z)) =
      (rawCollectionNumericalDecoder rate (completeObservation rate rewards C_star C_h u t z)).take
        (n - start rate rewards C_star C_h u t z) := by
  unfold completeObservation
  rw [datePrefix_eq_take rate rewards C_star C_h n hn]
  exact List.map_take

/-- The next LIVE projection keeps its real date even when absent. -/
theorem rawLive_next_lookup (z : Z) (hq : t.val + 1 < p.T) :
    (rawLiveNumericalDecoder rate (completeObservation rate rewards C_star C_h u t z))[
      t.val - start rate rewards C_star C_h u t z + 1]? =
        some ((⟨t.val + 1, hq⟩ : Fin p.T),
          (nextLive rate rewards C_star C_h u t z hq).map encodeNumerical) := by
  unfold completeObservation
  rw [rawLiveNumericalDecoder_completeSuffixRecords, List.getElem?_map]
  have hlookup := nextRecord_lookup rate rewards C_star C_h u t z hq
  dsimp only [sourceRecords] at hlookup
  rw [hlookup]
  change some ((nextRecord rate rewards C_star C_h u t z hq).input.time,
    (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
      (nextRecord rate rewards C_star C_h u t z hq)).map encodeNumerical) = _
  rw [(nextRecord_fields rate rewards C_star C_h u t z hq).1,
    (next_baseline_readouts rate rewards C_star C_h u t z hq).1]

/-- The next collection projection has the same original calendar position. -/
theorem rawCollection_next_lookup (z : Z) (hq : t.val + 1 < p.T) :
    (rawCollectionNumericalDecoder rate (completeObservation rate rewards C_star C_h u t z))[
      t.val - start rate rewards C_star C_h u t z + 1]? =
        some ((⟨t.val + 1, hq⟩ : Fin p.T),
          (nextCollection rate rewards C_star C_h u t z hq).map encodeNumerical) := by
  unfold completeObservation
  rw [rawCollectionNumericalDecoder_completeSuffixRecords, List.getElem?_map]
  have hlookup := nextRecord_lookup rate rewards C_star C_h u t z hq
  dsimp only [sourceRecords] at hlookup
  rw [hlookup]
  change some ((nextRecord rate rewards C_star C_h u t z hq).input.time,
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
      (nextRecord rate rewards C_star C_h u t z hq)).map encodeNumerical) = _
  rw [(nextRecord_fields rate rewards C_star C_h u t z hq).1,
    (next_baseline_readouts rate rewards C_star C_h u t z hq).2]

theorem rawLive_nextPrefix_append (z : Z) (hq : t.val + 1 < p.T) :
    rawLiveNumericalDecoder rate (datePrefix rate (t.val + 2)
      (completeObservation rate rewards C_star C_h u t z)) =
      rawLiveNumericalDecoder rate (datePrefix rate (t.val + 1)
        (completeObservation rate rewards C_star C_h u t z)) ++
          [((⟨t.val + 1, hq⟩ : Fin p.T),
            (nextLive rate rewards C_star C_h u t z hq).map encodeNumerical)] := by
  rw [rawLive_prefix_take rate rewards C_star C_h u t z _ (by omega),
    rawLive_prefix_take rate rewards C_star C_h u t z _ (by omega)]
  have hb := actual_boundaries rate rewards C_star C_h u t z
  have he : t.val + 2 - start rate rewards C_star C_h u t z =
      (t.val - start rate rewards C_star C_h u t z + 1) + 1 := by omega
  have he' : t.val + 1 - start rate rewards C_star C_h u t z =
      t.val - start rate rewards C_star C_h u t z + 1 := by omega
  rw [he, he', List.take_add_one, rawLive_next_lookup]
  rfl

theorem rawCollection_nextPrefix_append (z : Z) (hq : t.val + 1 < p.T) :
    rawCollectionNumericalDecoder rate (datePrefix rate (t.val + 2)
      (completeObservation rate rewards C_star C_h u t z)) =
      rawCollectionNumericalDecoder rate (datePrefix rate (t.val + 1)
        (completeObservation rate rewards C_star C_h u t z)) ++
          [((⟨t.val + 1, hq⟩ : Fin p.T),
            (nextCollection rate rewards C_star C_h u t z hq).map encodeNumerical)] := by
  rw [rawCollection_prefix_take rate rewards C_star C_h u t z _ (by omega),
    rawCollection_prefix_take rate rewards C_star C_h u t z _ (by omega)]
  have hb := actual_boundaries rate rewards C_star C_h u t z
  have he : t.val + 2 - start rate rewards C_star C_h u t z =
      (t.val - start rate rewards C_star C_h u t z + 1) + 1 := by omega
  have he' : t.val + 1 - start rate rewards C_star C_h u t z =
      t.val - start rate rewards C_star C_h u t z + 1 := by omega
  rw [he, he', List.take_add_one, rawCollection_next_lookup]
  rfl

/-- The literal joined raw numerical projection below a natural boundary. -/
def rawJoinedPrefix (z : Z) (n : ℕ) :=
  List.zipWith (fun a b => a.2.or b.2)
    (rawLiveNumericalDecoder rate (datePrefix rate n
      (completeObservation rate rewards C_star C_h u t z)))
    (rawCollectionNumericalDecoder rate (datePrefix rate n
      (completeObservation rate rewards C_star C_h u t z)))

/-- The raw join uses the existing source-prefix map with its complete
continuous controls. This is a factorization, not a conditional-law claim. -/
theorem rawJoinedPrefix_factor (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (n : ℕ) (hn : n ≤ p.T) :
    rawJoinedPrefix rate rewards C_star C_h u t z n =
      List.zipWith (fun a b => a.2.or b.2)
        (rawLiveNumericalDecoder rate (datePrefix rate n
          (completeBranchObservation rate rewards C_star C_h
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z.val))))
        (rawCollectionNumericalDecoder rate (datePrefix rate n
          (completeBranchObservation rate rewards C_star C_h
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z.val)))) := by
  unfold rawJoinedPrefix
  rw [completeObservationPrefix_factor rate rewards C_star C_h u t control0 n hn z]

/-- The full raw prefix appends the actual next option, including `none`. -/
theorem rawJoinedPrefix_next (z : Z) (hq : t.val + 1 < p.T) :
    rawJoinedPrefix rate rewards C_star C_h u t z (t.val + 2) =
      (currentCells rate rewards C_star C_h u t z).map (fun c => some (encodeNumerical c)) ++
        [(nextCell rate rewards C_star C_h u t z hq).map encodeNumerical] := by
  unfold rawJoinedPrefix
  rw [rawLive_nextPrefix_append rate rewards C_star C_h u t z hq,
    rawCollection_nextPrefix_append rate rewards C_star C_h u t z hq,
    List.zipWith_append (by rw [rawLiveNumericalDecoder_length,
      rawCollectionNumericalDecoder_length]), appendedCells_rawPrefix_join]
  simp only [currentCells, nextCell, Option.map_or]
  rfl

/-- Local list recursion, including all accepted histories and first overflow. -/
theorem run_append_one (cells : List (RecordedQueueRun.RoundInput p.K))
    (cell : RecordedQueueRun.RoundInput p.K) :
    RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) (cells ++ [cell]) =
      RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) cells) cell := by
  have happend (left right : List (RecordedQueueRun.RoundInput p.K))
      (state : RecordedQueueRun.RunState p.K) :
      RecordedQueueRun.execute (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (left ++ right) state =
        RecordedQueueRun.execute (ReferenceFirstLaunchNumericalCell.queueParameters rate) right
          (RecordedQueueRun.execute (ReferenceFirstLaunchNumericalCell.queueParameters rate) left state) := by
    induction left generalizing state with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.cons_append, RecordedQueueRun.execute]
        exact ih _
  unfold RecordedQueueRun.run
  rw [happend cells [cell] (RecordedQueueRun.initialState p.K)]
  rfl

theorem currentState_readout (z : Z) :
    ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
      (currentState rate rewards C_star C_h u t z) =
      ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
        rate rewards C_star C_h u t z :=
  (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout_fullPrefix
    rate rewards C_star C_h u t z).symm

/-- All three readout components follow the same one-element run recursion. -/
theorem nextRun_fullPrefix (z : Z) (c : RecordedQueueRun.RoundInput p.K) :
    ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (currentCells rate rewards C_star C_h u t z ++ [c])) =
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (currentState rate rewards C_star C_h u t z) c) := by
  rw [run_append_one]
  rfl

/-- Every accepted history is retained, including disabled and post-overflow
records; the current step is not removed when it first causes overflow. -/
theorem nextRun_acceptedHistories (z : Z) (c : RecordedQueueRun.RoundInput p.K) :
    (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (currentCells rate rewards C_star C_h u t z ++ [c])).records =
      fun a => (wholePostReadout rate rewards C_star C_h u t z).2.2 a ++
        [RecordedQueueRun.acceptedRecord (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (currentState rate rewards C_star C_h u t z) c a] := by
  funext a
  rw [run_append_one]
  change (currentState rate rewards C_star C_h u t z).records a ++ [_] = _
  have hr := congrArg (fun readout => readout.2.2)
    (currentState_readout rate rewards C_star C_h u t z)
  exact congrArg (fun history => history a ++
    [RecordedQueueRun.acceptedRecord (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (currentState rate rewards C_star C_h u t z) c a]) hr

/-- The incoming overflow flag, rather than the new flag, decides acceptance.
Enabled zero arrivals retain their true service bit; disabled cells do not. -/
theorem nextRun_acceptedRecord (z : Z) (c : RecordedQueueRun.RoundInput p.K) (a : Fin p.K) :
    RecordedQueueRun.acceptedRecord (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (currentState rate rewards C_star C_h u t z) c a =
      if (wholePostReadout rate rewards C_star C_h u t z).2.1 then (false, 0)
      else if c.enabled then (true, RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) else (false, 0) := by
  have hflag := congrArg (fun readout => readout.2.1)
    (currentState_readout rate rewards C_star C_h u t z)
  change (currentState rate rewards C_star C_h u t z).overflow = _ at hflag
  unfold RecordedQueueRun.acceptedRecord
  rw [hflag]

private theorem rawJoinedPrefix_of_some (z : Z) (hq : t.val + 1 < p.T)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : nextCell rate rewards C_star C_h u t z hq = some c) :
    rawJoinedPrefix rate rewards C_star C_h u t z (t.val + 2) =
      (currentCells rate rewards C_star C_h u t z ++ [c]).map
        (fun cell => some (encodeNumerical cell)) := by
  rw [rawJoinedPrefix_next rate rewards C_star C_h u t z hq, hc, List.map_append]
  rfl

/-- The original-source one-date numerical join. The successful constructors
produce their own canonical input; all other actual constructors append an
absent dated entry. The pre-readout and every accepted history are unchanged
parts of the one stopped numerical run. -/
theorem nextDate_physical_prefix (z : Z) (hq : t.val + 1 < p.T) :
    ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (currentState rate rewards C_star C_h u t z) =
      wholePostReadout rate rewards C_star C_h u t z ∧
    (∀ c : RecordedQueueRun.RoundInput p.K,
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (currentCells rate rewards C_star C_h u t z ++ [c])) =
        ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (currentState rate rewards C_star C_h u t z) c) ∧
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (currentCells rate rewards C_star C_h u t z ++ [c])).records =
        fun a => (wholePostReadout rate rewards C_star C_h u t z).2.2 a ++
          [RecordedQueueRun.acceptedRecord (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (currentState rate rewards C_star C_h u t z) c a]) ∧
    match (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator with
    | .live _ _ _ (.continuingChosen ..) =>
      ∃ c, nextLive rate rewards C_star C_h u t z hq = some c ∧
        nextCollection rate rewards C_star C_h u t z hq = none ∧
        nextCell rate rewards C_star C_h u t z hq = some c ∧
        c.enabled = true ∧
        c.reward = (fun a => ((rewards ⟨t.val + 1, hq⟩ a).val : ℝ) / (D p : ℝ)) ∧
        rawJoinedPrefix rate rewards C_star C_h u t z (t.val + 2) =
          (currentCells rate rewards C_star C_h u t z ++ [c]).map
            (fun cell => some (encodeNumerical cell))
    | .live _ _ _ (.cutoffChosen ..) =>
      ∃ c, nextCollection rate rewards C_star C_h u t z hq = some c ∧
        nextLive rate rewards C_star C_h u t z hq = none ∧
        nextCell rate rewards C_star C_h u t z hq = some c ∧
        c.reward = (fun a => ((rewards ⟨t.val + 1, hq⟩ a).val : ℝ) / (D p : ℝ)) ∧
        rawJoinedPrefix rate rewards C_star C_h u t z (t.val + 2) =
          (currentCells rate rewards C_star C_h u t z ++ [c]).map
            (fun cell => some (encodeNumerical cell))
    | _ => nextLive rate rewards C_star C_h u t z hq = none ∧
        nextCollection rate rewards C_star C_h u t z hq = none ∧
        nextCell rate rewards C_star C_h u t z hq = none ∧
        rawJoinedPrefix rate rewards C_star C_h u t z (t.val + 2) =
          (currentCells rate rewards C_star C_h u t z).map (fun c => some (encodeNumerical c)) ++
            [none] := by
  refine ⟨currentState_readout rate rewards C_star C_h u t z,
    fun c => ⟨nextRun_fullPrefix rate rewards C_star C_h u t z c,
      nextRun_acceptedHistories rate rewards C_star C_h u t z c⟩, ?_⟩
  have hread := nextDate_readouts rate rewards C_star C_h u t z hq
  have hlive := next_continuing_physical rate rewards C_star C_h u t z hq
  have hcollection := next_cutoff_physical rate rewards C_star C_h u t z hq
  dsimp only at hread hlive hcollection
  cases hnext : (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator
    <;> simp only [hnext] at hread hlive hcollection ⊢
  all_goals try
    obtain ⟨hL, _hL0, hC, _hC0⟩ := hread
    have hc : nextCell rate rewards C_star C_h u t z hq = none := by
      simp only [nextCell, hL, hC, Option.none_or]
    exact ⟨hL, hC, hc, by rw [rawJoinedPrefix_next rate rewards C_star C_h u t z hq, hc]; rfl⟩
  rename_i outcome
  cases outcome <;> simp only at hread hlive hcollection ⊢
  all_goals try
    obtain ⟨hL, _hL0, hC, _hC0⟩ := hread
    have hc : nextCell rate rewards C_star C_h u t z hq = none := by
      simp only [nextCell, hL, hC, Option.none_or]
    exact ⟨hL, hC, hc, by rw [rawJoinedPrefix_next rate rewards C_star C_h u t z hq, hc]; rfl⟩
  · obtain ⟨c, _payload, _ledger, _started, _weights, _out, hC, hL, _hcall,
      _henabled, _hrate, hreward, _⟩ := hcollection
    have hc : nextCell rate rewards C_star C_h u t z hq = some c := by
      simp only [nextCell, hL, hC, Option.none_or]
    exact ⟨c, hC, hL, hc, hreward, rawJoinedPrefix_of_some rate rewards C_star C_h u t z hq c hc⟩
  · obtain ⟨cell, hL, hC, henabled, hreward, _⟩ := hlive
    have hc : nextCell rate rewards C_star C_h u t z hq = some cell.input := by
      simp only [nextCell, hL, Option.some_or]
    exact ⟨cell.input, hL, hC, hc, henabled, hreward,
      rawJoinedPrefix_of_some rate rewards C_star C_h u t z hq cell.input hc⟩

/-- Terminal renewal dates expose the complete existing prefix. There is no
fabricated next action or `Fin (t + 1)` at the horizon. -/
theorem terminal_physical_prefix (z : Z) (ht : t.val + 1 = p.T) :
    datePrefix rate p.T (completeObservation rate rewards C_star C_h u t z) =
      completeObservation rate rewards C_star C_h u t z ∧
    rawJoinedPrefix rate rewards C_star C_h u t z p.T =
      (currentCells rate rewards C_star C_h u t z).map (fun c => some (encodeNumerical c)) := by
  refine ⟨completeObservation_terminalPrefix rate rewards C_star C_h u t z, ?_⟩
  rw [← ht]
  exact appendedCells_rawPrefix_join rate rewards C_star C_h u t z

end Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix

end
