/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalExponentialQueueStep

import Mathlib.Tactic

/-!
# The actual first-renewal current cell and original numerical prefix

This module reads the source-selected whole current cell at the first renewal
call and joins its actual stopped queue update to the original launch prefix.
The source record, reward table, and rate vector remain unchanged.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:93-188,245-290`,
`sources/zip4/manuscript/06_interruptions.tex:355-426`,
`sources/zip4/manuscript/05_binary_transport.tex:180-240`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:44-64,100-108`.
-/

@[expose] public section

noncomputable section

open scoped Classical
open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceFirstCollectionRenewalExponentialQueueStep

namespace Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev Source {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalInstallationCoupling.Source
    rate rewards C_star C_h u t

variable {p : Parameters}
variable (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

local notation "Z" => Source rate rewards C_star C_h u t
/-- The same actual selection is live at both the renewal boundary and
baseline zero; the source call is after round zero. -/
private theorem wholeCell_domain_at (z : Z) (s : ℕ)
    (hs : s = 0 ∨ s = _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
      rate rewards C_star C_h u t z) :
    _root_.Bandits.Support.ReferenceLaterLiveNumericalReadout.laterLiveDomain s
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
        rate rewards C_star C_h u t z) ∧
    _root_.Bandits.Support.ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
        rate rewards C_star C_h u t z) = none := by
  classical
  obtain ⟨d, consistent, output, hlocal, _hstart, _hvector, _hreconstruction,
      _hslow, _hslowSet, _hinstalledPayload, _hinstalledVector, _hinstalledReconstruction,
      _hanchor, _hqueues, _hretained, selection, _hchoice, hdispatch, hprep, hcoord,
      _harm, _hpost⟩ :=
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalSampleInstallation.actual_renewal_call_installation
      rate rewards C_star C_h u t z
  let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output := {
    priorClock := (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
      rate u d.record.input d.old d.ledger d.saved).clock
    pending := (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
      rate u d.record.input d.old d.ledger d.saved).ledger.pending
    proposalParameterValid := d.core.clock_parameter_valid
    priorClockValid := d.core.clock_registers_valid
    startTimeValid := by
      simpa only [ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
        ReferenceActivePhysicalStep.collectionInput, d.instruction_time] using
          d.core.clock_start_time_valid
    result := d.started
    startRound_eq := by
      simpa only [ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
        ReferenceActivePhysicalStep.collectionInput,
        ReferenceActivePhysicalStep.collectionClock, d.instruction_time] using d.clock_eq
    assignmentStart_eq := d.instruction_eq
    priorSigma_eq := d.core.clock_sigma_eq
    priorGrid_eq_freezeAt := by
      calc
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
          rate u d.record.input d.old d.ledger d.saved).clock.g =
            (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
              rate u d.record.input d.old d.ledger d.saved).ledger.freezeAt :=
          d.core.ledger_freeze_eq
        _ = consistent.oldFreezeAt := consistent.oldFreezeAt_eq.symm
        _ = output.localConsistency.oldFreezeAt := by rw [hlocal] }
  let installed := CoordinatorAssignmentRegisterInstall.installLater output clockData
  have hcut : (ReferenceActivePhysicalStep.prepare d.record.input).coordinator =
      .collection d.old d.ledger
        (ReferenceActivePhysicalStep.collectionClock d.old d.ledger d.saved u) u
        (.laterChosen d.core consistent d.started d.clock_eq d.instruction
          d.instruction_eq output hlocal clockData installed selection) := by
    rw [← hprep, hcoord, hdispatch]
  have hprepared :=
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalRecordingFeedback.actual_call_prepared_followers
      rate rewards C_star C_h u t z d
      consistent output hlocal clockData installed selection hcut
  rcases hprepared with ⟨hinstalled, _hrows, _hselected, _hrewards,
    states, memories, hstates⟩
  have hcompat := CoordinatorAssignmentRegisterInstall.later_start_round_compatibility
    output clockData
  have hpayload : installed.registers.payload = output.payload := by
    rw [hinstalled]
    rfl
  have hsigma : installed.registers.payload.sigma = d.record.input.time := by
    rw [hpayload]
    exact output.payload_start.trans d.instruction_time
  have htime : d.instruction.time = d.record.input.time := d.instruction_time
  have hselectionAtSome :
      (ReferenceActivePhysicalStep.selectionAt d.record.input
        installed.registers.payload d.started d.instruction.time
        installed.registers.complementWeights selection).isSome = true := by
    simp [ReferenceActivePhysicalStep.selectionAt, htime]
  let selected : ReferenceActivePhysicalStep.Selection d.record.input :=
    (ReferenceActivePhysicalStep.selectionAt d.record.input
      installed.registers.payload d.started d.instruction.time
      installed.registers.complementWeights selection).get hselectionAtSome
  have hselection : d.record.output.preparation.coordinator.selection = some selected := by
    rw [hcoord, hdispatch]
    simp [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt, htime, selected]
    rfl
  have hview : selected.view.payload = installed.registers.payload := by
    simp [selected, ReferenceActivePhysicalStep.selectionAt, htime]
    rfl
  have hselectedCutoff : selected.view.cutoff =
      CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u := by
    simp [selected, ReferenceActivePhysicalStep.selectionAt, htime]
  have hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
      selected.view.cutoff d.record.input.time := by
    rw [hview, hselectedCutoff]
    change (installed.registers.payload.sigma.val + 1 ≤ d.record.input.time.val + 1) ∧
      (d.record.input.time.val + 1 <
        CoordinatorLocalArmChoice.cutoffRound
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u))
    constructor
    · rw [hsigma]
    · rw [CoordinatorLiveChoiceRecorderStep.cutoffRoundFromClock, hcompat.2.2.1]
      have ht := d.record.input.time.isLt
      exact Nat.add_lt_add_right ht 1
  have hord : _root_.Bandits.Support.ReferenceLaterLiveNumericalReadout.preparedOrdinary
      d.record := by
    intro i
    have hi := (hstates i).2.2
    have hi' : (d.record.output.preparation.followers.followers i).configuration =
        .ordinary (states i) (memories i) := by
      rw [hprep]
      exact hi
    simp [_root_.Bandits.Support.ReferenceLaterLiveNumericalReadout.ordinaryData, hi']
  have hdomain : _root_.Bandits.Support.ReferenceLaterLiveNumericalReadout.laterLiveDomain
      s d.record := by
    refine ⟨selected, hselection, ?_, hlive, hord⟩
    have hb := _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.actual_boundaries
      rate rewards C_star C_h u t z
    have hlt : _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z < t.val := lt_of_le_of_lt hb.1 hb.2.1
    have hbase : s < t.val := by
      rcases hs with hzero | hstart
      · rw [hzero]
        omega
      · rw [hstart]
        exact hlt
    change s < selected.view.payload.sigma.val
    rw [hview, hsigma, d.time_eq]
    exact hbase
  have hrecord := _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.actual_call_record_eq
    rate rewards C_star C_h u t z d
  have hprep : d.record.output.preparation = ReferenceActivePhysicalStep.prepare d.record.input := by
    rw [d.record.output_eq]
    rfl
  have hcollection : _root_.Bandits.Support.ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
      s d.record = none := by
    simp [_root_.Bandits.Support.ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
      hprep, hcut]
  constructor
  · rw [← hrecord]
    exact hdomain
  · rw [← hrecord]
    exact hcollection

/-- The actual selected whole current cell is present at every source in the
renewal call subtype. -/
theorem wholeCell_present (z : Z) :
    (_root_.Bandits.Support.ReferenceLaterLiveNumericalReadout.laterLiveReadout
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z)
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
        rate rewards C_star C_h u t z)).isSome = true := by
  exact (_root_.Bandits.Support.ReferenceLaterLiveNumericalReadout.laterLiveReadout_domain
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
      rate rewards C_star C_h u t z)
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
      rate rewards C_star C_h u t z)).2
      (wholeCell_domain_at rate rewards C_star C_h u t z _ (Or.inr rfl)).1

/-- The whole actual cell is present under the original zero-baseline test as
well; this is a separately proved domain fact, not an assumed equality. -/
theorem wholeCell_present_zero (z : Z) :
    (_root_.Bandits.Support.ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
        rate rewards C_star C_h u t z)).isSome = true := by
  exact (_root_.Bandits.Support.ReferenceLaterLiveNumericalReadout.laterLiveReadout_domain
    0 (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
      rate rewards C_star C_h u t z)).2
      (wholeCell_domain_at rate rewards C_star C_h u t z 0 (Or.inl rfl)).1

/-- The actual later-chosen call has no collection readout at its date. -/
theorem wholeCollectionReadout_none (z : Z) :
    _root_.Bandits.Support.ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
        rate rewards C_star C_h u t z) = none :=
  (wholeCell_domain_at rate rewards C_star C_h u t z 0 (Or.inl rfl)).2

/-- The source literal is the canonical extraction from the present actual
whole-cell readout. -/
def wholeCell (z : Z) : RecordedQueueRun.RoundInput p.K :=
  (_root_.Bandits.Support.ReferenceLaterLiveNumericalReadout.laterLiveReadout
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
      rate rewards C_star C_h u t z)
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
      rate rewards C_star C_h u t z)).get
      (wholeCell_present rate rewards C_star C_h u t z)

/-- The literal option returns the canonical extracted whole cell. -/
private theorem present_get_eq_some {α : Type} (o : Option α)
    (h : o.isSome = true) : o = some (o.get h) := by
  exact (Option.coe_get h).symm

theorem wholeCell_readout (z : Z) :
    _root_.Bandits.Support.ReferenceLaterLiveNumericalReadout.laterLiveReadout
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z)
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
        rate rewards C_star C_h u t z) = some (wholeCell rate rewards C_star C_h u t z) := by
  exact present_get_eq_some _
    (wholeCell_present rate rewards C_star C_h u t z)

/-- The two baseline tests read one actual selection and yield equal cells. -/
theorem wholeCell_baseline_readout_eq (z : Z) :
    _root_.Bandits.Support.ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
          rate rewards C_star C_h u t z) =
      _root_.Bandits.Support.ReferenceLaterLiveNumericalReadout.laterLiveReadout
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
          rate rewards C_star C_h u t z)
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
          rate rewards C_star C_h u t z) := by
  let record := _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
    rate rewards C_star C_h u t z
  have hzero :=
    (_root_.Bandits.Support.ReferenceLaterLiveNumericalReadout.laterLiveReadout_domain
      0 record).mp (wholeCell_present_zero rate rewards C_star C_h u t z)
  have hstart :=
    (_root_.Bandits.Support.ReferenceLaterLiveNumericalReadout.laterLiveReadout_domain
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z) record).mp
      (wholeCell_present rate rewards C_star C_h u t z)
  rcases hzero with ⟨s0, hsel0, hzeroLt, hlive0, hord0⟩
  rcases hstart with ⟨ss, hselS, hstartLt, hliveS, hordS⟩
  change record.output.preparation.coordinator.selection = some s0 at hsel0
  change record.output.preparation.coordinator.selection = some ss at hselS
  have hsels : s0 = ss := Option.some.inj (hsel0.symm.trans hselS)
  subst ss
  have hlive : CoordinatorLocalArmChoice.assignmentIsLive s0.view.payload
      s0.view.cutoff record.input.time := hliveS
  have hz : 0 < s0.view.payload.sigma.val := hzeroLt
  have hs : _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
      rate rewards C_star C_h u t z < s0.view.payload.sigma.val := hstartLt
  unfold _root_.Bandits.Support.ReferenceLaterLiveNumericalReadout.laterLiveReadout
  simp [record, hsel0, hz, hs, hlive, hord0]

/-- The canonical baseline-zero extraction is the same actual whole cell. -/
theorem wholeCell_readout_zero (z : Z) :
    _root_.Bandits.Support.ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
        rate rewards C_star C_h u t z) = some (wholeCell rate rewards C_star C_h u t z) := by
  rw [wholeCell_baseline_readout_eq rate rewards C_star C_h u t z,
    wholeCell_readout rate rewards C_star C_h u t z]

/-- Full original numerical coordinates of the actual whole current cell. -/
def wholeCellNumericalCoordinates (z : Z) :
    Bool × (Option (Fin p.K) × ((Fin p.K → ℝ) × (Fin p.K → ℝ))) :=
  let c := wholeCell rate rewards C_star C_h u t z
  (c.enabled, (c.recordedArm, (c.reward, c.rate)))

def completeObservation (z : Z) :=
  _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.completeBranchObservation
    rate rewards C_star C_h z.val

private theorem wholeCell_suffix_index (z : Z) :
    let k : Fin (_root_.Bandits.Support.ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z.val rewards C_star C_h).length :=
      ⟨t.val - _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z,
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.call_index_lt
          rate rewards C_star C_h u t z⟩
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
        rate rewards C_star C_h u t z =
      (_root_.Bandits.Support.ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z.val rewards C_star C_h).get k := by
  rfl

/-- The same complete-suffix index gives the actual physical whole-cell
characterization, including the retained recorder and marker evidence. -/
theorem wholeCell_physical (z : Z) :
    let r := _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
      rate rewards C_star C_h u t z
    ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r,
      cell.input = wholeCell rate rewards C_star C_h u t z ∧
      cell.input.enabled = true ∧
      r.input.rows = z.val.1.2 ∧ r.input.selected =
        ActualInitializationPhysicalStep.selectedRowIndex p z.val ∧
      r.input.rewards = rewards ∧
      cell.input.recordedArm =
        ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord r
          cell.selected.view.payload true ∧
      ∀ a, cell.input.recordedArm = some a →
        ∃ owner : Fin p.m,
          SnapshotRecordingKernel.owns p (.live cell.selected.view.payload.assignment
            (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) owner a ∧
          (∀ other, SnapshotRecordingKernel.owns p (.live cell.selected.view.payload.assignment
            (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) other a →
            other = owner) ∧
          r.output.preparation.arms.actions owner = a ∧
          r.gridFeedback owner = rewards r.input.time a := by
  let k : Fin (_root_.Bandits.Support.ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z.val rewards C_star C_h).length :=
    ⟨t.val - _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
      rate rewards C_star C_h u t z,
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.call_index_lt
        rate rewards C_star C_h u t z⟩
  have hcall := wholeCell_suffix_index rate rewards C_star C_h u t z
  have hread : _root_.Bandits.Support.ReferenceLaterLiveNumericalReadout.laterLiveReadout
      (_root_.Bandits.Support.ReferenceCompletePhysicalHistory.physicalStart
        rate z.val rewards C_star C_h)
      ((_root_.Bandits.Support.ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z.val rewards C_star C_h).get k) =
      some (wholeCell rate rewards C_star C_h u t z) := by
    rw [← hcall, ← _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.start_eq_physicalStart
      rate rewards C_star C_h u t z]
    exact wholeCell_readout rate rewards C_star C_h u t z
  obtain ⟨cell, hinput, henabled, _hlive, _henabledTrace, hrows, hselected,
      hreward, hmarker, _hdown, howner, _hgate, _hunoccupied, _hlogging,
      _hrecording, _hcollection⟩ :=
    _root_.Bandits.Support.ReferenceLaterLiveNumericalReadout.laterLiveReadout_physical
      rate rewards C_star C_h z.val k (wholeCell rate rewards C_star C_h u t z) hread
  dsimp only
  have henabled' : cell.input.enabled = true := by
    simpa only [hinput] using henabled
  have hmarker' : cell.input.recordedArm =
      ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
          rate rewards C_star C_h u t z) cell.selected.view.payload true := by
    simpa only [hinput, hcall] using hmarker
  refine ⟨cell, hinput, henabled', hrows, hselected, hreward, hmarker', ?_⟩
  intro a ha
  have ha' : (wholeCell rate rewards C_star C_h u t z).recordedArm = some a := by
    simpa only [hinput] using ha
  obtain ⟨owner, howns, hunique, haction, hfeedback, _⟩ := howner a ha'
  exact ⟨owner, howns, hunique, haction, hfeedback⟩

/-- Every arm's numerical arrival is identified on the same actual whole cell,
with its original unique live owner and the occupied/unoccupied split. -/
theorem wholeCell_all_arm_numerical (z : Z) (a : Fin p.K) :
    let r := _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
      rate rewards C_star C_h u t z
    ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r,
      cell.input = wholeCell rate rewards C_star C_h u t z ∧
      (∃! owner : Fin p.m,
        SnapshotRecordingKernel.owns p (.live cell.selected.view.payload.assignment
          (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) owner a) ∧
      ((a ∉ cell.selected.view.payload.slowSet.1 ∧
        ∃ out, r.output.coordinator.recording = some out ∧
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
            (r.output.ownEntries
              (_root_.Bandits.Support.PublicDiscreteDraws.followerPlayer p.two_le_m i)).2) =
            RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a) := by
  let k : Fin (_root_.Bandits.Support.ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z.val rewards C_star C_h).length :=
    ⟨t.val - _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
      rate rewards C_star C_h u t z,
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.call_index_lt
        rate rewards C_star C_h u t z⟩
  have hcall := wholeCell_suffix_index rate rewards C_star C_h u t z
  have hread : _root_.Bandits.Support.ReferenceLaterLiveNumericalReadout.laterLiveReadout
      (_root_.Bandits.Support.ReferenceCompletePhysicalHistory.physicalStart
        rate z.val rewards C_star C_h)
      ((_root_.Bandits.Support.ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z.val rewards C_star C_h).get k) =
      some (wholeCell rate rewards C_star C_h u t z) := by
    rw [← hcall, ← _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.start_eq_physicalStart
      rate rewards C_star C_h u t z]
    exact wholeCell_readout rate rewards C_star C_h u t z
  have hall := _root_.Bandits.Support.ReferenceLaterLiveNumericalReadout.laterLiveReadout_all_arm_numerical
      rate rewards C_star C_h z.val k
      (wholeCell rate rewards C_star C_h u t z) hread a
  rw [← hcall] at hall
  rcases hall with ⟨cell, hinput, hrest⟩
  rw [← hinput] at hrest
  exact ⟨cell, hinput, hrest⟩

/-- The actual source-selected branch records the same baseline-zero numerical
cell in its LIVE component. -/
theorem wholeCell_branchReadout (z : Z) :
    _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.branchReadout
      rate 0
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
        rate rewards C_star C_h u t z) =
      some (.inl (_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical
        (wholeCell rate rewards C_star C_h u t z))) := by
  let record := _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
    rate rewards C_star C_h u t z
  have hproj := _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.branch_readout_projections
    rate 0 record
  rw [wholeCell_readout_zero rate rewards C_star C_h u t z,
    wholeCollectionReadout_none rate rewards C_star C_h u t z] at hproj
  cases hbranch : _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.branchReadout
      rate 0 record with
  | none => simp [hbranch,
      _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.leftProjection,
      _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.rightProjection] at hproj
  | some value =>
      cases value with
      | inl coords =>
          have hleft := congrArg Prod.fst hproj
          simp only [hbranch,
            _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.leftProjection] at hleft
          have hcoords := Option.some.inj hleft
          rw [hcoords]
      | inr coords =>
          have hleft := congrArg Prod.fst hproj
          simp only [hbranch,
            _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.leftProjection] at hleft
          cases hleft

/-- The literal post-current stopped queue state. -/
def wholePostReadout (z : Z) :
    (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
    (_root_.Bandits.Support.RecordedQueueRun.step
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
        rate rewards C_star C_h u t z)
      (wholeCell rate rewards C_star C_h u t z))

private theorem run_append_one
    (cells : List (RecordedQueueRun.RoundInput p.K))
    (cell : RecordedQueueRun.RoundInput p.K) :
    RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (cells ++ [cell]) =
      RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) cells)
        cell := by
  have happend (left right : List (RecordedQueueRun.RoundInput p.K))
      (state : RecordedQueueRun.RunState p.K) :
      RecordedQueueRun.execute (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (left ++ right) state =
        RecordedQueueRun.execute (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          right (RecordedQueueRun.execute
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) left state) := by
    induction left generalizing state with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.cons_append, RecordedQueueRun.execute]
        exact ih _
  unfold RecordedQueueRun.run
  rw [happend cells [cell] (RecordedQueueRun.initialState p.K)]
  rfl

/-- The literal step is the same run after appending the actual current cell;
all registers, overflow status, and accepted histories are retained. -/
theorem wholePostReadout_fullPrefix (z : Z) :
    wholePostReadout rate rewards C_star C_h u t z =
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (_root_.Bandits.Support.RecordedQueueRun.run
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
            rate rewards C_star C_h u t z ++
            [wholeCell rate rewards C_star C_h u t z])) := by
  unfold wholePostReadout
  change _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
      (_root_.Bandits.Support.RecordedQueueRun.step
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (_root_.Bandits.Support.RecordedQueueRun.run
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
            rate rewards C_star C_h u t z))
        (wholeCell rate rewards C_star C_h u t z)) = _
  rw [run_append_one rate]

/-- Explicit projections of the stopped queue output after appending the
whole current cell: all arm registers, the overflow flag, and each accepted
record history belong to the same run. -/
theorem wholePostReadout_projections (z : Z) :
    wholePostReadout rate rewards C_star C_h u t z =
      (((_root_.Bandits.Support.RecordedQueueRun.step
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
          rate rewards C_star C_h u t z)
        (wholeCell rate rewards C_star C_h u t z)).registers),
        ((_root_.Bandits.Support.RecordedQueueRun.step
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
            rate rewards C_star C_h u t z)
          (wholeCell rate rewards C_star C_h u t z)).overflow,
        (_root_.Bandits.Support.RecordedQueueRun.step
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
            rate rewards C_star C_h u t z)
          (wholeCell rate rewards C_star C_h u t z)).records)) := rfl

theorem wholePostReadout_registers (z : Z) :
    (wholePostReadout rate rewards C_star C_h u t z).1 =
      (_root_.Bandits.Support.RecordedQueueRun.run
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
          rate rewards C_star C_h u t z ++ [wholeCell rate rewards C_star C_h u t z])).registers := by
  rw [wholePostReadout_fullPrefix]
  rfl

theorem wholePostReadout_overflow (z : Z) :
    (wholePostReadout rate rewards C_star C_h u t z).2.1 =
      (_root_.Bandits.Support.RecordedQueueRun.run
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
          rate rewards C_star C_h u t z ++ [wholeCell rate rewards C_star C_h u t z])).overflow := by
  rw [wholePostReadout_fullPrefix]
  rfl

theorem wholePostReadout_acceptedHistories (z : Z) :
    (wholePostReadout rate rewards C_star C_h u t z).2.2 =
      (_root_.Bandits.Support.RecordedQueueRun.run
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
          rate rewards C_star C_h u t z ++ [wholeCell rate rewards C_star C_h u t z])).records := by
  rw [wholePostReadout_fullPrefix]
  rfl

/-- The actual incoming flag is exactly the strict first-crossing cutoff on
the actual appended whole cell, with the first overflow update included. -/
theorem incoming_noOverflow_iff_wholeCell_firstOverflow (z : Z) :
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
      rate rewards C_star C_h u t z).overflow = false ↔
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastLength
        rate rewards C_star C_h u t z <
        UnstoppedRecordedQueueComparison.firstOverflowPrefix
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
            rate rewards C_star C_h u t z ++
            [wholeCell rate rewards C_star C_h u t z]) := by
  exact _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming_noOverflow_iff_appended_firstOverflow
      rate rewards C_star C_h u t z
      (wholeCell rate rewards C_star C_h u t z)

open ReferenceFirstCollectionRenewalIncomingQueuePrefix
open ReferenceCompleteFirstPhaseObservationRecovery
open ReferenceCompleteObservationPrefixInformation
open ReferenceCompleteNumericalBranchObservation

private theorem rawLive_datePrefix (z : Z) (n : ℕ) (hn : n ≤ p.T) :
    rawLiveNumericalDecoder rate (datePrefix rate n
      (completeObservation rate rewards C_star C_h u t z)) =
      (rawLiveNumericalDecoder rate
        (completeObservation rate rewards C_star C_h u t z)).take
          (n - start rate rewards C_star C_h u t z) := by
  unfold completeObservation
  rw [datePrefix_eq_take rate rewards C_star C_h n hn]
  exact List.map_take

private theorem rawCollection_datePrefix (z : Z) (n : ℕ) (hn : n ≤ p.T) :
    rawCollectionNumericalDecoder rate (datePrefix rate n
      (completeObservation rate rewards C_star C_h u t z)) =
      (rawCollectionNumericalDecoder rate
        (completeObservation rate rewards C_star C_h u t z)).take
          (n - start rate rewards C_star C_h u t z) := by
  unfold completeObservation
  rw [datePrefix_eq_take rate rewards C_star C_h n hn]
  exact List.map_take

theorem rawLive_current_lookup (z : Z) :
    (rawLiveNumericalDecoder rate
      (completeObservation rate rewards C_star C_h u t z))[
        t.val - start rate rewards C_star C_h u t z]? =
      some (t, some (encodeNumerical (wholeCell rate rewards C_star C_h u t z))) := by
  unfold completeObservation
  rw [rawLiveNumericalDecoder_completeSuffixRecords, List.getElem?_map]
  have hlookup := List.getElem?_eq_getElem (call_index_lt rate rewards C_star C_h u t z)
  change (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h)[
    t.val - start rate rewards C_star C_h u t z]? =
      some (callRecord rate rewards C_star C_h u t z) at hlookup
  rw [hlookup]
  change some ((callRecord rate rewards C_star C_h u t z).input.time,
    (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
      (callRecord rate rewards C_star C_h u t z)).map encodeNumerical) = _
  rw [callRecord_time, wholeCell_readout_zero]
  rfl

theorem rawCollection_current_lookup (z : Z) :
    (rawCollectionNumericalDecoder rate
      (completeObservation rate rewards C_star C_h u t z))[
        t.val - start rate rewards C_star C_h u t z]? = some (t, none) := by
  unfold completeObservation
  rw [rawCollectionNumericalDecoder_completeSuffixRecords, List.getElem?_map]
  have hlookup := List.getElem?_eq_getElem (call_index_lt rate rewards C_star C_h u t z)
  change (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h)[
    t.val - start rate rewards C_star C_h u t z]? =
      some (callRecord rate rewards C_star C_h u t z) at hlookup
  rw [hlookup]
  change some ((callRecord rate rewards C_star C_h u t z).input.time,
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
      (callRecord rate rewards C_star C_h u t z)).map encodeNumerical) = _
  rw [callRecord_time, wholeCollectionReadout_none]
  rfl

/-- The original dated LIVE observation extends by the whole current cell.
Every earlier position, including absent entries, remains in the prefix. -/
theorem rawLive_datePrefix_append (z : Z) :
    rawLiveNumericalDecoder rate (datePrefix rate (t.val + 1)
      (completeObservation rate rewards C_star C_h u t z)) =
      rawLiveNumericalDecoder rate (datePrefix rate t.val
        (completeObservation rate rewards C_star C_h u t z)) ++
          [(t, some (encodeNumerical (wholeCell rate rewards C_star C_h u t z)))] := by
  rw [rawLive_datePrefix rate rewards C_star C_h u t z _ (by omega),
    rawLive_datePrefix rate rewards C_star C_h u t z _ (Nat.le_of_lt t.isLt)]
  have hb := actual_boundaries rate rewards C_star C_h u t z
  have he : t.val + 1 - start rate rewards C_star C_h u t z =
      (t.val - start rate rewards C_star C_h u t z) + 1 := by omega
  rw [he, List.take_add_one, rawLive_current_lookup]
  rfl

/-- At this same actual date the collection coordinate appends an absent
entry; dates are retained rather than filtered by successful recording. -/
theorem rawCollection_datePrefix_append (z : Z) :
    rawCollectionNumericalDecoder rate (datePrefix rate (t.val + 1)
      (completeObservation rate rewards C_star C_h u t z)) =
      rawCollectionNumericalDecoder rate (datePrefix rate t.val
        (completeObservation rate rewards C_star C_h u t z)) ++ [(t, none)] := by
  rw [rawCollection_datePrefix rate rewards C_star C_h u t z _ (by omega),
    rawCollection_datePrefix rate rewards C_star C_h u t z _ (Nat.le_of_lt t.isLt)]
  have hb := actual_boundaries rate rewards C_star C_h u t z
  have he : t.val + 1 - start rate rewards C_star C_h u t z =
      (t.val - start rate rewards C_star C_h u t z) + 1 := by omega
  rw [he, List.take_add_one, rawCollection_current_lookup]
  rfl

private theorem measurable_currentIndex : Measurable
    (fun z : Z => t.val - start rate rewards C_star C_h u t z) :=
  (measurable_of_countable (fun s : ℕ => t.val - s)).comp
    ((ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
      rate rewards C_star C_h).comp measurable_subtype_coe)

/-- The actual source restricted to its genuine suffix index. This only
changes the subtype certificates; all original coordinates are retained. -/
def indexedCurrentSource (k : ℕ)
    (z : {z : Z // t.val - start rate rewards C_star C_h u t z = k}) :
    ReferenceCompleteSuffixInputMeasurability.IndexedSource rate rewards C_star C_h k :=
  ⟨z.val.val, z.property.symm.trans_lt
    (call_index_lt rate rewards C_star C_h u t z.val)⟩

private theorem indexedCurrentSource_record (k : ℕ)
    (z : {z : Z // t.val - start rate rewards C_star C_h u t z = k}) :
    ReferenceLaterLiveReadoutValuesMeasurability.actualRecord
      rate rewards C_star C_h k (indexedCurrentSource rate rewards C_star C_h u t k z) =
      callRecord rate rewards C_star C_h u t z.val := by
  apply congrArg ((ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z.val.val rewards C_star C_h).get)
  exact Fin.ext z.property.symm

/-- The same present readout in V's induced product/subtype domain. -/
def currentReadoutSource (k : ℕ)
    (z : {z : Z // t.val - start rate rewards C_star C_h u t z = k}) :
    ReferenceLaterLiveReadoutValuesMeasurability.ReadoutSource rate rewards C_star C_h k :=
  ⟨(start rate rewards C_star C_h u t z.val,
    indexedCurrentSource rate rewards C_star C_h u t k z), by
      change (ReferenceLaterLiveNumericalReadout.laterLiveReadout
        (start rate rewards C_star C_h u t z.val)
        (ReferenceLaterLiveReadoutValuesMeasurability.actualRecord rate rewards C_star C_h k
          (indexedCurrentSource rate rewards C_star C_h u t k z))).isSome = true
      rw [indexedCurrentSource_record]
      exact wholeCell_present rate rewards C_star C_h u t z.val⟩

theorem currentReadoutSource_actualCell (k : ℕ)
    (z : {z : Z // t.val - start rate rewards C_star C_h u t z = k}) :
    ReferenceLaterLiveReadoutValuesMeasurability.actualCell rate rewards C_star C_h k
      (currentReadoutSource rate rewards C_star C_h u t k z) =
      wholeCell rate rewards C_star C_h u t z.val := by
  have he : ReferenceLaterLiveReadoutValuesMeasurability.actualRecord
      rate rewards C_star C_h k (indexedCurrentSource rate rewards C_star C_h u t k z) =
      callRecord rate rewards C_star C_h u t z.val := by
    exact indexedCurrentSource_record rate rewards C_star C_h u t k z
  apply Option.some.inj
  calc
    some (ReferenceLaterLiveReadoutValuesMeasurability.actualCell rate rewards C_star C_h k
      (currentReadoutSource rate rewards C_star C_h u t k z)) =
        ReferenceLaterLiveNumericalReadout.laterLiveReadout
          (start rate rewards C_star C_h u t z.val)
          (ReferenceLaterLiveReadoutValuesMeasurability.actualRecord
            rate rewards C_star C_h k
            (indexedCurrentSource rate rewards C_star C_h u t k z)) := Option.some_get _
    _ = some (wholeCell rate rewards C_star C_h u t z.val) := by
      rw [he, wholeCell_readout]

private theorem measurable_currentReadoutSource (k : ℕ) :
    Measurable (currentReadoutSource rate rewards C_star C_h u t k) := by
  apply Measurable.subtype_mk
  have hstart : Measurable (fun z :
      {z : Z // t.val - start rate rewards C_star C_h u t z = k} =>
      start rate rewards C_star C_h u t z.val) :=
    (ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
      rate rewards C_star C_h).comp
        (measurable_subtype_coe.comp measurable_subtype_coe)
  exact hstart.prodMk
    ((measurable_subtype_coe.comp measurable_subtype_coe).subtype_mk)

private theorem measurable_of_index_strata {A : Type*} [MeasurableSpace A]
    (f : Z → A)
    (hf : ∀ k : ℕ, Measurable (fun z :
      {z : Z // t.val - start rate rewards C_star C_h u t z = k} => f z.val)) :
    Measurable f := by
  intro s hs
  have he : f ⁻¹' s = ⋃ k : ℕ, Subtype.val ''
      ((fun z : {z : Z // t.val - start rate rewards C_star C_h u t z = k} =>
        f z.val) ⁻¹' s) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
    constructor
    · intro hz
      exact ⟨_, ⟨z, rfl⟩, hz, rfl⟩
    · rintro ⟨k, w, hw, rfl⟩
      exact hw
  rw [he]
  apply MeasurableSet.iUnion
  intro k
  exact ((measurableSet_singleton k).preimage
    (measurable_currentIndex rate rewards C_star C_h u t)).subtype_image (hf k hs)

/-- Borel numerical coordinates of the canonical actual whole cell, with the
ordinary product Borel fields on the entire reward and rate vectors. -/
theorem measurable_wholeCellNumericalCoordinates :
    Measurable (wholeCellNumericalCoordinates rate rewards C_star C_h u t) := by
  apply measurable_of_index_strata rate rewards C_star C_h u t
  intro k
  have h := (ReferenceLaterLiveReadoutValuesMeasurability.measurable_numericalCoordinates_actualCell
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) k).comp
      (measurable_currentReadoutSource rate rewards C_star C_h u t k)
  convert h using 1
  funext z
  simp only [Function.comp_apply, currentReadoutSource_actualCell]
  rfl

/-- The same enabled flag and all actual integer arrivals are Borel. -/
theorem measurable_wholeCellArrivalCoordinates : Measurable
    (fun z : Z => ReferenceLaterLiveReadoutValuesMeasurability.arrivalCoordinates rate
      (wholeCell rate rewards C_star C_h u t z)) := by
  apply measurable_of_index_strata rate rewards C_star C_h u t
  intro k
  have h := (ReferenceLaterLiveReadoutValuesMeasurability.measurable_arrivalCoordinates_actualCell
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) k).comp
      (measurable_currentReadoutSource rate rewards C_star C_h u t k)
  convert h using 1
  funext z
  simp only [Function.comp_apply, currentReadoutSource_actualCell]

theorem wholeCell_enabled (z : Z) :
    (wholeCell rate rewards C_star C_h u t z).enabled = true := by
  obtain ⟨cell, hcell, henabled, _⟩ := wholeCell_physical rate rewards C_star C_h u t z
  rw [← hcell]
  exact henabled

/-- The stopped branch emits a disabled zero record. Otherwise the actual
enabled cell serves each arm, including an arm with zero arrival. -/
theorem wholeCell_acceptedRecord (z : Z) (j : Fin p.K) :
    RecordedQueueRun.acceptedRecord (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (incoming rate rewards C_star C_h u t z)
      (wholeCell rate rewards C_star C_h u t z) j =
      if (incoming rate rewards C_star C_h u t z).overflow then (false, 0)
      else (true, RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (wholeCell rate rewards C_star C_h u t z) j) := by
  simp only [RecordedQueueRun.acceptedRecord, wholeCell_enabled, ite_true]

open ReferenceActiveHorizonMeasurability

private instance recordListMeasurableSingleton :
    MeasurableSingletonClass (List (Bool × ℕ)) where
  measurableSet_singleton l := by
    let : MeasurableSingletonClass (Unit ⊕ (Bool × ℕ)) := ⟨fun x => by
      cases x with
      | inl a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inl_image
      | inr a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inr_image⟩
    have hinj : Function.Injective (listObservationCoordinates (α := Bool × ℕ)) := by
      intro a b h
      apply List.ext_getElem (congrArg Prod.fst h)
      intro i hi hj
      have he := congrFun (congrArg Prod.snd h) i
      simpa only [listObservationCoordinates, listObservationAt,
        List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Sum.inr.injEq] using he
    have hh := measurable_listObservationCoordinates
      (MeasurableSet.singleton (listObservationCoordinates l))
    convert hh using 1
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, hinj.eq_iff]

private theorem measurable_readoutUpdate : Measurable (fun v :
      ((Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ)))) ×
        (Fin p.K → Bool × ℕ) =>
      let registers := fun j => QueueReplay.transition (4 * rate.n) (v.1.1 j) (v.2 j)
      (registers, v.1.2.1 || decide (∃ j, 32 * (registers j).2 > D p),
        fun j => v.1.2.2 j ++ [v.2 j])) := measurable_of_countable _

private theorem measurable_stoppedStep {Y : Type*} [MeasurableSpace Y]
    (state : Y → RecordedQueueRun.RunState p.K)
    (cell : Y → RecordedQueueRun.RoundInput p.K)
    (hs : Measurable (fun y =>
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout (state y)))
    (ha : Measurable (fun y =>
      ReferenceLaterLiveReadoutValuesMeasurability.arrivalCoordinates rate (cell y))) :
    Measurable (fun y => ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
      (RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (state y) (cell y))) := by
  have hflag : Measurable (fun y => (state y).overflow) :=
    measurable_fst.comp (measurable_snd.comp hs)
  have henabled : Measurable (fun y => (cell y).enabled) := measurable_fst.comp ha
  have harrival : Measurable (fun y => fun j : Fin p.K =>
      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (cell y) j) := measurable_snd.comp ha
  have haccepted : Measurable (fun y => fun j : Fin p.K =>
      RecordedQueueRun.acceptedRecord (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (state y) (cell y) j) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_of_countable (fun v : Bool × (Bool × ℕ) =>
      if v.1 then (false, 0) else if v.2.1 then (true, v.2.2) else (false, 0))).comp
        (hflag.prodMk (henabled.prodMk ((measurable_pi_apply j).comp harrival)))
  exact (measurable_readoutUpdate rate).comp (hs.prodMk haccepted)

/-- Borelness of the complete stopped output, including overflow and every
accepted history, uses the inherited incoming state and the actual arrivals. -/
theorem measurable_wholePostReadout :
    Measurable (wholePostReadout rate rewards C_star C_h u t) := by
  exact measurable_stoppedStep rate
    (incoming rate rewards C_star C_h u t) (wholeCell rate rewards C_star C_h u t)
    (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_incomingReadout
      rate rewards C_star C_h u t)
    (measurable_wholeCellArrivalCoordinates rate rewards C_star C_h u t)

/-- Prefix factorization retains J's original source-prefix map and every
continuous source coordinate, including the terminal prefix. -/
theorem completeObservationPrefix_factor (control0 : TimeControl p)
    (n : ℕ) (hn : n ≤ p.T) (z : Z) :
    datePrefix rate n (completeObservation rate rewards C_star C_h u t z) =
      datePrefix rate n (completeBranchObservation rate rewards C_star C_h
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z.val)) :=
  datePrefix_factor rate rewards C_star C_h control0 n hn z.val

/-- This is the induced original source-prefix field, without an assertion
that it equals the physical pre-sampler information field. -/
theorem measurable_completeObservationPrefix (control0 : TimeControl p)
    (n : ℕ) (hn : n ≤ p.T) :
    Measurable[MeasurableSpace.comap (fun z : Z => z.val)
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1))]
      (fun z : Z => datePrefix rate n
        (completeObservation rate rewards C_star C_h u t z)) :=
  (datePrefix_measurable rate rewards C_star C_h control0 n hn).comp (comap_measurable _)

/-- Every old LIVE cell is the actual raw LIVE entry, and the collection
projection at that same date is absent. This uses the original first window. -/
theorem liveCells_rawObservation (z : Z)
    (k : Fin (liveCells rate rewards C_star C_h u t z).length) :
    ∃ date : Fin p.T, date.val = start rate rewards C_star C_h u t z + k.val ∧
      (rawLiveNumericalDecoder rate
        (completeObservation rate rewards C_star C_h u t z))[k.val]? =
          some (date, some (encodeNumerical
            ((liveCells rate rewards C_star C_h u t z).get k))) ∧
      (rawCollectionNumericalDecoder rate
        (completeObservation rate rewards C_star C_h u t z))[k.val]? =
          some (date, none) := by
  let hc := crossing rate rewards C_star C_h u t z
  obtain ⟨_, _, hcells⟩ := actualFirstLiveRawObservationIdentity rate rewards C_star C_h z.val hc
  have hcellsEq : liveCells rate rewards C_star C_h u t z =
      ReferenceFirstWindowNumericalStream.actualLiveSourceCells
        rate z.val rewards C_star C_h hc
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h)
        (firstPhaseSpan rate rewards C_star C_h z.val) := by
    simp only [liveCells, start_eq_physicalStart]
  have hlen : (liveCells rate rewards C_star C_h u t z).length =
      (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate z.val rewards C_star C_h hc
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h)
        (firstPhaseSpan rate rewards C_star C_h z.val)).length := by
    rw [hcellsEq, ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length]
  let q : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z.val rewards C_star C_h hc
      (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h)
      (firstPhaseSpan rate rewards C_star C_h z.val)).length :=
    ⟨k.val, k.isLt.trans_eq hlen⟩
  obtain ⟨_, hdate, hlive, hcollection, _⟩ := hcells q
  refine ⟨_, hdate, ?_, hcollection⟩
  simpa only [completeObservation, hcellsEq, List.get_eq_getElem, q,
    encodeNumerical, ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates,
    ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates] using hlive

/-- The old collection inputs, including the cutoff head and disabled cells,
are read from their original complete-suffix positions. -/
theorem collectionCells_rawObservation (z : Z) (k : Fin (t.val - u.val)) :
    ∃ date : Fin p.T, date.val = u.val + k.val ∧
      (rawLiveNumericalDecoder rate
        (completeObservation rate rewards C_star C_h u t z))[
          u.val - start rate rewards C_star C_h u t z + k.val]? = some (date, none) ∧
      (rawCollectionNumericalDecoder rate
        (completeObservation rate rewards C_star C_h u t z))[
          u.val - start rate rewards C_star C_h u t z + k.val]? =
            some (date, some (encodeNumerical
              ((collectionCells rate rewards C_star C_h u t z)[k.val]'(by
                rw [collectionCells_length]; exact k.isLt)))) := by
  let record := collectionRecord rate rewards C_star C_h u t z k
  have hcollection := ReferenceFirstCollectionRenewalIncomingQueueMeasurability.collectionReadout_zero
    rate rewards C_star C_h u t z k
  have hnone : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = none := by
    cases h : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record with
    | none => rfl
    | some cell =>
        have hdisjoint := readouts_disjoint rate 0 record
        rw [h, hcollection] at hdisjoint
        exact False.elim (hdisjoint ⟨rfl, rfl⟩)
  refine ⟨record.input.time,
    (collectionRecord_facts rate rewards C_star C_h u t z k).2.2.2, ?_,
    ReferenceFirstCollectionRenewalIncomingQueueMeasurability.rawCollection_lookup
      rate rewards C_star C_h u t z k⟩
  unfold completeObservation
  rw [rawLiveNumericalDecoder_completeSuffixRecords, List.getElem?_map]
  have hlookup := collectionRecord_lookup rate rewards C_star C_h u t z k
  unfold sourceRecords at hlookup
  rw [hlookup, Option.map_some, hnone]
  rfl

/-- The two raw strict-past projections recover precisely the original
chronological `pastCells`, with the actual date and complementary absence. -/
theorem pastCells_rawPrefix_lookup (z : Z)
    (k : Fin (pastCells rate rewards C_star C_h u t z).length) :
    ∃ date : Fin p.T, date.val = start rate rewards C_star C_h u t z + k.val ∧
      (rawLiveNumericalDecoder rate (datePrefix rate t.val
        (completeObservation rate rewards C_star C_h u t z)))[k.val]? =
        some (date, if k.val < (liveCells rate rewards C_star C_h u t z).length
          then some (encodeNumerical ((pastCells rate rewards C_star C_h u t z).get k))
          else none) ∧
      (rawCollectionNumericalDecoder rate (datePrefix rate t.val
        (completeObservation rate rewards C_star C_h u t z)))[k.val]? =
        some (date, if k.val < (liveCells rate rewards C_star C_h u t z).length
          then none
          else some (encodeNumerical ((pastCells rate rewards C_star C_h u t z).get k))) := by
  have hk : k.val < t.val - start rate rewards C_star C_h u t z := by
    simpa only [pastCells_length, pastLength] using k.isLt
  rw [rawLive_datePrefix rate rewards C_star C_h u t z _ (Nat.le_of_lt t.isLt),
    rawCollection_datePrefix rate rewards C_star C_h u t z _ (Nat.le_of_lt t.isLt),
    List.getElem?_take_of_lt hk, List.getElem?_take_of_lt hk]
  by_cases hl : k.val < (liveCells rate rewards C_star C_h u t z).length
  · obtain ⟨date, hd, hL, hC⟩ := liveCells_rawObservation rate rewards C_star C_h u t z ⟨k.val, hl⟩
    have he : (pastCells rate rewards C_star C_h u t z).get k =
        (liveCells rate rewards C_star C_h u t z)[k.val] :=
      List.getElem_append_left hl
    exact ⟨date, hd, by simpa only [hl, ite_true, he, List.get_eq_getElem] using hL,
      by simpa only [hl, ite_true] using hC⟩
  · let q : Fin (t.val - u.val) :=
      ⟨k.val - (liveCells rate rewards C_star C_h u t z).length, by
        have hb := k.isLt
        have hlen : (pastCells rate rewards C_star C_h u t z).length =
            (liveCells rate rewards C_star C_h u t z).length + (t.val - u.val) := by
          rw [pastCells, List.length_append, collectionCells_length]
        omega⟩
    have hb := actual_boundaries rate rewards C_star C_h u t z
    have hlen := liveCells_length rate rewards C_star C_h u t z
    have hindex : u.val - start rate rewards C_star C_h u t z + q.val = k.val := by
      dsimp only [q]
      omega
    obtain ⟨date, hd, hL, hC⟩ := collectionCells_rawObservation rate rewards C_star C_h u t z q
    rw [hindex] at hL hC
    have he : (pastCells rate rewards C_star C_h u t z).get k =
        (collectionCells rate rewards C_star C_h u t z)[q.val]'(by
          rw [collectionCells_length]; exact q.isLt) :=
      List.getElem_append_right (Nat.le_of_not_gt hl)
    refine ⟨date, ?_, ?_, ?_⟩
    · omega
    · simpa only [hl, ite_false] using hL
    · simpa only [hl, ite_false, he] using hC

/-- The two dated raw projections jointly recover the full original input
list. Complementary absent entries remain in the two projections above. -/
theorem pastCells_rawPrefix_join (z : Z) :
    List.zipWith (fun a b => a.2.or b.2)
      (rawLiveNumericalDecoder rate (datePrefix rate t.val
        (completeObservation rate rewards C_star C_h u t z)))
      (rawCollectionNumericalDecoder rate (datePrefix rate t.val
        (completeObservation rate rewards C_star C_h u t z))) =
      (pastCells rate rewards C_star C_h u t z).map (fun c => some (encodeNumerical c)) := by
  have hlen : (datePrefix rate t.val
      (completeObservation rate rewards C_star C_h u t z)).length =
      (pastCells rate rewards C_star C_h u t z).length := by
    rw [completeObservation, datePrefix_length rate rewards C_star C_h
      t.val (Nat.le_of_lt t.isLt), pastCells_length]
    rfl
  apply List.ext_getElem?
  intro n
  by_cases hn : n < (pastCells rate rewards C_star C_h u t z).length
  · obtain ⟨date, _, hL, hC⟩ := pastCells_rawPrefix_lookup rate rewards C_star C_h u t z ⟨n, hn⟩
    rw [List.getElem?_zipWith, hL, hC, List.getElem?_map,
      List.getElem?_eq_getElem hn]
    by_cases hl : n < (liveCells rate rewards C_star C_h u t z).length
    · simp only [hl, ite_true, Option.some_or, Option.map_some, List.get_eq_getElem]
    · simp only [hl, ite_false, Option.none_or, Option.map_some, List.get_eq_getElem]
  · have hL : (rawLiveNumericalDecoder rate (datePrefix rate t.val
        (completeObservation rate rewards C_star C_h u t z))).length ≤ n := by
      rw [rawLiveNumericalDecoder_length, hlen]
      omega
    rw [List.getElem?_zipWith, List.getElem?_eq_none hL,
      List.getElem?_map, List.getElem?_eq_none (Nat.le_of_not_gt hn)]
    rfl

/-- This is the same original numerical prefix after the actual current
whole marker, with no replacement calendar or numerical completion. -/
theorem appendedCells_rawPrefix_join (z : Z) :
    List.zipWith (fun a b => a.2.or b.2)
      (rawLiveNumericalDecoder rate (datePrefix rate (t.val + 1)
        (completeObservation rate rewards C_star C_h u t z)))
      (rawCollectionNumericalDecoder rate (datePrefix rate (t.val + 1)
        (completeObservation rate rewards C_star C_h u t z))) =
      (pastCells rate rewards C_star C_h u t z ++ [wholeCell rate rewards C_star C_h u t z]).map
        (fun c => some (encodeNumerical c)) := by
  rw [rawLive_datePrefix_append, rawCollection_datePrefix_append,
    List.zipWith_append (by rw [rawLiveNumericalDecoder_length,
      rawCollectionNumericalDecoder_length]), pastCells_rawPrefix_join, List.map_append]
  rfl

/-- The actual whole reward vector is read at the original calendar date;
the full rate vector comes from the actual selected payload. -/
theorem wholeCell_numerical (z : Z) :
    (wholeCell rate rewards C_star C_h u t z).enabled = true ∧
    ∃ selected : ReferenceActivePhysicalStep.Selection
        (callRecord rate rewards C_star C_h u t z).input,
      (callRecord rate rewards C_star C_h u t z).output.preparation.coordinator.selection =
        some selected ∧
      (wholeCell rate rewards C_star C_h u t z).reward =
        (fun j => ((rewards t j).val : ℝ) / (D p : ℝ)) ∧
      (wholeCell rate rewards C_star C_h u t z).rate = selected.view.payload.rate := by
  obtain ⟨henabled, selected, hselected, hreward, hrate, _⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical
      (start rate rewards C_star C_h u t z) (callRecord rate rewards C_star C_h u t z)
      (wholeCell rate rewards C_star C_h u t z) (wholeCell_readout rate rewards C_star C_h u t z)
  obtain ⟨_, _, _, _, _, hwholeRewards, _⟩ := wholeCell_physical rate rewards C_star C_h u t z
  rw [hwholeRewards, callRecord_time] at hreward
  exact ⟨henabled, selected, hselected, hreward, hrate⟩

theorem measurable_wholeCellNumericalReadout : Measurable
    (fun z : Z => encodeNumerical (wholeCell rate rewards C_star C_h u t z)) :=
  measurable_wholeCellNumericalCoordinates rate rewards C_star C_h u t

/-- At the terminal observation boundary the entire existing observation
has been exposed. The boundary is a natural number, not another action. -/
theorem completeObservation_terminalPrefix (z : Z) :
    datePrefix rate p.T (completeObservation rate rewards C_star C_h u t z) =
      completeObservation rate rewards C_star C_h u t z := by
  apply List.filter_eq_self.mpr
  intro entry _
  exact decide_eq_true entry.1.isLt

theorem wholePostReadout_register (z : Z) (j : Fin p.K) :
    (wholePostReadout rate rewards C_star C_h u t z).1 j =
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (pastCells rate rewards C_star C_h u t z ++
          [wholeCell rate rewards C_star C_h u t z])).registers j :=
  congrFun (wholePostReadout_registers rate rewards C_star C_h u t z) j

theorem wholePostReadout_acceptedHistory (z : Z) (j : Fin p.K) :
    (wholePostReadout rate rewards C_star C_h u t z).2.2 j =
      (incoming rate rewards C_star C_h u t z).records j ++
        [if (incoming rate rewards C_star C_h u t z).overflow then (false, 0)
          else (true, RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (wholeCell rate rewards C_star C_h u t z) j)] := by
  change (incoming rate rewards C_star C_h u t z).records j ++
      [RecordedQueueRun.acceptedRecord (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (incoming rate rewards C_star C_h u t z)
        (wholeCell rate rewards C_star C_h u t z) j] = _
  rw [wholeCell_acceptedRecord]

theorem measurable_wholePostReadout_register (j : Fin p.K) : Measurable
    (fun z : Z => (wholePostReadout rate rewards C_star C_h u t z).1 j) :=
  (measurable_pi_apply j).comp (measurable_fst.comp
    (measurable_wholePostReadout rate rewards C_star C_h u t))

theorem measurable_wholePostReadout_overflow : Measurable
    (fun z : Z => (wholePostReadout rate rewards C_star C_h u t z).2.1) :=
  measurable_fst.comp (measurable_snd.comp
    (measurable_wholePostReadout rate rewards C_star C_h u t))

theorem measurable_wholePostReadout_acceptedHistory (j : Fin p.K) : Measurable
    (fun z : Z => (wholePostReadout rate rewards C_star C_h u t z).2.2 j) :=
  (measurable_pi_apply j).comp (measurable_snd.comp (measurable_snd.comp
    (measurable_wholePostReadout rate rewards C_star C_h u t)))

end Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix

end
