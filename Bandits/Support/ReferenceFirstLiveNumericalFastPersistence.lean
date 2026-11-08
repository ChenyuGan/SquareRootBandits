/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLaunchOriginalAuxiliaryReward
public import Bandits.Support.ReferenceCompleteOriginalCalendarRawLearningComparison

import Mathlib.Tactic
import Lean.Elab.Tactic.Omega

/-!
# Numerical FAST identity on the actual first-live source window

Every cell in this module is selected from the actual first-live physical
window on the original source input. The results identify its born payload,
its actual pre-choice complement weights, and its reserved FAST draw with the
full numerical queue weights. No path or sampling law is constructed here.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceFirstLiveOverflowReadout
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.ReferenceAssignmentPayloadPersistence
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CoordinatorAssignmentRegisterInstall
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.CanonicalFastSampling

namespace Bandits.Support.ReferenceFirstLiveNumericalFastPersistence

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable {p : Parameters}

private theorem actual_cell_of_whole_index
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p)
    (k : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h source).length) :
    ∃ (s : Fin (p.T + 1))
      (fiber : ReferenceFirstLiveOverflowReadout.LaunchFiber
        rate rewards C_star C_h s.val)
      (j : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate fiber.val rewards C_star C_h
        (ReferenceFirstLiveOverflowReadout.launch_crossing
          rate rewards C_star C_h s.val fiber)
        (p.T - s.val)
        (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
          s.val (p.T - s.val)
          (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber)).length),
      fiber.val = source ∧
      j.val = k.val ∧
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
        rate rewards C_star C_h source)[k.val]'k.isLt =
        (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
          rate fiber.val rewards C_star C_h
          (ReferenceFirstLiveOverflowReadout.launch_crossing
            rate rewards C_star C_h s.val fiber)
          (p.T - s.val)
          (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
            s.val (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s)
            fiber) j).input := by
  classical
  let boundary := ReferenceCompletePhysicalHistory.generatedBoundary
    rate source rewards C_star C_h
  by_cases hc : boundary.crossing.isSome = true
  · let start := ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h
    have hstart : start ≤ p.T :=
      ReferenceCompletePhysicalHistory.physicalStart_le_T rate source rewards C_star C_h
    let s : Fin (p.T + 1) := ⟨start, by omega⟩
    let fiber : ReferenceFirstLiveOverflowReadout.LaunchFiber
        rate rewards C_star C_h s.val :=
      ⟨source, by
        change boundary.crossing.isSome = true ∧
          ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = s.val
        exact ⟨hc, rfl⟩⟩
    have hwhole := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
      rate rewards C_star C_h s fiber
    have hlength :
        (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
          rate rewards C_star C_h source).length =
        (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
          rate fiber.val rewards C_star C_h
          (ReferenceFirstLiveOverflowReadout.launch_crossing
            rate rewards C_star C_h s.val fiber)
          (p.T - s.val)
          (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
            s.val (p.T - s.val)
            (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber)).length := by
      calc
        _ = (ReferenceFirstLiveOverflowReadout.firstLiveCells
            rate rewards C_star C_h s.val (p.T - s.val)
            (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber).length :=
              congrArg List.length hwhole.2
        _ = (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
            rate fiber.val rewards C_star C_h
            (ReferenceFirstLiveOverflowReadout.launch_crossing
              rate rewards C_star C_h s.val fiber)
            (p.T - s.val)
            (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
              s.val (p.T - s.val)
              (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber)).length := rfl
        _ = (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
            rate fiber.val rewards C_star C_h
            (ReferenceFirstLiveOverflowReadout.launch_crossing
              rate rewards C_star C_h s.val fiber)
            (p.T - s.val)
            (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
              s.val (p.T - s.val)
              (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber)).length :=
              ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
                rate fiber.val rewards C_star C_h
                (ReferenceFirstLiveOverflowReadout.launch_crossing
                  rate rewards C_star C_h s.val fiber)
                (p.T - s.val)
                (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
                  s.val (p.T - s.val)
                  (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber)
    let j : Fin ((ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate fiber.val rewards C_star C_h
        (ReferenceFirstLiveOverflowReadout.launch_crossing
          rate rewards C_star C_h s.val fiber)
        (p.T - s.val)
        (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
          s.val (p.T - s.val)
          (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber)).length) :=
      ⟨k.val, by rw [← hlength]; exact k.isLt⟩
    have hindex :
        (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
          rate rewards C_star C_h source)[k.val]'k.isLt =
          (ReferenceFirstLiveOverflowReadout.firstLiveCells
            rate rewards C_star C_h s.val (p.T - s.val)
            (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber)[j.val]'(by
              simpa only [ReferenceFirstLiveOverflowReadout.firstLiveCells] using
                (ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
                  rate fiber.val rewards C_star C_h
                  (ReferenceFirstLiveOverflowReadout.launch_crossing
                    rate rewards C_star C_h s.val fiber)
                  (p.T - s.val)
                  (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
                    s.val (p.T - s.val)
                    (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber)).symm ▸ j.isLt) := by
      have hget := getElem_congr_coll
        (c := ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
          rate rewards C_star C_h source)
        (d := ReferenceFirstLiveOverflowReadout.firstLiveCells
          rate rewards C_star C_h s.val (p.T - s.val)
          (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber)
        (i := k.val) (w := k.isLt) hwhole.2
      simpa only [j, Fin.val_mk] using hget
    have hget := ReferenceFirstWindowNumericalStream.actualLiveSourceCells_get
      rate fiber.val rewards C_star C_h
      (ReferenceFirstLiveOverflowReadout.launch_crossing
        rate rewards C_star C_h s.val fiber)
      (p.T - s.val)
      (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
        s.val (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber)
      j
    have hget' :
        (ReferenceFirstLiveOverflowReadout.firstLiveCells
          rate rewards C_star C_h s.val (p.T - s.val)
          (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber)[j.val]'(by
            rw [ReferenceFirstLiveOverflowReadout.firstLiveCells_length
              rate rewards C_star C_h s.val (p.T - s.val)
              (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber]
            exact j.isLt) =
        (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
          rate fiber.val rewards C_star C_h
          (ReferenceFirstLiveOverflowReadout.launch_crossing
            rate rewards C_star C_h s.val fiber)
          (p.T - s.val)
          (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
            s.val (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s)
            fiber) j).input := by
      simpa only [ReferenceFirstLiveOverflowReadout.firstLiveCells] using hget
    exact ⟨s, fiber, j, rfl, rfl, hindex.trans hget'⟩
  · have hcross :
        (ReferenceCompletePhysicalHistory.generatedBoundary
          rate source rewards C_star C_h).crossing.isSome = false := by
      cases h : boundary.crossing <;> simp [boundary, h] at hc ⊢
    have hnil : ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
        rate rewards C_star C_h source = [] := by
      simp only [ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells, hcross,
        Bool.false_eq_true, dite_false]
    have hk : k.val < 0 := by
      have hk' := k.isLt
      simp only [hnil] at hk'
      simp at hk'
    have : False := by omega
    exact this.elim

private theorem actual_cell_payload_birth
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (s : Fin (p.T + 1))
    (fiber : ReferenceFirstLiveOverflowReadout.LaunchFiber
      rate rewards C_star C_h s.val)
    (j : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate fiber.val rewards C_star C_h
      (ReferenceFirstLiveOverflowReadout.launch_crossing
        rate rewards C_star C_h s.val fiber)
      (p.T - s.val)
      (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
        s.val (p.T - s.val)
        (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber)).length) :
    ∃ birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      birth ∈ (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
        rate fiber.val rewards C_star C_h
        (ReferenceFirstLiveOverflowReadout.launch_crossing
          rate rewards C_star C_h s.val fiber)
        (p.T - s.val)
        (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
          s.val (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber)).records ∧
      birth.input.time.val = s.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth
        (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
          rate fiber.val rewards C_star C_h
          (ReferenceFirstLiveOverflowReadout.launch_crossing
            rate rewards C_star C_h s.val fiber)
          (p.T - s.val)
          (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
            s.val (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s)
            fiber) j).selected.view.payload ∧
      ∃ hs : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput fiber.val rewards C_star C_h rate)).completed < p.T,
        birth = ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
          rate fiber.val rewards C_star C_h
          (ReferenceFirstLiveOverflowReadout.launch_crossing
            rate rewards C_star C_h s.val fiber) hs := by
  classical
  let hc := ReferenceFirstLiveOverflowReadout.launch_crossing
    rate rewards C_star C_h s.val fiber
  let hspan := ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
    s.val (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput fiber.val rewards C_star C_h rate)).completed
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate fiber.val rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate fiber.val rewards C_star C_h hc
  let execution := ReferenceActivePhysicalHorizon.run initial fiber.val.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p fiber.val) rewards start
    (p.T - s.val) hspan seed.activeAtStart
  let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate fiber.val rewards C_star C_h hc (p.T - s.val) hspan
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate fiber.val rewards C_star C_h hc (p.T - s.val) hspan j
  obtain ⟨birth, hbirthMem, hbirthTime, hbirth, _, _⟩ :=
    ReferenceFirstDownRecoveryBudget.run_first_selected_payload
      initial fiber.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p fiber.val)
      rewards start (p.T - s.val) hspan seed.activeAtStart seed.coordinatorFirst
      j cell.selected cell.selection_actual
  have hcount : 0 < p.T - s.val := by
    have hwindow :
        window.length ≤ (p.T - s.val) := by
      have hcountEq := ReferenceActivePhysicalHorizon.run_record_count
        initial fiber.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p fiber.val)
        rewards start (p.T - s.val) hspan seed.activeAtStart
      exact (List.takeWhile_prefix _).length_le.trans hcountEq.le
    have hj : 0 < window.length := Nat.zero_lt_of_lt j.isLt
    omega
  have hfull : start + (p.T - s.val) ≤ p.T := hspan
  have hs : start < p.T := by omega
  let first := ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
    rate fiber.val rewards C_star C_h hc hs
  have hfirstMem : first ∈ execution.records := by
    obtain ⟨suffix, hprefix⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
      initial fiber.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p fiber.val)
      rewards start 1 ((p.T - s.val) - 1) (by omega) seed.activeAtStart
    have hprefix' : execution.records =
        (ReferenceActivePhysicalHorizon.run initial fiber.val.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p fiber.val) rewards
          start 1 (by omega) seed.activeAtStart).records ++ suffix := by
      simpa only [execution, Nat.add_sub_of_le hcount] using hprefix
    have hfirstRun :
        (ReferenceActivePhysicalHorizon.run initial fiber.val.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p fiber.val) rewards
          start 1 (by omega) seed.activeAtStart).records = [first] := by
      simpa only [ReferenceFirstLaunchNumericalCell.firstPhysicalRun] using
        ReferenceFirstLaunchNumericalCell.firstPhysicalRun_records
          rate fiber.val rewards C_star C_h hc hs
    rw [hprefix']
    rw [hfirstRun]
    exact List.mem_append_left _ (List.mem_singleton_self _)
  rcases ReferenceFirstLaunchNumericalCell.firstPhysicalRecord_source_inputs
      rate fiber.val rewards C_star C_h hc hs with
    ⟨hfirstState, hfirstTime, hfirstRows, hfirstSelected, hfirstRewards⟩
  have hbirthEq : birth = first :=
    ReferenceAssignmentPayloadChronology.run_records_time_injective
      initial fiber.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p fiber.val)
      rewards start (p.T - s.val) hspan seed.activeAtStart hbirthMem hfirstMem
      (hbirthTime.trans hfirstTime.symm)
  subst birth
  have hElapsed : start = s.val :=
    ReferenceFirstLiveOverflowReadout.launch_elapsed rate rewards C_star C_h s.val fiber
  exact ⟨first, hfirstMem, hfirstTime.trans hElapsed, hbirth,
    ⟨by simpa only [start] using hs, rfl⟩⟩

private theorem actual_cell_first_installation
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (s : Fin (p.T + 1))
    (fiber : ReferenceFirstLiveOverflowReadout.LaunchFiber
      rate rewards C_star C_h s.val)
    (j : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate fiber.val rewards C_star C_h
      (ReferenceFirstLiveOverflowReadout.launch_crossing
        rate rewards C_star C_h s.val fiber)
      (p.T - s.val)
      (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
        s.val (p.T - s.val)
        (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber)).length) :
    ∃ hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput fiber.val rewards C_star C_h rate)).completed < p.T,
      let first := ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
        rate fiber.val rewards C_star C_h
        (ReferenceFirstLiveOverflowReadout.launch_crossing rate rewards C_star C_h s.val fiber) hs
      let launch := CoordinatorRoundDispatch.firstLaunchInput
        (ReferenceActivePhysicalStep.firstInput first.input)
      let payload :=
        (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
          rate fiber.val rewards C_star C_h
          (ReferenceFirstLiveOverflowReadout.launch_crossing rate rewards C_star C_h s.val fiber)
          (p.T - s.val)
          (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
            s.val (p.T - s.val)
            (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber) j).selected.view.payload
      ∃ installed : CoordinatorAssignmentRegisterInstall.FirstInstallation launch,
      ∃ arm : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
        installed.startRoundResult installed.registers.time installed.registers.complementWeights
        (ReferenceActivePhysicalStep.firstInput first.input).row,
        CoordinatorRoundDispatch.dispatchFirst
          (ReferenceActivePhysicalStep.firstInput first.input) = .chosen installed arm ∧
        payload = installed.registers.payload ∧
        (∀ a : Fin p.K, payload.anchor a = 1) ∧
        (∀ i : Fin (p.m - 1),
          payload.assignment.assigned i = installed.start.assignment.assigned i ∧
          payload.downRecord i = installed.start.outgoing i ∧
          payload.rate (payload.assignment.assigned i) =
            OrdinaryMessageCodec.dyadicRate (payload.downRecord i).val.h) ∧
        payload.slowSet =
          CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
            (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
            launch.coordinates ∧
        first.input.rows = fiber.val.1.2 ∧
        first.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p fiber.val ∧
        first.input.rewards = rewards ∧
        ∀ i : Fin (p.K + 1),
          launch.coordinates i = (first.input.row.2 first.input.time).1
            (ContinuousControlSlice.Label.assign i) := by
  classical
  obtain ⟨birth, _hmem, _htime, hbirth, ⟨hs, hbirthFirst⟩⟩ :=
    actual_cell_payload_birth rate rewards C_star C_h s fiber j
  let hc := ReferenceFirstLiveOverflowReadout.launch_crossing rate rewards C_star C_h s.val fiber
  let first := ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
    rate fiber.val rewards C_star C_h hc hs
  let launch := CoordinatorRoundDispatch.firstLaunchInput
    (ReferenceActivePhysicalStep.firstInput first.input)
  let payload :=
    (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate fiber.val rewards C_star C_h hc (p.T - s.val)
      (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
        s.val (p.T - s.val)
        (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber) j).selected.view.payload
  have hfirstInputs := ReferenceFirstLaunchNumericalCell.firstPhysicalRecord_source_inputs
    rate fiber.val rewards C_star C_h hc hs
  have hdispatch : first.output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch first.input := by
    rw [first.output_eq]
    rfl
  have hfirstState : first.input.state.coordinator = .first := by
    rw [hfirstInputs.1]
    exact (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate fiber.val rewards C_star C_h hc).coordinatorFirst
  have hbirthFirstRecord :
      ReferenceAssignmentPayloadPersistence.InstallationBirth first payload :=
    (congrArg (fun record => ReferenceAssignmentPayloadPersistence.InstallationBirth
      record payload) hbirthFirst).mp hbirth
  simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth] at hbirthFirstRecord
  rw [hdispatch, ReferenceActivePhysicalStep.dispatch_first first.input hfirstState]
    at hbirthFirstRecord
  cases hchosen : CoordinatorRoundDispatch.dispatchFirst
      (ReferenceActivePhysicalStep.firstInput first.input) with
  | choiceDomainFailure installed => simp only [hchosen] at hbirthFirstRecord
  | recorderBoundaryFailure installed => simp only [hchosen] at hbirthFirstRecord
  | choiceRejected installed => simp only [hchosen] at hbirthFirstRecord
  | chosen installed arm =>
      simp only [hchosen] at hbirthFirstRecord
      have hpayload : payload = installed.registers.payload := hbirthFirstRecord.1
      have hfacts := ReferenceFirstLaunchNumericalCell.first_installation_payload_facts
        rate fiber.val rewards C_star C_h hc hs installed arm hchosen
      have hinstalled := ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
        first.input installed arm hchosen
      have hslow : installed.registers.payload.slowSet =
          CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
            (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
            launch.coordinates := by
        calc
          installed.registers.payload.slowSet =
              (CoordinatorAssignmentRegisterInstall.installFirst launch).registers.payload.slowSet := by
                rw [hinstalled]
          _ = (AssignmentStartPayload.Input.ofFirstAssignment launch).slowSet := by
                rw [CoordinatorAssignmentRegisterInstall.first_registers_payload]
          _ = launch.slowSet := rfl
          _ = CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
                (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
                launch.coordinates := rfl
      refine ⟨hs, installed, arm, ?_, hpayload, ?_, ?_, ?_, hfirstInputs.2.2.1,
        hfirstInputs.2.2.2.1, hfirstInputs.2.2.2.2, ?_⟩
      · exact hchosen
      · intro a
        change payload.anchor a = 1
        rw [hpayload]
        exact hfacts.2.1 a
      · intro i
        change payload.assignment.assigned i = installed.start.assignment.assigned i ∧
          payload.downRecord i = installed.start.outgoing i ∧
          payload.rate (payload.assignment.assigned i) =
            OrdinaryMessageCodec.dyadicRate (payload.downRecord i).val.h
        rw [hpayload]
        exact hfacts.2.2.1 i
      · change payload.slowSet = _
        rw [hpayload]
        exact hslow
      · intro i
        exact CoordinatorRoundDispatch.firstLaunchInput_coordinate
          (ReferenceActivePhysicalStep.firstInput first.input) i

/-- Every entry in the whole actual first-live source list is the input of an
actual selected cell. Its selected payload is the exact payload installed by
the first physical record, with the original launch vector and all assignment
and DOWN coordinates retained. -/
theorem wholeFirstLive_selected_payload_first_installation
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p)
    (k : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h source).length) :
    ∃ (s : Fin (p.T + 1))
      (fiber : ReferenceFirstLiveOverflowReadout.LaunchFiber
        rate rewards C_star C_h s.val)
      (j : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate fiber.val rewards C_star C_h
        (ReferenceFirstLiveOverflowReadout.launch_crossing
          rate rewards C_star C_h s.val fiber)
        (p.T - s.val)
        (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
          s.val (p.T - s.val)
          (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber)).length),
      fiber.val = source ∧
      j.val = k.val ∧
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
        rate rewards C_star C_h source)[k.val]'k.isLt =
        (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
          rate fiber.val rewards C_star C_h
          (ReferenceFirstLiveOverflowReadout.launch_crossing
            rate rewards C_star C_h s.val fiber)
          (p.T - s.val)
          (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
            s.val (p.T - s.val)
            (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber) j).input ∧
      ∃ hs : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput fiber.val rewards C_star C_h rate)).completed < p.T,
        let first := ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
          rate fiber.val rewards C_star C_h
          (ReferenceFirstLiveOverflowReadout.launch_crossing rate rewards C_star C_h s.val fiber) hs
        let launch := CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput first.input)
        let payload :=
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
            rate fiber.val rewards C_star C_h
            (ReferenceFirstLiveOverflowReadout.launch_crossing
              rate rewards C_star C_h s.val fiber)
            (p.T - s.val)
            (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
              s.val (p.T - s.val)
              (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber) j).selected.view.payload
        ∃ installed : CoordinatorAssignmentRegisterInstall.FirstInstallation launch,
        ∃ arm : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
          installed.startRoundResult installed.registers.time installed.registers.complementWeights
          (ReferenceActivePhysicalStep.firstInput first.input).row,
          CoordinatorRoundDispatch.dispatchFirst
            (ReferenceActivePhysicalStep.firstInput first.input) = .chosen installed arm ∧
          payload = installed.registers.payload ∧
          (∀ a : Fin p.K, payload.anchor a = 1) ∧
          (∀ i : Fin (p.m - 1),
            payload.assignment.assigned i = installed.start.assignment.assigned i ∧
            payload.downRecord i = installed.start.outgoing i ∧
            payload.rate (payload.assignment.assigned i) =
              OrdinaryMessageCodec.dyadicRate (payload.downRecord i).val.h) ∧
          payload.slowSet =
            CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
              (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
              launch.coordinates ∧
          first.input.rows = fiber.val.1.2 ∧
          first.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p fiber.val ∧
          first.input.rewards = rewards ∧
          ∀ i : Fin (p.K + 1),
            launch.coordinates i = (first.input.row.2 first.input.time).1
              (ContinuousControlSlice.Label.assign i) := by
  obtain ⟨s, fiber, j, hsource, hposition, hinput⟩ :=
    actual_cell_of_whole_index rate rewards C_star C_h source k
  exact ⟨s, fiber, j, hsource, hposition, hinput,
    actual_cell_first_installation rate rewards C_star C_h s fiber j⟩

/-- The full all-arm score vector before an actual first-live cell has the
source episode envelope. The queue input is the whole original source list
prefix, with no slow-arm fill-in. -/
theorem wholeFirstLive_full_scoreWeight_envelope
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p)
    (k : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h source).length)
    (a : Fin p.K) :
    1 ≤ RecordedQueueRun.scoreWeight
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (RecordedQueueRun.run
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
            rate rewards C_star C_h source).take k.val)) a ∧
      RecordedQueueRun.scoreWeight
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (RecordedQueueRun.run
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
            rate rewards C_star C_h source).take k.val)) a < 2 := by
  classical
  obtain ⟨s, fiber, j, hsource, hposition, _hinput⟩ :=
    actual_cell_of_whole_index rate rewards C_star C_h source k
  let hc := ReferenceFirstLiveOverflowReadout.launch_crossing
    rate rewards C_star C_h s.val fiber
  let count := p.T - s.val
  let hspan := ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
    s.val count (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber
  let initial := ReferenceFirstLaunchNumericalCell.launchState
    rate fiber.val rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate fiber.val rewards C_star C_h hc
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate fiber.val rewards C_star C_h hc count hspan j
  let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let rounds := (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate fiber.val rewards C_star C_h hc count hspan).take k.val
  have hgeometry := ReferenceFirstLiveDownNumericalRecovery.first_live_geometry
    initial fiber.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p fiber.val)
    rewards (ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput fiber.val rewards C_star C_h rate)).completed)
    count hspan seed.activeAtStart seed.coordinatorFirst
    j cell.selected cell.selection_actual
  rcases hgeometry with ⟨hsigma, htime, hgrid, _⟩
  let H := ReplayWeightStability.episodeHorizon rate.eta.val
  have hgrid' :
      ((ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate fiber.val rewards C_star C_h hc count hspan)[j.val]'j.isLt).input.time.val + 2 ≤
      H * ((cell.selected.view.payload.sigma.val + 1) / H + 1) := by
    rw [FollowerCutoffScan.gridBoundary] at hgrid
    exact hgrid.trans (Nat.min_le_right _ _)
  have hdiv := Nat.mod_add_div (cell.selected.view.payload.sigma.val + 1) H
  rw [hsigma] at hdiv
  have htime' :
      ((ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate fiber.val rewards C_star C_h hc count hspan)[j.val]'j.isLt).input.time.val =
        ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput
              fiber.val rewards C_star C_h rate)).completed + j.val := by
    simpa [ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun, initial] using htime
  have hsteps : k.val ≤ H := by
    change _ ≤ H * ((cell.selected.view.payload.sigma.val + 1) / H + 1) at hgrid'
    rw [Nat.mul_add, Nat.mul_one] at hgrid'
    rw [htime', hsigma] at hgrid'
    rw [← hposition]
    omega
  have hlength : rounds.length ≤ H := by
    dsimp [rounds]
    exact (List.length_take_le ..).trans hsteps
  have henvelope := RecordedEpisodeStability.execute_source_weight_envelope q
    (RecordedQueueRun.initialState p.K) rounds a hlength
  have hcellsFiber := (ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
    rate rewards C_star C_h s fiber).2
  have hcells :
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h source =
        ReferenceFirstWindowNumericalStream.actualLiveSourceCells
          rate fiber.val rewards C_star C_h hc count hspan := by
    calc
      _ = ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
          rate rewards C_star C_h fiber.val := by rw [← hsource]
      _ = ReferenceFirstLiveOverflowReadout.firstLiveCells
          rate rewards C_star C_h s.val count
          (ReferenceFirstLiveOverflowReadout.maximal_span s) fiber := hcellsFiber
      _ = ReferenceFirstWindowNumericalStream.actualLiveSourceCells
          rate fiber.val rewards C_star C_h hc count hspan := rfl
  have htake := congrArg
    (fun xs : List (RecordedQueueRun.RoundInput p.K) => xs.take k.val) hcells
  have hstate :
      RecordedQueueRun.run q
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
          rate rewards C_star C_h source).take k.val) =
      RecordedQueueRun.run q rounds := by
    change RecordedQueueRun.run q
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
          rate rewards C_star C_h source).take k.val) =
      RecordedQueueRun.run q
        ((ReferenceFirstWindowNumericalStream.actualLiveSourceCells
          rate fiber.val rewards C_star C_h hc count hspan).take k.val)
    exact congrArg (RecordedQueueRun.run q) htake
  rw [hstate]
  simpa only [RecordedQueueRun.run, RecordedQueueRun.scoreWeight,
    RecordedQueueRun.initialState, ScoreWeights.scoreWeight, pow_zero, mul_one] using
      And.intro henvelope.1 henvelope.2.1

private theorem actual_cell_prechoice_complement_weights
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (k : Fin (actualFirstLiveWindow rate source rewards C_star C_h hc count hspan).length)
    (hclear : (RecordedQueueRun.run
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((actualLiveSourceCells rate source rewards C_star C_h hc count hspan).take k.val)).overflow = false) :
    let cell := actualLiveSourceCellAt rate source rewards C_star C_h hc count hspan k
    ∀ a : FastArm cell.selected.view.payload.slowSet,
      cell.selected.view.complementWeights a = RecordedQueueRun.scoreWeight
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          ((actualLiveSourceCells rate source rewards C_star C_h hc count hspan).take k.val)) a.val := by
  classical
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let initial := ReferenceFirstLaunchNumericalCell.launchState
    rate source rewards C_star C_h hc
  let seed := actualFirstLiveSeed rate source rewards C_star C_h hc
  let record := (actualFirstLiveWindow rate source rewards C_star C_h hc count hspan)[k.val]
  let cell := actualLiveSourceCellAt rate source rewards C_star C_h hc count hspan k
  let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let cells := actualLiveSourceCells rate source rewards C_star C_h hc count hspan
  obtain ⟨hstep, hrecord, _⟩ :=
    ReferenceFirstLiveUnoccupiedEmission.window_record_eq_candidate
      initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards start count hspan seed.activeAtStart k
  have hstate : record.input.state =
      (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start k.val
        (by omega) seed.activeAtStart).finalState := by
    exact congrArg (fun current => current.input.state) hrecord
  have hactual : record.output.preparation.coordinator = dispatch record.input := by
    rw [record.output_eq]
    rfl
  have hbranches :=
    ReferenceFirstLiveCoordinatorNumericalService.actual_first_live_coordinator_service_branches
      rate source rewards C_star C_h hc count hspan k
  by_cases hkzero : k.val = 0
  · have hstateFirst : record.input.state.coordinator = .first := by
      rw [hstate]
      have hzero := ReferenceActivePhysicalHorizon.run_zero_final initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
        (by omega) seed.activeAtStart
      simpa only [hkzero, hzero] using seed.coordinatorFirst
    rcases hbranches with hfirst | hcontinuing
    · obtain ⟨installed, arm, hbranch, htime⟩ := hfirst
      have hchosen : CoordinatorRoundDispatch.dispatchFirst (firstInput record.input) =
          .chosen installed arm := by
        have heq := hactual
        rw [hbranch, dispatch_first record.input hstateFirst] at heq
        exact (DispatchCut.first.inj heq).symm
      have hinstallation := dispatchFirst_chosen_installation
        record.input installed arm hchosen
      have hone : ∀ a, installed.registers.complementWeights a = 1 := by
        rw [hinstallation]
        intro a
        exact CoordinatorAssignmentRegisterInstall.first_complementWeight_one _ a
      have hselection := cell.selection_actual
      rw [hbranch] at hselection
      have hselected := (ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq
        record.input installed.registers.payload installed.startRoundResult
        installed.registers.time installed.registers.complementWeights arm htime).symm.trans
          hselection
      have hview := congrArg (fun chosen : Selection record.input => chosen.view)
        (Option.some.inj hselected).symm
      change ∀ a : FastArm cell.selected.view.payload.slowSet, _ = _
      rw [hview]
      dsimp only [ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm]
      intro a
      rw [hone]
      simp only [hkzero, List.take_zero, RecordedQueueRun.run,
        RecordedQueueRun.scoreWeight, RecordedQueueRun.execute,
        RecordedQueueRun.initialState, ScoreWeights.scoreWeight, pow_zero]
    · obtain ⟨r, owned, base, dispatched, hstart, continuation, arm, hbranch⟩ := hcontinuing
      rw [hbranch, dispatch_first record.input hstateFirst] at hactual
      cases hactual
  · have hkpos : 0 < k.val := Nat.pos_of_ne_zero hkzero
    have hboundary :=
      ReferenceFirstLiveStoppedQueueComparison.actual_first_live_stopped_queue_common_boundary
        rate source rewards C_star C_h hc count hspan k.val k.isLt.le
    rcases hboundary with ⟨_, _, _, hoverflow, hsafe, _⟩
    change (RecordedQueueRun.run q (cells.take k.val)).overflow = true ↔
      UnstoppedRecordedQueueComparison.firstOverflowPrefix q cells ≤ k.val at hoverflow
    have hkappa : k.val ≤ UnstoppedRecordedQueueComparison.firstOverflowPrefix q cells := by
      by_contra hnot
      have hover := hoverflow.mpr (by omega)
      rw [hclear] at hover
      cases hover
    obtain ⟨hprefix, _, hpositive⟩ := hsafe hkappa
    obtain ⟨r, owned, base, hlive, _, _, _, _, hregisters, _⟩ := hpositive hkpos
    have hstateLive : record.input.state.coordinator = .live r owned base := by
      rw [hstate]
      exact hlive
    rcases hbranches with hfirst | hcontinuing
    · obtain ⟨installed, arm, hbranch, _⟩ := hfirst
      rw [hbranch] at hactual
      simp only [ReferenceActivePhysicalStep.dispatch, hstateLive,
        CoordinatorRoundDispatch.dispatch] at hactual
      cases hactual
    · obtain ⟨rNow, ownedNow, baseNow, dispatched, hstart, continuation, arm, hbranch⟩ :=
        hcontinuing
      have hregister : rNow = r := by
        have heq := hactual
        rw [hbranch] at heq
        have hprojection := congrArg
          (fun cut : DispatchCut record.input => match cut with
            | .live registers _ _ _ => some registers
            | _ => none) heq
        simp only [ReferenceActivePhysicalStep.dispatch, hstateLive,
        CoordinatorRoundDispatch.dispatch] at hprojection
        exact Option.some.inj hprojection
      subst rNow
      have hselection := cell.selection_actual
      rw [hbranch] at hselection
      have hselected := (ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq
        record.input r.payload dispatched.startResult record.input.time
        (liveRegistersAt r record.input.time).complementWeights arm rfl).symm.trans
          hselection
      have hview := congrArg (fun chosen : Selection record.input => chosen.view)
        (Option.some.inj hselected).symm
      change ∀ a : FastArm cell.selected.view.payload.slowSet, _ = _
      rw [hview]
      dsimp only [ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm]
      intro a
      have hscore := congrArg Prod.fst (hregisters a).1
      change r.complementScores a = _ at hscore
      change ScoreWeights.scoreWeight
        (AssignmentScoreReconstruction.sourceWeightBase p) (r.complementScores a) = _
      rw [hscore]
      rfl

/-- The selected complement weights at a whole-source index are the full
numerical queue weights restricted to that same selected complement. The only
localizer is the computed PRE-round overflow flag; the current update may be
the first one that detects overflow. -/
theorem wholeFirstLive_prechoice_complement_weights
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p)
    (k : Fin (wholeFirstLiveCells rate rewards C_star C_h source).length)
    (hclear : (RecordedQueueRun.run
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((wholeFirstLiveCells rate rewards C_star C_h source).take k.val)).overflow = false) :
    let W := RecordedQueueRun.scoreWeight
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        ((wholeFirstLiveCells rate rewards C_star C_h source).take k.val))
    ∃ (s : Fin (p.T + 1))
      (fiber : LaunchFiber rate rewards C_star C_h s.val)
      (j : Fin (actualFirstLiveWindow rate fiber.val rewards C_star C_h
        (launch_crossing rate rewards C_star C_h s.val fiber) (p.T - s.val)
        (launch_span rate rewards C_star C_h s.val (p.T - s.val)
          (maximal_span s) fiber)).length),
      fiber.val = source ∧ j.val = k.val ∧
      (wholeFirstLiveCells rate rewards C_star C_h source)[k.val]'k.isLt =
        (actualLiveSourceCellAt rate fiber.val rewards C_star C_h
          (launch_crossing rate rewards C_star C_h s.val fiber) (p.T - s.val)
          (launch_span rate rewards C_star C_h s.val (p.T - s.val)
            (maximal_span s) fiber) j).input ∧
      let cell := actualLiveSourceCellAt rate fiber.val rewards C_star C_h
        (launch_crossing rate rewards C_star C_h s.val fiber) (p.T - s.val)
        (launch_span rate rewards C_star C_h s.val (p.T - s.val)
          (maximal_span s) fiber) j
      ∀ a : FastArm cell.selected.view.payload.slowSet,
        cell.selected.view.complementWeights a = W a.val := by
  classical
  obtain ⟨s, fiber, j, hsource, hposition, hinput⟩ :=
    actual_cell_of_whole_index rate rewards C_star C_h source k
  let hc := launch_crossing rate rewards C_star C_h s.val fiber
  let hspan := launch_span rate rewards C_star C_h s.val (p.T - s.val)
    (maximal_span s) fiber
  have hcells : wholeFirstLiveCells rate rewards C_star C_h source =
      actualLiveSourceCells rate fiber.val rewards C_star C_h hc (p.T - s.val) hspan := by
    rw [← hsource]
    exact (wholeFirstLive_on_fiber rate rewards C_star C_h s fiber).2
  have hprefix : (wholeFirstLiveCells rate rewards C_star C_h source).take k.val =
      (actualLiveSourceCells rate fiber.val rewards C_star C_h hc
        (p.T - s.val) hspan).take j.val := by
    exact (congrArg (fun xs : List (RecordedQueueRun.RoundInput p.K) =>
      xs.take k.val) hcells).trans
        (congrArg (fun n => (actualLiveSourceCells rate fiber.val rewards C_star C_h hc
          (p.T - s.val) hspan).take n) hposition.symm)
  have hclear' : (RecordedQueueRun.run
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((actualLiveSourceCells rate fiber.val rewards C_star C_h hc
        (p.T - s.val) hspan).take j.val)).overflow = false := by
    rw [← hprefix]
    exact hclear
  refine ⟨s, fiber, j, hsource, hposition, hinput, ?_⟩
  dsimp only
  rw [hprefix]
  exact actual_cell_prechoice_complement_weights rate fiber.val rewards C_star C_h
    hc (p.T - s.val) hspan j hclear'

/-- Every scalar fed to the actual selected local FAST sampler gives the
canonical FAST draw with the full all-arm numerical queue vector. Positivity
and both envelope bounds are produced here, using the same unit anchor as
that cell's first installation. The second equality specializes to the
original current-round reserved FAST coordinate, even while DOWN is pending. -/
theorem wholeFirstLive_full_weight_fast
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p)
    (k : Fin (wholeFirstLiveCells rate rewards C_star C_h source).length)
    (hclear : (RecordedQueueRun.run
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((wholeFirstLiveCells rate rewards C_star C_h source).take k.val)).overflow = false) :
    let W := RecordedQueueRun.scoreWeight
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        ((wholeFirstLiveCells rate rewards C_star C_h source).take k.val))
    ∃ (s : Fin (p.T + 1))
      (fiber : LaunchFiber rate rewards C_star C_h s.val)
      (j : Fin (actualFirstLiveWindow rate fiber.val rewards C_star C_h
        (launch_crossing rate rewards C_star C_h s.val fiber) (p.T - s.val)
        (launch_span rate rewards C_star C_h s.val (p.T - s.val)
          (maximal_span s) fiber)).length),
      fiber.val = source ∧ j.val = k.val ∧
      (wholeFirstLiveCells rate rewards C_star C_h source)[k.val]'k.isLt =
        (actualLiveSourceCellAt rate fiber.val rewards C_star C_h
          (launch_crossing rate rewards C_star C_h s.val fiber) (p.T - s.val)
          (launch_span rate rewards C_star C_h s.val (p.T - s.val)
            (maximal_span s) fiber) j).input ∧
      let cell := actualLiveSourceCellAt rate fiber.val rewards C_star C_h
        (launch_crossing rate rewards C_star C_h s.val fiber) (p.T - s.val)
        (launch_span rate rewards C_star C_h s.val (p.T - s.val)
          (maximal_span s) fiber) j
      let record := (actualFirstLiveWindow rate fiber.val rewards C_star C_h
        (launch_crossing rate rewards C_star C_h s.val fiber) (p.T - s.val)
        (launch_span rate rewards C_star C_h s.val (p.T - s.val)
          (maximal_span s) fiber))[j.val]
      ∃ (hWpos : ∀ a, 0 < W a)
        (hWlower : ∀ a, cell.selected.view.payload.anchor a ≤ W a)
        (hWupper : ∀ a, W a ≤ 2 * cell.selected.view.payload.anchor a),
        (∀ a : FastArm cell.selected.view.payload.slowSet,
          cell.selected.view.complementWeights a = W a.val) ∧
        (∀ scalar : ContinuousCategorical.Scalar,
          FastComplementLocality.sampleLocalFast p rate.eta.val
            cell.choiceInputsValid.learning_rate_pos cell.choiceInputsValid.learning_rate_le_source_cap
            cell.selected.view.payload.anchor cell.choiceInputsValid.anchor_pos
            cell.selected.view.payload.slowSet cell.selected.view.complementWeights
            cell.choiceInputsValid.current_weight_pos cell.choiceInputsValid.anchor_le_current
            cell.choiceInputsValid.current_le_twice_anchor scalar =
          CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
            cell.selected.view.payload.anchor W cell.selected.view.payload.anchor_pos
            hWpos hWlower hWupper cell.selected.view.payload.slowSet scalar) ∧
        CoordinatorLocalArmChoice.localFastDraw cell.selected.view.payload
          cell.selected.view.cutoff record.input.time cell.selected.view.complementWeights
          cell.choiceInputsValid (record.input.row.2 record.input.time) =
        CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
          cell.selected.view.payload.anchor W cell.selected.view.payload.anchor_pos
          hWpos hWlower hWupper cell.selected.view.payload.slowSet
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
            (record.input.row.2 record.input.time).1) := by
  classical
  let W := RecordedQueueRun.scoreWeight
    (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((wholeFirstLiveCells rate rewards C_star C_h source).take k.val))
  obtain ⟨s, fiber, j, hsource, hposition, hinput, hweights⟩ :=
    wholeFirstLive_prechoice_complement_weights rate rewards C_star C_h source k hclear
  let hc := launch_crossing rate rewards C_star C_h s.val fiber
  let hspan := launch_span rate rewards C_star C_h s.val (p.T - s.val)
    (maximal_span s) fiber
  let cell := actualLiveSourceCellAt rate fiber.val rewards C_star C_h
    hc (p.T - s.val) hspan j
  obtain ⟨_, _, _, _, _, hanchor, _⟩ :=
    actual_cell_first_installation rate rewards C_star C_h s fiber j
  have henvelope (a : Fin p.K) : 1 ≤ W a ∧ W a < 2 :=
    wholeFirstLive_full_scoreWeight_envelope rate rewards C_star C_h source k a
  have hWpos : ∀ a, 0 < W a := by
    intro a
    exact lt_of_lt_of_le zero_lt_one (henvelope a).1
  have hWlower : ∀ a, cell.selected.view.payload.anchor a ≤ W a := by
    intro a
    rw [hanchor a]
    exact (henvelope a).1
  have hWupper : ∀ a, W a ≤ 2 * cell.selected.view.payload.anchor a := by
    intro a
    rw [hanchor a, mul_one]
    exact (henvelope a).2.le
  have hrestriction : cell.selected.view.complementWeights =
      fun a : FastArm cell.selected.view.payload.slowSet => W a.val := by
    funext a
    exact hweights a
  have hfast (scalar : ContinuousCategorical.Scalar) :
      FastComplementLocality.sampleLocalFast p rate.eta.val
        cell.choiceInputsValid.learning_rate_pos cell.choiceInputsValid.learning_rate_le_source_cap
        cell.selected.view.payload.anchor cell.choiceInputsValid.anchor_pos
        cell.selected.view.payload.slowSet cell.selected.view.complementWeights
        cell.choiceInputsValid.current_weight_pos cell.choiceInputsValid.anchor_le_current
        cell.choiceInputsValid.current_le_twice_anchor scalar =
      CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
        cell.selected.view.payload.anchor W cell.selected.view.payload.anchor_pos
        hWpos hWlower hWupper cell.selected.view.payload.slowSet scalar := by
    calc
      _ = FastComplementLocality.sampleLocalFast p rate.eta.val
          rate.eta.property rate.sourceCap cell.selected.view.payload.anchor
          cell.selected.view.payload.anchor_pos cell.selected.view.payload.slowSet
          (fun a => W a.val) (fun a => hWpos a.val)
          (fun a => hWlower a.val) (fun a => hWupper a.val) scalar :=
        FastComplementLocality.sampleLocalFast_eq_of_weights_eq p rate.eta.property
          rate.sourceCap cell.selected.view.payload.anchor cell.selected.view.payload.anchor_pos
          cell.selected.view.payload.slowSet cell.selected.view.complementWeights
          (fun a => W a.val) cell.choiceInputsValid.current_weight_pos
          (fun a => hWpos a.val) cell.choiceInputsValid.anchor_le_current
          (fun a => hWlower a.val) cell.choiceInputsValid.current_le_twice_anchor
          (fun a => hWupper a.val) hrestriction scalar
      _ = _ := FastComplementLocality.sampleLocalFast_eq_sampleFast p rate.eta.property
        rate.sourceCap cell.selected.view.payload.anchor W cell.selected.view.payload.anchor_pos
        hWpos hWlower hWupper cell.selected.view.payload.slowSet scalar
  refine ⟨s, fiber, j, hsource, hposition, hinput,
    hWpos, hWlower, hWupper, hweights, hfast, ?_⟩
  exact hfast _

end ReferenceFirstLiveNumericalFastPersistence
