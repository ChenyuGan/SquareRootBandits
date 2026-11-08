/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveChronologicalPrefixFoundation
import Lean.Elab.Tactic.Omega

/-!
# Actual first-cutoff refresh coordinate

This component follows the original source from its corrected launch to the
first actual pre-round cutoff. When that cutoff is strictly before the grid,
it identifies the preceding physical proposal and the corresponding label-1
residual coordinate on the existing first-live chronological prefix. The
clear-prestate branch includes the first update that detects overflow: its
proposal and refresh are retained before the frozen continuation.

This is a pathwise statement. It supplies no collection-call law, conditional
law, filtration, or Borel assertion.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveActualCutoffRefreshCoordinate

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceFirstLiveChronologicalPrefixFoundation.RateInput
abbrev RewardTable := ReferenceFirstLiveChronologicalPrefixFoundation.RewardTable
abbrev SourceInput := ReferenceFirstLiveChronologicalPrefixFoundation.SourceInput
abbrev AuxiliaryArray := ReferenceFirstLiveChronologicalPrefixFoundation.AuxiliaryArray

variable {p : Parameters}

private theorem takeWhile_length_le {α : Type} (predicate : α → Bool) (xs : List α) :
    (xs.takeWhile predicate).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
      by_cases hhead : predicate head
      · simp [List.takeWhile_cons_of_pos hhead, ih]
      · simp [List.takeWhile_cons_of_neg hhead]

/-- The complete deterministic alternatives for the first source cutoff.
The actual cutoff branch is obtained from the physical horizon run, not from
a supplied trigger or an arbitrary finite-window index. -/
theorem firstLiveChronologicalPrefix_actual_cutoff_refresh_coordinate
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p) (aux : AuxiliaryArray p) :
    let boundary := ReferenceCompletePhysicalHistory.generatedBoundary
      rate source rewards C_star C_h
    let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let window := ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source
    let cells := ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h source
    (boundary.crossing = none ∧ window = [] ∧ cells = []) ∨
      (∃ hc : (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          ).crossing.isSome = true,
        (start = p.T ∧ window = [] ∧ cells = []) ∨
        (start < p.T ∧ window = [] ∧ cells = []) ∨
        (start < p.T ∧ 0 < window.length ∧ window.length = p.T - start) ∨
        (start < p.T ∧ 0 < window.length ∧ window.length < p.T - start ∧
          let _initial := ReferenceFirstLaunchNumericalCell.launchState
            rate source rewards C_star C_h hc
          let _seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
            rate source rewards C_star C_h hc
          ∃ (cut : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate)
            (suffix : List (ReferenceFirstLiveChronologicalPrefixFoundation.Record rate))
            (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
            (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
            (base : Fin (p.m - 1) → ℕ),
            ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate source rewards C_star C_h = window ++ cut :: suffix ∧
              cut.input.state.coordinator = .live registers owned base ∧
              ReferenceCollectionPhaseHistory.cutoffChosen cut.input = true ∧
              0 < window.length ∧
              cut.input.time.val = start + window.length ∧
              (∃ birth,
                ReferenceAssignmentPayloadPersistence.InstallationBirth birth registers.payload ∧
                birth.input.time.val = start) ∧
              FollowerCutoffScan.firstCutoff p rate.eta.val registers.payload.sigma
                (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                  (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) =
                cut.input.time.val + 1 ∧
              cut.input.time.val + 1 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val
                registers.payload.sigma ∧
              (cut.input.time.val + 1 = FollowerCutoffScan.gridBoundary p rate.eta.val
                  registers.payload.sigma ∨
                (cut.input.time.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val
                  registers.payload.sigma ∧
                  ∃ last : Fin window.length,
                    last.val + 1 = window.length ∧
                    let record := window[last.val]'(by
                      simpa only [window,
                        ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow,
                        ReferenceFirstLiveChronologicalPrefixFoundation.LiveWindow] using
                        last.isLt)
                    let cell := ReferenceFirstLiveChronologicalPrefixFoundation.wholeLiveCell
                      rate rewards C_star C_h source record (List.getElem_mem (by
                        simpa only [window,
                          ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow,
                          ReferenceFirstLiveChronologicalPrefixFoundation.LiveWindow] using
                          last.isLt))
                    let v := record.input.time
                    let entry := (ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
                      rate rewards C_star C_h (source, aux))[last.val]'(by
                        rw [ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_length]
                        exact last.isLt)
                    v.val + 1 = cut.input.time.val ∧
                    v.val + 2 = cut.input.time.val + 1 ∧
                    FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) v =
                        true ∧
                    (∀ i : Fin p.T, start ≤ i.val →
                      i.val + 1 < cut.input.time.val →
                      FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) i =
                          false) ∧
                    (∀ t : Fin p.T,
                      ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellIndexPredicate
                        cut.input.time t (v, 1)) ∧
                    (∀ j : Fin window.length, j.val < last.val →
                      ((ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
                        rate rewards C_star C_h
                          (source, aux))[j.val]'(by
                            rw [ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_length]
                            exact j.isLt)).proposal = false) ∧
                    let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
                    let state := RecordedQueueRun.run q (cells.take last.val)
                    (state.overflow = true ∧ entry.proposal = false) ∨
                    (state.overflow = false ∧
                      entry.proposal = true ∧
                      entry.nextSlowSet =
                        ReferenceFirstLiveChronologicalPrefixFoundation.residualDraw rate state
                          cell.input cell.selected.view.payload.anchor
                          cell.selected.view.payload.anchor_pos (aux (v, 1)) ∧
                      (∀ U : ReferenceFirstLiveChronologicalPrefixFoundation.SlowSet p,
                        0 ≤ RecordedSlowRefresh.residualMass p q state cell.input
                          cell.selected.view.payload.anchor
                          cell.selected.view.payload.anchor_pos U) ∧
                      (∑ U : ReferenceFirstLiveChronologicalPrefixFoundation.SlowSet p,
                        RecordedSlowRefresh.residualMass p q state cell.input
                          cell.selected.view.payload.anchor
                          cell.selected.view.payload.anchor_pos U) = 1 ∧
                      (∀ replacement : AuxiliaryArray p,
                        (ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
                          rate rewards C_star C_h
                            (source, aux)).take last.val =
                          (ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
                            rate rewards C_star C_h
                              (source, replacement)).take last.val ∧
                        (ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
                          rate rewards C_star C_h
                            (source, aux)).map
                              ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell.beforeRefreshFields =
                          (ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
                            rate rewards C_star C_h
                              (source, replacement)).map
                                ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell.beforeRefreshFields ∧
                        ∀ U : ReferenceFirstLiveChronologicalPrefixFoundation.SlowSet p,
                          RecordedSlowRefresh.residualMass p q state cell.input
                            cell.selected.view.payload.anchor
                            cell.selected.view.payload.anchor_pos U =
                          RecordedSlowRefresh.residualMass p q state cell.input
                            cell.selected.view.payload.anchor
                            cell.selected.view.payload.anchor_pos U) ∧
                      (∀ a b : AuxiliaryArray p,
                        a (v, 1) = b (v, 1) →
                        ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
                          rate rewards C_star C_h (source, a) =
                        ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
                          rate rewards C_star C_h (source, b)) ∧
                      (∀ replacement : AuxiliaryArray p,
                        ((ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
                          rate rewards C_star C_h
                            (source, replacement))[last.val]'(by
                              rw [ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_length]
                              exact last.isLt)).nextSlowSet =
                          ReferenceFirstLiveChronologicalPrefixFoundation.residualDraw rate state
                            cell.input cell.selected.view.payload.anchor
                            cell.selected.view.payload.anchor_pos (replacement (v, 1))) ∧
                      (∀ replacementValue : ContinuousControlSlice.Scalar,
                        ∀ coordinate : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p,
                          coordinate ≠ (v, 1) →
                          Function.update aux (v, 1) replacementValue coordinate =
                            aux coordinate)))))) := by
  classical
  dsimp only
  by_cases hcBoundary : (ReferenceCompletePhysicalHistory.generatedBoundary
      rate source rewards C_star C_h).crossing.isSome = true
  · right
    have hc : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
        ).crossing.isSome = true := by
      simpa only [ReferenceCompletePhysicalHistory.generatedBoundary,
        ReferenceCompletePhysicalHistory.generatedInput] using hcBoundary
    refine ⟨hc, ?_⟩
    let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let window := ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source
    let cells := ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h source
    have hrecordsLength : (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length = p.T - start := by
      simpa only [start] using ReferenceCompletePhysicalHistory.completeSuffixRecords_length
        rate source rewards C_star C_h
    have hwindowLength : window.length ≤ p.T - start := by
      calc
        window.length ≤
            (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate source rewards C_star C_h).length := by
          dsimp [window, ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow,
            ReferenceFirstLiveConfirmationHistory.firstLiveWindow]
          exact takeWhile_length_le _ _
        _ = p.T - start := hrecordsLength
    have hcellsLength : cells.length = window.length := by
      simpa only [cells, window, ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells,
        ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow] using
        ReferenceFirstLiveChronologicalPrefixFoundation.wholeFirstLiveCells_length
          rate rewards C_star C_h source
    have hstartLeT : start ≤ p.T := by
      simpa only [start] using ReferenceCompletePhysicalHistory.physicalStart_le_T
        rate source rewards C_star C_h
    by_cases hterminal : start = p.T
    · left
      have hwindowZero : window.length = 0 := by
        rw [hterminal] at hwindowLength
        simpa using hwindowLength
      refine ⟨hterminal, ?_, ?_⟩
      · apply List.eq_nil_iff_length_eq_zero.mpr
        exact hwindowZero
      · apply List.eq_nil_iff_length_eq_zero.mpr
        rw [hcellsLength]
        exact hwindowZero
    · right
      have hstart : start < p.T := by omega
      by_cases hempty : window.length = 0
      · left
        refine ⟨hstart, ?_, ?_⟩
        · apply List.eq_nil_iff_length_eq_zero.mpr
          exact hempty
        · apply List.eq_nil_iff_length_eq_zero.mpr
          rw [hcellsLength, hempty]
      · have hpositive : 0 < window.length := Nat.pos_of_ne_zero hempty
        by_cases hshort : window.length < p.T - start
        · right
          right
          refine ⟨hstart, hpositive, hshort, ?_⟩
          let initial := ReferenceFirstLaunchNumericalCell.launchState
            rate source rewards C_star C_h hc
          let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
            rate source rewards C_star C_h hc
          have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
              rate source rewards C_star C_h = some initial := by
            exact ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
              rate source rewards C_star C_h hc
          have hspan : start + (p.T - start) ≤ p.T := by omega
          have hactive : ReferenceActivePhysicalHorizon.allActiveAtStart initial start := by
            simpa [start, ReferenceCompletePhysicalHistory.physicalStart,
              ReferenceCompletePhysicalHistory.generatedBoundary,
              ReferenceCompletePhysicalHistory.generatedInput] using seed.activeAtStart
          have hcomplete := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
            rate source rewards C_star C_h initial hlaunch
          let execution := ReferenceActivePhysicalHorizon.run initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
            (p.T - start) hspan hactive
          have hcompleteRun : ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate source rewards C_star C_h = execution.records := by
            simpa only [execution, start] using hcomplete
          have hwindowRun : window =
              ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records := by
            dsimp only [window, ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow,
              execution]
            rw [hcompleteRun]
          have hshortRun :
              (ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records).length <
                p.T - start := by
            rw [← hwindowRun]
            exact hshort
          have hcutResult :=
            ReferenceFirstCutoffOutsideInitialization.run_first_cutoff_outside_initializer
              initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
              rewards start (p.T - start) hspan hactive seed.coordinatorFirst hshortRun
          rcases hcutResult with ⟨cut, suffix, hcutData⟩
          rcases hcutData with ⟨hsplit, hindex, htime, hactual, hcutInfo⟩
          rcases hcutInfo with ⟨registers, owned, base, hcutState, hlive, hdispatch⟩
          dsimp only at hdispatch
          rcases hdispatch with
            ⟨dispatched, hstartRound, ledger, hinit, hledger, hdomain, hclock, hpending,
              hnoAssignment, selection, hpreparation, hrest⟩
          rcases hrest with ⟨hkpos, hsigma, hbase, hbirth, hearlierFalse, hdiagnostic,
            hcutTail⟩
          have hborn :
              ∃ birth,
                ReferenceAssignmentPayloadPersistence.InstallationBirth birth registers.payload ∧
                birth.input.time.val = start := by
            rcases hbirth with ⟨birth, _, hborn, hbirthTime, _⟩
            exact ⟨birth, hborn, hbirthTime⟩
          clear hbirth
          rcases hcutTail with ⟨hcutOne, _hcutAfterStart, _hcutBound, _hcutGridBound,
            _hgridBound, _hledgerSigma, _hledgerCutoff, _hfreezeAt, hfirstCut, _⟩
          have hcutTag : ReferenceCollectionPhaseHistory.cutoffChosen cut.input = true := by
            rw [cut.output_eq] at hpreparation
            have hprep : (ReferenceActivePhysicalStep.prepare cut.input).coordinator =
                .live registers owned base
                  (.cutoffChosen dispatched hstartRound ledger hinit hledger hdomain hclock
                    hpending hnoAssignment selection) := by
              simpa [ReferenceActivePhysicalStep.step] using hpreparation
            unfold ReferenceCollectionPhaseHistory.cutoffChosen
            rw [hprep]
          have hsplitSource :
              ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards
                  C_star C_h = window ++ cut :: suffix := by
            calc
              _ = execution.records := hcompleteRun
              _ = _ := by simpa only [hwindowRun] using hsplit
          have htimeWindow : cut.input.time.val = start + window.length := by
            simpa only [hwindowRun] using htime
          have hstateLive : cut.input.state.coordinator = .live registers owned base := by
            exact (congrArg (fun s : ReferenceActivePhysicalStep.State p rate =>
              s.coordinator) hcutState).trans hlive
          have hcutMin : FollowerCutoffScan.firstCutoff p rate.eta.val registers.payload.sigma
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) =
              cut.input.time.val + 1 := by
            simpa only [hcutOne] using hfirstCut
          have hcutLEScanGrid : cut.input.time.val + 1 ≤
              FollowerCutoffScan.gridBoundary p rate.eta.val registers.payload.sigma := by
            rw [← hcutMin, FollowerCutoffScan.firstCutoff]
            exact Finset.min'_le
              (FollowerCutoffScan.firstCutoffCarrier p rate.eta.val registers.payload.sigma
                (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                  (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))))
              (FollowerCutoffScan.gridBoundary p rate.eta.val registers.payload.sigma)
              (Finset.mem_insert_self _ _)
          by_cases hterminalCut : cut.input.time.val + 1 =
              FollowerCutoffScan.gridBoundary p rate.eta.val registers.payload.sigma
          · refine ⟨cut, suffix, registers, owned, base, ?_⟩
            exact ⟨hsplitSource, hstateLive, hcutTag, hpositive, htimeWindow, hborn,
              hcutMin, hcutLEScanGrid, Or.inl hterminalCut⟩
          · have hbeforeGrid : cut.input.time.val + 1 <
                FollowerCutoffScan.gridBoundary p rate.eta.val registers.payload.sigma := by
              exact Nat.lt_of_le_of_ne hcutLEScanGrid hterminalCut
            let last : Fin window.length :=
              ⟨window.length - 1, by omega⟩
            have hlast : last.val + 1 = window.length := by
              dsimp [last]
              omega
            let record := window[last.val]'last.isLt
            let cell := ReferenceFirstLiveChronologicalPrefixFoundation.wholeLiveCell
              rate rewards C_star C_h source record (List.getElem_mem last.isLt)
            let v := record.input.time
            let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
            let state := RecordedQueueRun.run q (cells.take last.val)
            let entry := (ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux))[last.val]'(by
                rw [ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_length]
                exact last.isLt)
            have hgeometry := ReferenceFirstLiveChronologicalPrefixFoundation.wholeLiveCell_geometry rate rewards C_star C_h source last
            dsimp only at hgeometry
            rcases hgeometry with ⟨hrow, hsigmaCell, hrecordTime, hrecordGrid, hrecordEarlier⟩
            have hvCut : v.val + 1 = cut.input.time.val := by
              dsimp [v]
              rw [hrecordTime]
              omega
            have hvCutTwo : v.val + 2 = cut.input.time.val + 1 := by omega
            have hminMem : cut.input.time.val + 1 ∈
                FollowerCutoffScan.firstCutoffCarrier p rate.eta.val registers.payload.sigma
                  (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                    (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) := by
              rw [← hcutMin]
              exact Finset.min'_mem _ _
            have hproposal : FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) v = true := by
              change cut.input.time.val + 1 ∈
                insert (FollowerCutoffScan.gridBoundary p rate.eta.val registers.payload.sigma)
                  (FollowerCutoffScan.trueProposalEndpoints
                    (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)))
                    (FollowerCutoffScan.proposalCoordinates p registers.payload.sigma)) at hminMem
              rcases Finset.mem_insert.mp hminMem with hgrid | hevent
              · omega
              · change cut.input.time.val + 1 ∈
                    FollowerCutoffScan.trueProposalEndpoints
                  (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                    (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)))
                  (FollowerCutoffScan.proposalCoordinates p registers.payload.sigma) at hevent
                unfold FollowerCutoffScan.trueProposalEndpoints at hevent
                rcases Finset.mem_image.mp hevent with ⟨i, hi, hendpoint⟩
                have hbit := (Finset.mem_filter.mp hi).2
                have hcoord : i.val = v.val := by
                  have hendpoint' : i.val + 2 = cut.input.time.val + 1 := by
                    simpa only [FollowerCutoffScan.proposalEndpoint] using hendpoint
                  omega
                have hiV : i = v := Fin.ext hcoord
                simpa only [hiV] using hbit
            have hearlierPhysical : ∀ i : Fin p.T, start ≤ i.val →
                i.val + 1 < cut.input.time.val →
                FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                  (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) i =
                    false := by
              intro i hiStart hiBefore
              apply hearlierFalse i hiStart
              rw [← hwindowRun, ← htimeWindow]
              exact hiBefore
            have hcoordinate : ∀ t : Fin p.T,
                ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellIndexPredicate
                  cut.input.time t (v, 1) := by
              intro t
              left
              exact ⟨rfl, hvCut⟩
            have hearlierLogical : ∀ j : Fin window.length, j.val < last.val →
                ((ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux))[j.val]'(by
                    rw [ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_length]
                    exact j.isLt)).proposal = false := by
              intro j hj
              exact ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_earlier_proposal
                  rate rewards C_star C_h source aux j last hj
            have hoverflowCriterion :
                (state.overflow = true ↔
                  ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowPrefix
                    rate rewards C_star C_h source ≤ last.val) := by
              have hstop := ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_stopped_replay
                  rate rewards C_star C_h source aux last
              dsimp only at hstop
              have hqueue := ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_queue_states
                  rate rewards C_star C_h source aux last
              dsimp only at hqueue
              have hstateEq : state =
                  ((ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
                    rate rewards C_star C_h (source, aux))[last.val]'(by
                      rw [ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_length]
                      exact last.isLt)).before := by
                dsimp only [state, q, cells]
                exact hqueue.1.symm
              rw [hstateEq]
              simpa only [ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowPrefix,
                cells, q] using hstop.1
            have hclearOfNoEarlierOverflow
                (hno : ¬ ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowPrefix
                  rate rewards C_star C_h source < window.length) :
                state.overflow = false := by
              have hbound : last.val <
                  ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowPrefix
                    rate rewards C_star C_h source := by
                have hlen := Nat.le_of_not_gt hno
                omega
              cases hstate : state.overflow with
              | false => rfl
              | true =>
                  have := (hoverflowCriterion.mp hstate)
                  omega
            have hoverflowBefore
                (hyes : ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowPrefix
                  rate rewards C_star C_h source < window.length) :
                state.overflow = true := by
              apply hoverflowCriterion.mpr
              have hlen : last.val + 1 = window.length := hlast
              omega
            have hentryProposalOfOverflow
                (hstate : state.overflow = true) : entry.proposal = false := by
              have hpost := ReferenceFirstLiveChronologicalPrefixFoundation.appendLogicalCell_after_overflow
                record cell state aux hstate
              dsimp only at hpost
              have hget := ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_get
                rate rewards C_star C_h source aux last
              have hentryEq : entry =
                  ReferenceFirstLiveChronologicalPrefixFoundation.appendLogicalCell
                    record cell state aux := by
                dsimp only [entry]
                simpa only [record, cell, state, cells, q] using hget
              exact (congrArg
                ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell.proposal hentryEq).trans
                  hpost.2.2.1
            have hclearOfNoEarlierOverflow' :
                ¬ ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowPrefix
                  rate rewards C_star C_h source < window.length → state.overflow = false :=
              hclearOfNoEarlierOverflow
            have hupdateTake (replacementValue : ContinuousControlSlice.Scalar) :
                (ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix rate rewards C_star C_h
                    (source, aux)).take last.val =
                (ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix rate rewards C_star C_h
                    (source, Function.update aux (v, 1) replacementValue)).take last.val :=
              ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_take_auxiliary_ext
                  rate rewards C_star C_h source aux
                  (Function.update aux (v, 1) replacementValue) last.val last.isLt
            have hupdateBeforeRefresh (replacementValue : ContinuousControlSlice.Scalar) :
                (ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix rate rewards C_star C_h
                    (source, aux)).map
                      ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell.beforeRefreshFields =
                (ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix rate rewards C_star C_h
                    (source, Function.update aux (v, 1) replacementValue)).map
                      ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell.beforeRefreshFields :=
              ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_beforeRefresh_auxiliary_ext
                  rate rewards C_star C_h source aux
                  (Function.update aux (v, 1) replacementValue)
            have hsameScalar (a b : AuxiliaryArray p)
                (hab : a (v, 1) = b (v, 1)) :
                ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix rate rewards C_star C_h (source, a) =
                ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix rate rewards C_star C_h (source, b) := by
              apply ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_last_auxiliary_ext
                  rate rewards C_star C_h source a b last hlast
              simpa only [v] using hab
            have hresidualInvariant (replacementValue : ContinuousControlSlice.Scalar)
                (U : ReferenceFirstLiveChronologicalPrefixFoundation.SlowSet p) :
                RecordedSlowRefresh.residualMass p q state cell.input
                    cell.selected.view.payload.anchor cell.selected.view.payload.anchor_pos U =
                  RecordedSlowRefresh.residualMass p q state cell.input
                    cell.selected.view.payload.anchor cell.selected.view.payload.anchor_pos U := rfl
            have hupdateOther (replacementValue : ContinuousControlSlice.Scalar)
                (coordinate : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p)
                (hne : coordinate ≠ (v, 1)) :
                Function.update aux (v, 1) replacementValue coordinate = aux coordinate := by
              simp [Function.update, hne]
            refine ⟨cut, suffix, registers, owned, base, ?_⟩
            refine ⟨hsplitSource, hstateLive, hcutTag, hpositive, htimeWindow, hborn,
              hcutMin, hcutLEScanGrid, Or.inr ⟨hbeforeGrid, ⟨last, hlast, ?_⟩⟩⟩
            refine ⟨hvCut, hvCutTwo, hproposal, hearlierPhysical, hcoordinate,
              hearlierLogical, ?_⟩
            by_cases hoverflowEarlier :
                ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowPrefix
                  rate rewards C_star C_h source < window.length
            · left
              exact ⟨hoverflowBefore hoverflowEarlier,
                hentryProposalOfOverflow (hoverflowBefore hoverflowEarlier)⟩
            · right
              have hclearBranch :
                  ¬ ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowPrefix
                    rate rewards C_star C_h source < window.length := hoverflowEarlier
              have hclear : state.overflow = false :=
                hclearOfNoEarlierOverflow hclearBranch
              have hendpoint :=
                ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_finite_window_endpoint_triggering_residual
                    rate rewards C_star C_h source aux last
                    (by simpa only [state, cells] using hclear)
                    (by simpa only [v] using hproposal)
              dsimp only at hendpoint
              rcases hendpoint with ⟨_, _, hentryProp, hnext, hnonneg, hsum, _⟩
              have hrefreshFor (replacement : AuxiliaryArray p) :
                  ((ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix rate rewards C_star C_h
                      (source, replacement))[last.val]'(by
                        rw [ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_length]
                        exact last.isLt)).nextSlowSet =
                    ReferenceFirstLiveChronologicalPrefixFoundation.residualDraw rate state
                      cell.input cell.selected.view.payload.anchor
                      cell.selected.view.payload.anchor_pos (replacement (v, 1)) := by
                have hres :=
                  ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_finite_window_endpoint_triggering_residual
                      rate rewards C_star C_h source replacement last
                      (by simpa only [state, cells] using hclear)
                      (by simpa only [v] using hproposal)
                dsimp only at hres
                rcases hres with ⟨_, _, _, hnextReplacement, _, _, _⟩
                exact hnextReplacement
              have hreplacementNext (replacement : AuxiliaryArray p) := hrefreshFor replacement
              refine ⟨hclearOfNoEarlierOverflow hoverflowEarlier, hentryProp, hnext,
                hnonneg, hsum, ?_, ?_, ?_, ?_⟩
              · intro replacement
                exact ⟨ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_take_auxiliary_ext
                      rate rewards C_star C_h source aux replacement last.val last.isLt,
                  ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_beforeRefresh_auxiliary_ext
                      rate rewards C_star C_h source aux replacement,
                  fun U => rfl⟩
              · intro a b hab
                exact hsameScalar a b hab
              · exact hreplacementNext
              · intro replacementValue coordinate hne
                exact hupdateOther replacementValue coordinate hne
        · right
          left
          have hfull : p.T - start ≤ window.length := Nat.le_of_not_gt hshort
          exact ⟨hstart, hpositive, Nat.le_antisymm hwindowLength hfull⟩
  · have hnone : (ReferenceCompletePhysicalHistory.generatedBoundary
        rate source rewards C_star C_h).crossing = none := by
      cases hcross : (ReferenceCompletePhysicalHistory.generatedBoundary
          rate source rewards C_star C_h).crossing <;> simp_all
    left
    have hno := ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
      rate rewards C_star C_h source hnone
    exact ⟨hnone, hno.1, hno.2.1⟩

end Bandits.Support.ReferenceFirstLiveActualCutoffRefreshCoordinate

end
