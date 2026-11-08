/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalCalendarRetainedBranchPartition
public import Bandits.Support.ReferenceOriginalCalendarFirstDispatchEnergyTransport

import Mathlib.Tactic

/-!
# Actual first-branch increment on the original calendar

The first chosen selector is identified on the whole original source with the
literal first-live birth phase. Its energy increment keeps the actual first
update and is integrated against the unchanged original source law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical

namespace Bandits.Support.ReferenceOriginalCalendarFirstBranchIncrementTransport

open ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
  (q : Fin p.T) (a : Fin p.K)

local notation "X" => SourceInput p
local notation "energy" => ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
  rate rewards C_star C_h
local notation "phase" => ReferenceFirstLiveSourcePhasePartition.sourcePhase
  rate rewards C_star C_h q
local notation "selector" =>
  ReferenceOriginalCalendarRetainedBranchPartition.firstChosenSelector
    rate rewards C_star C_h q

private theorem getElem?_takeWhile_eq {α : Type*} (test : α → Bool) :
    ∀ (xs : List α) (k : ℕ), k < (xs.takeWhile test).length →
      xs[k]? = (xs.takeWhile test)[k]? := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      intro k hk
      by_cases htest : test x
      · cases k with
        | zero => simp [List.takeWhile, htest]
        | succ k =>
            have hk' : k < (xs.takeWhile test).length := by
              simpa [List.takeWhile, htest] using hk
            simpa [List.takeWhile, htest] using ih k hk'
      · simp [List.takeWhile, htest] at hk

/-- The actual first chosen record selector on the unchanged original source. -/
public def firstSelectorEvent : Set X :=
  {z | (selector z).isSome = true}

/-- The true carried-energy increment at the first chosen calendar update,
restricted to the exact actual selector event. -/
public def firstSelectorIncrement : X → ℝ :=
  (firstSelectorEvent rate rewards C_star C_h q).indicator
    (fun z => energy (q.val + 1) a z - energy q.val a z)

private theorem birthStratum_of_sourcePhase
    (z : X) (hz : z ∈ phase 2) :
    ∃ j : Fin (M p),
      z ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h q
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q) := by
  have hu := ReferenceFirstLiveCalendarIntegralAssembly.sourcePhase_birth_iUnion
    rate rewards C_star C_h q
  rw [hu] at hz
  exact Set.mem_iUnion.mp hz

include control0 a in
private theorem firstSelector_of_birthPhase
    (z : X) (hz : z ∈ phase 2) :
    (selector z).isSome = true := by
  classical
  change (ReferenceCompletePhysicalHistory.generatedBoundary
      rate z rewards C_star C_h).crossing.isSome = true ∧
    q.val = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h at hz
  have hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := by
    simpa [ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using hz.1
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = q.val :=
    hz.2.symm
  obtain ⟨j, hj⟩ := birthStratum_of_sourcePhase rate rewards C_star C_h q z hz
  have hj' : BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z = j ∧
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true ∧
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = q.val := by
    change BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z = j ∧ _ ∧ _ at hj
    exact hj
  have hjEq : j = BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z := hj'.1.symm
  subst j
  let birth : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h q
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex
        (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z) q) := ⟨z, hj⟩
  have htransport := ReferenceOriginalCalendarFirstDispatchEnergyTransport.carried_initial_first_update_transport
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (t := q) (a := a)
    (q := BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z) birth
  have hlaunch := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate z rewards C_star C_h hcross
  let active := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hcross
  have hrecordActual := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h q z active hlaunch (by omega)
  have hrunRecord :
      ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (q.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (by rw [hstart]; omega)
        (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
          rate z rewards C_star C_h active hlaunch) =
      ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z rewards C_star C_h hcross
        (by
          rw [ReferenceFirstLaunchCommonUpdateSource.source_elapsed_eq
            rate rewards C_star C_h (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z) q birth]
          exact q.isLt) := by
    have helapsed := ReferenceFirstLaunchCommonUpdateSource.source_elapsed_eq
      rate rewards C_star C_h (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z) q birth
    have hindexElapsed : q.val - ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = 0 := by
      rw [helapsed]
      omega
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceFirstLaunchNumericalCell.firstPhysicalRecord,
      ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput,
      ReferenceActivePhysicalHorizon.roundInputAt,
      active]
    apply congrArg (fun input : ReferenceActivePhysicalStep.RoundInput p rate =>
      (⟨input, ReferenceActivePhysicalStep.step input, rfl⟩ :
        ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    congr 1
    · simp only [hindexElapsed]
    · all_goals simp [hindexElapsed]
  rw [hrunRecord] at hrecordActual
  have hactualRecord₀ : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h q z = some
        (ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z rewards C_star C_h hcross
          (by
            rw [ReferenceFirstLaunchCommonUpdateSource.source_elapsed_eq
              rate rewards C_star C_h (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z) q birth]
            exact q.isLt)) := hrecordActual
  let coords := ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
    rate rewards C_star C_h (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z) q control0 birth
  have hsourceRecord := ReferenceFirstLaunchRecordingSourceLaw.source_record_eq
    rate rewards C_star C_h (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z) q control0 birth
  let record := ReferenceFirstLaunchRecordingPhysicalMarker.record rate rewards C_star C_h
    (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z) q control0
    coords.1 coords.2.1 coords.2.2
  have hmarkerRecord : record = ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z rewards C_star C_h hcross
      (by
        rw [ReferenceFirstLaunchCommonUpdateSource.source_elapsed_eq
          rate rewards C_star C_h (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z) q birth]
        exact q.isLt) := by
    simpa only [record, ReferenceFirstLaunchRecordingPhysicalMarker.record] using hsourceRecord
  have hactualRecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h q z = some record := by
    rw [← hmarkerRecord] at hactualRecord₀
    exact hactualRecord₀
  obtain ⟨installed, arm, _, hprepared, _, _, _, _⟩ :=
    ReferenceFirstLaunchRecordingPhysicalMarker.dispatch_chosen_exists
      rate rewards C_star C_h (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z) q control0
      coords.1 coords.2.1 coords.2.2
  have hrecordDispatch : record.output.preparation.coordinator = .first (.chosen installed arm) := by
    simpa [record, ReferenceFirstLaunchRecordingPhysicalMarker.record] using hprepared
  have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
      .first (.chosen installed arm) := by
    calc
      _ = record.output.preparation.coordinator := record.output.preparation.coordinator_eq.symm
      _ = .first (.chosen installed arm) := hrecordDispatch
  let count := p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let hspan := ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseSpan
    rate rewards C_star C_h z
  let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate z rewards C_star C_h hcross count hspan
  let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate z rewards C_star C_h hcross count hspan
  have hwindowRecords := ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstLiveRun
    rate rewards C_star C_h z hcross
  have hwindow : W = ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) := by
    dsimp only [W, ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow]
    rw [← hwindowRecords]
  have hwindowPos : 0 < W.length := by
    have hpos := ReferenceFirstLiveSourcePhasePartition.source_birth_window_pos
      rate rewards C_star C_h q control0 z hz
    let start := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let s : Fin (p.T + 1) := ⟨start, Nat.lt_succ_of_le
      (ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h)⟩
    let fiber : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h start :=
      ⟨z, ⟨hz.1, rfl⟩⟩
    have hfiber := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
      rate rewards C_star C_h s fiber
    have hwholeW : ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h z = W := by
      rw [hfiber.1]
      dsimp [W, count, start, s, fiber, ReferenceFirstLiveOverflowReadout.firstLiveWindow,
        ReferenceFirstLiveOverflowReadout.launch_crossing,
        ReferenceFirstLiveOverflowReadout.launch_span]
    rw [hwholeW] at hpos
    exact hpos
  obtain ⟨_, _, hraw⟩ :=
    ReferenceCompleteFirstPhaseObservationRecovery.actualFirstLiveRawObservationIdentity
      rate rewards C_star C_h z hcross
  let k : Fin W.length := ⟨0, hwindowPos⟩
  have hraw0 := hraw k
  dsimp only at hraw0
  rcases hraw0 with ⟨_, _, _, _, _, _, hlive, hcollection, _, _, _, _, _, _, _, _⟩
  have hwindowLength :
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.cutoffChosen r.input)).length = W.length := by
    change (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)).length = W.length
    rw [← hwindow]
  have hlookup := getElem?_takeWhile_eq
    (fun (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) =>
      !ReferenceCollectionPhaseHistory.cutoffChosen r.input
    )
    (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)
    0 (by rw [hwindowLength]; exact hwindowPos)
  have hlookup' :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[0]? =
        some (W[0]'hwindowPos) := by
    calc
      _ = (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h))[0]? :=
            hlookup
      _ = some (W[0]'hwindowPos) := by
        rw [← hwindow]
        exact List.getElem?_eq_getElem hwindowPos
  have hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z =
      some (W[0]'hwindowPos) := by
    unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
    rw [hstart]
    simpa only [Nat.sub_self, ite_eq_left le_rfl] using hlookup'
  have hrecordEq := Option.some.inj (hrecord.symm.trans hactualRecord)
  have hliveW : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
      (W[0]'hwindowPos) = some (cells[0]'(by
        rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length]
        exact hwindowPos)) := by
    simpa [W, cells, k] using hlive
  have hcollectionW : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
      (W[0]'hwindowPos) = none := by
    simpa [W, cells, k] using hcollection
  have hlive' : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record =
      some (cells[0]'(by
        rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length]
        exact hwindowPos)) := by
    simpa only [hrecordEq] using hliveW
  have hcollection' : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = none := by
    simpa only [hrecordEq] using hcollectionW
  have hcell0 : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate record =
      some (cells[0]'(by
        rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length]
        exact hwindowPos)) := by
    change (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record).or
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record) = _
    rw [hlive', hcollection']
    rfl
  have hactualCell : ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
      rate rewards C_star C_h q z =
        some (cells[0]'(by
          rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length]
          exact hwindowPos)) := by
    unfold ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
    rw [hactualRecord]
    simp only [Option.bind_some, hcell0]
  have htransportCell := Option.some.inj (hactualCell.symm.trans htransport.2.1)
  have hselectorRecord : ReferenceOriginalCalendarRetainedBranchPartition.firstChosenRecordSelector
      rate record = some
        (cells[0]'(by
          rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length]
          exact hwindowPos),
          installed.registers.payload) := by
    simp [ReferenceOriginalCalendarRetainedBranchPartition.firstChosenRecordSelector,
      hlive', hdispatch]
  have hselectorRecordFirst : ReferenceOriginalCalendarRetainedBranchPartition.firstChosenRecordSelector
      rate record = some (ReferenceFirstLaunchCommonUpdateSource.firstCell rate rewards C_star C_h
        (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z) q control0 birth,
        installed.registers.payload) := by
    rw [htransportCell] at hselectorRecord
    exact hselectorRecord
  have hselector' : selector z = some ⟨record,
      (ReferenceFirstLaunchCommonUpdateSource.firstCell rate rewards C_star C_h
        (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z) q control0 birth,
        installed.registers.payload)⟩ := by
    unfold ReferenceOriginalCalendarRetainedBranchPartition.firstChosenSelector
    rw [hactualRecord]
    simp [hselectorRecordFirst]
  simp [hselector']

include control0 a in
/-- On every original source, the selector is present exactly at the literal
first-live birth date, including all source coordinates and the actual source
initialization outcome. -/
theorem firstChosenSelector_isSome_iff_sourcePhase
    (z : X) :
    (selector z).isSome = true ↔
      z ∈ phase 2 := by
  constructor
  · intro hselector
    classical
    cases h : selector z with
    | none => simp [h] at hselector
    | some data =>
        rcases data with ⟨r, c, payload⟩
        have hselected : selector z =
            some ⟨r, (c, payload)⟩ := by simpa using h
        obtain ⟨hdate, _, _, _, _⟩ :=
          ReferenceOriginalCalendarRetainedBranchPartition.firstSelector_initialPrefix
            rate rewards C_star C_h q z r c payload hselected
        have hparts := Option.bind_eq_some_iff.mp (by
          simpa only [ReferenceOriginalCalendarRetainedBranchPartition.firstChosenSelector] using
            hselected)
        obtain ⟨_, hrecord, _⟩ := hparts
        have hcross : (ReferenceCompletePhysicalHistory.generatedBoundary
            rate z rewards C_star C_h).crossing.isSome = true := by
          by_contra hn
          have hnone : (ReferenceCompletePhysicalHistory.generatedBoundary
              rate z rewards C_star C_h).crossing = none := by
            cases hc : (ReferenceCompletePhysicalHistory.generatedBoundary
                rate z rewards C_star C_h).crossing with
            | none => rfl
            | some crossing => exact False.elim (hn (by simp [hc]))
          have hrecordNone := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_no_crossing
            rate rewards C_star C_h q z hnone
          rw [hrecordNone] at hrecord
          cases hrecord
        have hdate' : q.val = ReferenceCompletePhysicalHistory.physicalStart
            rate z rewards C_star C_h := by
          simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart,
            ReferenceCompletePhysicalHistory.physicalStart] using hdate
        change (ReferenceCompletePhysicalHistory.generatedBoundary
            rate z rewards C_star C_h).crossing.isSome = true ∧
          q.val = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
        exact ⟨hcross, hdate'⟩
  · exact firstSelector_of_birthPhase rate rewards C_star C_h control0 q a z

include control0 a in
/-- The event is literally the source phase, not a selected subevent. -/
theorem firstSelectorEvent_eq_sourcePhase :
    firstSelectorEvent rate rewards C_star C_h q = phase 2 := by
  ext z
  exact firstChosenSelector_isSome_iff_sourcePhase rate rewards C_star C_h control0 q a z

include control0 a in
/-- The actual first-selector increment equals the identical birth-phase
indicator pointwise on every original source. -/
theorem firstSelectorIncrement_eq_sourcePhase_indicator :
    firstSelectorIncrement rate rewards C_star C_h q a =
      (phase 2).indicator
        (fun z => energy (q.val + 1) a z - energy q.val a z) := by
  funext z
  change Set.indicator (firstSelectorEvent rate rewards C_star C_h q)
    (fun z => energy (q.val + 1) a z - energy q.val a z) z =
    Set.indicator (phase 2)
      (fun z => energy (q.val + 1) a z - energy q.val a z) z
  rw [firstSelectorEvent_eq_sourcePhase rate rewards C_star C_h control0 q a]

include control0 a in
/-- Ambient measurability of the exact selector event. -/
theorem measurableSet_firstSelectorEvent :
    MeasurableSet (firstSelectorEvent rate rewards C_star C_h q) := by
  rw [firstSelectorEvent_eq_sourcePhase rate rewards C_star C_h control0 q a]
  exact ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
    rate rewards C_star C_h q control0 ⟨2, by omega⟩

include control0 a in
/-- Ambient measurability of the restricted actual energy increment. -/
theorem measurable_firstSelectorIncrement :
    Measurable (firstSelectorIncrement rate rewards C_star C_h q a) := by
  rw [firstSelectorIncrement_eq_sourcePhase_indicator rate rewards C_star C_h control0 q a]
  apply (ReferenceOriginalCalendarCarriedStoppedEnergy.measurable_carriedStoppedEnergy
      rate rewards C_star C_h (q.val + 1) a).sub
      (ReferenceOriginalCalendarCarriedStoppedEnergy.measurable_carriedStoppedEnergy
        rate rewards C_star C_h q.val a)
      |>.indicator
  exact ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
    rate rewards C_star C_h q control0 ⟨2, by omega⟩

include control0 a in
/-- Integrability under the original source-input law, using the public
carried-energy integrability bound and the exact measurable selector event. -/
theorem integrable_firstSelectorIncrement :
    Integrable (firstSelectorIncrement rate rewards C_star C_h q a)
      (sourceInputLaw p) := by
  rw [firstSelectorIncrement_eq_sourcePhase_indicator rate rewards C_star C_h control0 q a]
  have hnext := ReferenceOriginalCalendarCarriedStoppedEnergy.integrable_carriedStoppedEnergy
    rate rewards C_star C_h (q.val + 1) (by omega) a
  have hcurrent := ReferenceOriginalCalendarCarriedStoppedEnergy.integrable_carriedStoppedEnergy
    rate rewards C_star C_h q.val q.isLt.le a
  exact (hnext.sub hcurrent).indicator
    (ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
      rate rewards C_star C_h q control0 ⟨2, by omega⟩)

include control0 a in
/-- The exact first-selector energy increment is bounded by the true mass of
the same birth/selector event under the unchanged original source law. -/
theorem integral_firstSelectorIncrement_le_event_mass :
    (∫ z : X, firstSelectorIncrement rate rewards C_star C_h q a z
      ∂sourceInputLaw p) ≤
      (sourceInputLaw p).real (firstSelectorEvent rate rewards C_star C_h q) := by
  rw [firstSelectorIncrement_eq_sourcePhase_indicator rate rewards C_star C_h control0 q a,
    firstSelectorEvent_eq_sourcePhase rate rewards C_star C_h control0 q a]
  calc
    (∫ z : X, (phase 2).indicator
        (fun z => energy (q.val + 1) a z - energy q.val a z) z ∂sourceInputLaw p) =
      ∫ z in phase 2, energy (q.val + 1) a z - energy q.val a z ∂sourceInputLaw p :=
        integral_indicator
          (ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
            rate rewards C_star C_h q control0 ⟨2, by omega⟩)
    _ ≤ (sourceInputLaw p).real (phase 2) :=
      ReferenceOriginalCalendarFirstDispatchEnergyTransport.integral_carried_initial_increment_le_launch_mass
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (control0 := control0) (t := q) (a := a)

end Bandits.Support.ReferenceOriginalCalendarFirstBranchIncrementTransport

end
