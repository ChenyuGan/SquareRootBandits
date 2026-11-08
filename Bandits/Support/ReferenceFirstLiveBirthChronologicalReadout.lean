/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveChronologicalPrefixMeasurability
public import Bandits.Support.ReferenceFirstLaunchCommonUpdateSource
public import Bandits.Support.ReferenceRankInstallationCommonUpdateJointLaw

/-!
# Deterministic first-live chronological birth readout

On the original first-launch source stratum, this module identifies every
pre-refresh field of the actual zero-entry chronological prefix. The readout
retains the original physical record, whole first numerical cell, zero-state
update, recorder marker, reserved FAST coordinate, and proposal bit.

Sources: `sources/zip4/manuscript/06_interruptions.tex:381-426`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:142-215,323-366`, and
`sources/zip4/manuscript/08_main_theorem.tex:78-109`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceFirstLiveChronologicalPrefixFoundation
open Bandits.Support.ReferenceFirstLiveChronologicalPrefixMeasurability
open Bandits.Support.ReferenceFirstLaunchCommonUpdateSource
open Bandits.Support.ReferenceFirstLaunchRecordingPhysicalMarker
open Bandits.Support.ReferenceFirstLaunchRecordingSourceLaw
open Bandits.Support.ReferenceFirstLaunchOriginalAuxiliaryReward
open Bandits.Support.ReferenceRankInstallationRecorderFoundation
open Bandits.Support.ReferenceRankInstallationRecorderFastLaw

namespace Bandits.Support.ReferenceFirstLiveBirthChronologicalReadout

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p))
  (t : Fin p.T) (control0 : TimeControl p)

abbrev SourceStratum
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) :=
  ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
    (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)

abbrev AuxiliaryArray := ReferenceFirstLiveChronologicalPrefixFoundation.AuxiliaryArray p

private theorem actualCell_input_transport
    {r s : ReferenceFirstWindowNumericalStream.RoundRecord (p := p) (rate := rate)}
    (h : r = s) (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r) :
    (h ▸ cell).input = cell.input := by
  cases h
  rfl

private theorem actualCell_payload_transport
    {r s : ReferenceFirstWindowNumericalStream.RoundRecord (p := p) (rate := rate)}
    (h : r = s) (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r) :
    (h ▸ cell).selected.view.payload = cell.selected.view.payload := by
  cases h
  rfl

private theorem actualCell_pending_transport
    {r s : ReferenceFirstWindowNumericalStream.RoundRecord (p := p) (rate := rate)}
    (h : r = s) (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r) :
    (h ▸ cell).selected.view.pendingAtChoice = cell.selected.view.pendingAtChoice := by
  cases h
  rfl

private theorem actualCell_cutoff_transport
    {r s : ReferenceFirstWindowNumericalStream.RoundRecord (p := p) (rate := rate)}
    (h : r = s) (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r) :
    (h ▸ cell).selected.view.cutoff = cell.selected.view.cutoff := by
  cases h
  rfl

private theorem actualCell_reservedFast_transport
    {r s : ReferenceFirstWindowNumericalStream.RoundRecord (p := p) (rate := rate)}
    (h : r = s) (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r) :
    (ReferenceFirstLiveChronologicalPrefixFoundation.reservedFastArm s (h ▸ cell)).val =
      (ReferenceFirstLiveChronologicalPrefixFoundation.reservedFastArm r cell).val := by
  cases h
  rfl

local notation "coords" => ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
  rate rewards C_star C_h q t control0

/-! ## Canonical fixed first-assignment view -/

/-- The same unit-anchor, unoccupied, no-cutoff view used by the original
first-assignment source stratum. -/
def unitBirthView (v : ReferenceFirstLaunchRecordingPhysicalMarker.AssignmentVector (p := p)) :
    ReferenceDownReception.ChoiceTimeView p rate.eta where
  payload := AssignmentStartPayload.Input.ofFirstAssignment
    (ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t v)
  pendingAtChoice := Finset.univ
  cutoff := none
  complementWeights := fun _ => 1

/-- The fixed first-assignment view has valid choice inputs at its actual
source time. -/
theorem unitBirthView_valid
    (v : ReferenceFirstLaunchRecordingPhysicalMarker.AssignmentVector (p := p)) :
    CoordinatorLocalArmChoice.ChoiceInputsValid
      (unitBirthView rate t v).payload (unitBirthView rate t v).cutoff t
      (unitBirthView rate t v).complementWeights := by
  apply CoordinatorLocalArmChoice.choiceInputsValid_mk
  · change CoordinatorLocalArmChoice.assignmentStart
      (AssignmentStartPayload.Input.ofFirstAssignment
        (ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t v)) ≤
      CoordinatorLocalArmChoice.sourceRound t
    simp [CoordinatorLocalArmChoice.assignmentStart,
      CoordinatorLocalArmChoice.sourceRound,
      AssignmentStartPayload.Input.ofFirstAssignment,
      ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch]
  · simp [CoordinatorLocalArmChoice.assignmentStart,
      CoordinatorLocalArmChoice.cutoffRound, unitBirthView,
      ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch]
  · intro j
    simp [unitBirthView, ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch,
      AssignmentStartPayload.Input.ofFirstAssignment,
      FirstAssignmentLaunch.Input.anchor]

/-- The original same-slice recorder and reserved FAST output at the fixed
first-assignment view. -/
def unitBirthPair
    (v : ReferenceFirstLaunchRecordingPhysicalMarker.AssignmentVector (p := p))
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid
      (unitBirthView rate t v).payload (unitBirthView rate t v).cutoff t
      (unitBirthView rate t v).complementWeights)
    (slice : ContinuousControlSlice.Slice p.m p.K) : Option (Fin p.K) × Fin p.K :=
  ReferenceRankInstallationRecorderFastLaw.installationRecorderFastPair
    rate t (unitBirthView rate t v) valid slice

/-- The source marker and original reserved FAST arm form exactly the
same-slice pair at the canonical unit-anchor birth view. The pilot DATA arm
does not replace the reserved FAST coordinate. -/
theorem actual_birth_pair_eq_unitBirthPair
    (z : SourceStratum rate rewards C_star C_h q t) :
    (ReferenceFirstLaunchRecordingSourceLaw.sourceMarker
        rate rewards C_star C_h q t control0 z,
      (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm
        rate rewards C_star C_h q t control0 z).val) =
      unitBirthPair rate t (coords z).2.1
        (unitBirthView_valid rate t (coords z).2.1)
        (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl
          (coords z).2.1 (coords z).2.2).1 := by
  classical
  let c := coords z
  have hpair := ReferenceFirstLaunchRecordingPhysicalMarker.physical_marker_eq
    rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2
  have hsource : ReferenceFirstLaunchRecordingSourceLaw.sourceMarker
      rate rewards C_star C_h q t control0 z =
        ReferenceFirstLaunchRecordingPhysicalMarker.physicalMarker
          rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 := rfl
  have hfast := ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm_eq_originalFastScalar
    rate rewards C_star C_h q t control0 z
  have hvalid := unitBirthView_valid rate t c.2.1
  have hassign :
      (unitBirthView rate t c.2.1).payload.assignment =
        (ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t c.2.1).start.assignment :=
    ReferenceFirstLaunchRecordingPhysicalMarker.first_payload_assignment p rate.eta
      (ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t c.2.1)
  have hanchor : (unitBirthView rate t c.2.1).payload.anchor = fun _ => 1 := by
    funext i
    simp [unitBirthView, ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch,
      AssignmentStartPayload.Input.ofFirstAssignment, FirstAssignmentLaunch.Input.anchor]
  have hweights : ReferenceFirstWindowNumericalStream.sourceWeights
      (unitBirthView rate t c.2.1).payload
      (unitBirthView rate t c.2.1).complementWeights = fun _ => 1 := by
    funext i
    unfold ReferenceFirstWindowNumericalStream.sourceWeights
    split_ifs <;> simp [unitBirthView,
      ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch,
      AssignmentStartPayload.Input.ofFirstAssignment, FirstAssignmentLaunch.Input.anchor]
  have hmarkerView :
      ReferenceRankInstallationRecorderFoundation.installationRecordingMap
        rate t (unitBirthView rate t c.2.1) hvalid
        (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl c.2.1 c.2.2).1 =
      ReferenceFirstLaunchRecordingPhysicalMarker.unitRecordingMap rate
        (ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t c.2.1).start.assignment
        (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl c.2.1 c.2.2).1 := by
    simp only [ReferenceRankInstallationRecorderFoundation.installationRecordingMap,
      ReferenceRankInstallationRecorderFoundation.installationSnapshot,
      ReferenceFirstLaunchRecordingPhysicalMarker.unitRecordingMap,
      ReferenceFirstLaunchRecordingPhysicalMarker.unoccupiedSnapshot,
      hanchor, hweights]
    rw [hassign]
  have hslow :
      (unitBirthView rate t c.2.1).payload.slowSet =
        ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstSlowSet
          rate rewards C_star C_h q t control0 z := by
    rw [ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstSlowSet_eq_canonical]
    change (AssignmentStartPayload.Input.ofFirstAssignment
      (ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t c.2.1)).slowSet =
      CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
        (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
        c.2.1
    rw [AssignmentStartPayload.Input.slowSet_eq_first_start]
    rfl
  have hcontrol : ReferenceFirstLaunchRecordingPhysicalMarker.currentControl
      c.2.1 c.2.2 = (z.val.1.2 q).2 t := by
    change (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
      ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p)
        ((z.val.1.2 q).2 t)) = (z.val.1.2 q).2 t
    exact (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm_apply_apply _
  have hscalar :
      ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
        (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl c.2.1 c.2.2).1 =
          ((((z.val.1.2 q).2 t).1) ContinuousControlSlice.Label.fast) := by
    rw [hcontrol]
    rfl
  have hfastView :
      (ReferenceRankInstallationRecorderFastLaw.reservedFastAtView rate t
        (unitBirthView rate t c.2.1) hvalid
        (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl c.2.1 c.2.2).1).val =
      (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm
        rate rewards C_star C_h q t control0 z).val := by
    rw [ReferenceRankInstallationRecorderFastLaw.reservedFastAtView_eq_sampleFast
      rate t (unitBirthView rate t c.2.1) hvalid
      (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl c.2.1 c.2.2).1]
    simp only [hfast, hscalar, hanchor, hweights]
    exact congrArg (fun U : CanonicalOrientedSetLaw.SlowSet p.K p.m =>
      (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
        (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
        (by intro _; norm_num) (by intro _; norm_num) U
        ((((z.val.1.2 q).2 t).1) ContinuousControlSlice.Label.fast)).val) hslow
  rw [hsource, hpair]
  change (ReferenceFirstLaunchRecordingPhysicalMarker.unitRecordingMap rate
      (ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t c.2.1).start.assignment
      (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl c.2.1 c.2.2).1,
    (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm
      rate rewards C_star C_h q t control0 z).val) =
    (ReferenceRankInstallationRecorderFoundation.installationRecordingMap rate t
        (unitBirthView rate t (coords z).2.1) (unitBirthView_valid rate t (coords z).2.1)
        (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl (coords z).2.1
          (coords z).2.2).1,
      (ReferenceRankInstallationRecorderFastLaw.reservedFastAtView rate t
        (unitBirthView rate t (coords z).2.1) (unitBirthView_valid rate t (coords z).2.1)
        (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl (coords z).2.1
          (coords z).2.2).1).val)
  simp only [c, hmarkerView, hfastView]

/-! ## Actual first record and the whole-prefix cell -/

/-- The actual positive whole first-live window begins with the physical
first-launch record on this source stratum, including a launch at the final
physical round. -/
theorem actual_birth_whole_window_first
    (z : SourceStratum rate rewards C_star C_h q t) :
    ∃ tail,
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z.val =
        ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z.val rewards C_star C_h
          z.property.2.1 (by
            rw [ReferenceFirstLaunchCommonUpdateSource.source_elapsed_eq
              rate rewards C_star C_h q t z]
            exact t.isLt) :: tail := by
  classical
  let hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed < p.T := by
    rw [ReferenceFirstLaunchCommonUpdateSource.source_elapsed_eq rate rewards C_star C_h q t z]
    exact t.isLt
  let firstRecord := ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
    rate z.val rewards C_star C_h z.property.2.1 hs
  have hspan : t.val + 1 ≤ p.T := by omega
  have hfiber : z.val ∈
      ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
        (rate := rate) rewards C_star C_h t.val := by
    refine ⟨z.property.2.1, ?_⟩
    simpa only [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using
      (ReferenceFirstLaunchCommonUpdateSource.source_elapsed_eq
        rate rewards C_star C_h q t z)
  let fiber : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h t.val :=
    ⟨z.val, hfiber⟩
  have hshort := ReferenceFirstLaunchCommonUpdateSource.source_first_live_window_singleton
    rate rewards C_star C_h q t z
  have htake := ReferenceFirstLiveOverflowReadout.firstLiveWindow_eq_completeSuffix_take
    rate rewards C_star C_h t.val 1 hspan fiber
  have hshortSuffix :
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z.val rewards C_star C_h).take 1) = [firstRecord] := by
    have hshort' :
        ReferenceFirstLiveOverflowReadout.firstLiveWindow rate rewards C_star C_h
          t.val 1 hspan fiber = [firstRecord] := by
      simpa only [ReferenceFirstLiveOverflowReadout.firstLiveWindow,
        firstRecord, hs] using hshort
    exact htake.symm.trans hshort'
  let suffix := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z.val rewards C_star C_h
  cases hrecords : suffix with
  | nil =>
      simp [suffix, hrecords, ReferenceFirstLiveConfirmationHistory.firstLiveWindow] at hshortSuffix
  | cons record rest =>
      have hsmall :
          ReferenceFirstLiveConfirmationHistory.firstLiveWindow [record] = [firstRecord] := by
        change ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (List.take 1 suffix) = [firstRecord] at hshortSuffix
        rw [hrecords] at hshortSuffix
        have htakeOne : List.take 1 (record :: rest) = [record] := by simp
        rw [htakeOne] at hshortSuffix
        exact hshortSuffix
      have hcut : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
        cases h : ReferenceCollectionPhaseHistory.cutoffChosen record.input with
        | false => rfl
        | true => simp [ReferenceFirstLiveConfirmationHistory.firstLiveWindow, h] at hsmall
      have hrecord : record = firstRecord := by
        have hlist : [record] = [firstRecord] := by
          simpa [ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hcut] using hsmall
        exact (List.cons.inj hlist).1
      subst record
      refine ⟨rest.takeWhile (fun r => !ReferenceCollectionPhaseHistory.cutoffChosen r.input), ?_⟩
      change ReferenceFirstLiveConfirmationHistory.firstLiveWindow suffix =
        firstRecord :: rest.takeWhile (fun r => !ReferenceCollectionPhaseHistory.cutoffChosen r.input)
      rw [hrecords]
      simp [ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hcut]

/-- Positivity of the whole chronological prefix is derived from the actual
first-launch source stratum. -/
theorem actual_birth_chronological_prefix_positive
    (z : SourceStratum rate rewards C_star C_h q t) :
    0 < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z.val).length := by
  obtain ⟨tail, hwindow⟩ := actual_birth_whole_window_first rate rewards C_star C_h q t z
  rw [hwindow]
  exact Nat.zero_lt_succ _

/-- The global chronological cell at index zero is the very same selected
source cell as the one-round first-launch construction. This witness identity
prevents record or reward substitutions when the stream is extended. -/
private theorem actual_birth_first_cell_eq_one_round
    (z : SourceStratum rate rewards C_star C_h q t) :
    let hc := z.property.2.1
    let hspan := ReferenceFirstLaunchCommonUpdateSource.source_first_span rate rewards C_star C_h q t z
    let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z.val rewards C_star C_h hc 1 hspan
    let k : Fin window.length := ⟨0, by
      dsimp only [window]
      rw [ReferenceFirstLaunchCommonUpdateSource.source_first_live_window_singleton
        rate rewards C_star C_h q t z]
      simp⟩
    let hpositive : 0 < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z.val).length :=
      actual_birth_chronological_prefix_positive rate rewards C_star C_h q t z
    let record := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z.val)[0]'hpositive
    ReferenceFirstLiveChronologicalPrefixFoundation.wholeLiveCell rate rewards C_star C_h
      z.val record (List.getElem_mem hpositive) |>.input =
      (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h
        hc 1 hspan k).input := by
  classical
  obtain ⟨tail, hwindow⟩ := actual_birth_whole_window_first rate rewards C_star C_h q t z
  have hshort := ReferenceFirstLaunchCommonUpdateSource.source_first_live_window_singleton
    rate rewards C_star C_h q t z
  let rec0 := ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z.val rewards C_star C_h
    z.property.2.1 (by
      rw [ReferenceFirstLaunchCommonUpdateSource.source_elapsed_eq rate rewards C_star C_h q t z]
      exact t.isLt)
  have hglobal : ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z.val = rec0 :: tail := by
    simpa only [rec0] using hwindow
  have hlocal : ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z.val rewards C_star C_h z.property.2.1 1
        (ReferenceFirstLaunchCommonUpdateSource.source_first_span rate rewards C_star C_h q t z) =
      [rec0] := by
    simpa only [rec0] using hshort
  let hpositive := actual_birth_chronological_prefix_positive rate rewards C_star C_h q t z
  let fullRecord := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
    rate rewards C_star C_h z.val)[0]'hpositive
  let fullCell := ReferenceFirstLiveChronologicalPrefixFoundation.wholeLiveCell
    rate rewards C_star C_h z.val fullRecord (List.getElem_mem hpositive)
  let k : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z.val rewards C_star C_h z.property.2.1 1
        (ReferenceFirstLaunchCommonUpdateSource.source_first_span rate rewards C_star C_h q t z)).length :=
    ⟨0, by rw [hlocal]; simp⟩
  let localRecord := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate z.val rewards C_star C_h z.property.2.1 1
      (ReferenceFirstLaunchCommonUpdateSource.source_first_span rate rewards C_star C_h q t z))[k.val]'k.isLt
  let localCell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h
    z.property.2.1 1 (ReferenceFirstLaunchCommonUpdateSource.source_first_span rate rewards C_star C_h q t z) k
  have hfullRecord : fullRecord = rec0 := by
    simp only [fullRecord, hglobal, List.getElem_cons_zero]
  have hlocalRecord : localRecord = rec0 := by
    simp only [localRecord, k, hlocal, List.getElem_cons_zero]
  let fullCellAtRec : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell rec0 :=
    hfullRecord ▸ fullCell
  let localCellAtRec : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell rec0 :=
    hlocalRecord ▸ localCell
  have hcells := ReferenceFirstLiveChronologicalPrefixFoundation.actualLiveSourceCell_unique
    rec0 fullCellAtRec localCellAtRec
  change fullCell.input = localCell.input
  calc
    fullCell.input = fullCellAtRec.input :=
      (actualCell_input_transport rate hfullRecord fullCell).symm
    _ = localCellAtRec.input := congrArg
      (fun cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell rec0 => cell.input) hcells
    _ = localCell.input := actualCell_input_transport rate hlocalRecord localCell

/-- The first whole-suffix numerical input is the exact original source
`firstCell`, including its source recorder marker and whole reward and rate
vectors. -/
theorem actual_birth_whole_first_cell_input_eq
    (z : SourceStratum rate rewards C_star C_h q t) :
    let hpositive := actual_birth_chronological_prefix_positive rate rewards C_star C_h q t z
    let record := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z.val)[0]'hpositive
    (ReferenceFirstLiveChronologicalPrefixFoundation.wholeLiveCell rate rewards C_star C_h
      z.val record (List.getElem_mem hpositive)).input =
      ReferenceFirstLaunchCommonUpdateSource.firstCell rate rewards C_star C_h q t control0 z := by
  have hsame := actual_birth_first_cell_eq_one_round rate rewards C_star C_h q t z
  have hone := ReferenceFirstLaunchCommonUpdateSource.source_first_cell_chronological
    rate rewards C_star C_h q t control0 z
  change (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h
      z.property.2.1 1
      (ReferenceFirstLaunchCommonUpdateSource.source_first_span rate rewards C_star C_h q t z)
      ⟨0, by
        rw [ReferenceFirstLaunchCommonUpdateSource.source_first_live_window_singleton
          rate rewards C_star C_h q t z]
        simp⟩).input =
    ReferenceFirstLaunchCommonUpdateSource.firstCell rate rewards C_star C_h q t control0 z ∧ _ at hone
  exact hsame.trans hone.1

/-- The selected payload of the one-round source cell is the original
first-launch payload. -/
private theorem actual_birth_one_round_cell_payload_eq
    (z : SourceStratum rate rewards C_star C_h q t) :
    let hc := z.property.2.1
    let hspan := ReferenceFirstLaunchCommonUpdateSource.source_first_span rate rewards C_star C_h q t z
    let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z.val rewards C_star C_h hc 1 hspan
    let k : Fin window.length := ⟨0, by
      dsimp only [window]
      rw [ReferenceFirstLaunchCommonUpdateSource.source_first_live_window_singleton
        rate rewards C_star C_h q t z]
      simp⟩
    (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h
      hc 1 hspan k).selected.view.payload =
      ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstPayload
        rate rewards C_star C_h q t control0 z ∧
    (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h
      hc 1 hspan k).selected.view.pendingAtChoice = Finset.univ ∧
    (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h
      hc 1 hspan k).selected.view.cutoff = none ∧
    (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h
      hc 1 hspan k).selected.view.complementWeights = fun _ => 1 := by
  classical
  let c := coords z
  let hc := z.property.2.1
  let hspan := ReferenceFirstLaunchCommonUpdateSource.source_first_span
    rate rewards C_star C_h q t z
  let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate z.val rewards C_star C_h hc 1 hspan
  let k : Fin window.length := ⟨0, by
    dsimp only [window]
    rw [ReferenceFirstLaunchCommonUpdateSource.source_first_live_window_singleton
      rate rewards C_star C_h q t z]
    simp⟩
  let record := window[k.val]
  let liveCell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate z.val rewards C_star C_h hc 1 hspan k
  let physicalRecord := ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
    rate z.val rewards C_star C_h hc (by
      rw [ReferenceFirstLaunchCommonUpdateSource.source_elapsed_eq rate rewards C_star C_h q t z]
      exact t.isLt)
  have hwindow : window = [physicalRecord] := by
    simpa only [window, physicalRecord, hc] using
      ReferenceFirstLaunchCommonUpdateSource.source_first_live_window_singleton
        rate rewards C_star C_h q t z
  have hrecordAt : record = physicalRecord := by
    dsimp only [record]
    simp [k, hwindow]
  have hrecordSource : ReferenceFirstLaunchRecordingPhysicalMarker.record
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 = physicalRecord :=
    ReferenceFirstLaunchRecordingSourceLaw.source_record_eq
      rate rewards C_star C_h q t control0 z
  rcases ReferenceFirstLaunchRecordingPhysicalMarker.selection_exists
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 with
    ⟨selected, hselection, hpayload, hpending, hcutoff, hcomplement, _hlive, _hvalid⟩
  generalize hsourceDef : ReferenceFirstLaunchRecordingPhysicalMarker.record
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 = sourceRecord at *
  have hsourceActual : sourceRecord = record := hrecordSource.trans hrecordAt.symm
  cases hsourceActual
  have hselectionActual : record.output.preparation.coordinator.selection = some liveCell.selected := by
    change window[k.val].output.preparation.coordinator.selection = some liveCell.selected
    exact liveCell.selection_actual
  have hselected : liveCell.selected = selected := by
    exact Option.some.inj (hselectionActual.symm.trans hselection)
  have hpayload' : liveCell.selected.view.payload =
      ReferenceFirstLaunchRecordingPhysicalMarker.payload
        rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 := by
    rw [hselected]
    exact hpayload
  have hpending' : liveCell.selected.view.pendingAtChoice = Finset.univ := by
    rw [hselected]
    exact hpending
  have hcutoff' : liveCell.selected.view.cutoff = none := by
    rw [hselected]
    exact hcutoff
  have hcomplement' : liveCell.selected.view.complementWeights = fun _ => 1 := by
    rw [hselected]
    exact funext hcomplement
  change liveCell.selected.view.payload =
    ReferenceFirstLaunchRecordingPhysicalMarker.payload
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 ∧ _ ∧ _ ∧ _
  exact ⟨hpayload', hpending', hcutoff', hcomplement'⟩

/-- The whole-prefix selected payload is inherited from the exact same
first-launch record and one-round source cell. -/
private theorem actual_birth_whole_first_cell_payload_eq
    (z : SourceStratum rate rewards C_star C_h q t) :
    let hc := z.property.2.1
    let hspan := ReferenceFirstLaunchCommonUpdateSource.source_first_span rate rewards C_star C_h q t z
    let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z.val rewards C_star C_h hc 1 hspan
    let k : Fin window.length := ⟨0, by
      dsimp only [window]
      rw [ReferenceFirstLaunchCommonUpdateSource.source_first_live_window_singleton
        rate rewards C_star C_h q t z]
      simp⟩
    let hpositive := actual_birth_chronological_prefix_positive rate rewards C_star C_h q t z
    let record := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z.val)[0]'hpositive
    (ReferenceFirstLiveChronologicalPrefixFoundation.wholeLiveCell rate rewards C_star C_h
      z.val record (List.getElem_mem hpositive)).selected.view.payload =
      (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h
        hc 1 hspan k).selected.view.payload ∧
    (ReferenceFirstLiveChronologicalPrefixFoundation.wholeLiveCell rate rewards C_star C_h
      z.val record (List.getElem_mem hpositive)).selected.view.pendingAtChoice =
      (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h
        hc 1 hspan k).selected.view.pendingAtChoice ∧
    (ReferenceFirstLiveChronologicalPrefixFoundation.wholeLiveCell rate rewards C_star C_h
      z.val record (List.getElem_mem hpositive)).selected.view.cutoff =
      (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h
        hc 1 hspan k).selected.view.cutoff ∧
    (ReferenceFirstLiveChronologicalPrefixFoundation.reservedFastArm record
      (ReferenceFirstLiveChronologicalPrefixFoundation.wholeLiveCell rate rewards C_star C_h
        z.val record (List.getElem_mem hpositive))).val =
      (ReferenceFirstLiveChronologicalPrefixFoundation.reservedFastArm
        ((ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
          rate z.val rewards C_star C_h hc 1 hspan)[k.val]'k.isLt)
        (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h
          hc 1 hspan k)).val := by
  classical
  obtain ⟨tail, hwindow⟩ := actual_birth_whole_window_first rate rewards C_star C_h q t z
  have hshort := ReferenceFirstLaunchCommonUpdateSource.source_first_live_window_singleton
    rate rewards C_star C_h q t z
  let rec0 := ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z.val rewards C_star C_h
    z.property.2.1 (by
      rw [ReferenceFirstLaunchCommonUpdateSource.source_elapsed_eq rate rewards C_star C_h q t z]
      exact t.isLt)
  have hglobal : ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z.val = rec0 :: tail := by
    simpa only [rec0] using hwindow
  have hlocal : ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z.val rewards C_star C_h z.property.2.1 1
        (ReferenceFirstLaunchCommonUpdateSource.source_first_span rate rewards C_star C_h q t z) =
      [rec0] := by
    simpa only [rec0] using hshort
  let hpositive := actual_birth_chronological_prefix_positive rate rewards C_star C_h q t z
  let fullRecord := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
    rate rewards C_star C_h z.val)[0]'hpositive
  let fullCell := ReferenceFirstLiveChronologicalPrefixFoundation.wholeLiveCell
    rate rewards C_star C_h z.val fullRecord (List.getElem_mem hpositive)
  let k : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z.val rewards C_star C_h z.property.2.1 1
        (ReferenceFirstLaunchCommonUpdateSource.source_first_span rate rewards C_star C_h q t z)).length :=
    ⟨0, by rw [hlocal]; simp⟩
  let localRecord := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate z.val rewards C_star C_h z.property.2.1 1
      (ReferenceFirstLaunchCommonUpdateSource.source_first_span rate rewards C_star C_h q t z))[k.val]'k.isLt
  let localCell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h
    z.property.2.1 1 (ReferenceFirstLaunchCommonUpdateSource.source_first_span rate rewards C_star C_h q t z) k
  have hfullRecord : fullRecord = rec0 := by
    simp only [fullRecord, hglobal, List.getElem_cons_zero]
  have hlocalRecord : localRecord = rec0 := by
    simp only [localRecord, k, hlocal, List.getElem_cons_zero]
  let fullCellAtRec : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell rec0 :=
    hfullRecord ▸ fullCell
  let localCellAtRec : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell rec0 :=
    hlocalRecord ▸ localCell
  have hcells := ReferenceFirstLiveChronologicalPrefixFoundation.actualLiveSourceCell_unique
    rec0 fullCellAtRec localCellAtRec
  have hpayloadEq : fullCellAtRec.selected.view.payload = localCellAtRec.selected.view.payload :=
    congrArg (fun cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell rec0 =>
      cell.selected.view.payload) hcells
  have hpendingEq : fullCellAtRec.selected.view.pendingAtChoice =
      localCellAtRec.selected.view.pendingAtChoice := congrArg
    (fun cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell rec0 =>
      cell.selected.view.pendingAtChoice) hcells
  have hcutoffEq : fullCellAtRec.selected.view.cutoff = localCellAtRec.selected.view.cutoff :=
    congrArg (fun cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell rec0 =>
      cell.selected.view.cutoff) hcells
  have hfastEq :
      (ReferenceFirstLiveChronologicalPrefixFoundation.reservedFastArm rec0 fullCellAtRec).val =
        (ReferenceFirstLiveChronologicalPrefixFoundation.reservedFastArm rec0 localCellAtRec).val :=
    congrArg (fun cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell rec0 =>
      (ReferenceFirstLiveChronologicalPrefixFoundation.reservedFastArm rec0 cell).val) hcells
  have hpayloadFinal : fullCell.selected.view.payload = localCell.selected.view.payload := by
    calc
      fullCell.selected.view.payload = fullCellAtRec.selected.view.payload := by
        exact (actualCell_payload_transport rate hfullRecord fullCell).symm
      _ = localCellAtRec.selected.view.payload := hpayloadEq
      _ = localCell.selected.view.payload := actualCell_payload_transport rate hlocalRecord localCell
  have hpendingFinal : fullCell.selected.view.pendingAtChoice = localCell.selected.view.pendingAtChoice := by
    calc
      fullCell.selected.view.pendingAtChoice = fullCellAtRec.selected.view.pendingAtChoice := by
        exact (actualCell_pending_transport rate hfullRecord fullCell).symm
      _ = localCellAtRec.selected.view.pendingAtChoice := hpendingEq
      _ = localCell.selected.view.pendingAtChoice := actualCell_pending_transport rate hlocalRecord localCell
  have hcutoffFinal : fullCell.selected.view.cutoff = localCell.selected.view.cutoff := by
    calc
      fullCell.selected.view.cutoff = fullCellAtRec.selected.view.cutoff := by
        exact (actualCell_cutoff_transport rate hfullRecord fullCell).symm
      _ = localCellAtRec.selected.view.cutoff := hcutoffEq
      _ = localCell.selected.view.cutoff := actualCell_cutoff_transport rate hlocalRecord localCell
  have hfastFinal :
      (ReferenceFirstLiveChronologicalPrefixFoundation.reservedFastArm fullRecord fullCell).val =
        (ReferenceFirstLiveChronologicalPrefixFoundation.reservedFastArm localRecord localCell).val := by
    calc
      _ = (ReferenceFirstLiveChronologicalPrefixFoundation.reservedFastArm rec0 fullCellAtRec).val :=
        (actualCell_reservedFast_transport rate hfullRecord fullCell).symm
      _ = (ReferenceFirstLiveChronologicalPrefixFoundation.reservedFastArm rec0 localCellAtRec).val := hfastEq
      _ = _ := actualCell_reservedFast_transport rate hlocalRecord localCell
  exact ⟨hpayloadFinal, hpendingFinal, hcutoffFinal, hfastFinal⟩

/-- On the first source cell, the stored reserved FAST value is exactly the
original first-launch FAST draw from the original `Label.fast` scalar. -/
private theorem actual_birth_one_round_reservedFast_eq_actualFirstFast
    (z : SourceStratum rate rewards C_star C_h q t) :
    let hc := z.property.2.1
    let hspan := ReferenceFirstLaunchCommonUpdateSource.source_first_span rate rewards C_star C_h q t z
    let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z.val rewards C_star C_h hc 1 hspan
    let k : Fin window.length := ⟨0, by
      dsimp only [window]
      rw [ReferenceFirstLaunchCommonUpdateSource.source_first_live_window_singleton
        rate rewards C_star C_h q t z]
      simp⟩
    (ReferenceFirstLiveChronologicalPrefixFoundation.reservedFastArm
      (window[k.val]'k.isLt)
      (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h
        hc 1 hspan k)).val =
      (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm
        rate rewards C_star C_h q t control0 z).val := by
  classical
  let c := coords z
  let hc := z.property.2.1
  let hspan := ReferenceFirstLaunchCommonUpdateSource.source_first_span
    rate rewards C_star C_h q t z
  let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate z.val rewards C_star C_h hc 1 hspan
  let k : Fin window.length := ⟨0, by
    dsimp only [window]
    rw [ReferenceFirstLaunchCommonUpdateSource.source_first_live_window_singleton
      rate rewards C_star C_h q t z]
    simp⟩
  let record := window[k.val]
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate z.val rewards C_star C_h hc 1 hspan k
  have hone := actual_birth_one_round_cell_payload_eq rate rewards C_star C_h q t control0 z
  have hanchor :
      (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstPayload
        rate rewards C_star C_h q t control0 z).anchor = fun _ => 1 := by
    change (ReferenceFirstLaunchRecordingPhysicalMarker.payload
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2).anchor = fun _ => 1
    exact ReferenceFirstLaunchRecordingPhysicalMarker.payload_anchor
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2
  have hcellAnchor : cell.selected.view.payload.anchor = fun _ => 1 := by
    calc
      cell.selected.view.payload.anchor =
          (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstPayload
            rate rewards C_star C_h q t control0 z).anchor :=
        congrArg (fun payload => payload.anchor) hone.1
      _ = fun _ => 1 := hanchor
  have hslow : cell.selected.view.payload.slowSet =
      ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstSlowSet
        rate rewards C_star C_h q t control0 z := by
    rw [hone.1]
    unfold ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstSlowSet
    apply Subtype.ext
    change (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstPayload
      rate rewards C_star C_h q t control0 z).slowSet.1 =
      Finset.univ.image
        (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstPayload
          rate rewards C_star C_h q t control0 z).assignment.assigned
    exact (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstPayload
      rate rewards C_star C_h q t control0 z).assignment_image.symm
  have hcurrentControl : ReferenceFirstLaunchRecordingPhysicalMarker.currentControl
      c.2.1 c.2.2 = (z.val.1.2 q).2 t := by
    change (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
      ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p)
        ((z.val.1.2 q).2 t)) = (z.val.1.2 q).2 t
    exact (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm_apply_apply _
  have hrecordSource : ReferenceFirstLaunchRecordingPhysicalMarker.record
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 =
      ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z.val rewards C_star C_h hc
        (by
          rw [ReferenceFirstLaunchCommonUpdateSource.source_elapsed_eq rate rewards C_star C_h q t z]
          exact t.isLt) :=
    ReferenceFirstLaunchRecordingSourceLaw.source_record_eq
      rate rewards C_star C_h q t control0 z
  have hwindow : window = [ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
      rate z.val rewards C_star C_h hc
        (by
          rw [ReferenceFirstLaunchCommonUpdateSource.source_elapsed_eq rate rewards C_star C_h q t z]
          exact t.isLt)] := by
    simpa only [window, hc] using
      ReferenceFirstLaunchCommonUpdateSource.source_first_live_window_singleton
        rate rewards C_star C_h q t z
  have hrecordAt : record =
      ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z.val rewards C_star C_h hc
        (by
          rw [ReferenceFirstLaunchCommonUpdateSource.source_elapsed_eq rate rewards C_star C_h q t z]
          exact t.isLt) := by
    dsimp only [record]
    simp [k, hwindow]
  rcases ReferenceFirstLaunchRecordingPhysicalMarker.record_source_inputs
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 with
    ⟨_, hrows, hselected, htime, _⟩
  have hsource := ReferenceFirstLaunchRecordingSourceLaw.source_recover
    rate rewards C_star C_h q t control0 z
  have hrecordRow : record.input.row = z.val.1.2 q := by
    calc
      record.input.row =
          (ReferenceFirstLaunchRecordingPhysicalMarker.record
            rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2).input.row :=
        congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord => r.input.row)
          (hrecordAt.trans hrecordSource.symm)
      _ = z.val.1.2 q := by
        simp only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hselected]
        exact congrArg (fun s => s.1.2 q) hsource
  have hrecordTime : record.input.time = t := by
    calc
      record.input.time =
          (ReferenceFirstLaunchRecordingPhysicalMarker.record
            rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2).input.time :=
        congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord => r.input.time)
          (hrecordAt.trans hrecordSource.symm)
      _ = t := htime
  have hscalar : (record.input.row.2 record.input.time).1 ContinuousControlSlice.Label.fast =
      (((z.val.1.2 q).2 t).1 ContinuousControlSlice.Label.fast) := by
    rw [hrecordRow, hrecordTime]
  have hlocalCanonical :
      FastComplementLocality.sampleLocalFast p rate.eta.val rate.eta.property rate.sourceCap
        cell.selected.view.payload.anchor cell.selected.view.payload.anchor_pos
        cell.selected.view.payload.slowSet cell.selected.view.complementWeights
        cell.choiceInputsValid.current_weight_pos cell.choiceInputsValid.anchor_le_current
        cell.choiceInputsValid.current_le_twice_anchor
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
          (record.input.row.2 record.input.time).1) =
      CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
      cell.selected.view.payload.anchor (fun _ => 1)
        cell.selected.view.payload.anchor_pos (by intro _; norm_num)
        (by intro i; rw [hcellAnchor])
        (by intro i; norm_num [hcellAnchor])
      cell.selected.view.payload.slowSet
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
          (record.input.row.2 record.input.time).1) := by
    let U := cell.selected.view.payload.slowSet
    let w : CanonicalFastSampling.FastArm U → ℝ := cell.selected.view.complementWeights
    have hw : w = fun _ => 1 := by
      funext j
      dsimp [w]
      exact congrFun hone.2.2.2 j
    have hweight := FastComplementLocality.sampleLocalFast_eq_of_weights_eq
      p rate.eta.property rate.sourceCap cell.selected.view.payload.anchor
      cell.selected.view.payload.anchor_pos U w (fun _ => 1)
      cell.choiceInputsValid.current_weight_pos (by intro _; norm_num)
      cell.choiceInputsValid.anchor_le_current
      (by intro j; rw [hcellAnchor])
      cell.choiceInputsValid.current_le_twice_anchor
      (by intro j; norm_num [hcellAnchor])
      hw (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
        (record.input.row.2 record.input.time).1)
    have hcanonical := FastComplementLocality.sampleLocalFast_eq_sampleFast
      p rate.eta.property rate.sourceCap cell.selected.view.payload.anchor (fun _ => 1)
      cell.selected.view.payload.anchor_pos (by intro _; norm_num)
      (by intro i; rw [hcellAnchor])
      (by intro i; norm_num [hcellAnchor])
      cell.selected.view.payload.slowSet
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
        (record.input.row.2 record.input.time).1)
    exact hweight.trans hcanonical
  have hfirstFast := ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm_eq_originalFastScalar
    rate rewards C_star C_h q t control0 z
  have hreserved :
      (ReferenceFirstLiveChronologicalPrefixFoundation.reservedFastArm record cell).val =
      (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
        cell.selected.view.payload.anchor (fun _ => 1)
        cell.selected.view.payload.anchor_pos (by intro _; norm_num)
        (by intro i; rw [hcellAnchor])
        (by intro i; norm_num [hcellAnchor])
        cell.selected.view.payload.slowSet
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
          (record.input.row.2 record.input.time).1)).val := by
    unfold ReferenceFirstLiveChronologicalPrefixFoundation.reservedFastArm
    exact congrArg Subtype.val hlocalCanonical
  let fastValue := fun (U : CanonicalOrientedSetLaw.SlowSet p.K p.m)
      (x : ContinuousCategorical.Scalar) =>
    (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
      (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
      (by intro _; norm_num) (by intro _; norm_num) U x).val
  have hreservedValue :
      (ReferenceFirstLiveChronologicalPrefixFoundation.reservedFastArm record cell).val =
        fastValue cell.selected.view.payload.slowSet
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
            (record.input.row.2 record.input.time).1) := by
    simpa only [fastValue, hcellAnchor] using hreserved
  have hscalarCoordinate :
      ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
          (record.input.row.2 record.input.time).1 =
        ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
          (((z.val.1.2 q).2 t).1) := by
    change (record.input.row.2 record.input.time).1 ContinuousControlSlice.Label.fast = _
    exact hscalar
  have hmove :
      fastValue cell.selected.view.payload.slowSet
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
            (record.input.row.2 record.input.time).1) =
        fastValue
          (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstSlowSet
            rate rewards C_star C_h q t control0 z)
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
            (((z.val.1.2 q).2 t).1)) := by
    dsimp only [fastValue]
    rw [hslow, hscalarCoordinate]
  change (ReferenceFirstLiveChronologicalPrefixFoundation.reservedFastArm record cell).val =
    (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm
      rate rewards C_star C_h q t control0 z).val
  calc
    _ = fastValue cell.selected.view.payload.slowSet
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
          (record.input.row.2 record.input.time).1) := hreservedValue
    _ = fastValue
        (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstSlowSet
          rate rewards C_star C_h q t control0 z)
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
          (((z.val.1.2 q).2 t).1)) := hmove
    _ = _ := by
      simpa only [fastValue, ContinuousControlSlice.coordinate] using
        (congrArg Subtype.val hfirstFast).symm

/-- The payload attached to the whole-prefix first cell is the original
first-launch payload. -/
private theorem actual_birth_whole_first_cell_payload_eq_actual
    (z : SourceStratum rate rewards C_star C_h q t) :
    let hpositive := actual_birth_chronological_prefix_positive rate rewards C_star C_h q t z
    let record := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z.val)[0]'hpositive
    (ReferenceFirstLiveChronologicalPrefixFoundation.wholeLiveCell rate rewards C_star C_h
      z.val record (List.getElem_mem hpositive)).selected.view.payload =
      ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstPayload
        rate rewards C_star C_h q t control0 z := by
  have hwhole := actual_birth_whole_first_cell_payload_eq rate rewards C_star C_h q t z
  have hone := actual_birth_one_round_cell_payload_eq rate rewards C_star C_h q t control0 z
  exact hwhole.1.trans hone.1

/-- The actual zero-entry chronological path is constructed from its actual
whole-window first record and chosen source cell, starting at the canonical
zero learner state. -/
theorem actual_birth_chronological_entry_eq_append
    (z : SourceStratum rate rewards C_star C_h q t) (aux : AuxiliaryArray (p := p)) :
    let hpositive := actual_birth_chronological_prefix_positive rate rewards C_star C_h q t z
    let record := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z.val)[0]'hpositive
    let entry := (ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
      rate rewards C_star C_h (z.val, aux))[0]'(by
        rw [ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_length]
        exact hpositive)
    entry = ReferenceFirstLiveChronologicalPrefixFoundation.appendLogicalCell record
      (ReferenceFirstLiveChronologicalPrefixFoundation.wholeLiveCell rate rewards C_star C_h
        z.val record (List.getElem_mem hpositive))
      (RecordedQueueRun.initialState p.K) aux := by
  let hpositive := actual_birth_chronological_prefix_positive rate rewards C_star C_h q t z
  let k : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z.val).length := ⟨0, hpositive⟩
  have hget := ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_get
    rate rewards C_star C_h z.val aux k
  simpa only [k, List.take_zero, RecordedQueueRun.run, RecordedQueueRun.execute] using hget

/-- The reserved FAST value on the whole first-live cell is the original
first-launch scalar draw. -/
theorem actual_birth_whole_first_cell_reservedFast_eq_actualFirstFast
    (z : SourceStratum rate rewards C_star C_h q t) :
    let hpositive := actual_birth_chronological_prefix_positive rate rewards C_star C_h q t z
    let record := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z.val)[0]'hpositive
    let cell := ReferenceFirstLiveChronologicalPrefixFoundation.wholeLiveCell
      rate rewards C_star C_h z.val record (List.getElem_mem hpositive)
    (ReferenceFirstLiveChronologicalPrefixFoundation.reservedFastArm record cell).val =
      (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm
        rate rewards C_star C_h q t control0 z).val := by
  have hwhole := actual_birth_whole_first_cell_payload_eq rate rewards C_star C_h q t z
  have hone := actual_birth_one_round_reservedFast_eq_actualFirstFast
    rate rewards C_star C_h q t control0 z
  exact hwhole.2.2.2.trans hone

/-- Joint readout of every pre-refresh field at chronological entry zero.
The physical round, complete original source cell, initial-state update,
all-arm queue data, actual slow set, original reserved FAST draw, and the
unmodified proposal bit are tied to the same first-live record. The final pair
is the original source recorder/FAST pair at the canonical unit-anchor view. -/
theorem actual_birth_chronological_entry_readout
    (z : SourceStratum rate rewards C_star C_h q t)
    (aux : AuxiliaryArray (p := p)) :
    let hpositive := actual_birth_chronological_prefix_positive rate rewards C_star C_h q t z
    let record := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z.val)[0]'hpositive
    let entry := (ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
      rate rewards C_star C_h (z.val, aux))[0]'(by
        rw [ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_length]
        exact hpositive)
    let firstCell := ReferenceFirstLaunchCommonUpdateSource.firstCell
      rate rewards C_star C_h q t control0 z
    let qparams := ReferenceFirstLaunchNumericalCell.queueParameters rate
    entry.time = t ∧
    entry.physical = ReferenceActiveHorizonMeasurability.roundRecordCode record ∧
    entry.numerical = (firstCell.enabled,
      (firstCell.recordedArm, (firstCell.reward, firstCell.rate))) ∧
    entry.before = RecordedQueueRun.initialState p.K ∧
    entry.after = ReferenceFirstLaunchCommonUpdateSource.firstUpdate
      rate rewards C_star C_h q t control0 z ∧
    entry.arrivals = (fun i => RecordedQueueRun.acceptedRecord qparams
      (RecordedQueueRun.initialState p.K) firstCell i) ∧
    entry.service = (fun i => RecordedQueueRun.recordService (4 * qparams.n)
      ((RecordedQueueRun.initialState p.K).registers i)
      (RecordedQueueRun.acceptedRecord qparams
        (RecordedQueueRun.initialState p.K) firstCell i)) ∧
    entry.slowSet = ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstSlowSet
      rate rewards C_star C_h q t control0 z ∧
    entry.fastArm = (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm
      rate rewards C_star C_h q t control0 z).val ∧
    entry.proposal = FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      record.input.row record.input.time ∧
    (ReferenceFirstLaunchRecordingSourceLaw.sourceMarker
        rate rewards C_star C_h q t control0 z,
      (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm
        rate rewards C_star C_h q t control0 z).val) =
      unitBirthPair rate t (coords z).2.1 (unitBirthView_valid rate t (coords z).2.1)
        (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl
          (coords z).2.1 (coords z).2.2).1 := by
  let hpositive := actual_birth_chronological_prefix_positive rate rewards C_star C_h q t z
  let record := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
    rate rewards C_star C_h z.val)[0]'hpositive
  let cell := ReferenceFirstLiveChronologicalPrefixFoundation.wholeLiveCell
    rate rewards C_star C_h z.val record (List.getElem_mem hpositive)
  let entry := (ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
    rate rewards C_star C_h (z.val, aux))[0]'(by
      rw [ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_length]
      exact hpositive)
  let firstCell := ReferenceFirstLaunchCommonUpdateSource.firstCell
    rate rewards C_star C_h q t control0 z
  let qparams := ReferenceFirstLaunchNumericalCell.queueParameters rate
  have happend := actual_birth_chronological_entry_eq_append
    rate rewards C_star C_h q t z aux
  have hinput := actual_birth_whole_first_cell_input_eq
    rate rewards C_star C_h q t control0 z
  have hpayload := actual_birth_whole_first_cell_payload_eq_actual
    rate rewards C_star C_h q t control0 z
  have hwholeFast := actual_birth_whole_first_cell_reservedFast_eq_actualFirstFast
    rate rewards C_star C_h q t control0 z
  have hslowCell : cell.selected.view.payload.slowSet =
      ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstSlowSet
        rate rewards C_star C_h q t control0 z := by
    rw [hpayload]
    unfold ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstSlowSet
    apply Subtype.ext
    change (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstPayload
      rate rewards C_star C_h q t control0 z).slowSet.1 =
      Finset.univ.image
        (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstPayload
          rate rewards C_star C_h q t control0 z).assignment.assigned
    exact (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstPayload
      rate rewards C_star C_h q t control0 z).assignment_image.symm
  obtain ⟨tail, hwindow⟩ := actual_birth_whole_window_first rate rewards C_star C_h q t z
  have hwholeRecord : record =
      ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z.val rewards C_star C_h
        z.property.2.1 (by
          rw [ReferenceFirstLaunchCommonUpdateSource.source_elapsed_eq rate rewards C_star C_h q t z]
          exact t.isLt) := by
    simp only [record, hwindow, List.getElem_cons_zero]
  have hsourceRecord := ReferenceFirstLaunchRecordingSourceLaw.source_record_eq
    rate rewards C_star C_h q t control0 z
  let c := coords z
  obtain ⟨_, _, _, hrecordTime, _⟩ := ReferenceFirstLaunchRecordingPhysicalMarker.record_source_inputs
    rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2
  have htime : record.input.time = t := by
    calc
      record.input.time =
          (ReferenceFirstLaunchRecordingPhysicalMarker.record
            rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2).input.time :=
        congrArg (fun r => r.input.time) (hwholeRecord.trans hsourceRecord.symm)
      _ = t := hrecordTime
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [happend, ReferenceFirstLiveChronologicalPrefixFoundation.appendLogicalCell] using htime
  · simp only [happend, ReferenceFirstLiveChronologicalPrefixFoundation.appendLogicalCell]
  · simpa only [happend, ReferenceFirstLiveChronologicalPrefixFoundation.appendLogicalCell] using
      congrArg (fun x : RecordedQueueRun.RoundInput p.K =>
        (x.enabled, (x.recordedArm, (x.reward, x.rate)))) hinput
  · simp only [happend, ReferenceFirstLiveChronologicalPrefixFoundation.appendLogicalCell]
  · simp only [happend, ReferenceFirstLiveChronologicalPrefixFoundation.appendLogicalCell,
      hinput, ReferenceFirstLaunchCommonUpdateSource.firstUpdate,
      ReferenceFirstLaunchCommonUpdateSource.firstCell]
  · simp only [happend, ReferenceFirstLiveChronologicalPrefixFoundation.appendLogicalCell, hinput]
  · funext i
    simp only [happend, ReferenceFirstLiveChronologicalPrefixFoundation.appendLogicalCell, hinput]
  · simpa [happend, ReferenceFirstLiveChronologicalPrefixFoundation.appendLogicalCell,
      hslowCell]
  · simpa [happend, ReferenceFirstLiveChronologicalPrefixFoundation.appendLogicalCell,
      RecordedQueueRun.initialState] using hwholeFast
  · simp [happend, ReferenceFirstLiveChronologicalPrefixFoundation.appendLogicalCell,
      RecordedQueueRun.initialState]
  · exact actual_birth_pair_eq_unitBirthPair rate rewards C_star C_h q t control0 z

end Bandits.Support.ReferenceFirstLiveBirthChronologicalReadout

end
