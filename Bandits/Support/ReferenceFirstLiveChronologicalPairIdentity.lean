/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveCanonicalProposalJointLaw
public import Bandits.Support.ReferenceFirstLiveChronologicalPrefixMeasurability
public import Bandits.Support.ReferenceFirstLiveChronologicalPrefixCausality

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Tactic

/-!
# Original first-LIVE chronological cell identity

On either positive-offset original-source branch, the date-`t` cell of the
same generated chronological prefix retains the actual current record and
numerical cell. Under the computed clear PRE-overflow condition, its marker and
reserved FAST operation agree with that physical record's actual operations.

Sources: `sources/zip4/manuscript/06_interruptions.tex:381-397`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:142-215,323-366`, and
`sources/zip4/manuscript/08_main_theorem.tex:78-109`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Bandits.Support.ReferenceFirstLiveChronologicalPairIdentity

open ReferenceFirstLiveCanonicalProposalJointLaw
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLiveChronologicalPrefixCausality
open ReferenceFirstLiveChronologicalPrefixMeasurability
open ReferenceFirstLivePostUpdateProposalLaw

variable {p : ConstructorDimensions.Parameters}

abbrev RateInput := ReferenceFirstLiveCanonicalProposalJointLaw.RateInput
abbrev RewardTable := ReferenceFirstLiveCanonicalProposalJointLaw.RewardTable
abbrev SourceInput := ReferenceFirstLiveChronologicalPrefixFoundation.SourceInput
abbrev AuxiliaryArray := ReferenceFirstLiveChronologicalPrefixFoundation.AuxiliaryArray
abbrev NumericalPast :=
  (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ)))
abbrev LiveRemainder (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) :=
  ReferenceFirstLivePostUpdateProposalLaw.LiveRemainder
    rate rewards C_star C_h q t s hs control0

variable (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p)

private theorem actualCellInput_congr
    {left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (h : left = right)
    (a : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell left)
    (b : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell right) :
    a.input = b.input := by
  cases h
  exact ReferenceFirstLiveOverflowReadout.actualLiveSourceCell_input_unique left a b

private theorem actualCell_selected_transport
    {left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hrecord : left = right)
    (a : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell left)
    (b : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell right) :
    (hrecord ▸ a).selected = b.selected := by
  cases hrecord
  apply Option.some.inj
  exact a.selection_actual.symm.trans b.selection_actual

private theorem actualCell_payload_transport
    {left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hrecord : left = right)
    (a : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell left) :
    (hrecord ▸ a).selected.view.payload = a.selected.view.payload := by
  cases hrecord
  rfl

private theorem actualCell_reservedFast_transport
    {left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hrecord : left = right)
    (a : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell left) :
    (reservedFastArm right (hrecord ▸ a)).val = (reservedFastArm left a).val := by
  cases hrecord
  rfl

private theorem actualCell_reservedFast_same
    {record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (a b : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record)
    (hselected : a.selected = b.selected) :
    (reservedFastArm record a).val = (reservedFastArm record b).val := by
  have hview : a.selected.view = b.selected.view := congrArg
    (fun selected : ReferenceActivePhysicalStep.Selection record.input => selected.view)
    hselected
  let Data := {view : ReferenceDownReception.ChoiceTimeView p rate.eta //
    CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff
      record.input.time view.complementWeights}
  have hdata : (⟨a.selected.view, a.choiceInputsValid⟩ : Data) =
      ⟨b.selected.view, b.choiceInputsValid⟩ := by
    apply Subtype.ext
    exact hview
  unfold reservedFastArm
  let sample : Data → Fin p.K := fun d =>
    (FastComplementLocality.sampleLocalFast p rate.eta.val rate.eta.property
      rate.sourceCap d.1.payload.anchor d.2.anchor_pos d.1.payload.slowSet
      d.1.complementWeights d.2.current_weight_pos d.2.anchor_le_current
      d.2.current_le_twice_anchor
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
        (record.input.row.2 record.input.time).1)).val
  change sample ⟨a.selected.view, a.choiceInputsValid⟩ =
    sample ⟨b.selected.view, b.choiceInputsValid⟩
  exact congrArg sample hdata

/-- The date-`t` member of the same generated first-LIVE prefix is the
physical original-source cell. On clear PRE overflow its recorded arm is the
actual branch marker, and its FAST field is the cell constructor's reserved
draw. The original-source reserved operation is identified separately. -/
public theorem originalSource_clear_chronological_pair_cell
    (tagged : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
        rate rewards C_star C_h q t s hs control0 ⊕
      ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0)
    (aux : AuxiliaryArray p)
    (hclear : (liveNumericalPast rate rewards C_star C_h q t s hs control0
      (originalLiveRemainder rate rewards C_star C_h q t s hs control0 tagged)).2.1 = false) :
    let z := Sum.elim Subtype.val Subtype.val tagged
    let n := t.val - s
    let x := originalLiveRemainder rate rewards C_star C_h q t s hs control0 tagged
    let u := ReferenceFirstLiveRecordingSourceCylinder.originalControl
      rate rewards C_star C_h q t s hs z
    let entry := (firstLiveChronologicalPrefix rate rewards C_star C_h (z.val, aux))[n]'(by
      obtain ⟨hk, _, _, _⟩ := source_whole_prefix_alignment
        rate rewards C_star C_h q t s hs control0 tagged
      rw [firstLiveChronologicalPrefix_length,
        ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength]
      exact hk)
    let record := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z.val)[n]'(by
        obtain ⟨hk, _, _, _⟩ := source_whole_prefix_alignment
          rate rewards C_star C_h q t s hs control0 tagged
        exact hk)
    let cell := wholeLiveCell rate rewards C_star C_h z.val record
      (List.getElem_mem (by
        obtain ⟨hk, _, _, _⟩ := source_whole_prefix_alignment
          rate rewards C_star C_h q t s hs control0 tagged
        exact hk))
    entry.before.overflow = false ∧
      entry.numerical.2.1 = liveMarker rate rewards C_star C_h q t s hs control0 (x, u) ∧
      entry.fastArm = (reservedFastArm record cell).val ∧
      liveReservedFastOption rate rewards C_star C_h q t s hs control0 (x, u) =
        some entry.fastArm ∧
      liveReservedFastOption rate rewards C_star C_h q t s hs control0 (x, u) =
        reservedFastAtInput (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
          rate rewards C_star C_h q t s hs control0 z).input := by
  intro z n x u entry record cell
  obtain ⟨hk, hrecord, hcells, _⟩ :=
    source_whole_prefix_alignment rate rewards C_star C_h q t s hs control0 tagged
  let index : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h z.val).length := ⟨n, hcells⟩
  let past := RecordedQueueRun.run
    (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val).take n)
  have hnum : liveNumericalPast rate rewards C_star C_h q t s hs control0 x =
      (past.registers, past.overflow, past.records) := by
    simpa only [x, z, n, past, originalLiveRemainder] using
      originalSource_numerical_prefix rate rewards C_star C_h q t s hs control0 tagged
  have hoverflow : past.overflow = false := by
    have hprojection := congrArg (fun value : NumericalPast (p := p) => value.2.1) hnum
    exact hprojection.symm.trans hclear
  have hweight : liveNumericalWeights rate rewards C_star C_h q t s hs control0 x =
      RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate) past := by
    funext a
    rw [liveNumericalWeights, hnum]
    rfl
  have hentry : entry = appendLogicalCell record cell past aux := by
    convert firstLiveChronologicalPrefix_get rate rewards C_star C_h z.val aux ⟨n, hk⟩ using 1
  have hbefore : entry.before.overflow = false := by
    rw [hentry, appendLogicalCell]
    exact hoverflow
  have hentryMarker : entry.numerical.2.1 = cell.input.recordedArm := by
    rw [hentry, appendLogicalCell]
  have hmarker : cell.input.recordedArm =
      liveMarker rate rewards C_star C_h q t s hs control0 (x, u) := by
    cases tagged with
    | inl point =>
        let branchCell := ReferenceFirstLiveSourceCellReadout.cell
          rate rewards C_star C_h q t s hs control0 point
        obtain ⟨_, _, _, hbranchMarker, _⟩ :=
          ReferenceFirstLiveSourceCellReadout.source_current_cell_fields
            rate rewards C_star C_h q t s hs control0 point
        have hbranchRecord := ReferenceFirstLiveSourceCellReadout.source_current_record
          rate rewards C_star C_h q t s hs control0 point
        have hbranchRecord' := by
          simpa only [ReferenceFirstLiveSourceCellReadout.source_current_index_val] using hbranchRecord
        have hsameRecord := hbranchRecord'.trans hrecord.symm
        have hsameInput := actualCellInput_congr rate hsameRecord branchCell cell
        calc
          cell.input.recordedArm = branchCell.input.recordedArm :=
            congrArg RecordedQueueRun.RoundInput.recordedArm hsameInput.symm
          _ = ReferenceFirstLiveRecordingSourceCylinder.sourceMarker
              rate rewards C_star C_h q t s hs control0 point := hbranchMarker
          _ = liveMarker rate rewards C_star C_h q t s hs control0 (x, u) := rfl
    | inr point =>
        let branchInput := ReferenceFirstLiveEmptyPendingSourceMoments.cell
          rate rewards C_star C_h q t s hs control0 point
        obtain ⟨_, _, _, hbranchMarker, _, actualRecord, hactualRecord, sourceCell,
          hsourceInput, _⟩ := ReferenceFirstLiveEmptyPendingSourceMoments.cell_actual_facts
            rate rewards C_star C_h q t s hs control0 point
        have hsameRecord : actualRecord = record := hactualRecord.trans hrecord.symm
        have hsameInput := actualCellInput_congr rate hsameRecord sourceCell cell
        calc
          cell.input.recordedArm = sourceCell.input.recordedArm :=
            congrArg RecordedQueueRun.RoundInput.recordedArm hsameInput.symm
          _ = branchInput.recordedArm :=
            congrArg RecordedQueueRun.RoundInput.recordedArm hsourceInput
          _ = ReferenceFirstLiveEmptyPendingMarkerLaw.actualEmptyMarker
              rate rewards C_star C_h q t s hs control0 point := hbranchMarker
          _ = liveMarker rate rewards C_star C_h q t s hs control0 (x, u) := by
            rw [ReferenceFirstLiveEmptyPendingMarkerLaw.actualEmptyMarker_eq_control]
            simp [x, u, z, liveMarker, originalLiveRemainder,
              ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit]
  have hentryReserved : entry.fastArm = (reservedFastArm record cell).val := by
    rw [hentry, appendLogicalCell, hoverflow]
    simp

  let W := RecordedQueueRun.scoreWeight
    (ReferenceFirstLaunchNumericalCell.queueParameters rate) past
  obtain ⟨launch, fiber, fastIndex, hfiber, hposition, _hwholeInput,
      hWpos, hWlower, hWupper, hWcomplement, hWfast, _⟩ :=
    ReferenceFirstLiveNumericalFastPersistence.wholeFirstLive_full_weight_fast
      rate rewards C_star C_h z.val ⟨n, hcells⟩ hoverflow
  let fastRecord := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate fiber.val rewards C_star C_h
      (ReferenceFirstLiveOverflowReadout.launch_crossing
        rate rewards C_star C_h launch.val fiber)
      (p.T - launch.val)
      (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
        launch.val (p.T - launch.val)
        (ReferenceFirstLiveOverflowReadout.maximal_span launch) fiber))[fastIndex.val]'fastIndex.isLt
  let fastCell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate fiber.val rewards C_star C_h
      (ReferenceFirstLiveOverflowReadout.launch_crossing
        rate rewards C_star C_h launch.val fiber)
      (p.T - launch.val)
      (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
        launch.val (p.T - launch.val)
        (ReferenceFirstLiveOverflowReadout.maximal_span launch) fiber) fastIndex
  have hfiberWindow := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
    rate rewards C_star C_h launch fiber
  have hwindow : ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate fiber.val rewards C_star C_h
      (ReferenceFirstLiveOverflowReadout.launch_crossing
        rate rewards C_star C_h launch.val fiber)
      (p.T - launch.val)
      (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
        launch.val (p.T - launch.val)
        (ReferenceFirstLiveOverflowReadout.maximal_span launch) fiber) =
    ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z.val := by
    calc
      _ = ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h fiber.val := hfiberWindow.1.symm
      _ = ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h z.val := congrArg
            (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h) hfiber
  have hfastRecord : fastRecord = record := by
    dsimp only [fastRecord, record]
    have hposition' : fastIndex.val = n := by
      simpa using hposition
    calc
      _ = (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h z.val)[fastIndex.val]'_ :=
        getElem_congr_coll (i := fastIndex.val) (w := fastIndex.isLt) hwindow
      _ = (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h z.val)[n]'hk := by
        simp only [hposition']
  have hfastCellInput : fastCell.input = cell.input :=
    actualCellInput_congr rate hfastRecord fastCell cell
  have hretained : liveRetained rate rewards C_star C_h q t s hs control0 x =
      ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
        rate rewards C_star C_h q t s hs control0 z := by
    cases tagged <;> rfl
  let sourceInput := ReferenceFirstLiveRecordingReadoutMeasurability.sourceInputAtControl
    (liveRetained rate rewards C_star C_h q t s hs control0 x) u
  let sourceRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
    ⟨sourceInput, ReferenceActivePhysicalStep.step sourceInput, rfl⟩
  have hsourceRecordOriginal : sourceRecord =
      ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z := by
    change ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl
        (liveRetained rate rewards C_star C_h q t s hs control0 x) u = _
    rw [hretained]
    exact ReferenceFirstLiveRecordingSourceCylinder.sourceRecordAtControl_eq_original
      rate rewards C_star C_h q t s hs control0 z
  have hrecordSource : record = sourceRecord := hrecord.trans hsourceRecordOriginal.symm
  have hfastSourceRecord : fastRecord = sourceRecord := hfastRecord.trans hrecordSource
  let fastCellAtSource : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell sourceRecord :=
    hfastSourceRecord ▸ fastCell
  obtain ⟨payloadSelection, hpayloadSelection, hpayloadFast⟩ :=
    ReferenceFirstLiveCanonicalProposalJointLaw.livePayload_selected_at_control
      rate rewards C_star C_h q t s hs control0 x u
  have hprepSourceRecord :
      (ReferenceActivePhysicalStep.prepare sourceInput).coordinator.selection =
        sourceRecord.output.preparation.coordinator.selection := by
    dsimp only [sourceRecord]
    rfl
  have hselectedFastSource : payloadSelection = fastCellAtSource.selected := by
    apply Option.some.inj
    calc
      some payloadSelection =
          (ReferenceActivePhysicalStep.prepare sourceInput).coordinator.selection :=
        hpayloadSelection.symm
      _ = sourceRecord.output.preparation.coordinator.selection := hprepSourceRecord
      _ = some fastCellAtSource.selected := fastCellAtSource.selection_actual
  have hpayloadFastSource : fastCellAtSource.selected.view.payload =
      livePayload rate rewards C_star C_h q t s hs control0 x := by
    rw [← hselectedFastSource]
    exact hpayloadFast
  have hpayloadFastCell : fastCell.selected.view.payload =
      livePayload rate rewards C_star C_h q t s hs control0 x := by
    calc
      fastCell.selected.view.payload = fastCellAtSource.selected.view.payload :=
        (actualCell_payload_transport rate hfastSourceRecord fastCell).symm
      _ = livePayload rate rewards C_star C_h q t s hs control0 x := hpayloadFastSource
  let fastCellAtRecord : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record :=
    hfastRecord ▸ fastCell
  have hselectedFastRecord : fastCellAtRecord.selected = cell.selected := by
    exact actualCell_selected_transport rate hfastRecord fastCell cell
  have hfastArmTransport :=
    actualCell_reservedFast_transport rate hfastRecord fastCell
  have hfastArmSame := actualCell_reservedFast_same rate
    fastCellAtRecord cell hselectedFastRecord
  have hweight : ∀ a : Fin p.K,
      liveNumericalWeights rate rewards C_star C_h q t s hs control0 x a = W a := by
    intro a
    rw [liveNumericalWeights, hnum]
    rfl
  have hW : W = liveNumericalWeights rate rewards C_star C_h q t s hs control0 x := by
    funext a
    exact (hweight a).symm
  obtain ⟨hcanonicalPos, hcanonicalLower, hcanonicalUpper, hcanonicalFast⟩ :=
    ReferenceFirstLiveCanonicalProposalJointLaw.liveReservedFastOption_canonical
      rate rewards C_star C_h q t s hs control0 x hclear
  have hscalar :
      ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
          (fastRecord.input.row.2 fastRecord.input.time).1 =
        ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast u.1 := by
    have hinput := congrArg ReferenceActivePhysicalHorizon.RoundRecord.input hfastSourceRecord
    rw [hinput]
    simp [sourceRecord, sourceInput,
      ReferenceFirstLiveRecordingReadoutMeasurability.sourceInputAtControl,
      ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
      ReferenceContinuingLiveSlicePreparation.rowAtControl_time]
  have hfastArmCanonical :
      (reservedFastArm fastRecord fastCell).val =
        (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
          (fastCell.selected.view.payload).anchor W
          (fastCell.selected.view.payload).anchor_pos hWpos hWlower hWupper
          fastCell.selected.view.payload.slowSet
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
            u.1)).val := by
    have h := congrArg Subtype.val
      (hWfast (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast u.1))
    simpa only [reservedFastArm, hscalar] using h
  have hcanonicalSame :
      (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
        fastCell.selected.view.payload.anchor W
        fastCell.selected.view.payload.anchor_pos hWpos hWlower hWupper
        fastCell.selected.view.payload.slowSet
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast u.1)).val =
      (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
        (livePayload rate rewards C_star C_h q t s hs control0 x).anchor
        (liveNumericalWeights rate rewards C_star C_h q t s hs control0 x)
        (livePayload rate rewards C_star C_h q t s hs control0 x).anchor_pos
        hcanonicalPos hcanonicalLower hcanonicalUpper
        (livePayload rate rewards C_star C_h q t s hs control0 x).slowSet
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast u.1)).val := by
    let Data := {value : AssignmentStartPayload.Input p rate.eta × (Fin p.K → ℝ) //
      (∀ a, 0 < value.2 a) ∧ (∀ a, value.1.anchor a ≤ value.2 a) ∧
        ∀ a, value.2 a ≤ 2 * value.1.anchor a}
    let fastData : Data := ⟨(fastCell.selected.view.payload, W),
      ⟨hWpos, hWlower, hWupper⟩⟩
    let liveData : Data := ⟨(livePayload rate rewards C_star C_h q t s hs control0 x,
      liveNumericalWeights rate rewards C_star C_h q t s hs control0 x),
      ⟨hcanonicalPos, hcanonicalLower, hcanonicalUpper⟩⟩
    have hdata : fastData = liveData := by
      apply Subtype.ext
      exact Prod.ext hpayloadFastCell hW
    let sample : Data → Fin p.K := fun d =>
      (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
        d.1.1.anchor d.1.2 d.1.1.anchor_pos d.2.1 d.2.2.1 d.2.2.2
        d.1.1.slowSet
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast u.1)).val
    change sample fastData = sample liveData
    exact congrArg sample hdata
  have hfastArmEq : (reservedFastArm record cell).val =
      (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
        (livePayload rate rewards C_star C_h q t s hs control0 x).anchor
        (liveNumericalWeights rate rewards C_star C_h q t s hs control0 x)
        (livePayload rate rewards C_star C_h q t s hs control0 x).anchor_pos
        hcanonicalPos hcanonicalLower hcanonicalUpper
        (livePayload rate rewards C_star C_h q t s hs control0 x).slowSet
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast u.1)).val := by
    calc
      (reservedFastArm record cell).val =
          (reservedFastArm record fastCellAtRecord).val := hfastArmSame.symm
      _ = (reservedFastArm fastRecord fastCell).val := hfastArmTransport
      _ = (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
          (fastCell.selected.view.payload).anchor W
          (fastCell.selected.view.payload).anchor_pos hWpos hWlower hWupper
          fastCell.selected.view.payload.slowSet
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast u.1)).val := hfastArmCanonical
      _ = (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
          (livePayload rate rewards C_star C_h q t s hs control0 x).anchor
          (liveNumericalWeights rate rewards C_star C_h q t s hs control0 x)
          (livePayload rate rewards C_star C_h q t s hs control0 x).anchor_pos
          hcanonicalPos hcanonicalLower hcanonicalUpper
          (livePayload rate rewards C_star C_h q t s hs control0 x).slowSet
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast u.1)).val :=
        hcanonicalSame
  have hpointwisePhysical :
      liveReservedFastOption rate rewards C_star C_h q t s hs control0 (x, u) =
        some (reservedFastArm record cell).val := by
    calc
      _ = some (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property
          rate.sourceCap (livePayload rate rewards C_star C_h q t s hs control0 x).anchor
          (liveNumericalWeights rate rewards C_star C_h q t s hs control0 x)
          (livePayload rate rewards C_star C_h q t s hs control0 x).anchor_pos
          hcanonicalPos hcanonicalLower hcanonicalUpper
          (livePayload rate rewards C_star C_h q t s hs control0 x).slowSet
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast u.1)).val :=
        hcanonicalFast u
      _ = some (reservedFastArm record cell).val := congrArg some hfastArmEq.symm
  have hentryPhysicalFast :
      liveReservedFastOption rate rewards C_star C_h q t s hs control0 (x, u) =
        some entry.fastArm := by
    calc
      _ = some (reservedFastArm record cell).val := hpointwisePhysical
      _ = some entry.fastArm := congrArg some hentryReserved.symm
  have hmarkerFastCell : fastCell.input.recordedArm =
      liveMarker rate rewards C_star C_h q t s hs control0 (x, u) := by
    exact (congrArg RecordedQueueRun.RoundInput.recordedArm hfastCellInput).trans hmarker
  have hentryMarkerFastCell : entry.numerical.2.1 = fastCell.input.recordedArm :=
    hentryMarker.trans
      (congrArg RecordedQueueRun.RoundInput.recordedArm hfastCellInput.symm)
  have hactualReserved :=
    ReferenceFirstLiveCanonicalProposalJointLaw.originalSource_reservedFast
      rate rewards C_star C_h q t s hs control0 tagged
  refine ⟨hbefore, ?_, hentryReserved, hentryPhysicalFast, hactualReserved⟩
  exact hentryMarkerFastCell.trans hmarkerFastCell

end Bandits.Support.ReferenceFirstLiveChronologicalPairIdentity

end
