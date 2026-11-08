/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveChronologicalPrefixMeasurability
public import Bandits.Support.ReferenceFirstLiveChronologicalPrefixCausality
public import Bandits.Support.ReferenceFirstLiveActualCutoffRefreshCoordinate

import Mathlib.MeasureTheory.Integral.Prod

/-!
# Actual first-live auxiliary refresh tests

The source stratum below is cut out of the existing whole physical first-live
window and its canonical numerical cells. Its witness records the actual
calendar cell, the queue state computed before that update, and the physical
proposal bit. No sampled or supplied path is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw

open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLiveChronologicalPrefixCausality
open ReferenceFirstLiveChronologicalPrefixMeasurability

variable {p : Parameters}

local instance actualRefreshSlowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤

local instance actualRefreshSlowSetDiscreteMeasurableSpace :
    DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩

/-- A source witness for an actual clear-PRE proposal at the fixed calendar
date `t`. The state is the canonical queue run on the actual strict prefix of
the original numerical cell stream. -/
structure ActualRefreshSourceCell (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (t : Fin p.T) where
  index : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
    rate rewards C_star C_h source).length
  actual_time : ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
    rate rewards C_star C_h source)[index.val]).input.time = t
  clear_pre : (RecordedQueueRun.run
    (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h source).take index.val)).overflow = false
  proposal : FollowerCutoffScan.completeRowProposalBit p rate.eta.val
    ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source)[index.val]).input.row
    ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source)[index.val]).input.time = true

/-- The intrinsic source event of an actual active proposal whose computed
pre-update overflow bit is clear. In particular it contains no auxiliary
array, matching-cell premise, or future cutoff condition. -/
def actualRefreshSourceStratum (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) : Set (SourceInput p) :=
  {source | Nonempty (ActualRefreshSourceCell rate rewards C_star C_h source t)}

/-- The cell-field test used to recognize the source stratum in the canonical
logical path. It ignores the next slow set and therefore reads no auxiliary
coordinate. -/
def actualRefreshCellFieldSet (rate : RateInput p) (t : Fin p.T) :
    Set (LogicalCell p rate) :=
  {entry | entry.time = t ∧ entry.before.overflow = false ∧ entry.proposal = true}

/-- The corresponding sum-tagged observation set. The left tag denotes that
the actual path has no cell at that index. -/
def actualRefreshPathOutputSet (rate : RateInput p) (t : Fin p.T) :
    Set (Unit ⊕ LogicalCell p rate) :=
  Sum.inr '' actualRefreshCellFieldSet rate t

/-- A fixed scalar used only to take a measurable section of the product
space. The source-stratum equivalence below proves that this section does not
alter the mathematical event. -/
def scalarZero : ContinuousControlSlice.Scalar := ⟨0, by norm_num⟩

/-- The constant section used in the source-only Borelness proof. -/
def auxiliarySection : AuxiliaryArray p := fun _ => scalarZero

/-- The actual path event at a fixed date, evaluated on this measurable
section. It will be proved equal to the intrinsic source event above. -/
def actualRefreshPathSourceStratum (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) : Set (SourceInput p) :=
  {source | ∃ k : Fin p.T,
    ReferenceActiveHorizonMeasurability.listObservationAt
      (firstLiveChronologicalPrefix rate rewards C_star C_h
        (source, auxiliarySection)) k.val ∈ actualRefreshPathOutputSet rate t}

/-- Borelness of the fixed-date actual clear-PRE proposal field test. -/
theorem measurableSet_actualRefreshCellFieldSet (rate : RateInput p)
    (t : Fin p.T) : MeasurableSet (actualRefreshCellFieldSet rate t) := by
  have htime := measurable_logicalCell_time (p := p) (rate := rate)
  have hoverflow : Measurable (fun entry : LogicalCell p rate => entry.before.overflow) := by
    exact (measurable_of_countable
      (fun state : RecordedQueueRun.RunState p.K => state.overflow)).comp
        (measurable_logicalCell_before (p := p) (rate := rate))
  have hproposal := measurable_logicalCell_proposal (p := p) (rate := rate)
  have htimeSet : MeasurableSet {entry : LogicalCell p rate | entry.time = t} :=
    (measurableSet_singleton t).preimage htime
  have hoverflowSet : MeasurableSet
      {entry : LogicalCell p rate | entry.before.overflow = false} :=
    (measurableSet_singleton false).preimage hoverflow
  have hproposalSet : MeasurableSet
      {entry : LogicalCell p rate | entry.proposal = true} :=
    (measurableSet_singleton true).preimage hproposal
  have hset : actualRefreshCellFieldSet rate t =
      {entry : LogicalCell p rate | entry.time = t} ∩
        ({entry | entry.before.overflow = false} ∩ {entry | entry.proposal = true}) := by
    ext entry
    rfl
  rw [hset]
  exact htimeSet.inter (hoverflowSet.inter hproposalSet)

/-- Borelness of the tagged output test, retaining the genuine empty-path
tag. -/
theorem measurableSet_actualRefreshPathOutputSet (rate : RateInput p)
    (t : Fin p.T) :
    MeasurableSet (actualRefreshPathOutputSet rate t) :=
  MeasurableSet.inr_image (measurableSet_actualRefreshCellFieldSet rate t)

/-- The actual numerical cell associated to a source-stratum witness. -/
def ActualRefreshSourceCell.numericalCell {rate : RateInput p}
    {rewards : RewardTable p} {C_star C_h : ℝ} {source : SourceInput p}
    {t : Fin p.T} (w : ActualRefreshSourceCell rate rewards C_star C_h source t) :=
  ReferenceFirstLiveChronologicalPrefixFoundation.wholeLiveCell rate rewards
    C_star C_h source
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source)[w.index.val]
    (List.getElem_mem w.index.isLt)

/-- The source-computed actual before-refresh state of the selected date. -/
def ActualRefreshSourceCell.before {rate : RateInput p}
    {rewards : RewardTable p} {C_star C_h : ℝ} {source : SourceInput p}
    {t : Fin p.T} (w : ActualRefreshSourceCell rate rewards C_star C_h source t) :=
  RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h source).take w.index.val)

/-- A fixed calendar date occurs in at most one record of the same original
whole first-live window. -/
theorem actualRefreshSourceCell_index_unique (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (source : SourceInput p)
    (t : Fin p.T) (left right : ActualRefreshSourceCell rate rewards C_star C_h source t) :
    left.index = right.index := by
  apply Fin.ext
  have hleft := ReferenceFirstLiveChronologicalPrefixFoundation.wholeLiveCell_geometry
    rate rewards C_star C_h source left.index
  have hright := ReferenceFirstLiveChronologicalPrefixFoundation.wholeLiveCell_geometry
    rate rewards C_star C_h source right.index
  dsimp only at hleft hright
  rcases hleft with ⟨_, _, hleftTime, _, _⟩
  rcases hright with ⟨_, _, hrightTime, _, _⟩
  have hlt := congrArg Fin.val left.actual_time
  have hrt := congrArg Fin.val right.actual_time
  omega

/-- The source stratum's entries and their time are chosen internally. -/
noncomputable def actualRefreshSourceCellOfMem (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T)
    (source : {z : SourceInput p // z ∈
      actualRefreshSourceStratum rate rewards C_star C_h t}) :
    ActualRefreshSourceCell rate rewards C_star C_h source.1 t :=
  Classical.choice source.2

/-- Every selected numerical input is the one stored in the original whole
first-live cell at the same index. -/
theorem actualRefreshSourceCell_input_eq (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (source : SourceInput p)
    (t : Fin p.T) (w : ActualRefreshSourceCell rate rewards C_star C_h source t) :
    w.numericalCell.input =
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
        rate rewards C_star C_h source)[w.index.val]'(by
          rw [ReferenceFirstLiveChronologicalPrefixFoundation.wholeFirstLiveCells_length]
          exact w.index.isLt) :=
  ReferenceFirstLiveChronologicalPrefixFoundation.wholeLiveCell_input_eq
    rate rewards C_star C_h source w.index

/-- No source witness is fabricated when the actual first-live window is
empty. This covers absent launch, terminal launch, and a cutoff before any
live calendar update. -/
theorem actualRefreshSourceStratum_empty_of_window_eq_nil (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T)
    (source : SourceInput p)
    (hwindow : ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source = []) :
    source ∉ actualRefreshSourceStratum rate rewards C_star C_h t := by
  rintro ⟨w⟩
  have : w.index.val < 0 := by simpa [hwindow] using w.index.isLt
  omega

/-- The source-selected cell is literally the cell stored at its actual date
in the original canonical prefix. The index witness comes from the source
stratum; the auxiliary array is arbitrary. -/
theorem ActualRefreshSourceCell.actualEntry_eq (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (source : SourceInput p)
    (t : Fin p.T) (w : ActualRefreshSourceCell rate rewards C_star C_h source t)
    (aux : AuxiliaryArray p) :
    (firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux))[w.index.val]'(by
      rw [firstLiveChronologicalPrefix_length]
      exact w.index.isLt) =
      appendLogicalCell
        (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h source)[w.index.val]
        w.numericalCell w.before aux := by
  exact firstLiveChronologicalPrefix_get rate rewards C_star C_h source aux w.index

/-- On the actual clear-PRE proposal stratum, the canonical cell's proposal
and next slow set are the literal physical proposal and residual draw at
`auxiliary (t,1)`. No assumption is made about the post-update overflow bit. -/
theorem ActualRefreshSourceCell.actual_refresh (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (source : SourceInput p)
    (t : Fin p.T) (w : ActualRefreshSourceCell rate rewards C_star C_h source t)
    (aux : AuxiliaryArray p) :
    let entry :=
      (firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux))[w.index.val]'(by
        rw [firstLiveChronologicalPrefix_length]
        exact w.index.isLt)
    entry.proposal = true ∧
      entry.nextSlowSet = residualDraw rate w.before w.numericalCell.input
        w.numericalCell.selected.view.payload.anchor
        w.numericalCell.selected.view.payload.anchor_pos (aux (t, 1)) := by
  dsimp only
  rw [w.actualEntry_eq rate rewards C_star C_h source t aux]
  have h := appendLogicalCell_proposal_refresh
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source)[w.index.val]
    w.numericalCell w.before aux w.clear_pre w.proposal
  refine ⟨h.1, ?_⟩
  simpa only [w.actual_time] using h.2.1

/-- The intrinsic source stratum is exactly the actual-cell event in the SAME
canonical prefix. This identifies its unique whole-window cell and computed
pre-state; the auxiliary section is only a measurability argument. -/
theorem actualRefreshSourceStratum_eq_path (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T) :
    actualRefreshSourceStratum rate rewards C_star C_h t =
      actualRefreshPathSourceStratum rate rewards C_star C_h t := by
  ext source
  constructor
  · rintro ⟨w⟩
    have hgeometry := ReferenceFirstLiveChronologicalPrefixFoundation.wholeLiveCell_geometry
      rate rewards C_star C_h source w.index
    dsimp only at hgeometry
    rcases hgeometry with ⟨_, _, hcalendar, _, _⟩
    have htime := congrArg Fin.val w.actual_time
    have hindex : w.index.val < p.T := by
      have hrecord := ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source)[w.index.val]).input.time.isLt
      omega
    let k : Fin p.T := ⟨w.index.val, hindex⟩
    have hpathBound : k.val <
        (firstLiveChronologicalPrefix rate rewards C_star C_h
          (source, auxiliarySection)).length := by
      rw [firstLiveChronologicalPrefix_length,
        ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength]
      exact w.index.isLt
    let entry := (firstLiveChronologicalPrefix rate rewards C_star C_h
      (source, auxiliarySection))[k.val]'hpathBound
    have hentry := w.actualEntry_eq rate rewards C_star C_h source t auxiliarySection
    have hfields : entry ∈ actualRefreshCellFieldSet rate t := by
      change entry.time = t ∧ entry.before.overflow = false ∧ entry.proposal = true
      dsimp only [entry, k]
      rw [hentry]
      constructor
      · simpa only [appendLogicalCell] using w.actual_time
      constructor
      · simpa only [appendLogicalCell, ActualRefreshSourceCell.before] using w.clear_pre
      · simpa only [appendLogicalCell, ActualRefreshSourceCell.before, w.clear_pre,
          Bool.not_false, Bool.true_and] using w.proposal
    refine ⟨k, ?_⟩
    have hobs : ReferenceActiveHorizonMeasurability.listObservationAt
        (firstLiveChronologicalPrefix rate rewards C_star C_h
          (source, auxiliarySection)) k.val = Sum.inr entry := by
      simp [entry, ReferenceActiveHorizonMeasurability.listObservationAt,
        List.getElem?_eq_getElem hpathBound]
    rw [hobs]
    exact Set.mem_image_of_mem Sum.inr hfields
  · intro hpath
    rcases hpath with ⟨k, hmem⟩
    rcases hmem with ⟨entry, hfields, hobs⟩
    have hgetOption :
        (firstLiveChronologicalPrefix rate rewards C_star C_h
          (source, auxiliarySection))[k.val]? = some entry := by
      unfold ReferenceActiveHorizonMeasurability.listObservationAt at hobs
      cases hopt : (firstLiveChronologicalPrefix rate rewards C_star C_h
          (source, auxiliarySection))[k.val]? with
      | none => simp [hopt] at hobs
      | some value =>
          simp only [hopt] at hobs
          have hvalue : entry = value := Sum.inr.inj hobs
          subst value
          rfl
    have hpathBound : k.val <
        (firstLiveChronologicalPrefix rate rewards C_star C_h
          (source, auxiliarySection)).length :=
      (List.getElem?_eq_some_iff.mp hgetOption).1
    have hwindowBound : k.val <
        (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h source).length := by
      rw [firstLiveChronologicalPrefix_length,
        ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] at hpathBound
      exact hpathBound
    let index : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source).length := ⟨k.val, hwindowBound⟩
    have hitem : (firstLiveChronologicalPrefix rate rewards C_star C_h
        (source, auxiliarySection))[k.val]'hpathBound = entry := by
      rw [List.getElem?_eq_getElem hpathBound] at hgetOption
      exact Option.some.inj hgetOption
    have hget := firstLiveChronologicalPrefix_get rate rewards C_star C_h
      source auxiliarySection index
    have hcurrent : entry = appendLogicalCell
        (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h source)[k.val]
        (ReferenceFirstLiveChronologicalPrefixFoundation.wholeLiveCell rate rewards
          C_star C_h source _ (List.getElem_mem index.isLt))
        (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
            rate rewards C_star C_h source).take k.val)) auxiliarySection := by
      exact hitem.symm.trans hget
    have hstate : entry.before = RecordedQueueRun.run
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
          rate rewards C_star C_h source).take k.val) := by
      simpa only [appendLogicalCell] using
        congrArg LogicalCell.before hcurrent
    have hcalendar :
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h source)[k.val]).input.time = t := by
      have htime := ReferenceFirstLiveChronologicalPrefixCausality.firstLiveChronologicalPrefix_cellTime
        rate rewards C_star C_h source auxiliarySection index
      rw [hitem] at htime
      exact htime.symm.trans hfields.1
    have hclear : (RecordedQueueRun.run
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
          rate rewards C_star C_h source).take k.val)).overflow = false := by
      rw [← hstate]
      exact hfields.2.1
    have hproposalEq := congrArg LogicalCell.proposal hcurrent
    simp only [appendLogicalCell, hclear, Bool.not_false, Bool.true_and] at hproposalEq
    have hbit : FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h source)[k.val]).input.row
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h source)[k.val]).input.time = true :=
      hproposalEq.symm.trans hfields.2.2
    exact ⟨⟨index, hcalendar, hclear, hbit⟩⟩

/-- Borelness of the source-only actual refresh stratum, obtained from the
full canonical path measurability and the exact source-stratum identity. -/
theorem measurableSet_actualRefreshSourceStratum (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T) :
    MeasurableSet (actualRefreshSourceStratum rate rewards C_star C_h t) := by
  rw [actualRefreshSourceStratum_eq_path]
  unfold actualRefreshPathSourceStratum
  rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro k
  let sourceEmbedding : SourceInput p → SourceInput p × AuxiliaryArray p :=
    fun source => (source, auxiliarySection)
  have hsection : Measurable sourceEmbedding := measurable_id.prodMk measurable_const
  have hpath := (measurable_firstLiveChronologicalPrefix rate rewards C_star C_h).comp hsection
  have hcoordinates : Measurable (fun source =>
      ReferenceActiveHorizonMeasurability.listObservationCoordinates
        (firstLiveChronologicalPrefix rate rewards C_star C_h
          (sourceEmbedding source))) :=
    (ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
      (α := LogicalCell p rate)).comp hpath
  have hcoordinate : Measurable (fun source =>
      ReferenceActiveHorizonMeasurability.listObservationAt
        (firstLiveChronologicalPrefix rate rewards C_star C_h
          (sourceEmbedding source)) k.val) := by
    change Measurable (fun source =>
      (ReferenceActiveHorizonMeasurability.listObservationCoordinates
        (firstLiveChronologicalPrefix rate rewards C_star C_h
          (sourceEmbedding source))).2 k.val)
    have hsnd : Measurable
        (Prod.snd : ℕ × (ℕ → Unit ⊕ LogicalCell p rate) →
          (ℕ → Unit ⊕ LogicalCell p rate)) := measurable_snd
    have heval : Measurable
        (fun f : ℕ → Unit ⊕ LogicalCell p rate => f k.val) := measurable_pi_apply k.val
    exact heval.comp (hsnd.comp hcoordinates)
  exact (measurableSet_actualRefreshPathOutputSet rate t).preimage hcoordinate

/-- The auxiliary coordinates other than the one actual label-1 coordinate at
`t`. -/
def actualRefreshCoordinatePredicate (t : Fin p.T)
    (q : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p) : Prop :=
  q = (t, 1)

abbrev ActualRefreshCoordinate (t : Fin p.T) :=
  {q : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p //
    actualRefreshCoordinatePredicate t q}

/-- The complementary auxiliary-coordinate index type. -/
abbrev ErasedAuxiliaryArray (t : Fin p.T) :=
  {q : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p //
    ¬ actualRefreshCoordinatePredicate t q} →
    ContinuousControlSlice.Scalar

/-- The original Pi law on the erased coordinates. -/
def erasedAuxiliaryLaw (t : Fin p.T) : Measure (ErasedAuxiliaryArray (p := p) t) :=
  Measure.pi (fun _ : {q : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p //
    ¬ actualRefreshCoordinatePredicate t q} => ContinuousControlSlice.scalarLaw)

/-- Insert the one actual scalar refresh coordinate into the original
auxiliary array while retaining every erased coordinate literally. -/
def insertActualRefreshCoordinate (t : Fin p.T)
    (erased : ErasedAuxiliaryArray (p := p) t)
    (value : ContinuousControlSlice.Scalar) : AuxiliaryArray p :=
  fun q => if h : q = (t, 1) then value else erased ⟨q, h⟩

/-- A complete test observation: the original physical source, the entire
auxiliary array with only `(t,1)` erased, the exact canonical encoding of the
complete actual calendar past, and the current cell's full pre-refresh fields. -/
abbrev ActualRefreshTestObservation (rate : RateInput p) (t : Fin p.T) :=
  SourceInput p × (ErasedAuxiliaryArray (p := p) t ×
    ((ℕ × (ℕ → Unit ⊕ LogicalCell p rate)) × BeforeRefreshReadout p rate))

/-- The inherited product Borel structure on the complete observation. -/
abbrev actualRefreshObservationMeasurableSpace (rate : RateInput p) (t : Fin p.T) :
    MeasurableSpace (ActualRefreshTestObservation rate t) :=
  (inferInstance : MeasurableSpace (SourceInput p)).prod
    ((inferInstance : MeasurableSpace (ErasedAuxiliaryArray (p := p) t)).prod
      ((inferInstance : MeasurableSpace (ℕ × (ℕ → Unit ⊕ LogicalCell p rate))).prod
        (inferInstance : MeasurableSpace (BeforeRefreshReadout p rate))))

/-- Construct the test observation from the same actual source witness. The
zero section only fills the erased coordinate; the invariance theorem below
shows that both observed history fields are unchanged for every fill value. -/
def ActualRefreshSourceCell.testObservation (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (source : SourceInput p)
    (t : Fin p.T) (w : ActualRefreshSourceCell rate rewards C_star C_h source t)
    (erased : ErasedAuxiliaryArray (p := p) t) :
    ActualRefreshTestObservation rate t :=
  let aux := insertActualRefreshCoordinate t erased scalarZero
  (source, (erased,
    (ReferenceActiveHorizonMeasurability.listObservationCoordinates
      (calendarPast rate rewards C_star C_h (source, aux) t.val),
      ((firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux))[
        w.index.val]'(by
          rw [firstLiveChronologicalPrefix_length,
            ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength]
          exact w.index.isLt)).beforeRefreshFields)))

/-- The current canonical cell's actual next slow set, read from the original
first-live prefix. -/
def ActualRefreshSourceCell.currentNextSlowSet (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (source : SourceInput p)
    (t : Fin p.T) (w : ActualRefreshSourceCell rate rewards C_star C_h source t)
    (aux : AuxiliaryArray p) : SlowSet p :=
  ((firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux))[
    w.index.val]'(by
      rw [firstLiveChronologicalPrefix_length,
        ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength]
      exact w.index.isLt)).nextSlowSet

/-- Changing only `(t,1)` leaves the complete actual calendar past and every
current before-refresh field unchanged on the source stratum. -/
theorem ActualRefreshSourceCell.testObservation_insert_invariant (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (source : SourceInput p)
    (t : Fin p.T) (w : ActualRefreshSourceCell rate rewards C_star C_h source t)
    (erased : ErasedAuxiliaryArray (p := p) t)
    (value : ContinuousControlSlice.Scalar) :
    w.testObservation rate rewards C_star C_h source t erased =
      (source, (erased,
        (ReferenceActiveHorizonMeasurability.listObservationCoordinates
          (calendarPast rate rewards C_star C_h
            (source, insertActualRefreshCoordinate t erased value) t.val),
          ((firstLiveChronologicalPrefix rate rewards C_star C_h
            (source, insertActualRefreshCoordinate t erased value))[
              w.index.val]'(by
                rw [firstLiveChronologicalPrefix_length,
                  ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength]
                exact w.index.isLt)).beforeRefreshFields))) := by
  have hused : ∀ u : Fin p.T, u.val < t.val →
      insertActualRefreshCoordinate t erased scalarZero (u, 1) =
        insertActualRefreshCoordinate t erased value (u, 1) := by
    intro u hu
    have hne : u ≠ t := by
      intro heq
      subst u
      omega
    simp [insertActualRefreshCoordinate, hne]
  have hpast := calendarPast_auxiliary_ext rate rewards C_star C_h source
    (insertActualRefreshCoordinate t erased scalarZero)
    (insertActualRefreshCoordinate t erased value) t.val hused
  have hbound : w.index.val < (firstLiveChronologicalPrefix rate rewards C_star C_h
      (source, insertActualRefreshCoordinate t erased scalarZero)).length := by
    rw [firstLiveChronologicalPrefix_length,
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength]
    exact w.index.isLt
  have hfields := firstLiveChronologicalPrefix_beforeRefresh_auxiliary_ext
    rate rewards C_star C_h source
    (insertActualRefreshCoordinate t erased scalarZero)
    (insertActualRefreshCoordinate t erased value)
  have hboundRight : w.index.val <
      (firstLiveChronologicalPrefix rate rewards C_star C_h
        (source, insertActualRefreshCoordinate t erased value)).length := by
    rw [firstLiveChronologicalPrefix_length,
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength]
    exact w.index.isLt
  have hcurrent :
      ((firstLiveChronologicalPrefix rate rewards C_star C_h
        (source, insertActualRefreshCoordinate t erased scalarZero))[
          w.index.val]'hbound).beforeRefreshFields =
      ((firstLiveChronologicalPrefix rate rewards C_star C_h
        (source, insertActualRefreshCoordinate t erased value))[
          w.index.val]'hboundRight).beforeRefreshFields := by
    have hget := congrArg
      (fun xs : List (BeforeRefreshReadout p rate) => xs[w.index.val]?) hfields
    have hsome :
        some ((firstLiveChronologicalPrefix rate rewards C_star C_h
            (source, insertActualRefreshCoordinate t erased scalarZero))[
              w.index.val]'hbound).beforeRefreshFields =
          some ((firstLiveChronologicalPrefix rate rewards C_star C_h
            (source, insertActualRefreshCoordinate t erased value))[
              w.index.val]'hboundRight).beforeRefreshFields := by
      simpa only [List.getElem?_map, List.getElem?_eq_getElem hbound,
        List.getElem?_eq_getElem hboundRight, Option.map_some] using hget
    exact Option.some.inj hsome
  simp only [ActualRefreshSourceCell.testObservation, hpast, hcurrent,
    ReferenceActiveHorizonMeasurability.listObservationCoordinates]

/-- Split the existing full auxiliary Pi law at exactly `(t,1)`. The first
factor is the singleton coordinate Pi and the second retains every other
coordinate. -/
def actualRefreshAuxiliarySplit (t : Fin p.T) :
    AuxiliaryArray p ≃ᵐ
      (ActualRefreshCoordinate (p := p) t → ContinuousControlSlice.Scalar) ×
        ErasedAuxiliaryArray (p := p) t :=
  MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p =>
      ContinuousControlSlice.Scalar) (actualRefreshCoordinatePredicate t)

/-- The split preserves the literal original independent auxiliary law,
including when the complement coordinate type is empty. -/
theorem measurePreserving_actualRefreshAuxiliarySplit (t : Fin p.T) :
    MeasurePreserving (actualRefreshAuxiliarySplit (p := p) t)
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)
      ((Measure.pi (fun _ : ActualRefreshCoordinate (p := p) t =>
          ContinuousControlSlice.scalarLaw)).prod
        (erasedAuxiliaryLaw (p := p) t)) := by
  simpa only [actualRefreshAuxiliarySplit, erasedAuxiliaryLaw,
    ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw] using
      (measurePreserving_piEquivPiSubtypeProd
        (fun _ : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p =>
          ContinuousControlSlice.scalarLaw) (actualRefreshCoordinatePredicate t))

/-- The literal residual sampler at the actual cell has its original
unnormalized scalar fibre mass. The assertion includes zero atoms. -/
theorem ActualRefreshSourceCell.scalar_fibre_measure (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (source : SourceInput p)
    (t : Fin p.T) (w : ActualRefreshSourceCell rate rewards C_star C_h source t)
    (U : SlowSet p) :
    ContinuousControlSlice.scalarLaw
      (residualDraw rate w.before w.numericalCell.input
        w.numericalCell.selected.view.payload.anchor
        w.numericalCell.selected.view.payload.anchor_pos ⁻¹' {U}) =
      ENNReal.ofReal (RecordedSlowRefresh.residualMass p
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) w.before
        w.numericalCell.input w.numericalCell.selected.view.payload.anchor
        w.numericalCell.selected.view.payload.anchor_pos U) := by
  let masses : Fin (Fintype.card (SlowSet p)) → ℝ := fun k =>
    RecordedSlowRefresh.residualMass p
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) w.before
      w.numericalCell.input w.numericalCell.selected.view.payload.anchor
      w.numericalCell.selected.view.payload.anchor_pos (slowSetEnumeration p k)
  have hsum : ∑ k, masses k = 1 := by
    dsimp [masses]
    simpa only [Equiv.sum_comp] using RecordedSlowRefresh.residualMass_sum_eq_one p
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) w.before
      w.numericalCell.input w.numericalCell.selected.view.payload.anchor
      w.numericalCell.selected.view.payload.anchor_pos
  have hset : residualDraw rate w.before w.numericalCell.input
      w.numericalCell.selected.view.payload.anchor
      w.numericalCell.selected.view.payload.anchor_pos ⁻¹' {U} =
      ContinuousCategorical.sample (slowSet_card_pos p) masses hsum ⁻¹'
        {(slowSetEnumeration p).symm U} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, residualDraw, masses]
    exact ((slowSetEnumeration p).eq_symm_apply).symm
  rw [hset]
  change ContinuousCategorical.uniform
    (ContinuousCategorical.sample (slowSet_card_pos p) masses hsum ⁻¹'
      {(slowSetEnumeration p).symm U}) = _
  simpa only [Equiv.apply_symm_apply] using
    ContinuousCategorical.uniform_sample_singleton (slowSet_card_pos p)
    (fun k => RecordedSlowRefresh.residualMass_nonneg p
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) w.before
      w.numericalCell.input w.numericalCell.selected.view.payload.anchor
      w.numericalCell.selected.view.payload.anchor_pos (slowSetEnumeration p k)) hsum
    ((slowSetEnumeration p).symm U)

/-- On the same actual source cell, every bounded Borel test of the complete
erased-coordinate observation has the exact unnormalized refresh indicator
integral on the remaining scalar fibre. The next-set event is read from the
actual canonical path cell, and its scalar mass is the original residual mass,
including zero-mass outcomes. -/
theorem ActualRefreshSourceCell.bounded_test_scalar_fibre_identity
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p) (t : Fin p.T)
    (w : ActualRefreshSourceCell rate rewards C_star C_h source t)
    (erased : ErasedAuxiliaryArray (p := p) t)
    (F : ActualRefreshTestObservation rate t → ℝ) (B : ℝ)
    (hbound : ∀ observation, |F observation| ≤ B)
    (U : SlowSet p) :
    Integrable
        (fun x : ContinuousControlSlice.Scalar =>
          F (w.testObservation rate rewards C_star C_h source t erased) *
            if w.currentNextSlowSet rate rewards C_star C_h source t
                (insertActualRefreshCoordinate t erased x) = U then (1 : ℝ) else 0)
        ContinuousControlSlice.scalarLaw ∧
      (∫ x : ContinuousControlSlice.Scalar,
        F (w.testObservation rate rewards C_star C_h source t erased) *
          if w.currentNextSlowSet rate rewards C_star C_h source t
              (insertActualRefreshCoordinate t erased x) = U then (1 : ℝ) else 0
          ∂ContinuousControlSlice.scalarLaw) =
        F (w.testObservation rate rewards C_star C_h source t erased) *
          RecordedSlowRefresh.residualMass p
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) w.before
            w.numericalCell.input w.numericalCell.selected.view.payload.anchor
            w.numericalCell.selected.view.payload.anchor_pos U := by
  let observation := w.testObservation rate rewards C_star C_h source t erased
  let event : Set ContinuousControlSlice.Scalar :=
    {x | w.currentNextSlowSet rate rewards C_star C_h source t
      (insertActualRefreshCoordinate t erased x) = U}
  let mass := RecordedSlowRefresh.residualMass p
    (ReferenceFirstLaunchNumericalCell.queueParameters rate) w.before
    w.numericalCell.input w.numericalCell.selected.view.payload.anchor
    w.numericalCell.selected.view.payload.anchor_pos U
  have hrefresh (x : ContinuousControlSlice.Scalar) :
      w.currentNextSlowSet rate rewards C_star C_h source t
          (insertActualRefreshCoordinate t erased x) =
        residualDraw rate w.before w.numericalCell.input
          w.numericalCell.selected.view.payload.anchor
          w.numericalCell.selected.view.payload.anchor_pos x := by
    have h := w.actual_refresh rate rewards C_star C_h source t
      (insertActualRefreshCoordinate t erased x)
    dsimp only at h
    simpa [ActualRefreshSourceCell.currentNextSlowSet,
      insertActualRefreshCoordinate] using h.2
  have hdraw : Measurable (fun x : ContinuousControlSlice.Scalar =>
      residualDraw rate w.before w.numericalCell.input
        w.numericalCell.selected.view.payload.anchor
        w.numericalCell.selected.view.payload.anchor_pos x) := by
    apply measurable_residualDraw_of_measurable_residualMass rate
      (fun _ : ContinuousControlSlice.Scalar => w.before)
      (fun _ => w.numericalCell.input)
      (fun _ => w.numericalCell.selected.view.payload.anchor)
      (fun _ i => w.numericalCell.selected.view.payload.anchor_pos i)
      (fun x => x) measurable_id
    intro V
    exact measurable_const
  have hcurrentMeas : Measurable (fun x : ContinuousControlSlice.Scalar =>
      w.currentNextSlowSet rate rewards C_star C_h source t
        (insertActualRefreshCoordinate t erased x)) := by
    convert hdraw using 1
    funext x
    exact hrefresh x
  have hevent : MeasurableSet event := by
    exact (measurableSet_singleton U).preimage hcurrentMeas
  have hset : event =
      (fun x : ContinuousControlSlice.Scalar =>
        residualDraw rate w.before w.numericalCell.input
          w.numericalCell.selected.view.payload.anchor
          w.numericalCell.selected.view.payload.anchor_pos x) ⁻¹' {U} := by
    ext x
    simp only [event, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
      hrefresh]
  have hmeasure : ContinuousControlSlice.scalarLaw event = ENNReal.ofReal mass := by
    rw [hset]
    exact w.scalar_fibre_measure rate rewards C_star C_h source t U
  have hmass_nonneg : 0 ≤ mass := by
    exact RecordedSlowRefresh.residualMass_nonneg p
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) w.before
      w.numericalCell.input w.numericalCell.selected.view.payload.anchor
      w.numericalCell.selected.view.payload.anchor_pos U
  have hboundObservation := hbound observation
  have hindicator :
      (fun x : ContinuousControlSlice.Scalar =>
        F observation * if x ∈ event then (1 : ℝ) else 0) =
        event.indicator (fun _ => F observation) := by
    funext x
    by_cases hx : x ∈ event <;> simp [hx]
  constructor
  · change Integrable (fun x : ContinuousControlSlice.Scalar =>
      F observation * if x ∈ event then (1 : ℝ) else 0)
      ContinuousControlSlice.scalarLaw
    rw [hindicator]
    exact (integrable_const (F observation)).indicator hevent
  · change (∫ x : ContinuousControlSlice.Scalar,
        F observation * if x ∈ event then (1 : ℝ) else 0
          ∂ContinuousControlSlice.scalarLaw) = F observation * mass
    rw [hindicator, integral_indicator_const (F observation) hevent]
    simp only [smul_eq_mul, measureReal_def, hmeasure,
      ENNReal.toReal_ofReal hmass_nonneg]
    ring

/-- The genuine source-only stratum, with its inherited Borel structure. -/
abbrev ActualRefreshSource (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :=
  {z : SourceInput p // z ∈ actualRefreshSourceStratum rate rewards C_star C_h t}

/-- The original finite, unnormalized source restriction on its true subtype. -/
def actualRefreshSourceLaw (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :
    Measure (ActualRefreshSource rate rewards C_star C_h t) :=
  (BootstrapPrivateRoundStreams.sourceInputLaw p).comap Subtype.val

instance actualRefreshSourceLaw_finite (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :
    IsFiniteMeasure (actualRefreshSourceLaw rate rewards C_star C_h t) := by
  unfold actualRefreshSourceLaw
  infer_instance

/-- Pushing the subtype restriction back to the original source gives exactly
its original event restriction, including when that event has zero measure. -/
theorem actualRefreshSourceLaw_map (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :
    (actualRefreshSourceLaw rate rewards C_star C_h t).map Subtype.val =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (actualRefreshSourceStratum rate rewards C_star C_h t) :=
  map_comap_subtype_coe
    (measurableSet_actualRefreshSourceStratum rate rewards C_star C_h t) _

private theorem measurable_actualIndex (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :
    Measurable (fun z : ActualRefreshSource rate rewards C_star C_h t =>
      (actualRefreshSourceCellOfMem rate rewards C_star C_h t z).index.val) := by
  have hstart := (ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
    rate rewards C_star C_h).comp
      (measurable_subtype_coe : Measurable
        (Subtype.val : ActualRefreshSource rate rewards C_star C_h t → SourceInput p))
  have hm := (measurable_of_countable (fun n : ℕ => t.val - n)).comp hstart
  convert hm using 1
  funext z
  let w := actualRefreshSourceCellOfMem rate rewards C_star C_h t z
  have hg := wholeLiveCell_geometry rate rewards C_star C_h z.val w.index
  have ht := congrArg Fin.val w.actual_time
  dsimp only at hg
  change w.index.val = t.val -
    ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h
  omega

private theorem measurable_variable_list_get {X α : Type*}
    [MeasurableSpace X] [MeasurableSpace α]
    (records : X → List α) (hr : Measurable records)
    (index : X → ℕ) (hi : Measurable index)
    (hb : ∀ x, index x < (records x).length) :
    Measurable (fun x => (records x)[index x]'(hb x)) := by
  have hc := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp hr
  have heval : Measurable (fun z : ℕ × (ℕ → Unit ⊕ α) => z.2 z.1) :=
    measurable_from_prod_countable_right fun n => measurable_pi_apply n
  have hm := heval.comp (hi.prodMk (measurable_snd.comp hc))
  have hinr : MeasurableEmbedding (@Sum.inr Unit α) :=
    ⟨Sum.inr_injective, measurable_inr, fun _ hs => hs.inr_image⟩
  apply hinr.measurable_comp_iff.mp
  simpa only [Function.comp_def,
    ReferenceActiveHorizonMeasurability.listObservationCoordinates,
    ReferenceActiveHorizonMeasurability.listObservationAt,
    List.getElem?_eq_getElem (hb _)] using hm

/-- Read the unique actual cell, with no cell defined outside the source event. -/
def actualRefreshEntry (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : ActualRefreshSource rate rewards C_star C_h t) (aux : AuxiliaryArray p) :
    LogicalCell p rate :=
  let w := actualRefreshSourceCellOfMem rate rewards C_star C_h t z
  (firstLiveChronologicalPrefix rate rewards C_star C_h (z.val, aux))[
    w.index.val]'(by
      rw [firstLiveChronologicalPrefix_length]
      exact w.index.isLt)

/-- Source-varying selection is Borel in the full accepted continuous cell
space. The selected position is computed from the actual launch offset. -/
theorem measurable_actualRefreshEntry (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :
    Measurable (fun x : ActualRefreshSource rate rewards C_star C_h t × AuxiliaryArray p =>
      actualRefreshEntry rate rewards C_star C_h t x.1 x.2) := by
  apply measurable_variable_list_get
    (fun x : ActualRefreshSource rate rewards C_star C_h t × AuxiliaryArray p =>
      firstLiveChronologicalPrefix rate rewards C_star C_h (x.1.val, x.2))
    ((measurable_firstLiveChronologicalPrefix rate rewards C_star C_h).comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd))
    (fun x => (actualRefreshSourceCellOfMem rate rewards C_star C_h t x.1).index.val)
    ((measurable_actualIndex rate rewards C_star C_h t).comp measurable_fst)

/-- Every pre-refresh field retains its inherited measurable structure. -/
theorem measurable_beforeRefreshFields (rate : RateInput p) :
    Measurable (LogicalCell.beforeRefreshFields (p := p) (rate := rate)) := by
  exact measurable_logicalCell_time.prodMk
    (measurable_logicalCell_physical.prodMk
      (measurable_logicalCell_numerical.prodMk
        (measurable_logicalCell_before.prodMk
          (measurable_logicalCell_after.prodMk
            (measurable_logicalCell_arrivals.prodMk
              (measurable_logicalCell_service.prodMk
                (measurable_logicalCell_slowSet.prodMk
                  (measurable_logicalCell_fastArm.prodMk measurable_logicalCell_proposal))))))))

/-- Insertion is jointly Borel and preserves every complementary coordinate. -/
theorem measurable_insertActualRefreshCoordinate (t : Fin p.T) :
    Measurable (fun x : ErasedAuxiliaryArray (p := p) t × ContinuousControlSlice.Scalar =>
      insertActualRefreshCoordinate t x.1 x.2) := by
  apply measurable_pi_iff.mpr
  intro q
  by_cases hq : q = (t, 1)
  · simpa only [insertActualRefreshCoordinate, hq, dite_true] using
      (measurable_snd : Measurable (Prod.snd :
        ErasedAuxiliaryArray (p := p) t × ContinuousControlSlice.Scalar → _))
  · simp only [insertActualRefreshCoordinate, hq, dite_false]
    exact (measurable_pi_apply
      (⟨q, hq⟩ : {q : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p //
        ¬ actualRefreshCoordinatePredicate t q})).comp measurable_fst

private theorem measurable_variable_list_take {X α : Type*}
    [MeasurableSpace X] [MeasurableSpace α]
    (records : X → List α) (hr : Measurable records)
    (index : X → ℕ) (hi : Measurable index) :
    Measurable (fun x => (records x).take (index x)) := by
  classical
  have hc := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp hr
  apply measurable_comap_iff.mpr
  change Measurable (fun x => (((records x).take (index x)).length,
    fun k => ReferenceActiveHorizonMeasurability.listObservationAt
      ((records x).take (index x)) k))
  simp only [List.length_take]
  have hmin : Measurable (fun x => min (index x) (records x).length) :=
    (measurable_of_countable (fun z : ℕ × ℕ => min z.1 z.2)).comp
      (hi.prodMk (measurable_fst.comp hc))
  apply hmin.prodMk
  apply measurable_pi_iff.mpr
  intro k
  have htag := (measurable_pi_apply k).comp (measurable_snd.comp hc)
  have hset : MeasurableSet {x | k < index x} :=
    (MeasurableSet.of_discrete : MeasurableSet {n : ℕ | k < n}).preimage hi
  have hm : Measurable (fun x => if k < index x then
      ReferenceActiveHorizonMeasurability.listObservationAt (records x) k
      else (Sum.inl () : Unit ⊕ α)) :=
    htag.ite hset measurable_const
  convert hm using 1
  funext x
  simp only [ReferenceActiveHorizonMeasurability.listObservationAt, List.getElem?_take]
  by_cases hx : k < index x
  · simp only [hx, ite_true]
  · simp only [hx, ite_false]

/-- The complete calendar past is Borel; the actual launch offset determines
its positional length, including absent and terminal launches. -/
theorem measurable_calendarPast (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :
    Measurable (fun x : SourceInput p × AuxiliaryArray p =>
      calendarPast rate rewards C_star C_h x t.val) := by
  have hs := (ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
    rate rewards C_star C_h).comp
      (measurable_fst : Measurable (Prod.fst : SourceInput p × AuxiliaryArray p → _))
  have hn := (measurable_of_countable (fun n : ℕ => t.val - n)).comp hs
  convert measurable_variable_list_take _
    (measurable_firstLiveChronologicalPrefix rate rewards C_star C_h) _ hn using 1
  funext x
  exact calendarPast_eq_take_elapsed rate rewards C_star C_h x.1 x.2 t.val

/-- The same complete observation, on the intrinsic source subtype. -/
def actualRefreshObservation (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (x : ActualRefreshSource rate rewards C_star C_h t × ErasedAuxiliaryArray (p := p) t) :
    ActualRefreshTestObservation rate t :=
  let aux := insertActualRefreshCoordinate t x.2 scalarZero
  (x.1.val, (x.2,
    (ReferenceActiveHorizonMeasurability.listObservationCoordinates
      (calendarPast rate rewards C_star C_h (x.1.val, aux) t.val),
      (actualRefreshEntry rate rewards C_star C_h t x.1 aux).beforeRefreshFields)))

private def actualRefreshFilledAux (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (x : ActualRefreshSource rate rewards C_star C_h t × ErasedAuxiliaryArray (p := p) t) :
    AuxiliaryArray p :=
  insertActualRefreshCoordinate t x.2 scalarZero

private theorem measurable_actualRefreshFilledAux (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T) :
    Measurable (actualRefreshFilledAux rate rewards C_star C_h t) :=
  (measurable_insertActualRefreshCoordinate t).comp
    (measurable_snd.prodMk measurable_const)

private theorem measurable_actualRefreshPastObservation (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T) :
    Measurable (fun x : ActualRefreshSource rate rewards C_star C_h t ×
        ErasedAuxiliaryArray (p := p) t =>
      ReferenceActiveHorizonMeasurability.listObservationCoordinates
        (calendarPast rate rewards C_star C_h
          (x.1.val, actualRefreshFilledAux rate rewards C_star C_h t x) t.val)) := by
  have hsource : Measurable (fun x : ActualRefreshSource rate rewards C_star C_h t ×
      ErasedAuxiliaryArray (p := p) t => x.1.val) :=
    measurable_subtype_coe.comp measurable_fst
  exact ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp
    ((measurable_calendarPast rate rewards C_star C_h t).comp
      (hsource.prodMk (measurable_actualRefreshFilledAux rate rewards C_star C_h t)))

private theorem measurable_actualRefreshFilledEntry (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T) :
    Measurable (fun x : ActualRefreshSource rate rewards C_star C_h t ×
        ErasedAuxiliaryArray (p := p) t =>
      actualRefreshEntry rate rewards C_star C_h t x.1
        (actualRefreshFilledAux rate rewards C_star C_h t x)) := by
  let X := ActualRefreshSource rate rewards C_star C_h t ×
    ErasedAuxiliaryArray (p := p) t
  have hsource : Measurable (fun x : X => x.1.val) :=
    measurable_subtype_coe.comp measurable_fst
  have hpath : Measurable (fun x : X => firstLiveChronologicalPrefix rate rewards C_star C_h
      (x.1.val, actualRefreshFilledAux rate rewards C_star C_h t x)) :=
    (measurable_firstLiveChronologicalPrefix rate rewards C_star C_h).comp
      (hsource.prodMk (measurable_actualRefreshFilledAux rate rewards C_star C_h t))
  exact measurable_variable_list_get _ hpath
    (fun x => (actualRefreshSourceCellOfMem rate rewards C_star C_h t x.1).index.val)
    ((measurable_actualIndex rate rewards C_star C_h t).comp measurable_fst) _

private theorem measurable_actualRefreshBeforeObservation (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T) :
    Measurable (fun x : ActualRefreshSource rate rewards C_star C_h t ×
        ErasedAuxiliaryArray (p := p) t =>
      (actualRefreshEntry rate rewards C_star C_h t x.1
        (actualRefreshFilledAux rate rewards C_star C_h t x)).beforeRefreshFields) :=
  (measurable_beforeRefreshFields rate).comp
    (measurable_actualRefreshFilledEntry rate rewards C_star C_h t)

/-- Joint Borelness of the entire required test observation on the intrinsic
source stratum and the erased auxiliary array. -/
theorem measurable_actualRefreshTestObservation (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T) :
    @Measurable _ _ inferInstance (actualRefreshObservationMeasurableSpace rate t)
      (actualRefreshObservation rate rewards C_star C_h t) := by
  have hsource : Measurable (fun x : ActualRefreshSource rate rewards C_star C_h t ×
      ErasedAuxiliaryArray (p := p) t => x.1.val) :=
    measurable_subtype_coe.comp measurable_fst
  apply hsource.prodMk
  apply measurable_snd.prodMk
  exact (measurable_actualRefreshPastObservation rate rewards C_star C_h t).prodMk
    (measurable_actualRefreshBeforeObservation rate rewards C_star C_h t)

/-- The original residual mass of the unique actual source cell. -/
def actualRefreshMass (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : ActualRefreshSource rate rewards C_star C_h t) (U : SlowSet p) : ℝ :=
  let w := actualRefreshSourceCellOfMem rate rewards C_star C_h t z
  RecordedSlowRefresh.residualMass p
    (ReferenceFirstLaunchNumericalCell.queueParameters rate) w.before
    w.numericalCell.input w.numericalCell.selected.view.payload.anchor
    w.numericalCell.selected.view.payload.anchor_pos U

private theorem measurable_from_some {X α : Type*}
    [MeasurableSpace X] [MeasurableSpace α] (f : X → α)
    (hf : Measurable (fun x => some (f x))) : Measurable f := by
  have hsum := (comap_measurable (Equiv.optionEquivSumPUnit α)).comp hf
  have hinl : MeasurableEmbedding (@Sum.inl α PUnit) :=
    ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩
  exact hinl.measurable_comp_iff.mp hsum

private theorem measurable_actualRefreshAnchor (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T) :
    Measurable (fun z : ActualRefreshSource rate rewards C_star C_h t =>
      (actualRefreshSourceCellOfMem rate rewards C_star C_h t z).numericalCell.selected.view.payload.anchor) := by
  let w := actualRefreshSourceCellOfMem rate rewards C_star C_h t
  have he := (measurable_actualRefreshEntry rate rewards C_star C_h t).comp
    (measurable_id.prodMk (measurable_const (a := auxiliarySection)))
  have hm := measurable_fst.comp (measurable_fst.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_logicalCell_physical.comp he))))
  have hsome : Measurable (fun z : ActualRefreshSource rate rewards C_star C_h t =>
      some (ReferenceLiveDispatchOutputMeasurability.encodeSelection
        (w z).numericalCell.selected)) := by
    convert hm using 1
    funext z
    change some _ = (actualRefreshEntry rate rewards C_star C_h t z
      auxiliarySection).physical.2.2.1.1
    unfold actualRefreshEntry
    rw [(w z).actualEntry_eq rate rewards C_star C_h z.val t auxiliarySection]
    change some _ = (ReferenceActiveHorizonMeasurability.roundRecordCode
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h z.val)[(w z).index.val])).2.2.1.1
    have hfront := (ReferenceActiveHorizonMeasurability.roundRecordCode_front
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h z.val)[(w z).index.val])).1
    rw [hfront]
    have hout := ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z.val)[(w z).index.val]).output_eq
    have hs := (w z).numericalCell.selection_actual
    rw [hout] at hs
    exact congrArg (fun s => s.map
      ReferenceLiveDispatchOutputMeasurability.encodeSelection) hs.symm
  have hview := measurable_fst.comp (measurable_from_some _ hsome)
  have hobs := (comap_measurable
    (ReferenceDownReceptionMeasurability.choiceTimeViewObservation (p := p) (rate := rate))).comp hview
  exact AssignmentPayloadDerivedMeasurability.measurable_inputAnchor.comp
    (measurable_fst.comp hobs)

/-- Borelness of the source-varying residual mass is derived from the actual
PRE/POST states and the same positive payload anchor. -/
theorem measurable_actualRefreshMass (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (U : SlowSet p) :
    Measurable (fun z => actualRefreshMass rate rewards C_star C_h t z U) := by
  let w := actualRefreshSourceCellOfMem rate rewards C_star C_h t
  have he := (measurable_actualRefreshEntry rate rewards C_star C_h t).comp
    (measurable_id.prodMk (measurable_const (a := auxiliarySection)))
  have hb : Measurable (fun z => (w z).before) := by
    convert measurable_logicalCell_before.comp he using 1
    funext z
    exact (congrArg LogicalCell.before
      ((w z).actualEntry_eq rate rewards C_star C_h z.val t auxiliarySection)).symm
  have ha : Measurable (fun z => RecordedQueueRun.step
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (w z).before (w z).numericalCell.input) := by
    convert measurable_logicalCell_after.comp he using 1
    funext z
    exact (congrArg LogicalCell.after
      ((w z).actualEntry_eq rate rewards C_star C_h z.val t auxiliarySection)).symm
  exact measurable_residualMass_of_actualStep rate _ _ _ hb ha (fun _ => rfl) _
    (measurable_actualRefreshAnchor rate rewards C_star C_h t) _ U

instance actualRefreshCoordinate_unique (t : Fin p.T) :
    Unique (ActualRefreshCoordinate (p := p) t) where
  default := ⟨(t, 1), rfl⟩
  uniq q := Subtype.ext q.property

/-- The full original auxiliary array split into its erased coordinates and
its single scalar refresh coordinate. -/
def actualRefreshScalarSplit (t : Fin p.T) : AuxiliaryArray p ≃ᵐ
    ErasedAuxiliaryArray (p := p) t × ContinuousControlSlice.Scalar :=
  (actualRefreshAuxiliarySplit t).trans
    (((MeasurableEquiv.piUnique
      (fun _ : ActualRefreshCoordinate (p := p) t => ContinuousControlSlice.Scalar)).prodCongr
        (MeasurableEquiv.refl _)).trans MeasurableEquiv.prodComm)

instance erasedAuxiliaryLaw_probability (t : Fin p.T) :
    IsProbabilityMeasure (erasedAuxiliaryLaw (p := p) t) := by
  unfold erasedAuxiliaryLaw
  infer_instance

/-- This scalar split preserves the original finite-Pi auxiliary law. -/
theorem measurePreserving_actualRefreshScalarSplit (t : Fin p.T) :
    MeasurePreserving (actualRefreshScalarSplit (p := p) t)
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)
      ((erasedAuxiliaryLaw (p := p) t).prod ContinuousControlSlice.scalarLaw) := by
  have hsingle := measurePreserving_piUnique
    (fun _ : ActualRefreshCoordinate (p := p) t => ContinuousControlSlice.scalarLaw)
  have hproduct := hsingle.prod (MeasurePreserving.id (erasedAuxiliaryLaw (p := p) t))
  exact (Measure.measurePreserving_swap : MeasurePreserving Prod.swap
    (ContinuousControlSlice.scalarLaw.prod (erasedAuxiliaryLaw (p := p) t))
    ((erasedAuxiliaryLaw (p := p) t).prod ContinuousControlSlice.scalarLaw)).comp
    (hproduct.comp (measurePreserving_actualRefreshAuxiliarySplit t))

/-- The inverse split literally inserts the scalar and preserves all other
original coordinates. -/
theorem actualRefreshScalarSplit_symm_apply (t : Fin p.T)
    (x : ErasedAuxiliaryArray (p := p) t × ContinuousControlSlice.Scalar) :
    (actualRefreshScalarSplit (p := p) t).symm x =
      insertActualRefreshCoordinate t x.1 x.2 := by
  apply (actualRefreshScalarSplit (p := p) t).injective
  rw [MeasurableEquiv.apply_symm_apply]
  apply Prod.ext
  · funext q
    change x.1 q = insertActualRefreshCoordinate t x.1 x.2 q.val
    have hq : q.val ≠ (t, 1) := q.property
    simp only [insertActualRefreshCoordinate, hq, dite_false]
  · change x.2 = insertActualRefreshCoordinate t x.1 x.2 (t, 1)
    simp only [insertActualRefreshCoordinate, dite_true]

/-- Erase exactly the scalar coordinate of the actual fixed calendar date. -/
def actualRefreshErasure (t : Fin p.T) (aux : AuxiliaryArray p) :
    ErasedAuxiliaryArray (p := p) t :=
  fun q => aux q.val

/-- The complete test observation as a function of the original full array. -/
def actualRefreshFullObservation (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (x : ActualRefreshSource rate rewards C_star C_h t × AuxiliaryArray p) :
    ActualRefreshTestObservation rate t :=
  actualRefreshObservation rate rewards C_star C_h t
    (x.1, actualRefreshErasure t x.2)

private theorem measurable_actualRefreshErasure (t : Fin p.T) :
    Measurable (actualRefreshErasure (p := p) t) :=
  measurable_pi_iff.mpr fun q => measurable_pi_apply q.val

/-- Joint Borelness retains the whole source and every unerased coordinate. -/
theorem measurable_actualRefreshFullObservation (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T) :
    @Measurable _ _ inferInstance (actualRefreshObservationMeasurableSpace rate t)
      (actualRefreshFullObservation rate rewards C_star C_h t) :=
  (measurable_actualRefreshTestObservation rate rewards C_star C_h t).comp
    (measurable_fst.prodMk
      ((measurable_actualRefreshErasure t).comp measurable_snd))

/-- The tested event reads the next slow set of the actual current cell. -/
def actualRefreshIndicatorTest (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (F : ActualRefreshTestObservation rate t → ℝ) (U : SlowSet p)
    (x : ActualRefreshSource rate rewards C_star C_h t × AuxiliaryArray p) : ℝ :=
  F (actualRefreshFullObservation rate rewards C_star C_h t x) *
    if (actualRefreshEntry rate rewards C_star C_h t x.1 x.2).nextSlowSet = U
      then 1 else 0

/-- The tested mass uses the same actual PRE state, round input and anchor. -/
def actualRefreshMassTest (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (F : ActualRefreshTestObservation rate t → ℝ) (U : SlowSet p)
    (x : ActualRefreshSource rate rewards C_star C_h t × AuxiliaryArray p) : ℝ :=
  F (actualRefreshFullObservation rate rewards C_star C_h t x) *
    actualRefreshMass rate rewards C_star C_h t x.1 U

private theorem measurable_actualRefreshIndicatorTest (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T)
    (F : ActualRefreshTestObservation rate t → ℝ) (hF : @Measurable _ _ (actualRefreshObservationMeasurableSpace rate t) inferInstance F) (U : SlowSet p) :
    Measurable (actualRefreshIndicatorTest rate rewards C_star C_h t F U) := by
  have hnext := measurable_logicalCell_nextSlowSet.comp
    (measurable_actualRefreshEntry rate rewards C_star C_h t)
  exact (hF.comp (measurable_actualRefreshFullObservation rate rewards C_star C_h t)).mul
    (measurable_const.ite ((measurableSet_singleton U).preimage hnext) measurable_const)

private theorem measurable_actualRefreshMassTest (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T)
    (F : ActualRefreshTestObservation rate t → ℝ) (hF : @Measurable _ _ (actualRefreshObservationMeasurableSpace rate t) inferInstance F) (U : SlowSet p) :
    Measurable (actualRefreshMassTest rate rewards C_star C_h t F U) :=
  (hF.comp (measurable_actualRefreshFullObservation rate rewards C_star C_h t)).mul
    ((measurable_actualRefreshMass rate rewards C_star C_h t U).comp measurable_fst)

private theorem actualRefreshMass_mem_Icc (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : ActualRefreshSource rate rewards C_star C_h t) (U : SlowSet p) :
    actualRefreshMass rate rewards C_star C_h t z U ∈ Set.Icc (0 : ℝ) 1 := by
  let w := actualRefreshSourceCellOfMem rate rewards C_star C_h t z
  have hn (V : SlowSet p) : 0 ≤ actualRefreshMass rate rewards C_star C_h t z V :=
    RecordedSlowRefresh.residualMass_nonneg p
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) w.before
      w.numericalCell.input w.numericalCell.selected.view.payload.anchor
      w.numericalCell.selected.view.payload.anchor_pos V
  refine ⟨hn U, ?_⟩
  have hsum : ∑ V : SlowSet p, actualRefreshMass rate rewards C_star C_h t z V = 1 :=
    RecordedSlowRefresh.residualMass_sum_eq_one p
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) w.before
      w.numericalCell.input w.numericalCell.selected.view.payload.anchor
      w.numericalCell.selected.view.payload.anchor_pos
  rw [← hsum]
  exact Finset.single_le_sum (fun V _ => hn V) (Finset.mem_univ U)

private theorem integrable_real_bounded {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ x, |f x| ≤ B) : Integrable f μ :=
  Integrable.of_mem_Icc (-B) B hf.aemeasurable
    (Filter.Eventually.of_forall fun x => abs_le.mp (hb x))

/-- Both actual tested integrands are Bochner integrable for every bounded
Borel test, under the original unnormalized source restriction times the full
original auxiliary law. No positive stratum or atom mass is required. -/
theorem integrable_actualRefreshTests (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (F : ActualRefreshTestObservation rate t → ℝ) (hF : @Measurable _ _ (actualRefreshObservationMeasurableSpace rate t) inferInstance F)
    (B : ℝ) (hbound : ∀ observation, |F observation| ≤ B) (U : SlowSet p) :
    Integrable (actualRefreshIndicatorTest rate rewards C_star C_h t F U)
        ((actualRefreshSourceLaw rate rewards C_star C_h t).prod
          (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) ∧
      Integrable (actualRefreshMassTest rate rewards C_star C_h t F U)
        ((actualRefreshSourceLaw rate rewards C_star C_h t).prod
          (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) := by
  constructor
  · apply integrable_real_bounded _ _
      (measurable_actualRefreshIndicatorTest rate rewards C_star C_h t F hF U) B
    intro x
    unfold actualRefreshIndicatorTest
    split
    · simpa only [mul_one] using hbound
        (actualRefreshFullObservation rate rewards C_star C_h t x)
    · have hB := le_trans (abs_nonneg (F
        (actualRefreshFullObservation rate rewards C_star C_h t x)))
        (hbound (actualRefreshFullObservation rate rewards C_star C_h t x))
      simpa only [mul_zero, abs_zero] using hB
  · apply integrable_real_bounded _ _
      (measurable_actualRefreshMassTest rate rewards C_star C_h t F hF U) B
    intro x
    have hm := actualRefreshMass_mem_Icc rate rewards C_star C_h t x.1 U
    unfold actualRefreshMassTest
    rw [abs_mul, abs_of_nonneg hm.1]
    exact (mul_le_of_le_one_right (abs_nonneg _) hm.2).trans (hbound _)

private theorem actualRefreshErasure_insert (t : Fin p.T)
    (erased : ErasedAuxiliaryArray (p := p) t) (value : ContinuousControlSlice.Scalar) :
    actualRefreshErasure t (insertActualRefreshCoordinate t erased value) = erased := by
  funext q
  have hq : q.val ≠ (t, 1) := q.property
  simp only [actualRefreshErasure, insertActualRefreshCoordinate, hq, dite_false]

private theorem insertActualRefreshCoordinate_erasure (t : Fin p.T)
    (aux : AuxiliaryArray p) :
    insertActualRefreshCoordinate t (actualRefreshErasure t aux) (aux (t, 1)) = aux := by
  funext q
  by_cases hq : q = (t, 1)
  · subst q
    simp only [insertActualRefreshCoordinate, dite_true]
  · simp only [insertActualRefreshCoordinate, hq, dite_false, actualRefreshErasure]

/-- The observation really contains the complete actual calendar past and
actual current before-refresh fields for the supplied original full array. -/
theorem actualRefreshFullObservation_actual (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T)
    (z : ActualRefreshSource rate rewards C_star C_h t) (aux : AuxiliaryArray p) :
    actualRefreshFullObservation rate rewards C_star C_h t (z, aux) =
      (z.val, (actualRefreshErasure t aux,
        (ReferenceActiveHorizonMeasurability.listObservationCoordinates
          (calendarPast rate rewards C_star C_h (z.val, aux) t.val),
          (actualRefreshEntry rate rewards C_star C_h t z aux).beforeRefreshFields))) := by
  let w := actualRefreshSourceCellOfMem rate rewards C_star C_h t z
  have h := w.testObservation_insert_invariant rate rewards C_star C_h z.val t
    (actualRefreshErasure t aux) (aux (t, 1))
  simpa only [insertActualRefreshCoordinate_erasure, actualRefreshFullObservation,
    actualRefreshObservation, ActualRefreshSourceCell.testObservation, actualRefreshEntry, w] using h

private theorem actualRefresh_scalar_test_identity (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T)
    (z : ActualRefreshSource rate rewards C_star C_h t)
    (erased : ErasedAuxiliaryArray (p := p) t)
    (F : ActualRefreshTestObservation rate t → ℝ)
    (B : ℝ) (hbound : ∀ observation, |F observation| ≤ B) (U : SlowSet p) :
    (∫ value, actualRefreshIndicatorTest rate rewards C_star C_h t F U
      (z, insertActualRefreshCoordinate t erased value) ∂ContinuousControlSlice.scalarLaw) =
    ∫ value, actualRefreshMassTest rate rewards C_star C_h t F U
      (z, insertActualRefreshCoordinate t erased value) ∂ContinuousControlSlice.scalarLaw := by
  simp_rw [actualRefreshIndicatorTest, actualRefreshMassTest, actualRefreshFullObservation,
    actualRefreshErasure_insert]
  let w := actualRefreshSourceCellOfMem rate rewards C_star C_h t z
  change (∫ value, F (w.testObservation rate rewards C_star C_h z.val t erased) *
      if w.currentNextSlowSet rate rewards C_star C_h z.val t
        (insertActualRefreshCoordinate t erased value) = U then 1 else 0
      ∂ContinuousControlSlice.scalarLaw) =
    ∫ _value : ContinuousControlSlice.Scalar,
      F (w.testObservation rate rewards C_star C_h z.val t erased) *
        actualRefreshMass rate rewards C_star C_h t z U
      ∂ContinuousControlSlice.scalarLaw
  rw [(w.bounded_test_scalar_fibre_identity rate rewards C_star C_h z.val t
    erased F B hbound U).2]
  simp only [integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul]
  rfl

/-- Preserve the entire physical source while splitting just its auxiliary
refresh coordinate. -/
def actualRefreshSourceAuxiliarySplit (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :=
  (MeasurableEquiv.refl (ActualRefreshSource rate rewards C_star C_h t)).prodCongr
    (actualRefreshScalarSplit (p := p) t).symm

private theorem measurePreserving_actualRefreshSourceAuxiliarySplit (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T) :
    MeasurePreserving (actualRefreshSourceAuxiliarySplit rate rewards C_star C_h t)
      ((actualRefreshSourceLaw rate rewards C_star C_h t).prod
        ((erasedAuxiliaryLaw t).prod ContinuousControlSlice.scalarLaw))
      ((actualRefreshSourceLaw rate rewards C_star C_h t).prod
        (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) :=
  (MeasurePreserving.id _).prod
    ((measurePreserving_actualRefreshScalarSplit t).symm _)

private theorem integrable_actualRefreshSplitTests (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T)
    (F : ActualRefreshTestObservation rate t → ℝ)
    (hF : @Measurable _ _ (actualRefreshObservationMeasurableSpace rate t) inferInstance F)
    (B : ℝ) (hbound : ∀ observation, |F observation| ≤ B) (U : SlowSet p) :
    Integrable (actualRefreshIndicatorTest rate rewards C_star C_h t F U ∘
        actualRefreshSourceAuxiliarySplit rate rewards C_star C_h t)
      ((actualRefreshSourceLaw rate rewards C_star C_h t).prod
        ((erasedAuxiliaryLaw t).prod ContinuousControlSlice.scalarLaw)) ∧
      Integrable (actualRefreshMassTest rate rewards C_star C_h t F U ∘
        actualRefreshSourceAuxiliarySplit rate rewards C_star C_h t)
        ((actualRefreshSourceLaw rate rewards C_star C_h t).prod
          ((erasedAuxiliaryLaw t).prod ContinuousControlSlice.scalarLaw)) := by
  obtain ⟨hl, hr⟩ := integrable_actualRefreshTests rate rewards C_star C_h t F hF B hbound U
  have hE := measurePreserving_actualRefreshSourceAuxiliarySplit rate rewards C_star C_h t
  exact ⟨hE.integrable_comp_of_integrable hl, hE.integrable_comp_of_integrable hr⟩

private theorem integral_three_factors {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (κ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite κ] (f g : A × (B × C) → ℝ)
    (hf : Integrable f (μ.prod (ν.prod κ))) (hg : Integrable g (μ.prod (ν.prod κ)))
    (hfibre : ∀ a b, (∫ c, f (a, (b, c)) ∂κ) = ∫ c, g (a, (b, c)) ∂κ) :
    (∫ x, f x ∂μ.prod (ν.prod κ)) = ∫ x, g x ∂μ.prod (ν.prod κ) := by
  rw [integral_prod _ hf, integral_prod _ hg]
  apply integral_congr_ae
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae] with a ha hb
  rw [integral_prod _ ha, integral_prod _ hb]
  exact integral_congr_ae (Filter.Eventually.of_forall (hfibre a))

private theorem bounded_test_actual_split_product_identity (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T)
    (F : ActualRefreshTestObservation rate t → ℝ) (hF : @Measurable _ _ (actualRefreshObservationMeasurableSpace rate t) inferInstance F)
    (B : ℝ) (hbound : ∀ observation, |F observation| ≤ B) (U : SlowSet p) :
    (∫ x, (actualRefreshIndicatorTest rate rewards C_star C_h t F U ∘
        actualRefreshSourceAuxiliarySplit rate rewards C_star C_h t) x
      ∂(actualRefreshSourceLaw rate rewards C_star C_h t).prod
        ((erasedAuxiliaryLaw t).prod ContinuousControlSlice.scalarLaw)) =
      ∫ x, (actualRefreshMassTest rate rewards C_star C_h t F U ∘
          actualRefreshSourceAuxiliarySplit rate rewards C_star C_h t) x
        ∂(actualRefreshSourceLaw rate rewards C_star C_h t).prod
          ((erasedAuxiliaryLaw t).prod ContinuousControlSlice.scalarLaw) := by
  obtain ⟨hl, hr⟩ := integrable_actualRefreshSplitTests
    rate rewards C_star C_h t F hF B hbound U
  apply integral_three_factors _ _ _ _ _ hl hr
  intro z erased
  change (∫ value, actualRefreshIndicatorTest rate rewards C_star C_h t F U
      (z, (actualRefreshScalarSplit t).symm (erased, value))
      ∂ContinuousControlSlice.scalarLaw) =
    ∫ value, actualRefreshMassTest rate rewards C_star C_h t F U
      (z, (actualRefreshScalarSplit t).symm (erased, value))
      ∂ContinuousControlSlice.scalarLaw
  simp_rw [actualRefreshScalarSplit_symm_apply]
  exact actualRefresh_scalar_test_identity rate rewards C_star C_h t z erased F B hbound U

/-- The actual-source refresh bounded-test law under the original finite
unnormalized source restriction times the full original auxiliary law. -/
theorem bounded_test_actual_source_product_identity (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T)
    (F : ActualRefreshTestObservation rate t → ℝ)
    (hF : @Measurable _ _ (actualRefreshObservationMeasurableSpace rate t) inferInstance F)
    (B : ℝ) (hbound : ∀ observation, |F observation| ≤ B) (U : SlowSet p) :
    (∫ x, actualRefreshIndicatorTest rate rewards C_star C_h t F U x
      ∂(actualRefreshSourceLaw rate rewards C_star C_h t).prod
        (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) =
      ∫ x, actualRefreshMassTest rate rewards C_star C_h t F U x
        ∂(actualRefreshSourceLaw rate rewards C_star C_h t).prod
          (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p) := by
  have hE := measurePreserving_actualRefreshSourceAuxiliarySplit rate rewards C_star C_h t
  rw [← hE.integral_comp' (actualRefreshIndicatorTest rate rewards C_star C_h t F U),
    ← hE.integral_comp' (actualRefreshMassTest rate rewards C_star C_h t F U)]
  exact bounded_test_actual_split_product_identity rate rewards C_star C_h t F hF B hbound U

/-- The actual last active proposal whose following cutoff is within the
horizon and strictly before its unchanged episode grid. -/
def actualStrictCutoffRefreshStratum (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :
    Set (ActualRefreshSource rate rewards C_star C_h t) :=
  {z | let w := actualRefreshSourceCellOfMem rate rewards C_star C_h t z
    w.index.val + 1 = (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z.val).length ∧
    t.val + 1 < p.T ∧ t.val + 2 < FollowerCutoffScan.gridBoundary p rate.eta.val
      w.numericalCell.selected.view.payload.sigma}

private theorem measurable_actualRefreshSigma (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T) :
    Measurable (fun z : ActualRefreshSource rate rewards C_star C_h t =>
      (actualRefreshSourceCellOfMem rate rewards C_star C_h t z).numericalCell.selected.view.payload.sigma) := by
  apply measurable_to_countable'
  intro sigma
  have heq : {z : ActualRefreshSource rate rewards C_star C_h t |
      (actualRefreshSourceCellOfMem rate rewards C_star C_h t z).numericalCell.selected.view.payload.sigma = sigma} =
      {z | ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = sigma.val} := by
    ext z
    have hg := wholeLiveCell_geometry rate rewards C_star C_h z.val
      (actualRefreshSourceCellOfMem rate rewards C_star C_h t z).index
    have hsigma : (actualRefreshSourceCellOfMem rate rewards C_star C_h t z).numericalCell.selected.view.payload.sigma.val =
        ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h := hg.2.1
    exact Fin.ext_iff.trans (by change _ = sigma.val ↔ _ = sigma.val; rw [hsigma])
  change MeasurableSet {z : ActualRefreshSource rate rewards C_star C_h t |
    (actualRefreshSourceCellOfMem rate rewards C_star C_h t z).numericalCell.selected.view.payload.sigma = sigma}
  rw [heq]
  exact (measurableSet_singleton sigma.val).preimage
    ((ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
      rate rewards C_star C_h).comp measurable_subtype_coe)

/-- This cutoff specialization remains a Borel source-only restriction. -/
theorem measurableSet_actualStrictCutoffRefreshStratum (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T) :
    MeasurableSet (actualStrictCutoffRefreshStratum rate rewards C_star C_h t) := by
  have hi := (measurable_of_countable (fun n : ℕ => n + 1)).comp
    (measurable_actualIndex rate rewards C_star C_h t)
  have hl := (ReferenceFirstLiveOverflowReadout.measurable_wholeFirstLiveLength
    rate rewards C_star C_h).comp
      (measurable_subtype_coe : Measurable
        (Subtype.val : ActualRefreshSource rate rewards C_star C_h t → SourceInput p))
  have hg := (measurable_of_countable
    (FollowerCutoffScan.gridBoundary p rate.eta.val)).comp
      (measurable_actualRefreshSigma rate rewards C_star C_h t)
  exact (measurableSet_eq_fun hi hl).inter
    ((MeasurableSet.const _).inter
      ((MeasurableSet.of_discrete : MeasurableSet {n : ℕ | t.val + 2 < n}).preimage hg))

/-- The same finite cutoff event on the entire original physical source. -/
def actualStrictCutoffSourceEvent (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) : Set (SourceInput p) :=
  Subtype.val '' actualStrictCutoffRefreshStratum rate rewards C_star C_h t

private theorem measurableSet_actualStrictCutoffSourceEvent (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T) :
    MeasurableSet (actualStrictCutoffSourceEvent rate rewards C_star C_h t) :=
  (measurableSet_actualRefreshSourceStratum rate rewards C_star C_h t).subtype_image
    (measurableSet_actualStrictCutoffRefreshStratum rate rewards C_star C_h t)

/-- Restrict a test by the actual source calendar stratum. -/
def actualStrictCutoffTest (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (F : ActualRefreshTestObservation rate t → ℝ)
    (observation : ActualRefreshTestObservation rate t) : ℝ :=
  if observation.1 ∈ actualStrictCutoffSourceEvent rate rewards C_star C_h t
    then F observation else 0

/-- Finite actual-cutoff transport of the same refresh law. All integrals use
the original unnormalized source restrictions and full auxiliary law. -/
theorem bounded_test_actual_strict_cutoff_identity (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (F : ∀ t : Fin p.T, ActualRefreshTestObservation rate t → ℝ)
    (hF : ∀ t, @Measurable _ _ (actualRefreshObservationMeasurableSpace rate t) inferInstance (F t))
    (B : Fin p.T → ℝ) (hbound : ∀ t observation, |F t observation| ≤ B t) (U : SlowSet p) :
    (∑ t : Fin p.T, ∫ x, actualRefreshIndicatorTest rate rewards C_star C_h t
      (actualStrictCutoffTest rate rewards C_star C_h t (F t)) U x
      ∂(actualRefreshSourceLaw rate rewards C_star C_h t).prod
        (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) =
    ∑ t : Fin p.T, ∫ x, actualRefreshMassTest rate rewards C_star C_h t
      (actualStrictCutoffTest rate rewards C_star C_h t (F t)) U x
      ∂(actualRefreshSourceLaw rate rewards C_star C_h t).prod
        (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p) := by
  apply Finset.sum_congr rfl
  intro t _
  have hs : @Measurable _ _ (actualRefreshObservationMeasurableSpace rate t)
      inferInstance (Prod.fst : ActualRefreshTestObservation rate t → SourceInput p) := measurable_fst
  have htest : @Measurable _ _ (actualRefreshObservationMeasurableSpace rate t)
      inferInstance (actualStrictCutoffTest rate rewards C_star C_h t (F t)) :=
    (hF t).ite
      ((measurableSet_actualStrictCutoffSourceEvent rate rewards C_star C_h t).preimage hs)
      measurable_const
  apply bounded_test_actual_source_product_identity rate rewards C_star C_h t _ htest (|B t|) _ U
  intro observation
  unfold actualStrictCutoffTest
  split
  · exact (hbound t observation).trans (le_abs_self _)
  · exact (abs_zero).trans_le (abs_nonneg _)

/-- Every point of the strict-cutoff stratum has the actual following cutoff
record. Thus the finite transport uses the triggering date, never the past at
the cutoff date. Empty, terminal, horizon and grid-tie paths are excluded by
these literal source conditions; PRE-frozen paths have no parent source cell. -/
theorem actualStrictCutoffRefreshStratum_actual (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T)
    (z : ActualRefreshSource rate rewards C_star C_h t)
    (hz : z ∈ actualStrictCutoffRefreshStratum rate rewards C_star C_h t) :
    let w := actualRefreshSourceCellOfMem rate rewards C_star C_h t z
    ∃ (cut : Record rate) (suffix : List (Record rate)),
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h =
        ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z.val ++ cut :: suffix ∧
      ReferenceCollectionPhaseHistory.cutoffChosen cut.input = true ∧
      cut.input.time.val = t.val + 1 ∧
      FollowerCutoffScan.firstCutoff p rate.eta.val w.numericalCell.selected.view.payload.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val))) = t.val + 2 := by
  let w := actualRefreshSourceCellOfMem rate rewards C_star C_h t z
  have hg := wholeLiveCell_geometry rate rewards C_star C_h z.val w.index
  have ht := congrArg Fin.val w.actual_time
  have hpositive := w.index.isLt
  change w.index.val + 1 = _ ∧ _ ∧ _ at hz
  obtain ⟨hlast, hhorizon, _hstrict⟩ := hz
  have h := ReferenceFirstLiveActualCutoffRefreshCoordinate.firstLiveChronologicalPrefix_actual_cutoff_refresh_coordinate
    rate rewards C_star C_h z.val auxiliarySection
  dsimp only at h hg
  rcases h with hnone | ⟨_hc, hterminal | hempty | hhorizonRun | hcut⟩
  · simp only [hnone.2.1, List.length_nil, Nat.not_lt_zero] at hpositive
  · simp only [hterminal.2.1, List.length_nil, Nat.not_lt_zero] at hpositive
  · simp only [hempty.2.1, List.length_nil, Nat.not_lt_zero] at hpositive
  · omega
  · rcases hcut with ⟨_hs, _hpos, _hshort, cut, suffix, registers, _owned, _base,
      hsplit, _hstate, hchosen, _hpos', hdate, ⟨birth, hbirth, hbirthTime⟩,
      hfirst, _hgrid, _halternatives⟩
    have hsigma : registers.payload.sigma.val =
        ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h := by
      unfold ReferenceAssignmentPayloadPersistence.InstallationBirth at hbirth
      split at hbirth <;> first | exact hbirth.2.trans hbirthTime | exact hbirth.elim
    have heq : registers.payload.sigma = w.numericalCell.selected.view.payload.sigma :=
      Fin.ext (hsigma.trans hg.2.1.symm)
    have hdate' : cut.input.time.val = t.val + 1 := by omega
    refine ⟨cut, suffix, hsplit, hchosen, hdate', ?_⟩
    rw [← heq, hfirst, hdate']

end Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw

end
