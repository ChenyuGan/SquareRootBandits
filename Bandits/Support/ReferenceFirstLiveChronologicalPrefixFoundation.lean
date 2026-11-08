/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLaunchOriginalAuxiliaryReward
public import Bandits.Support.ReferenceCompleteOriginalCalendarRawLearningComparison

/-!
# Original-source first-live chronological foundation

The logical cells retain the original physical records while using the existing
queue machine, actual pre-round cutoff tags and reserved fast coordinates.
This module constructs the literal source-driven path and proves its
deterministic identities; it asserts no probability law or Borel property.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveChronologicalPrefixFoundation

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev AuxiliaryArray (p : Parameters) :=
  ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p

variable {p : Parameters}

/-- The supported slow-set carrier already used by the original assignment. -/
abbrev SlowSet (p : Parameters) := CanonicalOrientedSetLaw.SlowSet p.K p.m

/-- The prescribed post-overflow set consists of the first `m-1` arms. -/
def frozenSlowSet (p : Parameters) : SlowSet p :=
  ⟨Finset.Iio (⟨p.m - 1, by have hm := p.m_lt_K; omega⟩ : Fin p.K), by
    apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_univ _, Fin.card_Iio _⟩⟩

/-- The prescribed post-overflow fast arm is source arm `m`. -/
def frozenFastArm (p : Parameters) : Fin p.K := ⟨p.m - 1, by have hm := p.m_lt_K; omega⟩

/-- The fixed continuation fast arm is outside the fixed slow set. -/
theorem frozenFastArm_not_mem (p : Parameters) :
    frozenFastArm p ∉ (frozenSlowSet p).val := by
  simp only [frozenFastArm, frozenSlowSet, Finset.mem_Iio, lt_self_iff_false, not_false_eq_true]

theorem slowSet_card_pos (p : Parameters) : 0 < Fintype.card (SlowSet p) := by
  let : Nonempty (SlowSet p) := ⟨frozenSlowSet p⟩
  exact Fintype.card_pos

/-- Fixed finite enumeration for the categorical residual draw. -/
def slowSetEnumeration (p : Parameters) : Fin (Fintype.card (SlowSet p)) ≃ SlowSet p :=
  (Fintype.equivFin (SlowSet p)).symm

/-- Literal categorical sampling of the already proved one-step residual mass.
No normalized vector or residual law is an input. -/
def residualDraw (rate : RateInput p) (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K) (anchor : Fin p.K → ℝ)
    (hanchor : ∀ i, 0 < anchor i) (x : ContinuousControlSlice.Scalar) : SlowSet p :=
  slowSetEnumeration p (ContinuousCategorical.sample (slowSet_card_pos p)
    (fun k => RecordedSlowRefresh.residualMass p
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) state round anchor hanchor
      (slowSetEnumeration p k))
    (by
      rw [Equiv.sum_comp]
      exact RecordedSlowRefresh.residualMass_sum_eq_one p
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) state round anchor hanchor) x)

/-- The inverse-CDF comparisons use exactly the same source-varying masses
as `RecordedSlowRefresh.residualPMF`. -/
theorem residualDraw_eq_iff (rate : RateInput p)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (x : ContinuousControlSlice.Scalar) (U : SlowSet p) :
    residualDraw rate state round anchor hanchor x = U ↔
      ContinuousCategorical.lower
          (fun k => RecordedSlowRefresh.residualMass p
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) state round anchor hanchor
            (slowSetEnumeration p k)) ((slowSetEnumeration p).symm U) ≤ x.val ∧
        x.val < ContinuousCategorical.upper
          (fun k => RecordedSlowRefresh.residualMass p
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) state round anchor hanchor
            (slowSetEnumeration p k)) ((slowSetEnumeration p).symm U) := by
  unfold residualDraw
  apply ((slowSetEnumeration p).eq_symm_apply).symm.trans
  exact ContinuousCategorical.sample_eq_iff (slowSet_card_pos p)
    (fun k => RecordedSlowRefresh.residualMass_nonneg p
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) state round anchor hanchor
      (slowSetEnumeration p k)) _ x _

/-- One logical calendar cell. Its queue fields are the existing canonical
machine states, not a second protocol state. `arrivals` records the enabled
flag separately from the integer amount, including enabled zero arrivals. -/
structure LogicalCell (p : Parameters) (rate : RateInput p) where
  time : Fin p.T
  physical : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)
  numerical : ReferenceFirstLiveOverflowReadout.NumericalCellReadout p
  before : RecordedQueueRun.RunState p.K
  after : RecordedQueueRun.RunState p.K
  arrivals : Fin p.K → Bool × ℕ
  service : Fin p.K → ℕ
  slowSet : SlowSet p
  fastArm : Fin p.K
  proposal : Bool
  nextSlowSet : SlowSet p

abbrev Record (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

/-- The reserved fast draw is evaluated even when the coordinator physically
plays a pilot. It uses the actual selected complement and the original `fast`
coordinate, without consuming any auxiliary scalar. -/
def reservedFastArm {rate : RateInput p} (record : Record rate)
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record) :
    CanonicalFastSampling.FastArm cell.selected.view.payload.slowSet :=
  FastComplementLocality.sampleLocalFast p rate.eta.val rate.eta.property rate.sourceCap
    cell.selected.view.payload.anchor cell.choiceInputsValid.anchor_pos
    cell.selected.view.payload.slowSet cell.selected.view.complementWeights
    cell.choiceInputsValid.current_weight_pos cell.choiceInputsValid.anchor_le_current
    cell.choiceInputsValid.current_le_twice_anchor
    (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
      (record.input.row.2 record.input.time).1)

/-- One literal logical update. Only the PRE-update overflow flag suppresses
learning and refresh. In particular the first detecting update still retains
its proposal and its single label-1 residual draw. -/
def appendLogicalCell {rate : RateInput p} (record : Record rate)
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record)
    (state : RecordedQueueRun.RunState p.K) (aux : AuxiliaryArray p) : LogicalCell p rate :=
  let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let proposed := !state.overflow &&
    FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row record.input.time
  { time := record.input.time
    physical := ReferenceActiveHorizonMeasurability.roundRecordCode record
    numerical := (cell.input.enabled, (cell.input.recordedArm, (cell.input.reward, cell.input.rate)))
    before := state
    after := RecordedQueueRun.step q state cell.input
    arrivals := RecordedQueueRun.acceptedRecord q state cell.input
    service := fun i => RecordedQueueRun.recordService (4 * q.n) (state.registers i)
      (RecordedQueueRun.acceptedRecord q state cell.input i)
    slowSet := if state.overflow then frozenSlowSet p else cell.selected.view.payload.slowSet
    fastArm := if state.overflow then frozenFastArm p else (reservedFastArm record cell).val
    proposal := proposed
    nextSlowSet := if state.overflow then frozenSlowSet p else
      if proposed then residualDraw rate state cell.input cell.selected.view.payload.anchor
        cell.selected.view.payload.anchor_pos (aux (record.input.time, 1))
      else cell.selected.view.payload.slowSet }

abbrev LiveWindow {rate : RateInput p} (records : List (Record rate)) :=
  ReferenceFirstLiveConfirmationHistory.firstLiveWindow records

/-- Calendar scan on the original physical records. The constructor tests the
actual cutoff BEFORE appending a cell, so it excludes that round's COLLECTION
update. A source-derived witness supplies the existing numerical cell only
when this record belongs to the live prefix. -/
def scanCalendar {rate : RateInput p} :
    (records : List (Record rate)) →
    (∀ r ∈ LiveWindow records,
      ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r) →
    RecordedQueueRun.RunState p.K → AuxiliaryArray p → List (LogicalCell p rate)
  | [], _, _, _ => []
  | r :: rs, cells, state, aux =>
    if hcut : ReferenceCollectionPhaseHistory.cutoffChosen r.input then [] else
      let cell := cells r (by
        simp only [LiveWindow, ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
          hcut, Bool.not_false, List.takeWhile_cons_of_pos, List.mem_cons, true_or])
      appendLogicalCell r cell state aux ::
        scanCalendar rs
          (fun r hr => cells r (by
            simp only [LiveWindow, ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
              hcut, Bool.not_false, List.takeWhile_cons_of_pos, List.mem_cons]
            exact Or.inr hr))
          (RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            state cell.input) aux

/-- Every live record of the whole original source has its actual numerical
cell. The absent and terminal launch cases need no fabricated record. -/
theorem wholeLiveCell_exists (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (r : Record rate)
    (hr : r ∈ LiveWindow
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)) :
    Nonempty (ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r) := by
  by_cases hc : (ReferenceCompletePhysicalHistory.generatedBoundary
      rate source rewards C_star C_h).crossing.isSome = true
  · change (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true at hc
    let s : Fin (p.T + 1) :=
      ⟨ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h,
        Nat.lt_succ_of_le (ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate source rewards C_star C_h)⟩
    let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s.val :=
      ⟨source, hc, rfl⟩
    have hw := (ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
      rate rewards C_star C_h s x).1
    change r ∈ ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source at hr
    rw [hw] at hr
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hr
    have cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate source
      rewards C_star C_h hc (p.T - s.val)
      (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h s.val
        (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x) k
    change ReferenceFirstWindowNumericalStream.ActualLiveSourceCell
      ((ReferenceFirstLiveOverflowReadout.firstLiveWindow rate rewards C_star C_h
        s.val (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x).get k) at cell
    rw [hk] at cell
    exact ⟨cell⟩
  · have hnone : (ReferenceCompletePhysicalHistory.generatedBoundary
        rate source rewards C_star C_h).crossing = none := by
      cases h : (ReferenceCompletePhysicalHistory.generatedBoundary
        rate source rewards C_star C_h).crossing <;> simp_all
    have hw := (ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
      rate rewards C_star C_h source hnone).1
    change r ∈ ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source at hr
    rw [hw] at hr
    exact False.elim (List.not_mem_nil hr)

/-- The numerical cell of one actual first-live record, selected only from
its proved nonempty witness type. Its numerical input is independent of the
witness by `actualLiveSourceCell_unique` below. -/
def wholeLiveCell (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (r : Record rate)
    (hr : r ∈ LiveWindow
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)) :
    ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r :=
  Classical.choice (wholeLiveCell_exists rate rewards C_star C_h source r hr)

/-- The first-launch-to-first-cut logical calendar prefix on the unchanged
physical source and the existing independent auxiliary array. The recursion
starts with the actual zero registers and scans the whole physical suffix;
its actual cutoff test determines its length. -/
def firstLiveChronologicalPrefix (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (input : SourceInput p × AuxiliaryArray p) : List (LogicalCell p rate) :=
  scanCalendar
    (ReferenceCompletePhysicalHistory.completeSuffixRecords rate input.1 rewards C_star C_h)
    (wholeLiveCell rate rewards C_star C_h input.1)
    (RecordedQueueRun.initialState p.K) input.2

private theorem cell_input_congr {rate : RateInput p} {r s : Record rate}
    (hrs : r = s) (a : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (b : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell s) : a.input = b.input := by
  cases hrs
  exact ReferenceFirstLiveNumericalPrefixTemporal.actualLiveSourceCell_input_unique a b

private def numericalInputs {rate : RateInput p} :
    (records : List (Record rate)) →
    (∀ r ∈ LiveWindow records,
      ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r) →
    List (RecordedQueueRun.RoundInput p.K)
  | [], _ => []
  | r :: rs, cells =>
    if hcut : ReferenceCollectionPhaseHistory.cutoffChosen r.input then [] else
      let cell := cells r (by
        simp only [LiveWindow, ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
          hcut, Bool.not_false, List.takeWhile_cons_of_pos, List.mem_cons, true_or])
      cell.input :: numericalInputs rs
        (fun r hr => cells r (by
          simp only [LiveWindow, ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
            hcut, Bool.not_false, List.takeWhile_cons_of_pos, List.mem_cons]
          exact Or.inr hr))

private theorem numericalInputs_length {rate : RateInput p}
    (records : List (Record rate))
    (cells : ∀ r ∈ LiveWindow records,
      ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r) :
    (numericalInputs records cells).length = (LiveWindow records).length := by
  induction records with
  | nil => rfl
  | cons r rs ih =>
    cases hcut : ReferenceCollectionPhaseHistory.cutoffChosen r.input with
    | true => simp [numericalInputs, LiveWindow,
        ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hcut]
    | false => simpa [numericalInputs, LiveWindow,
        ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hcut] using
          congrArg Nat.succ (ih _)

private theorem numericalInputs_get {rate : RateInput p}
    (records : List (Record rate))
    (cells : ∀ r ∈ LiveWindow records,
      ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (k : ℕ) (hk : k < (LiveWindow records).length) :
    (numericalInputs records cells)[k]'(by rw [numericalInputs_length]; exact hk) =
      (cells ((LiveWindow records)[k]) (List.getElem_mem hk)).input := by
  induction records generalizing k with
  | nil => simp [LiveWindow, ReferenceFirstLiveConfirmationHistory.firstLiveWindow] at hk
  | cons r rs ih =>
    cases hcut : ReferenceCollectionPhaseHistory.cutoffChosen r.input with
    | true => simp [LiveWindow,
        ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hcut] at hk
    | false =>
      let head := cells r (by
        simp [LiveWindow, ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hcut])
      let tail := fun r hr => cells r (by
        simp only [LiveWindow, ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
          hcut, Bool.not_false, List.takeWhile_cons_of_pos, List.mem_cons]
        exact Or.inr hr)
      have hinputs : numericalInputs (r :: rs) cells = head.input :: numericalInputs rs tail := by
        simp only [numericalInputs, hcut, Bool.false_eq_true, dite_false, head, tail]
        rfl
      cases k with
      | zero =>
        simp only [hinputs, List.getElem_cons_zero]
        apply cell_input_congr
        simp [LiveWindow, ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hcut]
      | succ k =>
        have htail : k < (LiveWindow rs).length := by
          simpa [LiveWindow, ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hcut] using hk
        simp only [hinputs, List.getElem_cons_succ, ih tail k htail]
        apply cell_input_congr
        simp [LiveWindow, ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hcut]

private theorem appendLogicalCell_cell_congr {rate : RateInput p} {r s : Record rate}
    (hrs : r = s) (a : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (b : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell s)
    (state : RecordedQueueRun.RunState p.K) (aux : AuxiliaryArray p) :
    appendLogicalCell r a state aux = appendLogicalCell s b state aux := by
  cases hrs
  have hi := cell_input_congr rfl a b
  have hs : a.selected = b.selected :=
    Option.some.inj (a.selection_actual.symm.trans b.selection_actual)
  cases a
  cases b
  dsimp only at hi hs
  cases hs
  cases hi
  rfl

/-- The actual pre-round cutoff alone determines the generated calendar
length; overflow changes the logical fields, not the physical window. -/
theorem scanCalendar_length {rate : RateInput p} (records : List (Record rate))
    (cells : ∀ r ∈ LiveWindow records,
      ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (state : RecordedQueueRun.RunState p.K) (aux : AuxiliaryArray p) :
    (scanCalendar records cells state aux).length = (LiveWindow records).length := by
  induction records generalizing state with
  | nil => rfl
  | cons r rs ih =>
    cases hcut : ReferenceCollectionPhaseHistory.cutoffChosen r.input with
    | true => simp [scanCalendar, LiveWindow,
        ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hcut]
    | false => simpa [scanCalendar, LiveWindow,
        ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hcut] using
          congrArg Nat.succ (ih _ _)

private theorem scanCalendar_get {rate : RateInput p} (records : List (Record rate))
    (cells : ∀ r ∈ LiveWindow records,
      ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (state : RecordedQueueRun.RunState p.K) (aux : AuxiliaryArray p)
    (k : ℕ) (hk : k < (LiveWindow records).length) :
    (scanCalendar records cells state aux)[k]'(by rw [scanCalendar_length]; exact hk) =
      appendLogicalCell ((LiveWindow records)[k])
        (cells ((LiveWindow records)[k]) (List.getElem_mem hk))
        (RecordedQueueRun.execute (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          ((numericalInputs records cells).take k) state) aux := by
  induction records generalizing state k with
  | nil => simp [LiveWindow, ReferenceFirstLiveConfirmationHistory.firstLiveWindow] at hk
  | cons r rs ih =>
    cases hcut : ReferenceCollectionPhaseHistory.cutoffChosen r.input with
    | true => simp [LiveWindow,
        ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hcut] at hk
    | false =>
      let head := cells r (by
        simp [LiveWindow, ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hcut])
      let tail := fun r hr => cells r (by
        simp only [LiveWindow, ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
          hcut, Bool.not_false, List.takeWhile_cons_of_pos, List.mem_cons]
        exact Or.inr hr)
      have hscan : scanCalendar (r :: rs) cells state aux =
          appendLogicalCell r head state aux :: scanCalendar rs tail
            (RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              state head.input) aux := by
        simp only [scanCalendar, hcut, Bool.false_eq_true, dite_false, head, tail]
        rfl
      have hinputs : numericalInputs (r :: rs) cells = head.input :: numericalInputs rs tail := by
        simp only [numericalInputs, hcut, Bool.false_eq_true, dite_false, head, tail]
        rfl
      cases k with
      | zero =>
        simp only [hscan, List.getElem_cons_zero]
        simp only [List.take_zero, RecordedQueueRun.execute]
        apply appendLogicalCell_cell_congr
        simp [LiveWindow, ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hcut]
      | succ k =>
        have htail : k < (LiveWindow rs).length := by
          simpa [LiveWindow, ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hcut] using hk
        simp only [hscan, List.getElem_cons_succ, ih tail _ k htail, hinputs]
        simp only [List.take_succ_cons, RecordedQueueRun.execute]
        apply appendLogicalCell_cell_congr
        simp [LiveWindow, ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hcut]

/-- Length is identified AFTER the chronological scan with the canonical
whole first-live window, including empty and terminal cases. -/
theorem firstLiveChronologicalPrefix_length (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (input : SourceInput p × AuxiliaryArray p) :
    (firstLiveChronologicalPrefix rate rewards C_star C_h input).length =
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength rate rewards C_star C_h input.1 :=
  scanCalendar_length _ _ _ _

private theorem whole_numericalInputs_eq (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) :
    numericalInputs
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)
        (wholeLiveCell rate rewards C_star C_h source) =
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h source := by
  by_cases hc : (ReferenceCompletePhysicalHistory.generatedBoundary
      rate source rewards C_star C_h).crossing.isSome = true
  · change (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true at hc
    let s : Fin (p.T + 1) :=
      ⟨ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h,
        Nat.lt_succ_of_le (ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate source rewards C_star C_h)⟩
    let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s.val :=
      ⟨source, hc, rfl⟩
    obtain ⟨hw, hcells⟩ := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
      rate rewards C_star C_h s x
    change ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source = _ at hw
    change ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h source = _ at hcells
    apply List.ext_getElem
    · rw [numericalInputs_length]
      change (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source).length = _
      rw [hw, hcells]
      exact (ReferenceFirstLiveOverflowReadout.firstLiveCells_length
        rate rewards C_star C_h s.val (p.T - s.val)
        (ReferenceFirstLiveOverflowReadout.maximal_span s) x).symm
    · intro k hk hk'
      have hkW : k < (LiveWindow (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)).length := by
        rwa [numericalInputs_length] at hk
      rw [numericalInputs_get]
      let k' : Fin (ReferenceFirstLiveOverflowReadout.firstLiveWindow
          rate rewards C_star C_h s.val (p.T - s.val)
          (ReferenceFirstLiveOverflowReadout.maximal_span s) x).length :=
        ⟨k, by
          rw [numericalInputs_length] at hk
          change k < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
            rate rewards C_star C_h source).length at hk
          rwa [hw] at hk⟩
      let a := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate source
        rewards C_star C_h hc (p.T - s.val)
        (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h s.val
          (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x) k'
      have hkF : k < (ReferenceFirstLiveOverflowReadout.firstLiveWindow rate rewards C_star C_h
          s.val (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x).length := k'.isLt
      have hrecord :
          (LiveWindow (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h))[k] =
          (ReferenceFirstLiveOverflowReadout.firstLiveWindow rate rewards C_star C_h
            s.val (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x)[k'.val] := by
        change (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h source)[k] = _
        have hget := congrArg (fun L => L[k]?) hw
        change (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
            rate rewards C_star C_h source)[k]? = _ at hget
        have hkWhole : k < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h source).length := hkW
        rw [List.getElem?_eq_getElem hkWhole, List.getElem?_eq_getElem hkF] at hget
        exact Option.some.inj hget
      have heq := cell_input_congr hrecord
        (wholeLiveCell rate rewards C_star C_h source _ (List.getElem_mem hkW)) a
      have hget := congrArg (fun L => L[k]?) hcells
      change (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
        rate rewards C_star C_h source)[k]? =
        (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate source
          rewards C_star C_h hc (p.T - s.val) _)[k]? at hget
      have hkA : k < (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate source
          rewards C_star C_h hc (p.T - s.val)
          (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h s.val
            (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x)).length := by
        rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length]
        exact k'.isLt
      rw [List.getElem?_eq_getElem hk', List.getElem?_eq_getElem hkA] at hget
      exact heq.trans ((ReferenceFirstWindowNumericalStream.actualLiveSourceCells_get
        rate source rewards C_star C_h hc (p.T - s.val) _ k').symm.trans
          (Option.some.inj hget).symm)
  · have hnone : (ReferenceCompletePhysicalHistory.generatedBoundary
        rate source rewards C_star C_h).crossing = none := by
      cases h : (ReferenceCompletePhysicalHistory.generatedBoundary
        rate source rewards C_star C_h).crossing <;> simp_all
    obtain ⟨hw, hcells, _⟩ := ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
      rate rewards C_star C_h source hnone
    rw [hcells]
    apply List.eq_nil_iff_length_eq_zero.mpr
    rw [numericalInputs_length]
    exact congrArg List.length hw

/-- Each generated cell has the actual numerical source input and the
zero-origin all-arm queue state computed from exactly its strict predecessors.
No path-correctness or numerical-equality premise is supplied by a caller. -/
theorem firstLiveChronologicalPrefix_get (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (aux : AuxiliaryArray p)
    (k : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source).length) :
    (firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux))[k.val]'(by
      rw [firstLiveChronologicalPrefix_length]; exact k.isLt) =
      appendLogicalCell
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h source)[k.val])
        (wholeLiveCell rate rewards C_star C_h source _ (List.getElem_mem k.isLt))
        (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
            rate rewards C_star C_h source).take k.val)) aux := by
  have h := scanCalendar_get
    (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)
    (wholeLiveCell rate rewards C_star C_h source)
    (RecordedQueueRun.initialState p.K) aux k.val k.isLt
  simp only [whole_numericalInputs_eq] at h
  exact h

/-- The canonical whole numerical stream has exactly one cell per generated
first-live physical record. -/
theorem wholeFirstLiveCells_length (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) :
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h source).length =
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source).length := by
  rw [← whole_numericalInputs_eq]
  exact numericalInputs_length _ _

/-- The constructor's witness uses the SAME canonical numerical cell. -/
theorem wholeLiveCell_input_eq (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p)
    (k : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source).length) :
    (wholeLiveCell rate rewards C_star C_h source _ (List.getElem_mem k.isLt)).input =
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
        rate rewards C_star C_h source)[k.val]'(by rw [wholeFirstLiveCells_length]; exact k.isLt) := by
  have h := numericalInputs_get
    (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)
    (wholeLiveCell rate rewards C_star C_h source) k.val k.isLt
  simp only [whole_numericalInputs_eq] at h
  exact h.symm

/-- The complete actual physical record code is retained at each generated
date, rather than a sampled or selected substitute path. -/
theorem firstLiveChronologicalPrefix_physical (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (aux : AuxiliaryArray p) :
    (firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux)).map LogicalCell.physical =
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source).map ReferenceActiveHorizonMeasurability.roundRecordCode := by
  apply List.ext_getElem
  · simp only [List.length_map, firstLiveChronologicalPrefix_length,
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength]
  · intro k hk hk'
    have hkw : k < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source).length := by simpa only [List.length_map] using hk'
    simp only [List.getElem_map, firstLiveChronologicalPrefix_get rate rewards C_star C_h
      source aux ⟨k, hkw⟩, appendLogicalCell]

/-- Every generated numerical field is exactly its original source cell,
including its actual recorder marker and whole reward and rate vectors. -/
theorem firstLiveChronologicalPrefix_numerical (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (aux : AuxiliaryArray p) :
    (firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux)).map LogicalCell.numerical =
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveCellReadout
        rate rewards C_star C_h source := by
  apply List.ext_getElem
  · simp only [List.length_map, firstLiveChronologicalPrefix_length,
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength,
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveCellReadout, List.length_map,
      wholeFirstLiveCells_length]
  · intro k hk hk'
    have hkw : k < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source).length := by
      simpa only [ReferenceFirstLiveOverflowReadout.wholeFirstLiveCellReadout,
        List.length_map, wholeFirstLiveCells_length] using hk'
    simp only [List.getElem_map, firstLiveChronologicalPrefix_get rate rewards C_star C_h
      source aux ⟨k, hkw⟩, appendLogicalCell,
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveCellReadout, List.getElem_map,
      wholeLiveCell_input_eq rate rewards C_star C_h source ⟨k, hkw⟩]

/-- Exact strict-predecessor and post-update states of every generated cell.
The equations refer to ALL arms of the zero-origin canonical queue machine. -/
theorem firstLiveChronologicalPrefix_queue_states (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (aux : AuxiliaryArray p)
    (k : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source).length) :
    let cells := ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h source
    let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
    let entry := (firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux))[k.val]'(by
      rw [firstLiveChronologicalPrefix_length]; exact k.isLt)
    entry.before = RecordedQueueRun.run q (cells.take k.val) ∧
      entry.after = RecordedQueueRun.run q (cells.take (k.val + 1)) := by
  dsimp only
  simp only [firstLiveChronologicalPrefix_get, appendLogicalCell]
  refine ⟨trivial, ?_⟩
  rw [wholeLiveCell_input_eq]
  have hk : k.val < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h source).length := by rw [wholeFirstLiveCells_length]; exact k.isLt
  rw [← List.take_append_getElem hk, RecordedSlowRefresh.run_append_singleton]

/-- Literal all-arm accepted arrivals, bounded service, and queue transition
at a generated date. Virtual queues are never replaced by physical unoccupied
follower registers. -/
theorem firstLiveChronologicalPrefix_all_arm_update (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (aux : AuxiliaryArray p)
    (k : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source).length) :
    let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
    let cells := ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h source
    let round := cells[k.val]'(by rw [wholeFirstLiveCells_length]; exact k.isLt)
    let entry := (firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux))[k.val]'(by
      rw [firstLiveChronologicalPrefix_length]; exact k.isLt)
    ∀ i : Fin p.K,
      entry.arrivals i = RecordedQueueRun.acceptedRecord q entry.before round i ∧
      entry.service i = RecordedQueueRun.recordService (4 * q.n) (entry.before.registers i)
        (entry.arrivals i) ∧
      entry.service i ≤ 4 * q.n ∧
      entry.after.registers i = QueueReplay.transition (4 * q.n)
        (entry.before.registers i) (entry.arrivals i) := by
  dsimp only
  simp only [firstLiveChronologicalPrefix_get, appendLogicalCell, wholeLiveCell_input_eq]
  intro i
  exact ⟨trivial, trivial, RecordedQueueRun.recordService_le_capacity _ _ _, rfl⟩

/-- The generated continuation after an already detected overflow uses the
prescribed fixed arms, emits no arrivals or service, and preserves every
score and backlog. The original physical records remain present. -/
theorem appendLogicalCell_after_overflow {rate : RateInput p} (r : Record rate)
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (state : RecordedQueueRun.RunState p.K) (aux : AuxiliaryArray p)
    (hoverflow : state.overflow = true) :
    let entry := appendLogicalCell r cell state aux
    entry.slowSet = frozenSlowSet p ∧ entry.fastArm = frozenFastArm p ∧
      entry.proposal = false ∧ entry.nextSlowSet = frozenSlowSet p ∧
      ∀ i, entry.arrivals i = (false, 0) ∧ entry.service i = 0 ∧
        entry.after.registers i = state.registers i := by
  dsimp only
  simp only [appendLogicalCell, hoverflow, Bool.not_true, Bool.false_and, ite_true,
    true_and]
  intro i
  have h := RecordedQueueRun.step_after_overflow_preserves
    (ReferenceFirstLaunchNumericalCell.queueParameters rate) state cell.input hoverflow i
  exact ⟨h.2, by rw [h.2]; rfl, h.1⟩

/-- Before overflow the logical set is exactly the original full physical
assignment vector's image, whether or not its followers have confirmed. -/
theorem appendLogicalCell_actual_slow_set {rate : RateInput p} (r : Record rate)
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (state : RecordedQueueRun.RunState p.K) (aux : AuxiliaryArray p)
    (hoverflow : state.overflow = false) :
    (appendLogicalCell r cell state aux).slowSet =
      SnapshotRecordingKernel.assignmentSlowSet p cell.selected.view.payload.assignment := by
  simp only [appendLogicalCell, hoverflow, Bool.false_eq_true, ite_false]
  apply Subtype.ext
  exact cell.selected.view.payload.assignment_image.symm

/-- The clear PRE-state gate retains the actual proposal and the single
label-1 categorical residual, even if this update is the detecting overflow.
This is a pointwise construction identity, with no endpoint law premise. -/
theorem appendLogicalCell_proposal_refresh {rate : RateInput p} (r : Record rate)
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (state : RecordedQueueRun.RunState p.K) (aux : AuxiliaryArray p)
    (hoverflow : state.overflow = false)
    (hprop : FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time = true) :
    let entry := appendLogicalCell r cell state aux
    entry.proposal = true ∧
      entry.nextSlowSet = residualDraw rate state cell.input cell.selected.view.payload.anchor
        cell.selected.view.payload.anchor_pos (aux (r.input.time, 1)) ∧
      (∀ U : SlowSet p,
        0 ≤ RecordedSlowRefresh.residualMass p
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) state cell.input
          cell.selected.view.payload.anchor cell.selected.view.payload.anchor_pos U) ∧
      (∑ U : SlowSet p, RecordedSlowRefresh.residualMass p
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) state cell.input
        cell.selected.view.payload.anchor cell.selected.view.payload.anchor_pos U) = 1 := by
  dsimp only
  simp only [appendLogicalCell, hoverflow, hprop, Bool.not_false, Bool.true_and,
    Bool.false_eq_true, ite_false, ite_true, true_and]
  exact ⟨fun U => RecordedSlowRefresh.residualMass_nonneg p _ _ _ _ _ U,
    RecordedSlowRefresh.residualMass_sum_eq_one p _ _ _ _ _⟩

/-- The entire generated path ignores label 0; it remains reserved for the
later collection proposals. -/
theorem firstLiveChronologicalPrefix_auxiliary_ext (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (a b : AuxiliaryArray p)
    (hab : ∀ t : Fin p.T, a (t, 1) = b (t, 1)) :
    firstLiveChronologicalPrefix rate rewards C_star C_h (source, a) =
      firstLiveChronologicalPrefix rate rewards C_star C_h (source, b) := by
  apply List.ext_getElem
  · rw [firstLiveChronologicalPrefix_length, firstLiveChronologicalPrefix_length]
  · intro k hk hk'
    have hkw : k < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source).length := by
      simpa only [firstLiveChronologicalPrefix_length,
        ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hk
    simp only [firstLiveChronologicalPrefix_get rate rewards C_star C_h source a ⟨k, hkw⟩,
      firstLiveChronologicalPrefix_get rate rewards C_star C_h source b ⟨k, hkw⟩,
      appendLogicalCell, hab]

/-- Actual absence of launch produces the empty logical calendar prefix. -/
theorem firstLiveChronologicalPrefix_no_launch (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (aux : AuxiliaryArray p)
    (hc : (ReferenceCompletePhysicalHistory.generatedBoundary
      rate source rewards C_star C_h).crossing = none) :
    firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux) = [] := by
  apply List.eq_nil_iff_length_eq_zero.mpr
  rw [firstLiveChronologicalPrefix_length]
  exact (ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
    rate rewards C_star C_h source hc).2.2.1

/-- A terminal launch has no active calendar date, while remaining distinct
from the absent-launch event. -/
theorem firstLiveChronologicalPrefix_terminal (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (aux : AuxiliaryArray p)
    (hterminal : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h = p.T) :
    firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux) = [] := by
  apply List.eq_nil_iff_length_eq_zero.mpr
  rw [firstLiveChronologicalPrefix_length]
  have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate source rewards C_star C_h
  rw [hterminal, Nat.sub_self] at hrecords
  have hempty := List.eq_nil_iff_length_eq_zero.mpr hrecords
  simp only [ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength,
    ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow, hempty,
    ReferenceFirstLiveConfirmationHistory.firstLiveWindow, List.takeWhile_nil, List.length_nil]

private theorem cell_view_congr {rate : RateInput p} {r s : Record rate}
    (hrs : r = s) (a : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (b : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell s) :
    a.selected.view = b.selected.view := by
  cases hrs
  exact congrArg ReferenceActivePhysicalStep.Selection.view
    (Option.some.inj (a.selection_actual.symm.trans b.selection_actual))

/-- Actual calendar geometry and the full original selected row for each
generated live record. Earlier proposal coordinates are derived to be false;
there is no supplied successful-path or cutoff-correctness package. -/
theorem wholeLiveCell_geometry (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p)
    (k : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source).length) :
    let r := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source)[k.val]
    let cell := wholeLiveCell rate rewards C_star C_h source r (List.getElem_mem k.isLt)
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    r.input.row = source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) ∧
      cell.selected.view.payload.sigma.val = s ∧ r.input.time.val = s + k.val ∧
      r.input.time.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val
        cell.selected.view.payload.sigma ∧
      ∀ t : Fin p.T, s ≤ t.val → t.val < r.input.time.val →
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) t = false := by
  dsimp only
  by_cases hc : (ReferenceCompletePhysicalHistory.generatedBoundary
      rate source rewards C_star C_h).crossing.isSome = true
  · change (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true at hc
    let s : Fin (p.T + 1) :=
      ⟨ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h,
        Nat.lt_succ_of_le (ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate source rewards C_star C_h)⟩
    let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s.val :=
      ⟨source, hc, rfl⟩
    have hw := (ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
      rate rewards C_star C_h s x).1
    change ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source = _ at hw
    let k' : Fin (ReferenceFirstLiveOverflowReadout.firstLiveWindow rate rewards C_star C_h
        s.val (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x).length :=
      ⟨k.val, by
        have hk := k.isLt
        simpa only [hw] using hk⟩
    let span := ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h s.val
      (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x
    let a := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc (p.T - s.val) span k'
    have hrecord : (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source)[k.val] =
        (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate source rewards C_star C_h
          hc (p.T - s.val) span)[k'.val] := by
      have hget := congrArg (fun L => L[k.val]?) hw
      change (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source)[k.val]? = _ at hget
      have hk' : k.val < (ReferenceFirstLiveOverflowReadout.firstLiveWindow rate rewards C_star C_h
          s.val (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x).length := k'.isLt
      rw [List.getElem?_eq_getElem k.isLt, List.getElem?_eq_getElem hk'] at hget
      exact Option.some.inj hget
    have hv := cell_view_congr hrecord
      (wholeLiveCell rate rewards C_star C_h source _ (List.getElem_mem k.isLt)) a
    let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate source rewards C_star C_h hc
    have hg := ReferenceFirstLiveDownNumericalRecovery.first_live_geometry
      (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      s.val (p.T - s.val) span seed.activeAtStart seed.coordinatorFirst k'
      a.selected a.selection_actual
    have hf := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt_facts
      rate source rewards C_star C_h hc (p.T - s.val) span k'
    have hrow : ((ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate source rewards C_star C_h hc (p.T - s.val) span)[k'.val]).input.row =
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
      rw [ReferenceActivePhysicalStep.RoundInput.row, hf.1, hf.2.1]
    refine ⟨?_, ?_⟩
    · exact (congrArg (fun r : Record rate => r.input.row) hrecord).trans hrow
    · simpa only [hrecord, hv, s, k',
        ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
        ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
        ReferenceCompletePhysicalHistory.physicalStart,
        ReferenceCompletePhysicalHistory.generatedBoundary,
        ReferenceCompletePhysicalHistory.generatedInput] using hg
  · have hnone : (ReferenceCompletePhysicalHistory.generatedBoundary
        rate source rewards C_star C_h).crossing = none := by
      cases h : (ReferenceCompletePhysicalHistory.generatedBoundary
        rate source rewards C_star C_h).crossing <;> simp_all
    have hw := (ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
      rate rewards C_star C_h source hnone).1
    exact False.elim (Nat.not_lt_zero k.val
      (k.isLt.trans_le (congrArg List.length hw).le))

/-- Any proposal before a later generated live date is false. Hence the
first-live constructor can consume a residual coordinate only at its final
calendar cell. This includes grid/proposal ties without discarding that cell. -/
theorem firstLiveChronologicalPrefix_earlier_proposal (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (aux : AuxiliaryArray p)
    (j k : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source).length) (hjk : j.val < k.val) :
    ((firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux))[j.val]'(by
      rw [firstLiveChronologicalPrefix_length]; exact j.isLt)).proposal = false := by
  have hj := wholeLiveCell_geometry rate rewards C_star C_h source j
  have hk := wholeLiveCell_geometry rate rewards C_star C_h source k
  have hbit := hk.2.2.2.2
    ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source)[j.val]).input.time
    (by rw [hj.2.2.1]; exact Nat.le_add_right _ _)
    (by rw [hj.2.2.1, hk.2.2.1]; exact Nat.add_lt_add_left hjk _)
  simp only [firstLiveChronologicalPrefix_get, appendLogicalCell, hj.1, hbit, Bool.and_false]

/-- Changing any auxiliary coordinates leaves every strict predecessor of a
later live date unchanged. The already generated path itself is retained. -/
theorem firstLiveChronologicalPrefix_take_auxiliary_ext (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (a b : AuxiliaryArray p)
    (n : ℕ) (hn : n < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source).length) :
    (firstLiveChronologicalPrefix rate rewards C_star C_h (source, a)).take n =
      (firstLiveChronologicalPrefix rate rewards C_star C_h (source, b)).take n := by
  apply List.ext_getElem
  · simp only [List.length_take, firstLiveChronologicalPrefix_length]
  · intro j hj hj'
    have hjn : j < n := lt_of_lt_of_le hj (List.length_take_le ..)
    have hjW : j < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source).length := hjn.trans hn
    have hg := wholeLiveCell_geometry rate rewards C_star C_h source ⟨j, hjW⟩
    have hk := wholeLiveCell_geometry rate rewards C_star C_h source ⟨n, hn⟩
    have hbit := hk.2.2.2.2
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source)[j]).input.time
      (by rw [hg.2.2.1]; exact Nat.le_add_right _ _)
      (by rw [hg.2.2.1, hk.2.2.1]; exact Nat.add_lt_add_left hjn _)
    simp only [List.getElem_take,
      firstLiveChronologicalPrefix_get rate rewards C_star C_h source a ⟨j, hjW⟩,
      firstLiveChronologicalPrefix_get rate rewards C_star C_h source b ⟨j, hjW⟩,
      appendLogicalCell, hg.1, hbit, Bool.and_false, Bool.false_eq_true, ite_false]

/-- The entire generated path uses at most the final cell's label-1 scalar.
All previous cells are the same actual constructed prefix for arbitrary
changes to every auxiliary coordinate. -/
theorem firstLiveChronologicalPrefix_last_auxiliary_ext (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (a b : AuxiliaryArray p)
    (last : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source).length)
    (hlast : last.val + 1 = (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source).length)
    (hab : a (((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source)[last.val]).input.time, 1) =
      b (((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source)[last.val]).input.time, 1)) :
    firstLiveChronologicalPrefix rate rewards C_star C_h (source, a) =
      firstLiveChronologicalPrefix rate rewards C_star C_h (source, b) := by
  apply List.ext_getElem
  · rw [firstLiveChronologicalPrefix_length, firstLiveChronologicalPrefix_length]
  · intro j hj hj'
    have hjW : j < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source).length := by
      simpa only [firstLiveChronologicalPrefix_length,
        ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hj
    by_cases hjlast : j = last.val
    · subst j
      simp only [firstLiveChronologicalPrefix_get, appendLogicalCell, hab]
    · have hjlt : j < last.val := by omega
      have heq := firstLiveChronologicalPrefix_take_auxiliary_ext
        rate rewards C_star C_h source a b last.val last.isLt
      have hget := congrArg (fun L => L[j]?) heq
      have hja : j < ((firstLiveChronologicalPrefix
          rate rewards C_star C_h (source, a)).take last.val).length := by
        simp only [List.length_take, firstLiveChronologicalPrefix_length,
          ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength]
        omega
      have hjb : j < ((firstLiveChronologicalPrefix
          rate rewards C_star C_h (source, b)).take last.val).length := by
        simp only [List.length_take, firstLiveChronologicalPrefix_length,
          ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength]
        omega
      simpa only [List.getElem?_eq_getElem hja, List.getElem?_eq_getElem hjb,
        Option.some.injEq, List.getElem_take] using hget

/-- The actual generated pre-state weights obey the source episode envelope,
derived from the physical calendar grid and zero-origin bounded service. -/
theorem firstLiveChronologicalPrefix_weight_envelope (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (aux : AuxiliaryArray p)
    (k : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source).length) (i : Fin p.K) :
    let entry := (firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux))[k.val]'(by
      rw [firstLiveChronologicalPrefix_length]; exact k.isLt)
    1 ≤ RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        entry.before i ∧
      RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        entry.before i < 2 := by
  have hg := wholeLiveCell_geometry rate rewards C_star C_h source k
  let sigma := (wholeLiveCell rate rewards C_star C_h source
    ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source)[k.val]) (List.getElem_mem k.isLt)).selected.view.payload.sigma
  let H := ReplayWeightStability.episodeHorizon rate.eta.val
  have hgrid := hg.2.2.2.1
  rw [FollowerCutoffScan.gridBoundary] at hgrid
  have hgrid' := hgrid.trans (Nat.min_le_right _ _)
  have hdiv := Nat.mod_add_div (sigma.val + 1) H
  have htime := hg.2.2.1
  have hsigma := hg.2.1
  have hsteps : k.val ≤ H := by
    change _ ≤ H * ((sigma.val + 1) / H + 1) at hgrid'
    rw [Nat.mul_add, Nat.mul_one] at hgrid'
    change sigma.val = _ at hsigma
    omega
  have hlen : ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h source).take k.val).length ≤ H :=
    (List.length_take_le ..).trans hsteps
  have he := RecordedEpisodeStability.execute_source_weight_envelope
    (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (RecordedQueueRun.initialState p.K)
    ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h source).take k.val) i hlen
  dsimp only
  simp only [firstLiveChronologicalPrefix_get, appendLogicalCell]
  simpa only [RecordedQueueRun.run, RecordedQueueRun.scoreWeight,
    RecordedQueueRun.initialState, ScoreWeights.scoreWeight, pow_zero, mul_one] using
      And.intro he.1 he.2.1

/-- The generated queue flags and registers retain exactly the inclusive
first-overflow prefix of the SAME whole numerical stream. -/
theorem firstLiveChronologicalPrefix_stopped_replay (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (aux : AuxiliaryArray p)
    (k : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source).length) :
    let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
    let cells := ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h source
    let entry := (firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux))[k.val]'(by
      rw [firstLiveChronologicalPrefix_length]; exact k.isLt)
    let cutoff := UnstoppedRecordedQueueComparison.firstOverflowPrefix q cells
    (entry.before.overflow = true ↔ cutoff ≤ k.val) ∧
      (entry.after.overflow = true ↔ cutoff ≤ k.val + 1) ∧
      ∀ i : Fin p.K, entry.after.registers i =
        UnstoppedRecordedQueueComparison.unstoppedReplay q cells (min (k.val + 1) cutoff) i := by
  dsimp only
  obtain ⟨hbefore, hafter⟩ := firstLiveChronologicalPrefix_queue_states
    rate rewards C_star C_h source aux k
  rw [hbefore, hafter]
  have hk : k.val + 1 ≤ (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h source).length := by
    rw [wholeFirstLiveCells_length]
    exact k.isLt
  have hb := UnstoppedRecordedQueueComparison.prefix_state_comparison
    (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h source)
    k.val (by omega)
  have ha := UnstoppedRecordedQueueComparison.prefix_state_comparison
    (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h source)
    (k.val + 1) hk
  exact ⟨hb.2, ha.2, ha.1⟩

/-- When the physical choice actually uses FAST, its arm is exactly the
reserved draw already stored by this constructor; no scalar is redrawn. -/
theorem reservedFastArm_eq_selected_of_empty {rate : RateInput p} (r : Record rate)
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (hempty : cell.selected.view.pendingAtChoice = ∅) :
    (reservedFastArm r cell).val = cell.selected.arm := by
  have hfast := CoordinatorLocalArmChoice.coordinatorArmChoiceCore_live_empty
    cell.selected.view.payload cell.selected.view.pendingAtChoice cell.selected.view.cutoff
    r.input.time cell.selected.view.complementWeights (r.input.row.2 r.input.time)
    cell.choiceInputsValid cell.assignment_live hempty
  have hchoice := cell.selected.choice_eq
  change CoordinatorLocalArmChoice.coordinatorArmChoiceCore _ _ _ _ _ _ = _ at hchoice
  exact Option.some.inj (hfast.symm.trans hchoice)

/-- At the inclusive retained endpoint, the generated ALL-arm numerical
state gives the actual coordinator's complete complement registers. The
physical run is the original run and continues after this boundary. -/
theorem firstLiveChronologicalPrefix_inclusive_physical_complement
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p) (aux : AuxiliaryArray p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hpositive : 0 < ReferenceFirstLiveOverflowReadout.wholeFirstLiveInclusiveCount
      rate rewards C_star C_h source) :
    let b := ReferenceFirstLiveOverflowReadout.wholeFirstLiveInclusiveCount
      rate rewards C_star C_h source
    let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
    let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate source rewards C_star C_h hc
    let entry := (firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux))[b - 1]'(by
      rw [firstLiveChronologicalPrefix_length]
      exact (Nat.sub_lt hpositive (by decide : 0 < 1)).trans_le (Nat.min_le_left _ _))
    ∃ hspan : start + b ≤ p.T,
      ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
        (base : Fin (p.m - 1) → ℕ),
        (ReferenceActivePhysicalHorizon.run initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start b
          hspan seed.activeAtStart).finalState.coordinator = .live r owned base ∧
        (∀ i, base i = 0) ∧
        ∀ a : CanonicalFastSampling.FastArm r.payload.slowSet,
          (r.complementScores a, owned.queue a) = entry.after.registers a.val := by
  let s : Fin (p.T + 1) :=
    ⟨ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h,
      Nat.lt_succ_of_le (ReferenceCompletePhysicalHistory.physicalStart_le_T
        rate source rewards C_star C_h)⟩
  let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s.val :=
    ⟨source, hc, rfl⟩
  have hread := ReferenceFirstLiveOverflowReadout.wholeFirstLive_readouts_on_fiber
    rate rewards C_star C_h s x
  have hcount : ReferenceFirstLiveOverflowReadout.firstLiveInclusiveCount rate rewards C_star C_h
      s.val (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x =
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveInclusiveCount
        rate rewards C_star C_h source := hread.2.2.2.1.symm
  have hboundary := ReferenceFirstLiveOverflowReadout.firstLiveInclusive_common_boundary
    rate rewards C_star C_h s.val (p.T - s.val)
    (ReferenceFirstLiveOverflowReadout.maximal_span s) x
  dsimp only at hboundary
  simp only [hcount] at hboundary
  obtain ⟨hspan, hboundary⟩ := hboundary
  obtain ⟨r, owned, base, hcoord, _hsigma, _hn, hbase, _hbirth, hcomp, _hrest⟩ :=
    hboundary.2 hpositive
  dsimp only
  refine ⟨hspan, r, owned, base, hcoord, hbase, ?_⟩
  intro a
  have hbc : ReferenceFirstLiveOverflowReadout.wholeFirstLiveInclusiveCount
      rate rewards C_star C_h source ≤
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source).length := Nat.min_le_left _ _
  let k : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source).length :=
    ⟨ReferenceFirstLiveOverflowReadout.wholeFirstLiveInclusiveCount
      rate rewards C_star C_h source - 1, (Nat.sub_lt hpositive (by decide : 0 < 1)).trans_le hbc⟩
  have hafter := (firstLiveChronologicalPrefix_queue_states
    rate rewards C_star C_h source aux k).2
  have hsucc : k.val + 1 = ReferenceFirstLiveOverflowReadout.wholeFirstLiveInclusiveCount
      rate rewards C_star C_h source := Nat.sub_add_cancel hpositive
  have hcells := (ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
    rate rewards C_star C_h s x).2
  change ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
    rate rewards C_star C_h source = _ at hcells
  have hrun :
      RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        ((ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate source rewards C_star C_h hc
          (p.T - s.val)
          (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h s.val
            (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x)).take
          (ReferenceFirstLiveOverflowReadout.wholeFirstLiveInclusiveCount
            rate rewards C_star C_h source)) =
      ((firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux))[k.val]'(by
        rw [firstLiveChronologicalPrefix_length]; exact k.isLt)).after := by
    rw [hsucc] at hafter
    rw [hcells] at hafter
    exact hafter.symm
  exact (hcomp a).1.trans (congrArg (fun state : RecordedQueueRun.RunState p.K =>
    state.registers a.val) hrun)

/-- The complete numerical-cell witness is unique, including every actual
ordinary follower state and memory. Thus the constructor's classical witness
selection cannot change any generated field. -/
theorem actualLiveSourceCell_unique {rate : RateInput p} (r : Record rate)
    (a b : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r) : a = b := by
  have hstates : a.states = b.states := by
    funext i
    have h := (a.ordinary i).symm.trans (b.ordinary i)
    exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj h).1
  have hmemories : a.memories = b.memories := by
    funext i
    have h := (a.ordinary i).symm.trans (b.ordinary i)
    exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj h).2
  have hselected : a.selected = b.selected :=
    Option.some.inj (a.selection_actual.symm.trans b.selection_actual)
  have hinput := cell_input_congr rfl a b
  cases a
  cases b
  dsimp only at hstates hmemories hselected hinput
  cases hstates
  cases hmemories
  cases hselected
  cases hinput
  rfl

/-- On an actual positive proposal with a clear PRE-state, the source-derived
residual is consumed at the final date of the finite live window. The endpoint
may be the first pre-round cutoff or the horizon; this does not assert that a
cutoff occurs. The old path and weights exclude the consumed scalar. No
residual distribution, normalizer, score identity or history is supplied. -/
theorem firstLiveChronologicalPrefix_finite_window_endpoint_triggering_residual
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p) (aux : AuxiliaryArray p)
    (k : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source).length)
    (hclear : (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
        rate rewards C_star C_h source).take k.val)).overflow = false)
    (hprop : FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source)[k.val]).input.time = true) :
    let r := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source)[k.val]
    let cell := wholeLiveCell rate rewards C_star C_h source r (List.getElem_mem k.isLt)
    let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
    let state := RecordedQueueRun.run q
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h source).take k.val)
    let entry := (firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux))[k.val]'(by
      rw [firstLiveChronologicalPrefix_length]; exact k.isLt)
    k.val + 1 = (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source).length ∧
      r.input.time.val + 1 = ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h +
        (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h source).length ∧
      entry.proposal = true ∧
      entry.nextSlowSet = residualDraw rate state cell.input cell.selected.view.payload.anchor
        cell.selected.view.payload.anchor_pos (aux (r.input.time, 1)) ∧
      (∀ U : SlowSet p,
        0 ≤ RecordedSlowRefresh.residualMass p q state cell.input
          cell.selected.view.payload.anchor cell.selected.view.payload.anchor_pos U) ∧
      (∑ U : SlowSet p, RecordedSlowRefresh.residualMass p q state cell.input
        cell.selected.view.payload.anchor cell.selected.view.payload.anchor_pos U) = 1 ∧
      ∀ a b : AuxiliaryArray p,
        (firstLiveChronologicalPrefix rate rewards C_star C_h (source, a)).take k.val =
          (firstLiveChronologicalPrefix rate rewards C_star C_h (source, b)).take k.val := by
  have hg := wholeLiveCell_geometry rate rewards C_star C_h source k
  have hrprop : FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source)[k.val]).input.row
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source)[k.val]).input.time = true := by
    rw [hg.1]
    exact hprop
  have hrefresh := appendLogicalCell_proposal_refresh
    ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source)[k.val])
    (wholeLiveCell rate rewards C_star C_h source _ (List.getElem_mem k.isLt))
    (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
        rate rewards C_star C_h source).take k.val)) aux hclear hrprop
  have hentry : ((firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux))[k.val]'(by
      rw [firstLiveChronologicalPrefix_length]; exact k.isLt)).proposal = true := by
    simp only [firstLiveChronologicalPrefix_get]
    exact hrefresh.1
  have hlast : k.val + 1 = (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source).length := by
    by_contra hne
    have hlt : k.val + 1 < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source).length := by have hk := k.isLt; omega
    have hfalse := firstLiveChronologicalPrefix_earlier_proposal
      rate rewards C_star C_h source aux k ⟨k.val + 1, hlt⟩ (Nat.lt_succ_self k.val)
    rw [hentry] at hfalse
    cases hfalse
  dsimp only
  refine ⟨hlast, ?_, hentry, ?_, hrefresh.2.2.1, hrefresh.2.2.2, ?_⟩
  · calc
      _ = (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + k.val) + 1 :=
        congrArg (fun n => n + 1) hg.2.2.1
      _ = ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + (k.val + 1) :=
        Nat.add_assoc _ _ _
      _ = _ := congrArg (fun n =>
        ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + n) hlast
  · simp only [firstLiveChronologicalPrefix_get]
    exact hrefresh.2.1
  · intro a b
    exact firstLiveChronologicalPrefix_take_auxiliary_ext
      rate rewards C_star C_h source a b k.val k.isLt

/-- All fields through the proposal, strictly before the residual refresh. -/
abbrev BeforeRefreshReadout (p : Parameters) (rate : RateInput p) :=
  Fin p.T × ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) ×
    ReferenceFirstLiveOverflowReadout.NumericalCellReadout p ×
    RecordedQueueRun.RunState p.K × RecordedQueueRun.RunState p.K ×
    (Fin p.K → Bool × ℕ) × (Fin p.K → ℕ) × SlowSet p × Fin p.K × Bool

/-- Literal projection of the generated cell before its residual refresh. -/
def LogicalCell.beforeRefreshFields {rate : RateInput p} (entry : LogicalCell p rate) :
    BeforeRefreshReadout p rate :=
  (entry.time, entry.physical, entry.numerical, entry.before, entry.after,
    entry.arrivals, entry.service, entry.slowSet, entry.fastArm, entry.proposal)

/-- Even the final detecting update and proposal, before its refresh, use no
auxiliary coordinate. This is a projection of the actual constructed path. -/
theorem firstLiveChronologicalPrefix_beforeRefresh_auxiliary_ext
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p) (a b : AuxiliaryArray p) :
    (firstLiveChronologicalPrefix rate rewards C_star C_h (source, a)).map
        LogicalCell.beforeRefreshFields =
      (firstLiveChronologicalPrefix rate rewards C_star C_h (source, b)).map
        LogicalCell.beforeRefreshFields := by
  apply List.ext_getElem
  · simp only [List.length_map, firstLiveChronologicalPrefix_length]
  · intro k hk hk'
    have hkw : k < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source).length := by
      simpa only [List.length_map, firstLiveChronologicalPrefix_length,
        ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hk
    simp only [List.getElem_map,
      firstLiveChronologicalPrefix_get rate rewards C_star C_h source a ⟨k, hkw⟩,
      firstLiveChronologicalPrefix_get rate rewards C_star C_h source b ⟨k, hkw⟩,
      LogicalCell.beforeRefreshFields, appendLogicalCell]

/-- Birth initializes the actual assignment's canonical image and the same
zero score/backlog state; the reserved physical fast scalar is already used
for the logical fast arm on this first calendar date. -/
theorem firstLiveChronologicalPrefix_birth (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (aux : AuxiliaryArray p)
    (hpositive : 0 < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source).length) :
    let r := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source)[0]
    let cell := wholeLiveCell rate rewards C_star C_h source r (List.getElem_mem hpositive)
    let entry := (firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux))[0]'(by
      rw [firstLiveChronologicalPrefix_length]; exact hpositive)
    entry.before = RecordedQueueRun.initialState p.K ∧
      entry.slowSet = SnapshotRecordingKernel.assignmentSlowSet p cell.selected.view.payload.assignment ∧
      entry.fastArm = (reservedFastArm r cell).val := by
  dsimp only
  have hget := firstLiveChronologicalPrefix_get rate rewards C_star C_h source aux ⟨0, hpositive⟩
  simp only [hget, List.take_zero, RecordedQueueRun.run, RecordedQueueRun.execute]
  refine ⟨rfl, ?_, rfl⟩
  exact appendLogicalCell_actual_slow_set _ _ _ _ rfl

end Bandits.Support.ReferenceFirstLiveChronologicalPrefixFoundation

end
