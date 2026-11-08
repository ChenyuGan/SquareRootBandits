/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveNumericalFastPersistence
public import Bandits.Support.ReferenceFirstLivePostUpdateProposalLaw
public import Bandits.Support.ReferenceContinuingRecordingFastLaw

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Tactic

/-!
# Canonical recorder, reserved FAST and proposal laws on the actual first-LIVE source

On the two existing positive-offset branches, identify the physical marker and
reserved FAST readouts with the correlated canonical pair at the ALL-arm
numerical weights. The localizer is the computed strict-past overflow flag;
the detecting current update and proposal remain included. Restore the pair
against arbitrary remainder/affine tests and the full pre-proposal readout
against every nonproposal control on the original finite unnormalized sources.

Sources: `sources/zip4/manuscript/06_interruptions.tex:381-397`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:142-215,323-366`, and
`sources/zip4/manuscript/08_main_theorem.tex:78-109`.

These are scoped internal laws, not an acquired physical-history law, a whole
logical-path induction, or a manuscript closure claim.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Bandits.Support.ReferenceFirstLiveCanonicalProposalJointLaw

open ReferenceFirstLivePostUpdateProposalLaw

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

/-- The continuing original-source restriction, with an arbitrary bounded
Borel test of the retained remainder, all nonproposal controls, and the actual
preproposal readout. The multiplier is the computed PRE-round strict-past
overflow flag, so the detecting current update remains in the readout. -/
theorem continuingSource_clearProposal_integral (_hpos : s < t.val)
    (F : ((LiveRemainder rate rewards C_star C_h q t s hs control0 ×
      PropRestControl p) ×
      (Option (Fin p.K) × (Option (Fin p.K) × NumericalUpdateFields p))) → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ y, ‖F y‖ ≤ C) :
    let split := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
      rate rewards C_star C_h q t s hs control0
    let obs := fun z => liveNonpropObservation rate rewards C_star C_h q t s hs control0
      (.inl (split z).1, (proposalControlSplit p (split z).2).2)
    let μ := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
      rate rewards C_star C_h q t s hs control0
    Integrable (fun z =>
      (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
        (obs z).1.1).2.1 = false then F (obs z) else 0)) μ ∧
    Integrable (fun z =>
      (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
        (obs z).1.1).2.1 = false then F (obs z) else 0) *
        (if physicalProposalBit rate (split z).2 = true then 1 else 0)) μ ∧
    (∫ z,
      (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
        (obs z).1.1).2.1 = false then F (obs z) else 0) *
        (if physicalProposalBit rate (split z).2 = true then 1 else 0) ∂μ) =
      FollowerCutoffScan.proposalHazard p rate.eta.val *
        (∫ z,
          (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
            (obs z).1.1).2.1 = false then F (obs z) else 0) ∂μ) := by
  let split := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
    rate rewards C_star C_h q t s hs control0
  let obs := fun z => liveNonpropObservation rate rewards C_star C_h q t s hs control0
    (.inl (split z).1, (proposalControlSplit p (split z).2).2)
  let μ := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
    rate rewards C_star C_h q t s hs control0
  let clear : ((LiveRemainder rate rewards C_star C_h q t s hs control0 ×
      PropRestControl p) ×
      (Option (Fin p.K) × (Option (Fin p.K) × NumericalUpdateFields p))) → Prop :=
    fun y => (liveNumericalPast rate rewards C_star C_h q t s hs control0
      y.1.1).2.1 = false
  let G := fun y => if clear y then F y else 0
  have hPast : Measurable (fun y : ((LiveRemainder rate rewards C_star C_h q t s hs control0 ×
      PropRestControl p) ×
      (Option (Fin p.K) × (Option (Fin p.K) × NumericalUpdateFields p))) =>
      liveNumericalPast rate rewards C_star C_h q t s hs control0 y.1.1) := by
    exact (measurable_liveNumericalPast rate rewards C_star C_h q t s hs control0).comp
      (measurable_fst.comp measurable_fst)
  have hOverflow : Measurable (fun y : ((LiveRemainder rate rewards C_star C_h q t s hs control0 ×
      PropRestControl p) ×
      (Option (Fin p.K) × (Option (Fin p.K) × NumericalUpdateFields p))) =>
      (liveNumericalPast rate rewards C_star C_h q t s hs control0 y.1.1).2.1) := by
    exact measurable_fst.comp (measurable_snd.comp hPast)
  have hClearSet : MeasurableSet {y | clear y} :=
    measurableSet_eq_fun hOverflow measurable_const
  have hG : Measurable G := Measurable.ite hClearSet hF measurable_const
  have hGbound : ∀ y, ‖G y‖ ≤ C + 1 := by
    intro y
    by_cases hy : clear y
    · simp only [G, hy, ↓reduceIte]
      exact le_trans (hC y) (by linarith)
    · simp only [G, hy, ↓reduceIte, norm_zero]
      have hCnonneg : 0 ≤ C := le_trans (norm_nonneg (F y)) (hC y)
      linarith
  have hsource :=
    ReferenceFirstLivePostUpdateProposalLaw.continuingSource_actualUpdate_integral
      rate rewards C_star C_h q t s hs control0 _hpos G hG (C + 1) hGbound
  refine ⟨?_, ?_, ?_⟩
  · simpa only [μ, obs, split, G, clear] using hsource.1
  · simpa only [μ, obs, split, G, clear] using hsource.2.1
  · simpa only [μ, obs, split, G, clear] using hsource.2.2

/-- The empty-pending original-source restriction has the same bounded-test
proposal identity, retaining its own source remainder, every nonproposal
coordinate, and the full actual numerical update. -/
theorem emptySource_clearProposal_integral (_hpos : s < t.val)
    (F : ((LiveRemainder rate rewards C_star C_h q t s hs control0 ×
      PropRestControl p) ×
      (Option (Fin p.K) × (Option (Fin p.K) × NumericalUpdateFields p))) → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ y, ‖F y‖ ≤ C) :
    let split := ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
      rate rewards C_star C_h q t s hs control0
    let obs := fun z => liveNonpropObservation rate rewards C_star C_h q t s hs control0
      (.inr (split z).1, (proposalControlSplit p (split z).2).2)
    let μ := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
      rate rewards C_star C_h q t s hs control0
    Integrable (fun z =>
      (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
        (obs z).1.1).2.1 = false then F (obs z) else 0)) μ ∧
    Integrable (fun z =>
      (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
        (obs z).1.1).2.1 = false then F (obs z) else 0) *
        (if physicalProposalBit rate (split z).2 = true then 1 else 0)) μ ∧
    (∫ z,
      (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
        (obs z).1.1).2.1 = false then F (obs z) else 0) *
        (if physicalProposalBit rate (split z).2 = true then 1 else 0) ∂μ) =
      FollowerCutoffScan.proposalHazard p rate.eta.val *
        (∫ z,
          (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
            (obs z).1.1).2.1 = false then F (obs z) else 0) ∂μ) := by
  let split := ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
    rate rewards C_star C_h q t s hs control0
  let obs := fun z => liveNonpropObservation rate rewards C_star C_h q t s hs control0
    (.inr (split z).1, (proposalControlSplit p (split z).2).2)
  let μ := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
    rate rewards C_star C_h q t s hs control0
  let clear : ((LiveRemainder rate rewards C_star C_h q t s hs control0 ×
      PropRestControl p) ×
      (Option (Fin p.K) × (Option (Fin p.K) × NumericalUpdateFields p))) → Prop :=
    fun y => (liveNumericalPast rate rewards C_star C_h q t s hs control0
      y.1.1).2.1 = false
  let G := fun y => if clear y then F y else 0
  have hPast : Measurable (fun y : ((LiveRemainder rate rewards C_star C_h q t s hs control0 ×
      PropRestControl p) ×
      (Option (Fin p.K) × (Option (Fin p.K) × NumericalUpdateFields p))) =>
      liveNumericalPast rate rewards C_star C_h q t s hs control0 y.1.1) := by
    exact (measurable_liveNumericalPast rate rewards C_star C_h q t s hs control0).comp
      (measurable_fst.comp measurable_fst)
  have hOverflow : Measurable (fun y : ((LiveRemainder rate rewards C_star C_h q t s hs control0 ×
      PropRestControl p) ×
      (Option (Fin p.K) × (Option (Fin p.K) × NumericalUpdateFields p))) =>
      (liveNumericalPast rate rewards C_star C_h q t s hs control0 y.1.1).2.1) := by
    exact measurable_fst.comp (measurable_snd.comp hPast)
  have hClearSet : MeasurableSet {y | clear y} :=
    measurableSet_eq_fun hOverflow measurable_const
  have hG : Measurable G := Measurable.ite hClearSet hF measurable_const
  have hGbound : ∀ y, ‖G y‖ ≤ C + 1 := by
    intro y
    by_cases hy : clear y
    · simp only [G, hy, ↓reduceIte]
      exact le_trans (hC y) (by linarith)
    · simp only [G, hy, ↓reduceIte, norm_zero]
      have hCnonneg : 0 ≤ C := le_trans (norm_nonneg (F y)) (hC y)
      linarith
  have hsource :=
    ReferenceFirstLivePostUpdateProposalLaw.emptySource_actualUpdate_integral
      rate rewards C_star C_h q t s hs control0 _hpos G hG (C + 1) hGbound
  refine ⟨?_, ?_, ?_⟩
  · simpa only [μ, obs, split, G, clear] using hsource.1
  · simpa only [μ, obs, split, G, clear] using hsource.2.1
  · simpa only [μ, obs, split, G, clear] using hsource.2.2

open ReferenceFirstWindowNumericalStream
open ReferenceFirstLiveRecordingReadoutMeasurability
open ReferenceFirstLiveOverflowReadout

private theorem actualCell_input_congr
    {left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (h : left = right) (a : ActualLiveSourceCell left) (b : ActualLiveSourceCell right) :
    a.input = b.input := by
  cases h
  exact actualLiveSourceCell_input_unique left a b

/-- Truncating the actual physical horizon truncates its numerical inputs at
exactly the same calendar position. Cell choices are reconciled by uniqueness. -/
theorem actualLiveSourceCells_take
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (left right : ℕ) (hle : left ≤ right)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + right ≤ p.T) :
    actualLiveSourceCells rate source rewards C_star C_h hc left ((Nat.add_le_add_left hle _).trans hspan) =
      (actualLiveSourceCells rate source rewards C_star C_h hc right hspan).take left := by
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let seed := actualFirstLiveSeed rate source rewards C_star C_h hc
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  have hrecords : (actualFirstLiveRun rate source rewards C_star C_h hc right hspan).records.take left =
      (actualFirstLiveRun rate source rewards C_star C_h hc left (by omega)).records := by
    obtain ⟨tail, htail⟩ := ReferenceCollectionPhaseHistory.run_records_prefix initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start left (right - left)
      (by dsimp only [start]; omega) seed.activeAtStart
    have hcount : left + (right - left) = right := by omega
    simp only [hcount] at htail
    change (ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start right hspan
      seed.activeAtStart).records.take left = _
    rw [htail, List.take_append_of_le_length]
    · have hlen := ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start left
        (by omega) seed.activeAtStart
      simpa only [hlen, actualFirstLiveRun, initial, seed, start] using (List.take_length
        (l := (ReferenceActivePhysicalHorizon.run initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start left
          (by omega) seed.activeAtStart).records))
    · rw [ReferenceActivePhysicalHorizon.run_record_count]
  have hwindow : actualFirstLiveWindow rate source rewards C_star C_h hc left (by omega) =
      (actualFirstLiveWindow rate source rewards C_star C_h hc right hspan).take left := by
    simp only [actualFirstLiveWindow, ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
      List.take_takeWhile, hrecords]
  apply List.ext_getElem
  · rw [actualLiveSourceCells_length, List.length_take, actualLiveSourceCells_length, hwindow,
      List.length_take]
  · intro j hj hj'
    have hjSmall : j < (actualFirstLiveWindow rate source rewards C_star C_h hc left (by omega)).length := by
      simpa only [actualLiveSourceCells_length] using hj
    have hjBig : j < (actualFirstLiveWindow rate source rewards C_star C_h hc right hspan).length := by
      rw [hwindow, List.length_take] at hjSmall
      omega
    rw [List.getElem_take]
    rw [actualLiveSourceCells_get rate source rewards C_star C_h hc left (by omega) ⟨j, hjSmall⟩,
      actualLiveSourceCells_get rate source rewards C_star C_h hc right hspan ⟨j, hjBig⟩]
    apply actualCell_input_congr rate
    rw [getElem_congr_coll hwindow, List.getElem_take]

/-- Both actual positive-offset branches select the same whole-source
calendar index. Their numerical strict past is literally the whole-list prefix. -/
theorem source_whole_prefix_alignment
    (tagged : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
        rate rewards C_star C_h q t s hs control0 ⊕
      ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0) :
    let z := Sum.elim Subtype.val Subtype.val tagged
    let source := z.val
    let n := t.val - s
    ∃ hk : n < (wholeFirstLiveWindow rate rewards C_star C_h source).length,
      (wholeFirstLiveWindow rate rewards C_star C_h source)[n]'hk =
        ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
          rate rewards C_star C_h q t s hs control0 z ∧
      n < (wholeFirstLiveCells rate rewards C_star C_h source).length ∧
      (wholeFirstLiveCells rate rewards C_star C_h source).take n =
        actualLiveSourceCells rate source rewards C_star C_h z.property.2.1 n (by
          have he := z.property.2.2
          change ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s at he
          rw [he]
          omega) := by
  intro z source n
  have he : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s :=
    z.property.2.2
  have hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true :=
    z.property.2.1
  let s0 : Fin (p.T + 1) := ⟨s, by omega⟩
  let fiber : LaunchFiber rate rewards C_star C_h s := ⟨source, hc, he⟩
  let span : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
        (p.T - s) ≤ p.T := by rw [he]; omega
  have hwhole := wholeFirstLive_on_fiber rate rewards C_star C_h s0 fiber
  have hwindow : wholeFirstLiveWindow rate rewards C_star C_h source =
      actualFirstLiveWindow rate source rewards C_star C_h hc (p.T - s) span := hwhole.1
  have hcells : wholeFirstLiveCells rate rewards C_star C_h source =
      actualLiveSourceCells rate source rewards C_star C_h hc (p.T - s) span := hwhole.2
  have hcurrent : ∃ hn : n < (actualFirstLiveWindow rate source rewards C_star C_h hc
        (n + 1) (by rw [he]; dsimp only [n]; omega)).length,
      (actualFirstLiveWindow rate source rewards C_star C_h hc (n + 1)
        (by rw [he]; dsimp only [n]; omega))[n]'hn =
        ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
          rate rewards C_star C_h q t s hs control0 z := by
    cases tagged with
    | inl point => exact (ReferenceFirstLiveSourceCellReadout.source_current_window
        rate rewards C_star C_h q t s hs control0 point).2.2
    | inr point =>
        exact ReferenceFirstLiveEmptyPendingSourceMoments.currentOriginalWindowIndex
          rate rewards C_star C_h q t s hs control0 point
  obtain ⟨hn, hrecord⟩ := hcurrent
  have htake := actualLiveSourceCells_take rate rewards C_star C_h source
    hc (n + 1) (p.T - s) (by dsimp only [n]; omega) span
  have hlength := congrArg List.length htake
  simp only [actualLiveSourceCells_length, List.length_take] at hlength
  have hnBig : n < (actualFirstLiveWindow rate source rewards C_star C_h hc
      (p.T - s) span).length := by omega
  have hwindowTake : (actualFirstLiveWindow rate source rewards C_star C_h hc
      (p.T - s) span).take (n + 1) =
      actualFirstLiveWindow rate source rewards C_star C_h hc (n + 1)
        (by rw [he]; dsimp only [n]; omega) := by
    calc
      _ = (wholeFirstLiveWindow rate rewards C_star C_h source).take (n + 1) :=
        congrArg (fun records => records.take (n + 1)) hwindow.symm
      _ = firstLiveWindow rate rewards C_star C_h s (n + 1) (by dsimp only [n]; omega) fiber := by
        rw [firstLiveWindow_eq_completeSuffix_take]
        exact List.take_takeWhile
  have hnWhole : n < (wholeFirstLiveWindow rate rewards C_star C_h source).length := by
    simpa only [hwindow] using hnBig
  have hnTake : n < ((actualFirstLiveWindow rate source rewards C_star C_h hc
      (p.T - s) span).take (n + 1)).length := by
    rw [List.length_take]
    omega
  refine ⟨hnWhole, ?_, ?_, ?_⟩
  · exact (getElem_congr_coll (i := n) (w := hnWhole) hwindow).trans
      ((List.getElem_take (xs := actualFirstLiveWindow rate source rewards C_star C_h hc
        (p.T - s) span) (i := n) (j := n + 1) (h := hnTake)).symm.trans
          ((getElem_congr_coll (i := n) (w := hnTake) hwindowTake).trans hrecord))
  · rw [hcells, actualLiveSourceCells_length]
    exact hnBig
  · rw [hcells]
    exact (actualLiveSourceCells_take rate rewards C_star C_h source
      hc n (p.T - s) (by dsimp only [n]; omega) span).symm


/-- The actual two readouts, retaining the marker and the original optional
reserved FAST coordinate on the same whole control. -/
def liveMarkerFastPair
    (xu : LiveRemainder rate rewards C_star C_h q t s hs control0 × TimeControl p) :
    Option (Fin p.K) × Option (Fin p.K) :=
  (liveMarker rate rewards C_star C_h q t s hs control0 xu,
    liveReservedFastOption rate rewards C_star C_h q t s hs control0 xu)

theorem measurable_liveMarkerFastPair :
    Measurable (liveMarkerFastPair rate rewards C_star C_h q t s hs control0) :=
  (measurable_liveMarker rate rewards C_star C_h q t s hs control0).prodMk
    (measurable_liveReservedFastOption rate rewards C_star C_h q t s hs control0)

/-- Only the finite output representation changes: the proved complement arm
is retained as a present optional arm. -/
def retainOptionalFast {U : CanonicalOrientedSetLaw.SlowSet p.K p.m}
    (pair : Option (Fin p.K) × CanonicalFastSampling.FastArm U) :
    Option (Fin p.K) × Option (Fin p.K) :=
  (pair.1, some pair.2.val)

private theorem reservedFastAtInput_prepare
    (input : ReferenceActivePhysicalStep.RoundInput p rate) :
    reservedFastAtInput input =
      match (ReferenceActivePhysicalStep.prepare input).coordinator with
      | .live r _ _ _ => reservedFastForRegisters (rate := rate) r input.time input.row
      | _ => none := by
  rw [(ReferenceActivePhysicalStep.prepare input).coordinator_eq]
  cases hc : input.state.coordinator with
  | first =>
      simp only [reservedFastAtInput, ReferenceActivePhysicalStep.dispatch, hc,
        CoordinatorRoundDispatch.dispatch]
      rfl
  | live r owned base =>
      simp only [reservedFastAtInput, ReferenceActivePhysicalStep.dispatch, hc,
        CoordinatorRoundDispatch.dispatch]
      rfl
  | dagger => simp only [reservedFastAtInput, ReferenceActivePhysicalStep.dispatch, hc]
  | collection payload ledger saved =>
      simp only [reservedFastAtInput, ReferenceActivePhysicalStep.dispatch, hc]
      split_ifs <;> rfl

/-- The existing reserved operation uses the original FAST scalar on every
slot. Only complement agreement with the full comparison vector is required. -/
theorem reservedFastForRegisters_eq_sampleFast
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (time : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p))
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid r.payload cutoff time r.complementWeights)
    (W : Fin p.K → ℝ) (hpos : ∀ a, 0 < W a)
    (hlower : ∀ a, r.payload.anchor a ≤ W a)
    (hupper : ∀ a, W a ≤ 2 * r.payload.anchor a)
    (hcomp : ∀ a : CanonicalFastSampling.FastArm r.payload.slowSet,
      r.complementWeights a = W a.val) :
    reservedFastForRegisters (rate := rate) r time row =
      some (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
        r.payload.anchor W r.payload.anchor_pos hpos hlower hupper r.payload.slowSet
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast (row.2 time).1)).val := by
  have hcut : CoordinatorLocalArmChoice.assignmentStart r.payload ≤
      CoordinatorLocalArmChoice.cutoffRound (p := p) none := by
    have hstart := valid.time.assignment_started
    simp only [CoordinatorLocalArmChoice.cutoffRound, Option.elim_none,
      CoordinatorLocalArmChoice.sourceRound] at *
    omega
  have hv := CoordinatorLocalArmChoice.choiceInputsValid_mk r.payload none time r.complementWeights
    valid.time.assignment_started hcut
    (fun a => ⟨valid.current_weight_pos a, valid.anchor_le_current a,
      valid.current_le_twice_anchor a⟩)
  have hlive : CoordinatorLocalArmChoice.assignmentIsLive r.payload none time :=
    ⟨valid.time.assignment_started, by
      simp only [CoordinatorLocalArmChoice.cutoffRound, Option.elim_none,
        CoordinatorLocalArmChoice.sourceRound]
      omega⟩
  simp only [reservedFastForRegisters, hlive, ↓reduceIte,
    CoordinatorLocalArmChoice.coordinatorArmChoice]
  rw [CoordinatorLocalArmChoice.coordinatorArmChoiceCore_live_empty
    r.payload ∅ none time r.complementWeights (row.2 time) hv hlive rfl]
  rw [CoordinatorLocalArmChoice.localFastDraw_eq_canonical r.payload none time
    r.complementWeights hv W hpos hlower hupper (funext hcomp)]

/-- ALL-arm numerical score weights from the computed strict-past registers.
No anchor fill-in is performed on slow arms. -/
def liveNumericalWeights
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0) (a : Fin p.K) : ℝ :=
  ScoreWeights.scoreWeight (1 + 1 / (ConstructorDimensions.D p : ℝ))
    ((liveNumericalPast rate rewards C_star C_h q t s hs control0 x).1 a).1

/-- The actual pre-round numerical vector is the score-weight vector of the
SAME whole source's first-live prefix at the original calendar offset. -/
theorem liveNumericalWeights_whole_prefix
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0) :
    let z := ReferenceFirstLiveRecordingSourceCylinder.sourceRecover
      rate rewards C_star C_h q t s hs control0
      (liveRetained rate rewards C_star C_h q t s hs control0 x, control0)
    let n := t.val - s
    ∃ hk : n < (wholeFirstLiveWindow rate rewards C_star C_h z.val).length,
      (wholeFirstLiveWindow rate rewards C_star C_h z.val)[n]'hk =
        sourceRecordAtControl (liveRetained rate rewards C_star C_h q t s hs control0 x) control0 ∧
      n < (wholeFirstLiveCells rate rewards C_star C_h z.val).length ∧
      (∀ a : Fin p.K,
        liveNumericalWeights rate rewards C_star C_h q t s hs control0 x a =
          RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              ((wholeFirstLiveCells rate rewards C_star C_h z.val).take n)) a) ∧
      (liveNumericalPast rate rewards C_star C_h q t s hs control0 x).2.1 =
        (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          ((wholeFirstLiveCells rate rewards C_star C_h z.val).take n)).overflow := by
  intro z n
  have hsplit := ReferenceFirstLiveRecordingSourceCylinder.sourceSplit_sourceRecover
    rate rewards C_star C_h q t s hs control0
      (liveRetained rate rewards C_star C_h q t s hs control0 x, control0)
  have hretained : ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
      rate rewards C_star C_h q t s hs control0 z =
      liveRetained rate rewards C_star C_h q t s hs control0 x := congrArg Prod.fst hsplit
  have hcontrol : ReferenceFirstLiveRecordingSourceCylinder.originalControl
      rate rewards C_star C_h q t s hs z = control0 := congrArg Prod.snd hsplit
  have htag : ∃ tagged : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
      rate rewards C_star C_h q t s hs control0 ⊕
      ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0,
      Sum.elim Subtype.val Subtype.val tagged = z := by
    cases x with
    | inl x =>
        refine ⟨.inl ⟨z, ?_⟩, rfl⟩
        rw [hretained]
        exact x.property
    | inr x =>
        refine ⟨.inr ⟨z, ?_⟩, rfl⟩
        rw [hretained]
        exact x.property
  obtain ⟨tagged, htagged⟩ := htag
  have halign := source_whole_prefix_alignment rate rewards C_star C_h q t s hs control0 tagged
  dsimp only at halign
  simp only [htagged] at halign
  obtain ⟨hk, hrecord, hcell, hprefix⟩ := halign
  have horiginal := ReferenceFirstLiveRecordingSourceCylinder.sourceRecordAtControl_eq_original
    rate rewards C_star C_h q t s hs control0 z
  rw [hretained, hcontrol] at horiginal
  refine ⟨hk, hrecord.trans horiginal.symm, hcell, ?_, ?_⟩
  · intro a
    rw [hprefix]
    rfl
  · rw [hprefix]
    rfl

/-- The numerical ALL-arm vector is positive and stays in the first episode's
unit-anchor envelope, including the strict past of the detecting update. -/
theorem liveNumericalWeights_envelope
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0) (a : Fin p.K) :
    0 < liveNumericalWeights rate rewards C_star C_h q t s hs control0 x a ∧
      1 ≤ liveNumericalWeights rate rewards C_star C_h q t s hs control0 x a ∧
      liveNumericalWeights rate rewards C_star C_h q t s hs control0 x a < 2 := by
  obtain ⟨_, _, hk, hweights, _⟩ :=
    liveNumericalWeights_whole_prefix rate rewards C_star C_h q t s hs control0 x
  rw [hweights a]
  have h := ReferenceFirstLiveNumericalFastPersistence.wholeFirstLive_full_scoreWeight_envelope
    rate rewards C_star C_h _ ⟨t.val - s, hk⟩ a
  exact ⟨lt_of_lt_of_le zero_lt_one h.1, h⟩

theorem measurable_liveNumericalWeights (a : Fin p.K) :
    Measurable (fun x => liveNumericalWeights rate rewards C_star C_h q t s hs control0 x a) := by
  have hscore : Measurable (fun x : LiveRemainder rate rewards C_star C_h q t s hs control0 =>
      ((liveNumericalPast rate rewards C_star C_h q t s hs control0 x).1 a).1) :=
    measurable_fst.comp ((measurable_pi_apply a).comp
      ((measurable_liveNumericalPast rate rewards C_star C_h q t s hs control0).fst))
  exact (measurable_of_countable
    (ScoreWeights.scoreWeight (1 + 1 / (ConstructorDimensions.D p : ℝ)))).comp hscore

/-- The payload of the SAME actual baseline selection in each source branch. -/
def livePayload (x : LiveRemainder rate rewards C_star C_h q t s hs control0) :
    ReferenceActivePhysicalStep.Payload rate :=
  match x with
  | .inl x => selectedBaselinePayload x
  | .inr x => (ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty
      rate rewards C_star C_h q t s hs control0 x).view.payload

/-- Every replacement retains that actual selected payload. The selection
and its preparation equation are produced from the accepted source constructors. -/
theorem livePayload_selected_at_control
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0) (u : TimeControl p) :
    ∃ selected : ReferenceActivePhysicalStep.Selection
        (sourceInputAtControl (liveRetained rate rewards C_star C_h q t s hs control0 x) u),
      (ReferenceActivePhysicalStep.prepare
        (sourceInputAtControl (liveRetained rate rewards C_star C_h q t s hs control0 x) u)).coordinator.selection =
          some selected ∧
      selected.view.payload = livePayload rate rewards C_star C_h q t s hs control0 x := by
  cases x with
  | inl x =>
      obtain ⟨states, memories, ho, r, owned, base, d, hsStart, c, arm, hcoord, _⟩ :=
        ReferenceFirstLiveRecordingSourceBranch.actual_continuing_recording_inputs
          rate rewards C_star C_h q t s hs control0 x.val x.property
      obtain ⟨cu, au, hu⟩ := ReferenceContinuingLiveSlicePreparation.continuing_cut_at_control
        (sourceCurrentInput x.val) r owned base d hsStart c arm hcoord u
      have hpayload := selectedBaselinePayload_eq_of_continuing x
        r owned base d hsStart c arm hcoord
      refine ⟨ReferenceContinuingLiveSlicePreparation.continuingSelection
        (sourceInputAtControl x.val u) r owned base d hsStart cu au, ?_, ?_⟩
      · exact ReferenceContinuingLiveSlicePreparation.continuingSelection_eq_actual
          (sourceInputAtControl x.val u) r owned base d hsStart cu au hu
      · exact hpayload.symm
  | inr x =>
      obtain ⟨states, memories, ho, r, owned, base, d, hsStart, c, arm, hcoord, _⟩ :=
        ReferenceFirstLiveEmptyPendingMarkerLaw.actual_empty_recording_inputs
          rate rewards C_star C_h q t s hs control0 x.val x.property
      obtain ⟨cu, au, hu⟩ := ReferenceContinuingLiveSlicePreparation.continuing_cut_at_control
        (sourceCurrentInput x.val) r owned base d hsStart c arm hcoord u
      have hpayload := ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty_payload_eq
        rate rewards C_star C_h q t s hs control0 x r owned base d hsStart c arm hcoord
      refine ⟨ReferenceContinuingLiveSlicePreparation.continuingSelection
        (sourceInputAtControl x.val u) r owned base d hsStart cu au, ?_, ?_⟩
      · exact ReferenceContinuingLiveSlicePreparation.continuingSelection_eq_actual
          (sourceInputAtControl x.val u) r owned base d hsStart cu au hu
      · exact hpayload.symm

private theorem actualCell_view_congr
    {left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hrecord : left = right) (cell : ActualLiveSourceCell left)
    (selected : ReferenceActivePhysicalStep.Selection right.input)
    (hselected : (ReferenceActivePhysicalStep.prepare right.input).coordinator.selection = some selected) :
    cell.selected.view = selected.view := by
  cases hrecord
  have hcell : (ReferenceActivePhysicalStep.prepare left.input).coordinator.selection =
      some cell.selected := by
    simpa only [left.output_eq, ReferenceActivePhysicalStep.step] using cell.selection_actual
  exact congrArg (fun chosen => chosen.view) (Option.some.inj (hcell.symm.trans hselected))

private theorem witness_record_eq_whole
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (wholeFirstLiveWindow rate rewards C_star C_h source).length)
    (launch : Fin (p.T + 1)) (fiber : LaunchFiber rate rewards C_star C_h launch.val)
    (j : Fin (actualFirstLiveWindow rate fiber.val rewards C_star C_h
      (launch_crossing rate rewards C_star C_h launch.val fiber) (p.T - launch.val)
      (launch_span rate rewards C_star C_h launch.val (p.T - launch.val)
        (maximal_span launch) fiber)).length)
    (hsource : fiber.val = source) (hposition : j.val = k.val) :
    (actualFirstLiveWindow rate fiber.val rewards C_star C_h
      (launch_crossing rate rewards C_star C_h launch.val fiber) (p.T - launch.val)
      (launch_span rate rewards C_star C_h launch.val (p.T - launch.val)
        (maximal_span launch) fiber))[j.val]'j.isLt =
      (wholeFirstLiveWindow rate rewards C_star C_h source)[k.val]'k.isLt := by
  subst source
  have hw := (wholeFirstLive_on_fiber rate rewards C_star C_h launch fiber).1
  change wholeFirstLiveWindow rate rewards C_star C_h fiber.val =
    actualFirstLiveWindow rate fiber.val rewards C_star C_h
      (launch_crossing rate rewards C_star C_h launch.val fiber) (p.T - launch.val)
      (launch_span rate rewards C_star C_h launch.val (p.T - launch.val)
        (maximal_span launch) fiber) at hw
  apply Option.some.inj
  calc
    _ = (actualFirstLiveWindow rate fiber.val rewards C_star C_h
        (launch_crossing rate rewards C_star C_h launch.val fiber) (p.T - launch.val)
        (launch_span rate rewards C_star C_h launch.val (p.T - launch.val)
          (maximal_span launch) fiber))[j.val]? := (List.getElem?_eq_getElem j.isLt).symm
    _ = (actualFirstLiveWindow rate fiber.val rewards C_star C_h
        (launch_crossing rate rewards C_star C_h launch.val fiber) (p.T - launch.val)
        (launch_span rate rewards C_star C_h launch.val (p.T - launch.val)
          (maximal_span launch) fiber))[k.val]? :=
      congrArg (fun n => (actualFirstLiveWindow rate fiber.val rewards C_star C_h
        (launch_crossing rate rewards C_star C_h launch.val fiber) (p.T - launch.val)
        (launch_span rate rewards C_star C_h launch.val (p.T - launch.val)
          (maximal_span launch) fiber))[n]?) hposition
    _ = (wholeFirstLiveWindow rate rewards C_star C_h fiber.val)[k.val]? :=
      (congrArg (fun records => records[k.val]?) hw).symm
    _ = _ := List.getElem?_eq_getElem k.isLt

/-- The selected numerical cell's payload is the original unit-anchor first
installation, on BOTH actual positive-offset branches. -/
theorem livePayload_anchor_unit
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0) (a : Fin p.K) :
    (livePayload rate rewards C_star C_h q t s hs control0 x).anchor a = 1 := by
  let z := ReferenceFirstLiveRecordingSourceCylinder.sourceRecover
    rate rewards C_star C_h q t s hs control0
      (liveRetained rate rewards C_star C_h q t s hs control0 x, control0)
  obtain ⟨hkWindow, hrecord, hkCells, _, _⟩ :=
    liveNumericalWeights_whole_prefix rate rewards C_star C_h q t s hs control0 x
  obtain ⟨launch, fiber, j, hsource, hposition, _, installation⟩ :=
    ReferenceFirstLiveNumericalFastPersistence.wholeFirstLive_selected_payload_first_installation
      rate rewards C_star C_h z.val ⟨t.val - s, hkCells⟩
  have hrec := witness_record_eq_whole rate rewards C_star C_h z.val
    ⟨t.val - s, hkWindow⟩ launch fiber j hsource hposition
  have hactual := hrec.trans hrecord
  obtain ⟨selected, hselected, hpayload⟩ :=
    livePayload_selected_at_control rate rewards C_star C_h q t s hs control0 x control0
  let cell := actualLiveSourceCellAt rate fiber.val rewards C_star C_h
    (launch_crossing rate rewards C_star C_h launch.val fiber) (p.T - launch.val)
    (launch_span rate rewards C_star C_h launch.val (p.T - launch.val)
      (maximal_span launch) fiber) j
  have hview := actualCell_view_congr rate hactual cell selected hselected
  obtain ⟨_, installed, arm, hdispatch, hborn, hunit, _⟩ := installation
  have hcellPayload : cell.selected.view.payload = livePayload rate rewards C_star C_h q t s hs control0 x :=
    (congrArg ReferenceDownReception.ChoiceTimeView.payload hview).trans hpayload
  rw [← hcellPayload]
  exact hunit a

/-- The accepted numerical FAST witness is reconciled with the actual
baseline physical record and selected payload. The only localizer is the
computed PRE overflow flag, and the sampler identity holds for EVERY scalar. -/
theorem liveNumericalCell_fast
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0)
    (hclear : (liveNumericalPast rate rewards C_star C_h q t s hs control0 x).2.1 = false) :
    let W := liveNumericalWeights rate rewards C_star C_h q t s hs control0 x
    ∃ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (cell : ActualLiveSourceCell record),
      record = sourceRecordAtControl
        (liveRetained rate rewards C_star C_h q t s hs control0 x) control0 ∧
      cell.selected.view.payload = livePayload rate rewards C_star C_h q t s hs control0 x ∧
      ∃ (hpos : ∀ a, 0 < W a)
        (hlower : ∀ a, cell.selected.view.payload.anchor a ≤ W a)
        (hupper : ∀ a, W a ≤ 2 * cell.selected.view.payload.anchor a),
        (∀ a : CanonicalFastSampling.FastArm cell.selected.view.payload.slowSet,
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
            hpos hlower hupper cell.selected.view.payload.slowSet scalar) := by
  intro W
  let z := ReferenceFirstLiveRecordingSourceCylinder.sourceRecover
    rate rewards C_star C_h q t s hs control0
      (liveRetained rate rewards C_star C_h q t s hs control0 x, control0)
  obtain ⟨hkWindow, hrecord, hkCells, hweights, hoverflow⟩ :=
    liveNumericalWeights_whole_prefix rate rewards C_star C_h q t s hs control0 x
  have hclearWhole : (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((wholeFirstLiveCells rate rewards C_star C_h z.val).take (t.val - s))).overflow = false :=
    hoverflow.symm.trans hclear
  obtain ⟨launch, fiber, j, hsource, hposition, _, hpos, hlower, hupper, hcomp, hfast, _⟩ :=
    ReferenceFirstLiveNumericalFastPersistence.wholeFirstLive_full_weight_fast
      rate rewards C_star C_h z.val ⟨t.val - s, hkCells⟩ hclearWhole
  let record := (actualFirstLiveWindow rate fiber.val rewards C_star C_h
    (launch_crossing rate rewards C_star C_h launch.val fiber) (p.T - launch.val)
    (launch_span rate rewards C_star C_h launch.val (p.T - launch.val)
      (maximal_span launch) fiber))[j.val]'j.isLt
  let cell := actualLiveSourceCellAt rate fiber.val rewards C_star C_h
    (launch_crossing rate rewards C_star C_h launch.val fiber) (p.T - launch.val)
    (launch_span rate rewards C_star C_h launch.val (p.T - launch.val)
      (maximal_span launch) fiber) j
  have hrec := witness_record_eq_whole rate rewards C_star C_h z.val
    ⟨t.val - s, hkWindow⟩ launch fiber j hsource hposition
  have hactual : record = sourceRecordAtControl
      (liveRetained rate rewards C_star C_h q t s hs control0 x) control0 := hrec.trans hrecord
  obtain ⟨selected, hselected, hpayload⟩ :=
    livePayload_selected_at_control rate rewards C_star C_h q t s hs control0 x control0
  have hview := actualCell_view_congr rate hactual cell selected hselected
  have hcellPayload : cell.selected.view.payload = livePayload rate rewards C_star C_h q t s hs control0 x :=
    (congrArg ReferenceDownReception.ChoiceTimeView.payload hview).trans hpayload
  have hW : W = RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        ((wholeFirstLiveCells rate rewards C_star C_h z.val).take (t.val - s))) := funext hweights
  have hpos' : ∀ a, 0 < W a := by
    simpa only [hW] using hpos
  have hlower' : ∀ a, cell.selected.view.payload.anchor a ≤ W a := by
    simpa only [hW] using hlower
  have hupper' : ∀ a, W a ≤ 2 * cell.selected.view.payload.anchor a := by
    simpa only [hW] using hupper
  refine ⟨record, cell, hactual, hcellPayload, hpos', hlower', hupper', ?_, ?_⟩
  · simpa only [hW] using hcomp
  · intro scalar
    simpa only [hW] using hfast scalar

/-- Every actual continuing or empty-pending remainder supplies all physical
operational inputs internally. The pair law retains EVERY fixed original
affine family and the marker/FAST dependence. The comparison weights here are
the actual anchor-filled complement extension; numerical replacement is a
separate equality on the computed clear event. -/
theorem liveRemainder_physical_joint_law
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0) :
    ∃ (payload : ReferenceActivePhysicalStep.Payload rate) (W : Fin p.K → ℝ)
      (hpos : ∀ a, 0 < W a) (hlower : ∀ a, payload.anchor a ≤ W a)
      (hupper : ∀ a, W a ≤ 2 * payload.anchor a)
      (snapshot : ActiveRoundActions.Snapshot payload.assignment),
      payload = livePayload rate rewards C_star C_h q t s hs control0 x ∧
      ((liveNumericalPast rate rewards C_star C_h q t s hs control0 x).2.1 = false →
        ∀ a : CanonicalFastSampling.FastArm payload.slowSet,
          W a.val = liveNumericalWeights rate rewards C_star C_h q t s hs control0 x a.val) ∧
      (∀ u : TimeControl p,
        liveMarkerFastPair rate rewards C_star C_h q t s hs control0 (x, u) =
          retainOptionalFast (FastRewardSliceLaw.liveRecordingFastPair
            p rate.eta.val rate.eta.property rate.sourceCap payload.anchor W payload.anchor_pos
            hpos hlower hupper payload.assignment snapshot u.1)) ∧
      (ContinuousLearningRows.timeControlLaw p).map
        (fun u => liveMarkerFastPair rate rewards C_star C_h q t s hs control0 (x, u)) =
        (FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property
          rate.sourceCap payload.anchor W payload.anchor_pos hpos hlower hupper
          payload.assignment snapshot).map retainOptionalFast ∧
      (∀ family : ContinuousLearningRows.AffineSamples p,
        Measurable (fun slice : CanonicalRecordingSlice.Slice p.m p.K =>
          liveMarkerFastPair rate rewards C_star C_h q t s hs control0 (x, (slice, family))) ∧
        (ContinuousControlSlice.sliceLaw p.m p.K).map
          (fun slice => liveMarkerFastPair rate rewards C_star C_h q t s hs control0
            (x, (slice, family))) =
          (FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property
            rate.sourceCap payload.anchor W payload.anchor_pos hpos hlower hupper
            payload.assignment snapshot).map retainOptionalFast) := by
  cases x with
  | inl x =>
      obtain ⟨states, memories, ho, r, owned, base, d, hsStart, c, arm, hcoord,
          henabled, _, _, _, hfirst, hseed, _, _, _, _, _, hunoccupied, _,
          hvalid, hpairwise, htime, _, _⟩ :=
        ReferenceFirstLiveRecordingSourceBranch.actual_continuing_recording_inputs
          rate rewards C_star C_h q t s hs control0 x.val x.property
      have hpayload := selectedBaselinePayload_eq_of_continuing x
        r owned base d hsStart c arm hcoord
      let time := (sourceCurrentInput x.val).time
      let W := ReferenceContinuingLiveSlicePreparation.liveSliceWeights r time
      let hpos := ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u) arm.choiceInputsValid
      let hlower := ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u) arm.choiceInputsValid
      let hupper := ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u) arm.choiceInputsValid
      let snapshot := ReferenceContinuingLiveSlicePreparation.liveSliceSnapshot r owned base time d states
      have hlaw := ReferenceContinuingRecordingFastLaw.actual_continuing_live_joint_law
        (retainedSourceInitial x.val) (retainedSourceSplit x.val).1.2 q rewards s
        (t.val - s) (retainedSourceCurrentSpan hs) (retainedSourceInitialMode x.val)
        (ReferenceFirstLiveRecordingSourceBranch.actualRetainedSeed
          rate rewards C_star C_h q t s hs control0 x.val).followers
        (ReferenceFirstLiveRecordingSourceBranch.actualRetainedSeed
          rate rewards C_star C_h q t s hs control0 x.val).memory
        hfirst hseed hunoccupied hvalid hpairwise htime
        r owned base d hsStart c arm hcoord states memories ho henabled
      have hpoint := ReferenceContinuingRecordingFastPair.prefix_physical_fast_pair_eq
        (retainedSourceInitial x.val) (retainedSourceSplit x.val).1.2 q rewards s
        (t.val - s) (retainedSourceCurrentSpan hs) (retainedSourceInitialMode x.val)
        (ReferenceFirstLiveRecordingSourceBranch.actualRetainedSeed
          rate rewards C_star C_h q t s hs control0 x.val).followers
        (ReferenceFirstLiveRecordingSourceBranch.actualRetainedSeed
          rate rewards C_star C_h q t s hs control0 x.val).memory
        hfirst hseed hunoccupied hvalid hpairwise htime
        r owned base d hsStart c arm hcoord states memories ho henabled
      let pair := ReferenceContinuingRecordingFastPair.candidatePhysicalFastPair
        (retainedSourceInitial x.val) (retainedSourceSplit x.val).1.2 q rewards s
        (t.val - s) (retainedSourceCurrentSpan hs) (retainedSourceInitialMode x.val)
        r.payload true W hpos hlower hupper
      have hreserved (u : TimeControl p) :
          liveReservedFastOption rate rewards C_star C_h q t s hs control0
            (.inl x, u) = some (pair u).2.val := by
        obtain ⟨cu, au, hu⟩ := ReferenceContinuingLiveSlicePreparation.continuing_cut_at_control
          (sourceCurrentInput x.val) r owned base d hsStart c arm hcoord u
        change reservedFastAtInput
          (ReferenceContinuingLiveSlicePreparation.inputAtControl (sourceCurrentInput x.val) u) = _
        rw [reservedFastAtInput_prepare]
        simp only [hu]
        rw [ReferenceContinuingLiveSlicePreparation.inputAtControl_time,
          ReferenceContinuingLiveSlicePreparation.inputAtControl_row]
        have valid : CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            time r.complementWeights := by
          have hw : (ReferenceActivePhysicalStep.liveRegistersAt r time).complementWeights =
              r.complementWeights := by
            funext a
            rfl
          have hv := arm.choiceInputsValid
          change CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            time (ReferenceActivePhysicalStep.liveRegistersAt r time).complementWeights at hv
          rw [hw] at hv
          exact hv
        rw [reservedFastForRegisters_eq_sampleFast rate r time _ _ valid W hpos hlower hupper]
        · simp only [time, ReferenceContinuingLiveSlicePreparation.rowAtControl_time,
            pair, ReferenceContinuingRecordingFastPair.candidatePhysicalFastPair,
            SnapshotRecordingKernel.fastArmDraw]
          rw [CoordinatorRecorderComplementBridge.assignmentSlowSet_eq_payload r.payload]
        · intro a
          exact (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_restrict r time a).symm
      have hactual (u : TimeControl p) :
          liveMarkerFastPair rate rewards C_star C_h q t s hs control0 (.inl x, u) =
            retainOptionalFast (pair u) := by
        simp only [liveMarkerFastPair, liveMarker, currentPhysicalMarker]
        rw [hpayload, sourcePhysicalMarker_eq_candidatePhysicalMarker]
        exact congrArg₂ Prod.mk rfl (hreserved u)
      have hmPair : Measurable pair := by
        simpa only [pair, W, time, sourceCurrentInput, ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput,
          retainedSourceInitial, retainedSourceSplit, retainedSourceCurrentCount, hpos, hlower, hupper] using hlaw.1
      have hlaw' : (ContinuousLearningRows.timeControlLaw p).map pair =
          FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property
            rate.sourceCap r.payload.anchor W r.payload.anchor_pos hpos hlower hupper
            r.payload.assignment snapshot := by
        simpa only [pair, W, time, snapshot, sourceCurrentInput, ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput,
          retainedSourceInitial, retainedSourceSplit, retainedSourceCurrentCount, hpos, hlower, hupper] using hlaw.2.1
      refine ⟨r.payload, W, hpos, hlower, hupper, snapshot, ?_, ?_, ?_, ?_, ?_⟩
      · exact hpayload.symm
      · intro hclear a
        obtain ⟨record, cell, hrecord, _, _, _, _, hcomp, _⟩ :=
          liveNumericalCell_fast rate rewards C_star C_h q t s hs control0 (.inl x) hclear
        obtain ⟨c0, a0, hc0⟩ := ReferenceContinuingLiveSlicePreparation.continuing_cut_at_control
          (sourceCurrentInput x.val) r owned base d hsStart c arm hcoord control0
        let selected := ReferenceContinuingLiveSlicePreparation.continuingSelection
          (sourceInputAtControl x.val control0) r owned base d hsStart c0 a0
        have hselected := ReferenceContinuingLiveSlicePreparation.continuingSelection_eq_actual
          (sourceInputAtControl x.val control0) r owned base d hsStart c0 a0 hc0
        have hview := actualCell_view_congr rate hrecord cell selected hselected
        have hcompView : ∀ b : CanonicalFastSampling.FastArm selected.view.payload.slowSet,
            selected.view.complementWeights b =
              liveNumericalWeights rate rewards C_star C_h q t s hs control0 (.inl x) b.val :=
          hview ▸ hcomp
        have hcomp' : ∀ b : CanonicalFastSampling.FastArm r.payload.slowSet,
            (ReferenceActivePhysicalStep.liveRegistersAt r time).complementWeights b =
              liveNumericalWeights rate rewards C_star C_h q t s hs control0 (.inl x) b.val := by
          simpa only [selected, ReferenceContinuingLiveSlicePreparation.continuingSelection,
            sourceInputAtControl, ReferenceContinuingLiveSlicePreparation.inputAtControl_time,
            ReferenceActivePhysicalStep.liveInput, ReferenceActivePhysicalStep.liveRegistersAt,
            time] using hcompView
        exact (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_restrict r time a).trans (hcomp' a)

      · intro u
        exact (hactual u).trans (congrArg retainOptionalFast (by
          simpa only [pair, W, time, snapshot, sourceCurrentInput, ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput,
          retainedSourceInitial, retainedSourceSplit, retainedSourceCurrentCount, hpos, hlower, hupper] using hpoint u))
      · rw [← hlaw', Measure.map_map (measurable_of_finite retainOptionalFast) hmPair]
        exact congrArg (fun f => (ContinuousLearningRows.timeControlLaw p).map f) (funext hactual)
      · intro family
        have hf : Measurable (fun slice : CanonicalRecordingSlice.Slice p.m p.K =>
            pair (slice, family)) ∧
            (ContinuousControlSlice.sliceLaw p.m p.K).map (fun slice => pair (slice, family)) =
              FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property
                rate.sourceCap r.payload.anchor W r.payload.anchor_pos hpos hlower hupper
                r.payload.assignment snapshot := by
          simpa only [pair, W, time, snapshot, sourceCurrentInput, ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput,
          retainedSourceInitial, retainedSourceSplit, retainedSourceCurrentCount, hpos, hlower, hupper]
            using hlaw.2.2.1 family
        constructor
        · exact (measurable_liveMarkerFastPair rate rewards C_star C_h q t s hs control0).comp
            (measurable_const.prodMk (measurable_id.prodMk measurable_const))
        · rw [← hf.2, Measure.map_map (measurable_of_finite retainOptionalFast) hf.1]
          exact congrArg (fun f => (ContinuousControlSlice.sliceLaw p.m p.K).map f)
            (funext fun slice => hactual (slice, family))
  | inr x =>
      obtain ⟨states, memories, ho, r, owned, base, d, hsStart, c, arm, hcoord,
          henabled, hfirst, hseed, hunoccupied, hvalid, hpairwise, htime⟩ :=
        ReferenceFirstLiveEmptyPendingMarkerLaw.actual_empty_recording_inputs
          rate rewards C_star C_h q t s hs control0 x.val x.property
      have hpayload := ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty_payload_eq
        rate rewards C_star C_h q t s hs control0 x r owned base d hsStart c arm hcoord
      let time := (sourceCurrentInput x.val).time
      let W := ReferenceContinuingLiveSlicePreparation.liveSliceWeights r time
      let hpos := ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u) arm.choiceInputsValid
      let hlower := ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u) arm.choiceInputsValid
      let hupper := ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u) arm.choiceInputsValid
      let snapshot := ReferenceContinuingLiveSlicePreparation.liveSliceSnapshot r owned base time d states
      have hlaw := ReferenceContinuingRecordingFastLaw.actual_continuing_live_joint_law
        (retainedSourceInitial x.val) (retainedSourceSplit x.val).1.2 q rewards s
        (t.val - s) (retainedSourceCurrentSpan hs) (retainedSourceInitialMode x.val)
        (ReferenceFirstLiveRecordingSourceBranch.actualRetainedSeed
          rate rewards C_star C_h q t s hs control0 x.val).followers
        (ReferenceFirstLiveRecordingSourceBranch.actualRetainedSeed
          rate rewards C_star C_h q t s hs control0 x.val).memory
        hfirst hseed hunoccupied hvalid hpairwise htime
        r owned base d hsStart c arm hcoord states memories ho henabled
      have hpoint := ReferenceContinuingRecordingFastPair.prefix_physical_fast_pair_eq
        (retainedSourceInitial x.val) (retainedSourceSplit x.val).1.2 q rewards s
        (t.val - s) (retainedSourceCurrentSpan hs) (retainedSourceInitialMode x.val)
        (ReferenceFirstLiveRecordingSourceBranch.actualRetainedSeed
          rate rewards C_star C_h q t s hs control0 x.val).followers
        (ReferenceFirstLiveRecordingSourceBranch.actualRetainedSeed
          rate rewards C_star C_h q t s hs control0 x.val).memory
        hfirst hseed hunoccupied hvalid hpairwise htime
        r owned base d hsStart c arm hcoord states memories ho henabled
      let pair := ReferenceContinuingRecordingFastPair.candidatePhysicalFastPair
        (retainedSourceInitial x.val) (retainedSourceSplit x.val).1.2 q rewards s
        (t.val - s) (retainedSourceCurrentSpan hs) (retainedSourceInitialMode x.val)
        r.payload true W hpos hlower hupper
      have hreserved (u : TimeControl p) :
          liveReservedFastOption rate rewards C_star C_h q t s hs control0
            (.inr x, u) = some (pair u).2.val := by
        obtain ⟨cu, au, hu⟩ := ReferenceContinuingLiveSlicePreparation.continuing_cut_at_control
          (sourceCurrentInput x.val) r owned base d hsStart c arm hcoord u
        change reservedFastAtInput
          (ReferenceContinuingLiveSlicePreparation.inputAtControl (sourceCurrentInput x.val) u) = _
        rw [reservedFastAtInput_prepare]
        simp only [hu]
        rw [ReferenceContinuingLiveSlicePreparation.inputAtControl_time,
          ReferenceContinuingLiveSlicePreparation.inputAtControl_row]
        have valid : CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            time r.complementWeights := by
          have hw : (ReferenceActivePhysicalStep.liveRegistersAt r time).complementWeights =
              r.complementWeights := by
            funext a
            rfl
          have hv := arm.choiceInputsValid
          change CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            time (ReferenceActivePhysicalStep.liveRegistersAt r time).complementWeights at hv
          rw [hw] at hv
          exact hv
        rw [reservedFastForRegisters_eq_sampleFast rate r time _ _ valid W hpos hlower hupper]
        · simp only [time, ReferenceContinuingLiveSlicePreparation.rowAtControl_time,
            pair, ReferenceContinuingRecordingFastPair.candidatePhysicalFastPair,
            SnapshotRecordingKernel.fastArmDraw]
          rw [CoordinatorRecorderComplementBridge.assignmentSlowSet_eq_payload r.payload]
        · intro a
          exact (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_restrict r time a).symm
      have hactual (u : TimeControl p) :
          liveMarkerFastPair rate rewards C_star C_h q t s hs control0 (.inr x, u) =
            retainOptionalFast (pair u) := by
        simp only [liveMarkerFastPair, liveMarker, ReferenceFirstLiveEmptyPendingMarkerLaw.currentEmptyMarker]
        rw [hpayload, sourcePhysicalMarker_eq_candidatePhysicalMarker]
        exact congrArg₂ Prod.mk rfl (hreserved u)
      have hmPair : Measurable pair := by
        simpa only [pair, W, time, sourceCurrentInput, ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput,
          retainedSourceInitial, retainedSourceSplit, retainedSourceCurrentCount, hpos, hlower, hupper] using hlaw.1
      have hlaw' : (ContinuousLearningRows.timeControlLaw p).map pair =
          FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property
            rate.sourceCap r.payload.anchor W r.payload.anchor_pos hpos hlower hupper
            r.payload.assignment snapshot := by
        simpa only [pair, W, time, snapshot, sourceCurrentInput, ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput,
          retainedSourceInitial, retainedSourceSplit, retainedSourceCurrentCount, hpos, hlower, hupper] using hlaw.2.1
      refine ⟨r.payload, W, hpos, hlower, hupper, snapshot, ?_, ?_, ?_, ?_, ?_⟩
      · exact hpayload.symm
      · intro hclear a
        obtain ⟨record, cell, hrecord, _, _, _, _, hcomp, _⟩ :=
          liveNumericalCell_fast rate rewards C_star C_h q t s hs control0 (.inr x) hclear
        obtain ⟨c0, a0, hc0⟩ := ReferenceContinuingLiveSlicePreparation.continuing_cut_at_control
          (sourceCurrentInput x.val) r owned base d hsStart c arm hcoord control0
        let selected := ReferenceContinuingLiveSlicePreparation.continuingSelection
          (sourceInputAtControl x.val control0) r owned base d hsStart c0 a0
        have hselected := ReferenceContinuingLiveSlicePreparation.continuingSelection_eq_actual
          (sourceInputAtControl x.val control0) r owned base d hsStart c0 a0 hc0
        have hview := actualCell_view_congr rate hrecord cell selected hselected
        have hcompView : ∀ b : CanonicalFastSampling.FastArm selected.view.payload.slowSet,
            selected.view.complementWeights b =
              liveNumericalWeights rate rewards C_star C_h q t s hs control0 (.inr x) b.val :=
          hview ▸ hcomp
        have hcomp' : ∀ b : CanonicalFastSampling.FastArm r.payload.slowSet,
            (ReferenceActivePhysicalStep.liveRegistersAt r time).complementWeights b =
              liveNumericalWeights rate rewards C_star C_h q t s hs control0 (.inr x) b.val := by
          simpa only [selected, ReferenceContinuingLiveSlicePreparation.continuingSelection,
            sourceInputAtControl, ReferenceContinuingLiveSlicePreparation.inputAtControl_time,
            ReferenceActivePhysicalStep.liveInput, ReferenceActivePhysicalStep.liveRegistersAt,
            time] using hcompView
        exact (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_restrict r time a).trans (hcomp' a)

      · intro u
        exact (hactual u).trans (congrArg retainOptionalFast (by
          simpa only [pair, W, time, snapshot, sourceCurrentInput, ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput,
          retainedSourceInitial, retainedSourceSplit, retainedSourceCurrentCount, hpos, hlower, hupper] using hpoint u))
      · rw [← hlaw', Measure.map_map (measurable_of_finite retainOptionalFast) hmPair]
        exact congrArg (fun f => (ContinuousLearningRows.timeControlLaw p).map f) (funext hactual)
      · intro family
        have hf : Measurable (fun slice : CanonicalRecordingSlice.Slice p.m p.K =>
            pair (slice, family)) ∧
            (ContinuousControlSlice.sliceLaw p.m p.K).map (fun slice => pair (slice, family)) =
              FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property
                rate.sourceCap r.payload.anchor W r.payload.anchor_pos hpos hlower hupper
                r.payload.assignment snapshot := by
          simpa only [pair, W, time, snapshot, sourceCurrentInput, ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput,
          retainedSourceInitial, retainedSourceSplit, retainedSourceCurrentCount, hpos, hlower, hupper]
            using hlaw.2.2.1 family
        constructor
        · exact (measurable_liveMarkerFastPair rate rewards C_star C_h q t s hs control0).comp
            (measurable_const.prodMk (measurable_id.prodMk measurable_const))
        · rw [← hf.2, Measure.map_map (measurable_of_finite retainOptionalFast) hf.1]
          exact congrArg (fun f => (ContinuousControlSlice.sliceLaw p.m p.K).map f)
            (funext fun slice => hactual (slice, family))

/-- The full same-slice recording/FAST pair depends on current weights only
on the assignment complement. Slow-arm numerical weights are never replaced
by the anchor in the conclusion. -/
theorem liveRecordingFastPair_eq_of_complement
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (snapshot : ActiveRoundActions.Snapshot payload.assignment)
    (W V : Fin p.K → ℝ) (hW : ∀ a, 0 < W a) (hV : ∀ a, 0 < V a)
    (hWL : ∀ a, payload.anchor a ≤ W a) (hVL : ∀ a, payload.anchor a ≤ V a)
    (hWU : ∀ a, W a ≤ 2 * payload.anchor a) (hVU : ∀ a, V a ≤ 2 * payload.anchor a)
    (hcomp : ∀ a : CanonicalFastSampling.FastArm payload.slowSet, W a.val = V a.val)
    (slice : CanonicalRecordingSlice.Slice p.m p.K) :
    FastRewardSliceLaw.liveRecordingFastPair p rate.eta.val rate.eta.property rate.sourceCap
      payload.anchor W payload.anchor_pos hW hWL hWU payload.assignment snapshot slice =
    FastRewardSliceLaw.liveRecordingFastPair p rate.eta.val rate.eta.property rate.sourceCap
      payload.anchor V payload.anchor_pos hV hVL hVU payload.assignment snapshot slice := by
  classical
  let U := SnapshotRecordingKernel.assignmentSlowSet p payload.assignment
  have hset : U = payload.slowSet :=
    CoordinatorRecorderComplementBridge.assignmentSlowSet_eq_payload payload
  have heq : ∀ a, a ∉ U.val → W a = V a := by
    intro a ha
    rw [hset] at ha
    exact hcomp ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩
  have hfast := FastComplementLocality.sampleFast_eq_of_eq_on_complement p
    rate.eta.property rate.sourceCap payload.anchor W V payload.anchor_pos hW hV
    hWL hVL hWU hVU U heq
  have hq := FastComplementLocality.qGamma_eq_of_eq_on_complement p
    rate.eta.property rate.sourceCap payload.anchor W V payload.anchor_pos hW hV
    hWL hVL hWU hVU U heq
  have haction (source : Fin p.m) :
      SnapshotRecordingKernel.dataAction p (.live payload.assignment snapshot)
        rate.eta.val rate.eta.property rate.sourceCap payload.anchor W payload.anchor_pos hW hWL hWU slice source =
      SnapshotRecordingKernel.dataAction p (.live payload.assignment snapshot)
        rate.eta.val rate.eta.property rate.sourceCap payload.anchor V payload.anchor_pos hV hVL hVU slice source := by
    simp only [SnapshotRecordingKernel.dataAction]
    split_ifs <;> try rfl
    exact congrArg Subtype.val (hfast _)
  have hprob (source : Fin p.m) (a : Fin p.K) :
      SnapshotRecordingKernel.actionProbability p (.live payload.assignment snapshot)
        rate.eta.val rate.eta.property rate.sourceCap payload.anchor W payload.anchor_pos hW hWL hWU source a =
      SnapshotRecordingKernel.actionProbability p (.live payload.assignment snapshot)
        rate.eta.val rate.eta.property rate.sourceCap payload.anchor V payload.anchor_pos hV hVL hVU source a := by
    simp only [SnapshotRecordingKernel.actionProbability]
    split_ifs <;> try rfl
    exact hq _
  apply Prod.ext
  · simp only [FastRewardSliceLaw.liveRecordingFastPair, SnapshotRecordingKernel.recordingMap,
      haction, SnapshotRecordingKernel.thinningThreshold, SnapshotRecordingKernel.rawGateMass, hprob]
    rfl
  · exact hfast _

/-- At the actual computed clear PRE prefix, BOTH branches have the canonical
correlated numerical-weight pair law. The reserved FAST is present for every
original scalar, including DATA and DOWN controls. -/
theorem liveRemainder_canonical_joint_law
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0)
    (hclear : (liveNumericalPast rate rewards C_star C_h q t s hs control0 x).2.1 = false) :
    let payload := livePayload rate rewards C_star C_h q t s hs control0 x
    let W := liveNumericalWeights rate rewards C_star C_h q t s hs control0 x
    ∃ (hpos : ∀ a, 0 < W a) (hlower : ∀ a, payload.anchor a ≤ W a)
      (hupper : ∀ a, W a ≤ 2 * payload.anchor a)
      (snapshot : ActiveRoundActions.Snapshot payload.assignment),
      (∀ a, payload.anchor a = 1) ∧
      (∀ u : TimeControl p,
        liveMarkerFastPair rate rewards C_star C_h q t s hs control0 (x, u) =
          retainOptionalFast (FastRewardSliceLaw.liveRecordingFastPair p rate.eta.val rate.eta.property
            rate.sourceCap payload.anchor W payload.anchor_pos hpos hlower hupper
            payload.assignment snapshot u.1)) ∧
      (ContinuousLearningRows.timeControlLaw p).map
        (fun u => liveMarkerFastPair rate rewards C_star C_h q t s hs control0 (x, u)) =
        (FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property rate.sourceCap
          payload.anchor W payload.anchor_pos hpos hlower hupper payload.assignment snapshot).map retainOptionalFast ∧
      (∀ family : ContinuousLearningRows.AffineSamples p,
        (ContinuousControlSlice.sliceLaw p.m p.K).map
          (fun slice => liveMarkerFastPair rate rewards C_star C_h q t s hs control0 (x, (slice, family))) =
          (FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property rate.sourceCap
            payload.anchor W payload.anchor_pos hpos hlower hupper payload.assignment snapshot).map retainOptionalFast) := by
  intro payload W
  obtain ⟨physicalPayload, V, hV, hVL, hVU, snapshot, hpayload, hcomp, hpoint, hlaw, hfamily⟩ :=
    liveRemainder_physical_joint_law rate rewards C_star C_h q t s hs control0 x
  subst physicalPayload
  have hunit : ∀ a, payload.anchor a = 1 :=
    livePayload_anchor_unit rate rewards C_star C_h q t s hs control0 x
  have hpos : ∀ a, 0 < W a := fun a =>
    (liveNumericalWeights_envelope rate rewards C_star C_h q t s hs control0 x a).1
  have hlower : ∀ a, payload.anchor a ≤ W a := by
    intro a
    rw [hunit a]
    exact (liveNumericalWeights_envelope rate rewards C_star C_h q t s hs control0 x a).2.1
  have hupper : ∀ a, W a ≤ 2 * payload.anchor a := by
    intro a
    rw [hunit a, mul_one]
    exact (liveNumericalWeights_envelope rate rewards C_star C_h q t s hs control0 x a).2.2.le
  have hpair (slice : CanonicalRecordingSlice.Slice p.m p.K) :=
    liveRecordingFastPair_eq_of_complement rate payload snapshot V W hV hpos
      hVL hlower hVU hupper (hcomp hclear) slice
  have hmeasure : FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property rate.sourceCap
      payload.anchor V payload.anchor_pos hV hVL hVU payload.assignment snapshot =
      FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property rate.sourceCap
        payload.anchor W payload.anchor_pos hpos hlower hupper payload.assignment snapshot :=
    Measure.map_congr (Filter.Eventually.of_forall hpair)
  refine ⟨hpos, hlower, hupper, snapshot, hunit, ?_, ?_, ?_⟩
  · intro u
    exact (hpoint u).trans (congrArg retainOptionalFast (hpair u.1))
  · exact hlaw.trans (congrArg (fun μ => μ.map retainOptionalFast) hmeasure)
  · intro family
    exact (hfamily family).2.trans (congrArg (fun μ => μ.map retainOptionalFast) hmeasure)

/-- The actual optional reserved draw is the canonical numerical-weight
sampler at the ORIGINAL current FAST scalar, for every whole current control. -/
theorem liveReservedFastOption_canonical
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0)
    (hclear : (liveNumericalPast rate rewards C_star C_h q t s hs control0 x).2.1 = false) :
    let payload := livePayload rate rewards C_star C_h q t s hs control0 x
    let W := liveNumericalWeights rate rewards C_star C_h q t s hs control0 x
    ∃ (hpos : ∀ a, 0 < W a) (hlower : ∀ a, payload.anchor a ≤ W a)
      (hupper : ∀ a, W a ≤ 2 * payload.anchor a),
      ∀ u : TimeControl p,
        liveReservedFastOption rate rewards C_star C_h q t s hs control0 (x, u) =
          some (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
            payload.anchor W payload.anchor_pos hpos hlower hupper payload.slowSet
            (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast u.1)).val := by
  intro payload W
  obtain ⟨hpos, hlower, hupper, snapshot, _, hpoint, _, _⟩ :=
    liveRemainder_canonical_joint_law rate rewards C_star C_h q t s hs control0 x hclear
  refine ⟨hpos, hlower, hupper, ?_⟩
  intro u
  have h := congrArg Prod.snd (hpoint u)
  simp only [liveMarkerFastPair, retainOptionalFast, FastRewardSliceLaw.liveRecordingFastPair,
    SnapshotRecordingKernel.fastArmDraw] at h
  rw [CoordinatorRecorderComplementBridge.assignmentSlowSet_eq_payload payload] at h
  exact h

/-- The actual FAST marginal has the canonical finite-arm law at the full
numerical vector. The physical marker is retained in the separate joint law. -/
theorem liveReservedFastOption_marginal
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0)
    (hclear : (liveNumericalPast rate rewards C_star C_h q t s hs control0 x).2.1 = false) :
    let payload := livePayload rate rewards C_star C_h q t s hs control0 x
    let W := liveNumericalWeights rate rewards C_star C_h q t s hs control0 x
    ∃ (hpos : ∀ a, 0 < W a) (hlower : ∀ a, payload.anchor a ≤ W a)
      (hupper : ∀ a, W a ≤ 2 * payload.anchor a),
      (ContinuousLearningRows.timeControlLaw p).map
        (fun u => liveReservedFastOption rate rewards C_star C_h q t s hs control0 (x, u)) =
        (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap
          payload.anchor W payload.anchor_pos hpos hlower hupper payload.slowSet).toMeasure.map
            (fun arm => some arm.val) := by
  intro payload W
  obtain ⟨hpos, hlower, hupper, snapshot, _, _, hlaw, _⟩ :=
    liveRemainder_canonical_joint_law rate rewards C_star C_h q t s hs control0 x hclear
  refine ⟨hpos, hlower, hupper, ?_⟩
  have hm : Measurable (fun u : TimeControl p =>
      liveMarkerFastPair rate rewards C_star C_h q t s hs control0 (x, u)) :=
    (measurable_liveMarkerFastPair rate rewards C_star C_h q t s hs control0).comp
      (measurable_const.prodMk measurable_id)
  have h := congrArg (fun μ => μ.map Prod.snd) hlaw
  rw [Measure.map_map measurable_snd hm,
    Measure.map_map measurable_snd (measurable_of_finite retainOptionalFast)] at h
  change (ContinuousLearningRows.timeControlLaw p).map
    (fun u => liveReservedFastOption rate rewards C_star C_h q t s hs control0 (x, u)) =
      (FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property rate.sourceCap
        payload.anchor W payload.anchor_pos hpos hlower hupper payload.assignment snapshot).map
          ((fun arm => some arm.val) ∘ Prod.snd) at h
  have hemb : Measurable (fun arm : CanonicalFastSampling.FastArm
      (SnapshotRecordingKernel.assignmentSlowSet p payload.assignment) => some arm.val) := measurable_of_finite _
  rw [← Measure.map_map hemb measurable_snd,
    FastRewardSliceLaw.liveRecordingFastPushforward_snd,
    CoordinatorRecorderComplementBridge.assignmentSlowSet_eq_payload payload] at h
  exact h

private theorem fixedFamily_joint_map {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (ν : Measure α) [SFinite ν] (tag : α → γ) (htag : Measurable tag)
    (pair : α × TimeControl p → β) (hm : Measurable pair)
    (family0 : ContinuousLearningRows.AffineSamples p)
    (hfamily : ∀ x family,
      (ContinuousControlSlice.sliceLaw p.m p.K).map (fun slice => pair (x, (slice, family))) =
        (ContinuousControlSlice.sliceLaw p.m p.K).map (fun slice => pair (x, (slice, family0)))) :
    (ν.prod (ContinuousLearningRows.timeControlLaw p)).map
      (fun xu => ((tag xu.1, xu.2.2), pair xu)) =
    (ν.prod (ContinuousLearningRows.timeControlLaw p)).map
      (fun xu => ((tag xu.1, xu.2.2), pair (xu.1, (xu.2.1, family0)))) := by
  let obs := fun xu : α × TimeControl p => ((tag xu.1, xu.2.2), pair xu)
  let obs0 := fun xu : α × TimeControl p => ((tag xu.1, xu.2.2), pair (xu.1, (xu.2.1, family0)))
  have ho : Measurable obs :=
    ((htag.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)).prodMk hm
  have ho0 : Measurable obs0 :=
    ((htag.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)).prodMk
      (hm.comp (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk measurable_const)))
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply ho hA, Measure.map_apply ho0 hA,
    Measure.prod_apply (hA.preimage ho), Measure.prod_apply (hA.preimage ho0)]
  apply lintegral_congr
  intro x
  have hs : MeasurableSet (Prod.mk x ⁻¹' obs ⁻¹' A) :=
    (hA.preimage ho).preimage measurable_prodMk_left
  have hs0 : MeasurableSet (Prod.mk x ⁻¹' obs0 ⁻¹' A) :=
    (hA.preimage ho0).preimage measurable_prodMk_left
  rw [ContinuousLearningRows.timeControlLaw, Measure.prod_apply_symm hs, Measure.prod_apply_symm hs0]
  apply lintegral_congr
  intro family
  have hB : MeasurableSet {b : β | ((tag x, family), b) ∈ A} :=
    hA.preimage (measurable_const.prodMk measurable_id)
  have h := congrArg (fun ρ : Measure β => ρ {b | ((tag x, family), b) ∈ A}) (hfamily x family)
  have hmf : Measurable (fun slice : CanonicalRecordingSlice.Slice p.m p.K => pair (x, (slice, family))) :=
    hm.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have hmf0 : Measurable (fun slice : CanonicalRecordingSlice.Slice p.m p.K => pair (x, (slice, family0))) :=
    hm.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  rw [Measure.map_apply hmf hB, Measure.map_apply hmf0 hB] at h
  exact h

/-- Preserve the original remainder and arbitrary current affine-family tests.
The fixed-family clause of the ACTUAL physical pair law supplies the transport. -/
theorem liveRemainder_fixedFamily_pair_map
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0)
    (family : ContinuousLearningRows.AffineSamples p) :
    (ContinuousControlSlice.sliceLaw p.m p.K).map
      (fun slice => liveMarkerFastPair rate rewards C_star C_h q t s hs control0 (x, (slice, family))) =
    (ContinuousControlSlice.sliceLaw p.m p.K).map
      (fun slice => liveMarkerFastPair rate rewards C_star C_h q t s hs control0 (x, (slice, control0.2))) := by
  obtain ⟨payload, W, hpos, hlower, hupper, snapshot, _, _, _, _, hfamily⟩ :=
    liveRemainder_physical_joint_law rate rewards C_star C_h q t s hs control0 x
  exact (hfamily family).2.trans (hfamily control0.2).2.symm

private theorem joint_map_restrict {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (τ : Measure Bool) [SFinite ν] [SFinite τ]
    (f : α → β × Bool) (hf : Measurable f) (hjoint : μ.map f = ν.prod τ)
    (B : Set β) (hB : MeasurableSet B) :
    (μ.restrict {z | (f z).1 ∈ B}).map f = (ν.restrict B).prod τ := by
  have h := congrArg (fun ρ : Measure (β × Bool) => ρ.restrict (B ×ˢ Set.univ)) hjoint
  rw [Measure.restrict_map hf (hB.prod MeasurableSet.univ),
    ← Measure.restrict_prod_eq_prod_univ B] at h
  simpa only [Set.preimage, Set.mem_prod, Set.mem_univ, and_true] using h

/-- The local event tests the COMPUTED strict-past flag only. -/
theorem measurableSet_liveClear :
    MeasurableSet {x | (liveNumericalPast rate rewards C_star C_h q t s hs control0 x).2.1 = false} :=
  measurableSet_eq_fun
    (measurable_fst.comp ((measurable_liveNumericalPast rate rewards C_star C_h q t s hs control0).snd))
    measurable_const

/-- The continuing finite UNNORMALIZED original source retains its remainder
and arbitrary affine-family tests while carrying the actual correlated pair. -/
theorem continuingSource_pair_affine_pushforward :
    let split := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
      rate rewards C_star C_h q t s hs control0
    let tag : ReferenceFirstLiveRecordingReadoutMeasurability.XPlus rate rewards C_star C_h q t s hs control0 →
      LiveRemainder rate rewards C_star C_h q t s hs control0 := Sum.inl
    let pair := fun xu => liveMarkerFastPair rate rewards C_star C_h q t s hs control0 (tag xu.1, xu.2)
    (ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
      rate rewards C_star C_h q t s hs control0).map
        (fun z => ((tag (split z).1, (split z).2.2), pair (split z))) =
    ((ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure
      rate rewards C_star C_h q t s hs control0).prod (ContinuousLearningRows.timeControlLaw p)).map
        (fun xu => ((tag xu.1, xu.2.2), pair (xu.1, (xu.2.1, control0.2)))) := by
  intro split tag pair
  have hm : Measurable pair :=
    (measurable_liveMarkerFastPair rate rewards C_star C_h q t s hs control0).comp
      ((measurable_inl.comp measurable_fst).prodMk measurable_snd)
  have ho : Measurable (fun xu : ReferenceFirstLiveRecordingReadoutMeasurability.XPlus
      rate rewards C_star C_h q t s hs control0 × TimeControl p =>
      ((tag xu.1, xu.2.2), pair xu)) :=
    ((measurable_inl.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)).prodMk hm
  change Measure.map ((fun xu => ((tag xu.1, xu.2.2), pair xu)) ∘ split) _ = _
  rw [← Measure.map_map ho (ReferenceFirstLiveRecordingSourceCylinder.measurable_branchSourceSplit
    rate rewards C_star C_h q t s hs control0), ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit_product]
  exact fixedFamily_joint_map _ tag measurable_inl pair hm control0.2
    (fun x family => liveRemainder_fixedFamily_pair_map
      rate rewards C_star C_h q t s hs control0 (tag x) family)

/-- The actual continuing pair/update readout retains ALL nonproposal
controls and has the independent original Bernoulli proposal law, also after
restriction to the COMPUTED clear PRE event. The detecting update is retained. -/
theorem continuingSource_pair_update_proposal_pushforward :
    let split := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
      rate rewards C_star C_h q t s hs control0
    let tag : ReferenceFirstLiveRecordingReadoutMeasurability.XPlus rate rewards C_star C_h q t s hs control0 →
      LiveRemainder rate rewards C_star C_h q t s hs control0 := Sum.inl
    let obs := fun z => ((tag (split z).1, (proposalControlSplit p (split z).2).2),
      liveFullPreProposalReadout rate rewards C_star C_h q t s hs control0 (tag (split z).1, (split z).2))
    let μ := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t s hs control0
    let ν := ((ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure
      rate rewards C_star C_h q t s hs control0).prod (proposalRestControlLaw p)).map
        (fun xr => liveNonpropObservation rate rewards C_star C_h q t s hs control0 (tag xr.1, xr.2))
    μ.map (fun z => (obs z, physicalProposalBit rate (split z).2)) = ν.prod (proposalBitLaw rate) ∧
    (μ.restrict {z | (liveNumericalPast rate rewards C_star C_h q t s hs control0 (obs z).1.1).2.1 = false}).map
      (fun z => (obs z, physicalProposalBit rate (split z).2)) =
      (ν.restrict {y | (liveNumericalPast rate rewards C_star C_h q t s hs control0 y.1.1).2.1 = false}).prod
        (proposalBitLaw rate) := by
  intro split tag obs μ ν
  let g := fun xr : ReferenceFirstLiveRecordingReadoutMeasurability.XPlus
      rate rewards C_star C_h q t s hs control0 × PropRestControl p =>
    liveNonpropObservation rate rewards C_star C_h q t s hs control0 (tag xr.1, xr.2)
  have hg : Measurable g :=
    (measurable_liveNonpropObservation rate rewards C_star C_h q t s hs control0).comp
      ((measurable_inl.comp measurable_fst).prodMk measurable_snd)
  let H := fun xu : ReferenceFirstLiveRecordingReadoutMeasurability.XPlus
      rate rewards C_star C_h q t s hs control0 × TimeControl p =>
    (g (xu.1, (proposalControlSplit p xu.2).2), physicalProposalBit rate xu.2)
  have hH : Measurable H :=
    (hg.comp (measurable_fst.prodMk
      (measurable_snd.comp ((proposalControlSplit p).measurable.comp measurable_snd)))).prodMk
      ((measurable_physicalProposalBit rate).comp measurable_snd)
  have heq : (fun z => (obs z, physicalProposalBit rate (split z).2)) = H ∘ split := by
    funext z
    exact congrArg (fun y => (y, physicalProposalBit rate (split z).2))
      (liveNonpropObservation_atControl rate rewards C_star C_h q t s hs control0
        (tag (split z).1) (split z).2).symm
  have hsplit := ReferenceFirstLiveRecordingSourceCylinder.measurable_branchSourceSplit rate rewards C_star C_h q t s hs control0
  have hactual : Measurable (fun z => (obs z, physicalProposalBit rate (split z).2)) := by
    rw [heq]
    exact hH.comp hsplit
  have hjoint : μ.map (fun z => (obs z, physicalProposalBit rate (split z).2)) = ν.prod (proposalBitLaw rate) := by
    rw [heq, ← Measure.map_map hH hsplit, ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit_product]
    exact proposalSplit_joint_pushforward _ g hg rate
  refine ⟨hjoint, ?_⟩
  exact joint_map_restrict μ ν (proposalBitLaw rate) _ hactual hjoint _
    ((measurableSet_liveClear rate rewards C_star C_h q t s hs control0).preimage
      (measurable_fst.comp measurable_fst))

/-- The empty finite UNNORMALIZED original source retains its remainder
and arbitrary affine-family tests while carrying the actual correlated pair. -/
theorem emptySource_pair_affine_pushforward :
    let split := ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
      rate rewards C_star C_h q t s hs control0
    let tag : ReferenceFirstLiveEmptyPendingMarkerLaw.Xempty rate rewards C_star C_h q t s hs control0 →
      LiveRemainder rate rewards C_star C_h q t s hs control0 := Sum.inr
    let pair := fun xu => liveMarkerFastPair rate rewards C_star C_h q t s hs control0 (tag xu.1, xu.2)
    (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
      rate rewards C_star C_h q t s hs control0).map
        (fun z => ((tag (split z).1, (split z).2.2), pair (split z))) =
    ((ReferenceFirstLiveEmptyPendingMarkerLaw.nuEmpty
      rate rewards C_star C_h q t s hs control0).prod (ContinuousLearningRows.timeControlLaw p)).map
        (fun xu => ((tag xu.1, xu.2.2), pair (xu.1, (xu.2.1, control0.2)))) := by
  intro split tag pair
  have hm : Measurable pair :=
    (measurable_liveMarkerFastPair rate rewards C_star C_h q t s hs control0).comp
      ((measurable_inr.comp measurable_fst).prodMk measurable_snd)
  have ho : Measurable (fun xu : ReferenceFirstLiveEmptyPendingMarkerLaw.Xempty
      rate rewards C_star C_h q t s hs control0 × TimeControl p =>
      ((tag xu.1, xu.2.2), pair xu)) :=
    ((measurable_inr.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)).prodMk hm
  change Measure.map ((fun xu => ((tag xu.1, xu.2.2), pair xu)) ∘ split) _ = _
  rw [← Measure.map_map ho (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_emptySourceSplit
    rate rewards C_star C_h q t s hs control0), ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit_product]
  exact fixedFamily_joint_map _ tag measurable_inr pair hm control0.2
    (fun x family => liveRemainder_fixedFamily_pair_map
      rate rewards C_star C_h q t s hs control0 (tag x) family)

/-- The actual empty pair/update readout retains ALL nonproposal
controls and has the independent original Bernoulli proposal law, also after
restriction to the COMPUTED clear PRE event. The detecting update is retained. -/
theorem emptySource_pair_update_proposal_pushforward :
    let split := ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
      rate rewards C_star C_h q t s hs control0
    let tag : ReferenceFirstLiveEmptyPendingMarkerLaw.Xempty rate rewards C_star C_h q t s hs control0 →
      LiveRemainder rate rewards C_star C_h q t s hs control0 := Sum.inr
    let obs := fun z => ((tag (split z).1, (proposalControlSplit p (split z).2).2),
      liveFullPreProposalReadout rate rewards C_star C_h q t s hs control0 (tag (split z).1, (split z).2))
    let μ := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t s hs control0
    let ν := ((ReferenceFirstLiveEmptyPendingMarkerLaw.nuEmpty
      rate rewards C_star C_h q t s hs control0).prod (proposalRestControlLaw p)).map
        (fun xr => liveNonpropObservation rate rewards C_star C_h q t s hs control0 (tag xr.1, xr.2))
    μ.map (fun z => (obs z, physicalProposalBit rate (split z).2)) = ν.prod (proposalBitLaw rate) ∧
    (μ.restrict {z | (liveNumericalPast rate rewards C_star C_h q t s hs control0 (obs z).1.1).2.1 = false}).map
      (fun z => (obs z, physicalProposalBit rate (split z).2)) =
      (ν.restrict {y | (liveNumericalPast rate rewards C_star C_h q t s hs control0 y.1.1).2.1 = false}).prod
        (proposalBitLaw rate) := by
  intro split tag obs μ ν
  let g := fun xr : ReferenceFirstLiveEmptyPendingMarkerLaw.Xempty
      rate rewards C_star C_h q t s hs control0 × PropRestControl p =>
    liveNonpropObservation rate rewards C_star C_h q t s hs control0 (tag xr.1, xr.2)
  have hg : Measurable g :=
    (measurable_liveNonpropObservation rate rewards C_star C_h q t s hs control0).comp
      ((measurable_inr.comp measurable_fst).prodMk measurable_snd)
  let H := fun xu : ReferenceFirstLiveEmptyPendingMarkerLaw.Xempty
      rate rewards C_star C_h q t s hs control0 × TimeControl p =>
    (g (xu.1, (proposalControlSplit p xu.2).2), physicalProposalBit rate xu.2)
  have hH : Measurable H :=
    (hg.comp (measurable_fst.prodMk
      (measurable_snd.comp ((proposalControlSplit p).measurable.comp measurable_snd)))).prodMk
      ((measurable_physicalProposalBit rate).comp measurable_snd)
  have heq : (fun z => (obs z, physicalProposalBit rate (split z).2)) = H ∘ split := by
    funext z
    exact congrArg (fun y => (y, physicalProposalBit rate (split z).2))
      (liveNonpropObservation_atControl rate rewards C_star C_h q t s hs control0
        (tag (split z).1) (split z).2).symm
  have hsplit := ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_emptySourceSplit rate rewards C_star C_h q t s hs control0
  have hactual : Measurable (fun z => (obs z, physicalProposalBit rate (split z).2)) := by
    rw [heq]
    exact hH.comp hsplit
  have hjoint : μ.map (fun z => (obs z, physicalProposalBit rate (split z).2)) = ν.prod (proposalBitLaw rate) := by
    rw [heq, ← Measure.map_map hH hsplit, ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit_product]
    exact proposalSplit_joint_pushforward _ g hg rate
  refine ⟨hjoint, ?_⟩
  exact joint_map_restrict μ ν (proposalBitLaw rate) _ hactual hjoint _
    ((measurableSet_liveClear rate rewards C_star C_h q t s hs control0).preimage
      (measurable_fst.comp measurable_fst))

/-- Read the existing source split on either original source restriction. -/
def originalLiveRemainder
    (tagged : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
        rate rewards C_star C_h q t s hs control0 ⊕
      ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0) :
    LiveRemainder rate rewards C_star C_h q t s hs control0 :=
  match tagged with
  | .inl z => .inl (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
      rate rewards C_star C_h q t s hs control0 z).1
  | .inr z => .inr (ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
      rate rewards C_star C_h q t s hs control0 z).1

/-- Numerical registers, flag and records on the restored source are exactly
the SAME ORIGINAL source's whole first-live strict prefix, on both branches. -/
theorem originalSource_numerical_prefix
    (tagged : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
        rate rewards C_star C_h q t s hs control0 ⊕
      ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0) :
    let z := Sum.elim Subtype.val Subtype.val tagged
    let past := RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((wholeFirstLiveCells rate rewards C_star C_h z.val).take (t.val - s))
    liveNumericalPast rate rewards C_star C_h q t s hs control0
      (originalLiveRemainder rate rewards C_star C_h q t s hs control0 tagged) =
        (past.registers, past.overflow, past.records) := by
  intro z past
  obtain ⟨_, _, _, hprefix⟩ := source_whole_prefix_alignment rate rewards C_star C_h q t s hs control0 tagged
  have hpast : liveNumericalPast rate rewards C_star C_h q t s hs control0
      (originalLiveRemainder rate rewards C_star C_h q t s hs control0 tagged) =
      ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout
        rate rewards C_star C_h q t s hs control0 z := by
    cases tagged with
    | inl point =>
        have h := continuingPreProposalReadout_actual rate rewards C_star C_h q t s hs control0 point
        exact congrArg (fun y : Option (Fin p.K) × NumericalUpdateFields p =>
          (y.2.beforeRegisters, y.2.beforeOverflow, y.2.beforeRecords)) h
    | inr point =>
        have h := emptyPreProposalReadout_actual rate rewards C_star C_h q t s hs control0 point
        exact congrArg (fun y : Option (Fin p.K) × NumericalUpdateFields p =>
          (y.2.beforeRegisters, y.2.beforeOverflow, y.2.beforeRecords)) h
  dsimp only [past]
  rw [hprefix]
  exact hpast

/-- The restored reserved readout is the existing operation at the original
physical record, with its original whole current control. -/
theorem originalSource_reservedFast
    (tagged : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
        rate rewards C_star C_h q t s hs control0 ⊕
      ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0) :
    let z := Sum.elim Subtype.val Subtype.val tagged
    liveReservedFastOption rate rewards C_star C_h q t s hs control0
      (originalLiveRemainder rate rewards C_star C_h q t s hs control0 tagged,
        ReferenceFirstLiveRecordingSourceCylinder.originalControl rate rewards C_star C_h q t s hs z) =
      reservedFastAtInput (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z).input := by
  intro z
  have hretained : liveRetained rate rewards C_star C_h q t s hs control0
      (originalLiveRemainder rate rewards C_star C_h q t s hs control0 tagged) =
      ReferenceFirstLiveRecordingSourceCylinder.sourceRetained rate rewards C_star C_h q t s hs control0 z := by
    cases tagged <;> rfl
  change reservedFastAtInput (sourceInputAtControl _ _) = _
  dsimp only [Prod.map, Function.id_def]
  rw [hretained, ReferenceFirstLiveRecordingSourceCylinder.sourceInputAtControl_eq_original]

end Bandits.Support.ReferenceFirstLiveCanonicalProposalJointLaw

end
