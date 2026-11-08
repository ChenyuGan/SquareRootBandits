/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveOriginalCalendarRoundedComparison
public import Bandits.Support.ReferenceFirstCollectionOldOriginalComparatorRounding
public import Bandits.Support.ReferenceFirstCollectionOriginalWeightedArrivalBudget

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic

/-!
# Original first-invocation calendar rounding join

This module adds the original LIVE, OLD, and actual CURRENT calendar observer
sums on the unchanged source law. It retains the datewise floor losses and
charges them against the shared actual source-cell mass budget.
-/

public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionOriginalCalendarRoundingJoin

open ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ActualInitializationPhysicalStep (GridRewardTable)
open ContinuousLearningRows (TimeControl)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefixFiltration)
open Bandits.Support.ReferenceFirstCollectionOldOriginalComparatorRounding

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ)

local notation "μ" => sourceInputLaw p
local notation "L" => ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells
  rate rewards C_star C_h
local notation "a" => ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart
  rate rewards C_star C_h

local instance sourceInputMeasurableSpace : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

private theorem firstLiveCell_rate_le_one (omega : SourceInput p)
    (k : Fin (L omega).length) (j : Fin p.K) :
    (L omega)[k.val].rate j ≤ 1 := by
  classical
  let boundary := ReferenceCompletePhysicalHistory.generatedBoundary
    rate omega rewards C_star C_h
  cases hcross : boundary.crossing with
  | none =>
      have hno := ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
        rate rewards C_star C_h omega (by simpa [boundary] using hcross)
      have hL : L omega = [] := by
        simpa [ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells] using hno.2.1
      rw [hL] at k
      exact Fin.elim0 k
  | some crossing =>
      have hc : (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput omega rewards C_star C_h rate)).crossing.isSome = true := by
        simpa [boundary, ReferenceCompletePhysicalHistory.generatedBoundary,
          ReferenceCompletePhysicalHistory.generatedInput] using
          (show boundary.crossing.isSome = true by simp [hcross])
      let start := ReferenceInitializationRun.elapsed p boundary.completed
      have hstart : a omega = start := by rfl
      have hstartLe : start ≤ p.T := by
        rw [← hstart]
        exact ReferenceCompletePhysicalHistory.physicalStart_le_T rate omega rewards C_star C_h
      let sf : Fin (p.T + 1) := ⟨start, Nat.lt_succ_of_le hstartLe⟩
      let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h start :=
        ⟨omega, ⟨hc, rfl⟩⟩
      let count := p.T - start
      let hspanFiber := ReferenceFirstLiveOverflowReadout.maximal_span sf
      have hwhole := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
        rate rewards C_star C_h sf x
      have hspan := ReferenceFirstLiveOverflowReadout.launch_span
        rate rewards C_star C_h start count hspanFiber x
      have hcellsActual : L omega =
          ReferenceFirstWindowNumericalStream.actualLiveSourceCells
            rate omega rewards C_star C_h hc count hspan := by
        simpa [ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells,
          ReferenceFirstLiveOverflowReadout.firstLiveCells, count, hspanFiber] using hwhole.2
      have hlenCells : (L omega).length =
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
            rate omega rewards C_star C_h hc count hspan).length :=
        congrArg List.length hcellsActual
      have hkActual : k.val <
          (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
            rate omega rewards C_star C_h hc count hspan).length := by
        calc
          k.val < (L omega).length := k.isLt
          _ = (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
              rate omega rewards C_star C_h hc count hspan).length := hlenCells
          _ = (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
              rate omega rewards C_star C_h hc count hspan).length :=
            ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
              rate omega rewards C_star C_h hc count hspan
      let kActual : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
          rate omega rewards C_star C_h hc count hspan).length := ⟨k.val, hkActual⟩
      let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
        rate omega rewards C_star C_h hc count hspan kActual
      have hfacts := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt_facts
        rate omega rewards C_star C_h hc count hspan kActual
      dsimp only at hfacts
      rcases hfacts with ⟨_, _, _, _, _, _, hrate, _, _⟩
      have hsourceGet := ReferenceFirstWindowNumericalStream.actualLiveSourceCells_get
        rate omega rewards C_star C_h hc count hspan kActual
      have hgetActual :
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
            rate omega rewards C_star C_h hc count hspan)[k.val]'(by
              rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
                rate omega rewards C_star C_h hc count hspan]
              exact kActual.isLt) = cell.input := by
        simpa [cell, kActual] using hsourceGet
      have hgetOption := congrArg
        (fun cells : List (RecordedQueueRun.RoundInput p.K) => cells[k.val]?) hcellsActual
      have hactualIndex : k.val <
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
            rate omega rewards C_star C_h hc count hspan).length := by
        calc
          k.val < (L omega).length := k.isLt
          _ = (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
              rate omega rewards C_star C_h hc count hspan).length := hlenCells
      rw [List.getElem?_eq_getElem k.isLt,
        List.getElem?_eq_getElem hactualIndex] at hgetOption
      have hget : (L omega)[k.val] =
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
            rate omega rewards C_star C_h hc count hspan)[k.val] :=
        Option.some.inj hgetOption
      change ((L omega)[k.val]'k.isLt).rate j ≤ 1
      rw [hget, hgetActual, hrate, cell.selected.view.payload.rate_eq_canonical]
      have hxi := CanonicalRecordingRates.xi_le_one_div_16mK p rate.eta.property
        rate.sourceCap cell.selected.view.payload.anchor
        cell.selected.view.payload.anchor_pos j
      have hm : (1 : ℝ) ≤ (p.m : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt (ConstructorDimensions.m_pos p))
      have hKnat : 1 ≤ p.K :=
        Nat.le_trans (Nat.succ_le_of_lt (ConstructorDimensions.m_pos p))
          (Nat.le_of_lt p.m_lt_K)
      have hK : (1 : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast hKnat
      have hmk : (1 : ℝ) ≤ (p.m : ℝ) * (p.K : ℝ) := by
        calc
          1 = 1 * 1 := by ring
          _ ≤ (p.m : ℝ) * (p.K : ℝ) :=
            mul_le_mul hm hK (by norm_num) (by positivity)
      have hden : (1 : ℝ) ≤ 16 * (p.m : ℝ) * (p.K : ℝ) := by nlinarith [hmk]
      have hdenPos : 0 < 16 * (p.m : ℝ) * (p.K : ℝ) := by positivity
      have hsmall : 1 / (16 * (p.m : ℝ) * (p.K : ℝ)) ≤ 1 :=
        (div_le_one hdenPos).2 hden
      exact hxi.trans hsmall

private theorem calendarRate_le_one (t : Fin p.T) (j : Fin p.K)
    (omega : SourceInput p) :
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRate
      rate rewards C_star C_h t j omega ≤ 1 := by
  unfold ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRate
  by_cases hstart : a omega ≤ t.val
  · rw [ite_eq_left hstart]
    cases hcell : (L omega)[t.val - a omega]? with
    | none => simp
    | some cell =>
        rcases List.getElem?_eq_some_iff.mp hcell with ⟨hidx, hget⟩
        let k : Fin (L omega).length := ⟨t.val - a omega, hidx⟩
        have hrate := firstLiveCell_rate_le_one rate rewards C_star C_h omega k j
        simpa only [k, hget] using hrate
  · simp [hstart]

/-- Pointwise LIVE floor payment on the actual retained-enabled mask, using
each actual calendar rate and the comparator cardinality. -/
theorem calendarFloorLoss_le_actualGateConstant (t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) (z : SourceInput p) :
    ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
        rate rewards C_star C_h t S z ≤
      (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
        rate rewards C_star C_h t).indicator
          (fun _ : SourceInput p =>
            (p.m : ℝ) / (rate.eta.val * (ConstructorDimensions.D p : ℝ))) z := by
  let g := ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
    rate rewards C_star C_h t
  let c := (p.m : ℝ) / (rate.eta.val * (ConstructorDimensions.D p : ℝ))
  have hden : 0 < rate.eta.val * (ConstructorDimensions.D p : ℝ) :=
    mul_pos rate.eta.property (by exact_mod_cast ConstructorDimensions.D_pos p)
  have hcard : S.1.card = p.m := (Finset.mem_powersetCard.mp S.2).2
  by_cases hz : z ∈ g
  · simp only [ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss]
    have hsum :
        (∑ j ∈ S.1,
          ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRate
            rate rewards C_star C_h t j z /
              (rate.eta.val * (ConstructorDimensions.D p : ℝ))) ≤ c := by
      calc
        _ ≤ ∑ j ∈ S.1,
            (1 : ℝ) / (rate.eta.val * (ConstructorDimensions.D p : ℝ)) := by
          apply Finset.sum_le_sum
          intro j hj
          exact div_le_div_of_nonneg_right
            (calendarRate_le_one rate rewards C_star C_h t j z) hden.le
        _ = (S.1.card : ℝ) *
            (1 / (rate.eta.val * (ConstructorDimensions.D p : ℝ))) := by simp
        _ = c := by rw [hcard]; dsimp [c]; ring
    simpa only [g, c, Set.indicator_of_mem hz] using hsum
  · simp [ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss,
      g, hz]

/-- Integrating the sharp LIVE pointwise estimate retains its actual mask. -/
theorem integral_calendarFloorLoss_le_actualGateMass (control0 : TimeControl p)
    (t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z, ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
      rate rewards C_star C_h t S z ∂μ) ≤
      (p.m : ℝ) / (rate.eta.val * (ConstructorDimensions.D p : ℝ)) *
        (sourceInputLaw p).real
          (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
          rate rewards C_star C_h t) := by
  let g := ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
    rate rewards C_star C_h t
  let c := (p.m : ℝ) / (rate.eta.val * (ConstructorDimensions.D p : ℝ))
  have hG := ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.measurableSet_retainedEnabledEvent
    rate rewards C_star C_h t control0
  have hfloor :=
    ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarFloorLoss
      rate rewards C_star C_h t S control0
  have hc : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) (le_of_lt
    (mul_pos rate.eta.property (by exact_mod_cast ConstructorDimensions.D_pos p)))
  have hconst : Integrable (g.indicator (fun _ : SourceInput p => c)) μ :=
    (integrable_const c).indicator hG
  have hpoint (z : SourceInput p) :
      ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
        rate rewards C_star C_h t S z ≤ g.indicator (fun _ => c) z := by
    have hb := calendarFloorLoss_le_actualGateConstant rate rewards C_star C_h t S z
    by_cases hz : z ∈ g
    · simpa [g, c, Set.indicator_of_mem hz] using hb
    · simpa [g, c, Set.indicator_of_notMem hz] using hb
  calc
    _ ≤ ∫ z, g.indicator (fun _ => c) z ∂μ :=
      integral_mono hfloor hconst hpoint
    _ = c * (sourceInputLaw p).real g := by
      rw [integral_indicator_const c hG, smul_eq_mul]
      dsimp [g]
      ring

/-- The LIVE retained mask is contained in the exact original phase 2/3/4
source cell, whose unnormalized mass is the accepted source-cell mass. -/
theorem integral_calendarFloorLoss_le_sourceCellMass (control0 : TimeControl p)
    (t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z, ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
      rate rewards C_star C_h t S z ∂μ) ≤
      (p.m : ℝ) / (rate.eta.val * (ConstructorDimensions.D p : ℝ)) *
        ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
          rate rewards C_star C_h t control0 := by
  let g := ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
    rate rewards C_star C_h t
  have hsubset : g ⊆
      (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
        (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
          ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4)) := by
    change ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
      rate rewards C_star C_h t ⊆ _
    rw [ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent_eq_phaseRestriction
      rate rewards C_star C_h t control0]
    intro z hz
    exact hz.1
  have hmass : (sourceInputLaw p).real g ≤
      ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
        rate rewards C_star C_h t control0 := by
    rw [ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass_eq_sourcePhase234
      rate rewards C_star C_h t control0, Set.union_assoc]
    exact MeasureTheory.measureReal_mono hsubset
  calc
    _ ≤ (p.m : ℝ) / (rate.eta.val * (ConstructorDimensions.D p : ℝ)) *
        (sourceInputLaw p).real g :=
      integral_calendarFloorLoss_le_actualGateMass rate rewards C_star C_h control0 t S
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (div_nonneg (Nat.cast_nonneg _)
      (le_of_lt (mul_pos rate.eta.property
        (by exact_mod_cast ConstructorDimensions.D_pos p))))

/-- An actual CURRENT floor term is charged only to its own retained-gate
mass, with the source-dependent calendar parameters and canonical rate. -/
theorem integral_currentFloorLoss_le_gateMass (control0 : TimeControl p)
    (u t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z, ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
      rate rewards C_star C_h u t S z ∂μ) ≤
      (p.m : ℝ) / (rate.eta.val * (ConstructorDimensions.D p : ℝ)) *
        (sourceInputLaw p).real
          (ReferenceFirstCollectionCurrentRetainedGate.G
            rate rewards C_star C_h u t) := by
  let g := ReferenceFirstCollectionCurrentRetainedGate.G
    rate rewards C_star C_h u t
  let c := (p.m : ℝ) / (rate.eta.val * (ConstructorDimensions.D p : ℝ))
  have hFle := (sourcePrefixFiltration control0).le' (t.val + 1)
  have hG : MeasurableSet g := hFle _
    (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
      rate rewards C_star C_h control0 u t)
  have hfloor :=
    ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss_integrable
      rate rewards C_star C_h control0 u t S
  have hc : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) (le_of_lt
    (mul_pos rate.eta.property (by exact_mod_cast ConstructorDimensions.D_pos p)))
  have hconst : Integrable (g.indicator (fun _ : SourceInput p => c)) μ :=
    (integrable_const c).indicator hG
  have hpoint (z : SourceInput p) :
      ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
        rate rewards C_star C_h u t S z ≤ g.indicator (fun _ => c) z := by
    by_cases hz : z ∈ g
    · have hb := ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss_le
        rate rewards C_star C_h u t S z
      simpa [g, c, Set.indicator_of_mem hz] using hb
    · simp [ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss,
        g, hz]
  calc
    _ ≤ ∫ z, g.indicator (fun _ => c) z ∂μ :=
      integral_mono hfloor hconst hpoint
    _ = c * (sourceInputLaw p).real g := by
      dsimp [g]
      rw [integral_indicator_const c hG, smul_eq_mul]
      ring

/-- The actual OLD raw comparator gap minus the predictable weighted raw
arrival readout, on its original retained gate. -/
@[expose] public def oldRawGap (t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) (z : SourceInput p) : ℝ :=
  ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorRaw
      rate rewards C_star C_h t S z -
    ∑ i : Fin p.K,
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i z *
      (ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t).indicator
        (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
          rate rewards C_star C_h t i) z

/-- The actual OLD rounded comparator gap minus its predictable rounded
weighted readout, on the same retained gate. -/
@[expose] public def oldRoundedGap (t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) (z : SourceInput p) : ℝ :=
  (ReferenceFirstCollectionOldCalendarExponentialStep.G
    rate rewards C_star C_h t).indicator (fun z =>
      (∑ i ∈ S.1,
        ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) -
      ∑ i : Fin p.K,
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) z

/-- Literal source-law sum of the actual LIVE, OLD, and first-invocation
CURRENT raw comparator gaps. -/
@[expose] public def originalCalendarRawGap
    (S : ProductSetLaw.ProductSet p.K p.m) (z : SourceInput p) : ℝ :=
  (∑ t : Fin p.T,
    ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarRawGap
      rate rewards C_star C_h t S z) +
  (∑ t : Fin p.T, oldRawGap rate rewards C_star C_h t S z) +
  ∑ u : Fin p.T, ∑ t : Fin p.T,
    ReferenceFirstCollectionCurrentOriginalRoundedComparison.rawGap
      rate rewards C_star C_h u t S z

/-- Literal source-law sum of the actual LIVE, OLD, and first-invocation
CURRENT rounded comparator gaps. -/
@[expose] public def originalCalendarRoundedGap
    (S : ProductSetLaw.ProductSet p.K p.m) (z : SourceInput p) : ℝ :=
  (∑ t : Fin p.T,
    ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarRoundedGap
      rate rewards C_star C_h t S z) +
  (∑ t : Fin p.T, oldRoundedGap rate rewards C_star C_h t S z) +
  ∑ u : Fin p.T, ∑ t : Fin p.T,
    ReferenceFirstCollectionCurrentOriginalRoundedComparison.roundedGap
      rate rewards C_star C_h u t S z

/-- Literal sum of the existing LIVE, OLD, and actual CURRENT positive floor
loss readouts, retaining every branch gate and the original unnormalized law. -/
@[expose] public def originalCalendarFloorLoss
    (S : ProductSetLaw.ProductSet p.K p.m) (z : SourceInput p) : ℝ :=
  (∑ t : Fin p.T,
    ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
      rate rewards C_star C_h t S z) +
  (∑ t : Fin p.T,
    ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
      rate rewards C_star C_h t S z) +
  ∑ u : Fin p.T, ∑ t : Fin p.T,
    ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
      rate rewards C_star C_h u t S z

private theorem integrable_of_bounded_measurable
    {f : SourceInput p → ℝ} (hf : Measurable f) (C : ℝ)
    (_hC : 0 ≤ C) (hbound : ∀ z, ‖f z‖ ≤ C) : Integrable f μ := by
  have hconst : Integrable (fun _ : SourceInput p => C) μ := integrable_const C
  refine hconst.mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with z
  simpa [Real.norm_eq_abs, abs_of_nonneg _hC] using hbound z

private def oldWeightedRaw (t : Fin p.T) (z : SourceInput p) : ℝ :=
  ∑ i : Fin p.K,
    ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
      rate rewards C_star C_h t i z *
    (ReferenceFirstCollectionOldCalendarExponentialStep.G
      rate rewards C_star C_h t).indicator
      (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
        rate rewards C_star C_h t i) z

private def oldWeightedRounded (t : Fin p.T) (z : SourceInput p) : ℝ :=
  (ReferenceFirstCollectionOldCalendarExponentialStep.G
    rate rewards C_star C_h t).indicator (fun z =>
      ∑ i : Fin p.K,
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) z

private theorem oldWeightedRaw_integrable (control0 : TimeControl p)
    (t : Fin p.T) : Integrable (oldWeightedRaw rate rewards C_star C_h t) μ := by
  unfold oldWeightedRaw
  exact integrable_finsetSum Finset.univ (fun i _ =>
    ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldWeightedArrival_integrable
      rate rewards C_star C_h control0 t i)

private theorem oldWeightedRounded_integrable (control0 : TimeControl p)
    (t : Fin p.T) : Integrable (oldWeightedRounded rate rewards C_star C_h t) μ := by
  let g := ReferenceFirstCollectionOldCalendarExponentialStep.G
    rate rewards C_star C_h t
  have hFle := (sourcePrefixFiltration control0).le' (t.val + 1)
  have hG : MeasurableSet g := hFle _
    (ReferenceFirstCollectionOldCalendarExponentialStep.measurableSet_G
      rate rewards C_star C_h control0 t)
  have htheta (i : Fin p.K) :
      Measurable (fun z : SourceInput p =>
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z) := by
    exact Measurable.mono
      (ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldIncomingTheta_predictable_bounds
        rate rewards C_star C_h control0 t i).1 hFle le_rfl
  have hsum : Measurable (fun z : SourceInput p =>
      ∑ i : Fin p.K,
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) := by
    exact Finset.measurable_sum Finset.univ (fun i hi =>
      (htheta i).mul measurable_const)
  have hmeas : Measurable (oldWeightedRounded rate rewards C_star C_h t) := by
    change Measurable (g.indicator _)
    exact hsum.indicator hG
  have hbound (z : SourceInput p) :
      ‖oldWeightedRounded rate rewards C_star C_h t z‖ ≤ (p.K : ℝ) := by
    have hthetaBounds := fun i =>
      (ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldIncomingTheta_predictable_bounds
        rate rewards C_star C_h control0 t i).2 z
    have hreward (i : Fin p.K) :
        0 ≤ ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i ∧
        ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i ≤ 1 := by
      exact ReferenceFirstCollectionOldRecorderFoundation.roundedReward_bounds rewards t i
    have hterm (i : Fin p.K) :
        0 ≤ ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i ∧
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i ≤ 1 := by
      refine ⟨mul_nonneg (hthetaBounds i).1 (hreward i).1, ?_⟩
      calc
        _ ≤ ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
              rate rewards C_star C_h t i z * 1 :=
          mul_le_mul_of_nonneg_left (hreward i).2 (hthetaBounds i).1
        _ = ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
              rate rewards C_star C_h t i z := mul_one _
        _ ≤ 1 := (hthetaBounds i).2
    have hsum0 : 0 ≤ ∑ i : Fin p.K,
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i :=
      Finset.sum_nonneg fun i _ => (hterm i).1
    have hsum1 : (∑ i : Fin p.K,
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) ≤
        (p.K : ℝ) := by
      calc
        _ ≤ ∑ _i : Fin p.K, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hterm i).2
        _ = (p.K : ℝ) := by simp
    by_cases hz : z ∈ g
    · unfold oldWeightedRounded
      change ‖(g.indicator (fun z =>
        ∑ i : Fin p.K,
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) z)‖ ≤ _
      rw [Set.indicator_of_mem hz]
      rw [Real.norm_eq_abs, abs_of_nonneg hsum0]
      exact hsum1
    · unfold oldWeightedRounded
      change ‖(g.indicator (fun z =>
        ∑ i : Fin p.K,
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) z)‖ ≤ _
      rw [Set.indicator_of_notMem hz]
      simp
  exact integrable_of_bounded_measurable hmeas (p.K : ℝ)
    (Nat.cast_nonneg _) hbound

/-- The OLD predictable weighted raw arrival integral is no larger than the
same-gate rounded weighted reward integral. -/
private theorem integral_oldWeightedRaw_le_rounded (control0 : TimeControl p)
    (t : Fin p.T) :
    (∫ z, oldWeightedRaw rate rewards C_star C_h t z ∂μ) ≤
      ∫ z, oldWeightedRounded rate rewards C_star C_h t z ∂μ := by
  have hFle := (sourcePrefixFiltration control0).le' (t.val + 1)
  have hraw : Integrable (oldWeightedRaw rate rewards C_star C_h t) μ :=
    oldWeightedRaw_integrable rate rewards C_star C_h control0 t
  have hround : Integrable (oldWeightedRounded rate rewards C_star C_h t) μ :=
    oldWeightedRounded_integrable rate rewards C_star C_h control0 t
  have hcond (i : Fin p.K) :
      μ[(fun z =>
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t).indicator
          (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
            rate rewards C_star C_h t i) z) |
        sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[μ]
      (fun z => ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i z *
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
          rate rewards C_star C_h t i z) :=
    ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldWeightedArrival_condExp
      rate rewards C_star C_h control0 t i
  have hce (i : Fin p.K) :
      (∫ z, (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z) *
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t).indicator
          (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
            rate rewards C_star C_h t i) z ∂μ) =
      ∫ z, ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
          rate rewards C_star C_h t i z ∂μ := by
    let f : SourceInput p → ℝ := fun z =>
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i z *
      (ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t).indicator
        (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
          rate rewards C_star C_h t i) z
    change (∫ z : SourceInput p, f z ∂μ) = _
    calc
      _ = ∫ z : SourceInput p, μ[f | sourcePrefixFiltration control0 (t.val + 1)] z ∂μ := by
            symm
            exact integral_condExp (f := f) hFle
      _ = ∫ z : SourceInput p,
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
            rate rewards C_star C_h t i z ∂μ := by
            exact integral_congr_ae (hcond i)
  have hsum_raw :
      (∫ z, oldWeightedRaw rate rewards C_star C_h t z ∂μ) =
        ∑ i : Fin p.K, ∫ z,
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          (ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h t).indicator
            (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
              rate rewards C_star C_h t i) z ∂μ := by
    simp only [oldWeightedRaw]
    rw [integral_finsetSum Finset.univ (fun i hi =>
      ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldWeightedArrival_integrable
        rate rewards C_star C_h control0 t i)]
  have hpoint (z : SourceInput p) :
      (∑ i : Fin p.K,
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
          rate rewards C_star C_h t i z) ≤
      oldWeightedRounded rate rewards C_star C_h t z := by
    let g := ReferenceFirstCollectionOldCalendarExponentialStep.G
      rate rewards C_star C_h t
    by_cases hz : z ∈ g
    · unfold oldWeightedRounded
      change (∑ i : Fin p.K,
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
            rate rewards C_star C_h t i z) ≤
        (g.indicator (fun z =>
          ∑ i : Fin p.K,
            ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
              rate rewards C_star C_h t i z *
            ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) z)
      rw [Set.indicator_of_mem hz]
      apply Finset.sum_le_sum
      intro i _
      have hb := old_retained_moment_one_reward_bounds rate rewards C_star C_h t i z
      have htheta :=
        (ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldIncomingTheta_predictable_bounds
          rate rewards C_star C_h control0 t i).2 z
      have hmoment :
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
            rate rewards C_star C_h t i z ≤
          ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i := by
        simpa [g, Set.indicator_of_mem hz] using hb.2.1
      exact mul_le_mul_of_nonneg_left hmoment htheta.1
    · have hmoment (i : Fin p.K) :
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
          rate rewards C_star C_h t i z = 0 := by
        have hb := old_retained_moment_one_reward_bounds rate rewards C_star C_h t i z
        have hz' : z ∉ ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h t := hz
        have hzero : (ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h t).indicator (fun _ =>
            ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) z = 0 :=
          Set.indicator_of_notMem hz' _
        have hm0 : ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
            rate rewards C_star C_h t i z ≤ 0 := by
          calc
            _ ≤ (ReferenceFirstCollectionOldCalendarExponentialStep.G
                rate rewards C_star C_h t).indicator (fun _ =>
                  ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) z :=
              hb.2.1
            _ = 0 := hzero
        exact le_antisymm hm0 hb.1
      unfold oldWeightedRounded
      change (∑ i : Fin p.K,
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
            rate rewards C_star C_h t i z) ≤
        (g.indicator (fun z =>
          ∑ i : Fin p.K,
            ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
              rate rewards C_star C_h t i z *
            ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) z)
      rw [Set.indicator_of_notMem hz]
      simp [hmoment]
  have hmomentInt (i : Fin p.K) : Integrable (fun z : SourceInput p =>
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i z *
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
        rate rewards C_star C_h t i z) μ := by
    exact (integrable_condExp
      (m := sourcePrefixFiltration control0 (t.val + 1))
      (f := fun z =>
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t).indicator
          (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
            rate rewards C_star C_h t i) z)).congr (hcond i)
  have hsumMoment :
      (∑ i : Fin p.K, ∫ z,
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t).indicator
          (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
            rate rewards C_star C_h t i) z ∂μ) =
      ∫ z, (∑ i : Fin p.K,
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
          rate rewards C_star C_h t i z) ∂μ := by
    calc
      (∑ i : Fin p.K, ∫ z,
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          (ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h t).indicator
            (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
              rate rewards C_star C_h t i) z ∂μ) =
        ∑ i : Fin p.K, ∫ z,
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
            rate rewards C_star C_h t i z ∂μ := by
        exact Finset.sum_congr rfl fun i _ => hce i
      _ = ∫ z, (∑ i : Fin p.K,
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
            rate rewards C_star C_h t i z) ∂μ := by
        symm
        rw [integral_finsetSum Finset.univ (fun i hi => hmomentInt i)]
  have hmomentSumInt : Integrable (fun z : SourceInput p =>
      ∑ i : Fin p.K,
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
          rate rewards C_star C_h t i z) μ :=
    integrable_finsetSum Finset.univ (fun i _ => hmomentInt i)
  rw [hsum_raw, hsumMoment]
  exact integral_mono hmomentSumInt hround hpoint

private theorem oldRawGap_eq (t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m) :
    oldRawGap rate rewards C_star C_h t S = fun z =>
      ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorRaw
        rate rewards C_star C_h t S z - oldWeightedRaw rate rewards C_star C_h t z := rfl

private theorem oldRoundedGap_eq (t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    oldRoundedGap rate rewards C_star C_h t S = fun z =>
      ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorRounded
        rate rewards C_star C_h t S z - oldWeightedRounded rate rewards C_star C_h t z := by
  funext z
  let g := ReferenceFirstCollectionOldCalendarExponentialStep.G
    rate rewards C_star C_h t
  by_cases hz : z ∈ g
  · simp [oldRoundedGap, oldWeightedRounded,
      ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorRounded,
      g, Set.indicator_of_mem hz]
  · simp [oldRoundedGap, oldWeightedRounded,
      ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorRounded,
      g, Set.indicator_of_notMem hz]

/-- Original-law integrability of the literal OLD raw-gap readout. -/
theorem oldRawGap_integrable (control0 : TimeControl p) (t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (oldRawGap rate rewards C_star C_h t S) μ := by
  rw [oldRawGap_eq]
  exact
    (ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_raw_integrable
      rate rewards C_star C_h control0 t S).sub
      (oldWeightedRaw_integrable rate rewards C_star C_h control0 t)

/-- Original-law integrability of the literal OLD rounded-gap readout. -/
theorem oldRoundedGap_integrable (control0 : TimeControl p) (t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (oldRoundedGap rate rewards C_star C_h t S) μ := by
  rw [oldRoundedGap_eq]
  exact
    (ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_rounded_integrable
      rate rewards C_star C_h control0 t S).sub
      (oldWeightedRounded_integrable rate rewards C_star C_h control0 t)

/-- The missing OLD weighted-gap transfer, with the comparator's accepted
floor estimate and the actual predictable weighted raw/rounded comparison. -/
theorem integral_oldRoundedGap_le_raw_add_floor (control0 : TimeControl p)
    (t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z, oldRoundedGap rate rewards C_star C_h t S z ∂μ) ≤
      (∫ z, oldRawGap rate rewards C_star C_h t S z ∂μ) +
        ∫ z, ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
          rate rewards C_star C_h t S z ∂μ := by
  have hcompR :=
    ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_rounded_integrable
      rate rewards C_star C_h control0 t S
  have hcompA :=
    ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_raw_integrable
      rate rewards C_star C_h control0 t S
  have hfloor :=
    ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_floor_loss_integrable
      rate rewards C_star C_h control0 t S
  have hweightedR := oldWeightedRounded_integrable rate rewards C_star C_h control0 t
  have hweightedA := oldWeightedRaw_integrable rate rewards C_star C_h control0 t
  have hrounded :=
    old_comparator_integral_rounded_le_raw_add_floor
      rate rewards C_star C_h control0 t S
  have hweight := integral_oldWeightedRaw_le_rounded rate rewards C_star C_h control0 t
  rw [oldRoundedGap_eq, oldRawGap_eq, integral_sub hcompR hweightedR,
    integral_sub hcompA hweightedA]
  linarith

/-- The complete original raw calendar observer is integrable. -/
theorem originalCalendarRawGap_integrable (control0 : TimeControl p)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (originalCalendarRawGap rate rewards C_star C_h S) μ := by
  unfold originalCalendarRawGap
  apply Integrable.add
  · apply Integrable.add
    · exact integrable_finsetSum Finset.univ (fun t _ =>
        ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarRawGap
          rate rewards C_star C_h t S control0)
    · exact integrable_finsetSum Finset.univ (fun t _ =>
        oldRawGap_integrable rate rewards C_star C_h control0 t S)
  · exact integrable_finsetSum Finset.univ (fun u _ =>
      integrable_finsetSum Finset.univ (fun t _ =>
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.rawGap_integrable
          rate rewards C_star C_h control0 u t S))

/-- The complete original rounded calendar observer is integrable. -/
theorem originalCalendarRoundedGap_integrable (control0 : TimeControl p)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (originalCalendarRoundedGap rate rewards C_star C_h S) μ := by
  unfold originalCalendarRoundedGap
  apply Integrable.add
  · apply Integrable.add
    · exact integrable_finsetSum Finset.univ (fun t _ =>
        ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarRoundedGap
          rate rewards C_star C_h t S control0)
    · exact integrable_finsetSum Finset.univ (fun t _ =>
        oldRoundedGap_integrable rate rewards C_star C_h control0 t S)
  · exact integrable_finsetSum Finset.univ (fun u _ =>
      integrable_finsetSum Finset.univ (fun t _ =>
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.roundedGap_integrable
          rate rewards C_star C_h control0 u t S))

/-- The complete explicit calendar floor loss is integrable. -/
theorem originalCalendarFloorLoss_integrable (control0 : TimeControl p)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (originalCalendarFloorLoss rate rewards C_star C_h S) μ := by
  unfold originalCalendarFloorLoss
  apply Integrable.add
  · apply Integrable.add
    · exact integrable_finsetSum Finset.univ (fun t _ =>
        ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarFloorLoss
          rate rewards C_star C_h t S control0)
    · exact integrable_finsetSum Finset.univ (fun t _ =>
        ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_floor_loss_integrable
          rate rewards C_star C_h control0 t S)
  · exact integrable_finsetSum Finset.univ (fun u _ =>
      integrable_finsetSum Finset.univ (fun t _ =>
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss_integrable
          rate rewards C_star C_h control0 u t S))

/-- The complete original-calendar rounded gap is bounded by the raw gap and
the exact LIVE, OLD, and actual CURRENT floor losses, without yet relaxing
that explicit floor loss to a horizon constant. -/
theorem integral_originalCalendarRoundedGap_le_raw_add_floorLoss
    (control0 : TimeControl p) (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z, originalCalendarRoundedGap rate rewards C_star C_h S z ∂μ) ≤
      (∫ z, originalCalendarRawGap rate rewards C_star C_h S z ∂μ) +
        ∫ z, originalCalendarFloorLoss rate rewards C_star C_h S z ∂μ := by
  let liveR := fun z : SourceInput p =>
    ∑ t : Fin p.T,
      ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarRoundedGap
        rate rewards C_star C_h t S z
  let liveA := fun z : SourceInput p =>
    ∑ t : Fin p.T,
      ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarRawGap
        rate rewards C_star C_h t S z
  let liveF := fun z : SourceInput p =>
    ∑ t : Fin p.T,
      ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
        rate rewards C_star C_h t S z
  let oldR := fun z : SourceInput p =>
    ∑ t : Fin p.T, oldRoundedGap rate rewards C_star C_h t S z
  let oldA := fun z : SourceInput p =>
    ∑ t : Fin p.T, oldRawGap rate rewards C_star C_h t S z
  let oldF := fun z : SourceInput p =>
    ∑ t : Fin p.T,
      ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
        rate rewards C_star C_h t S z
  let curR := fun z : SourceInput p =>
    ∑ u : Fin p.T, ∑ t : Fin p.T,
      ReferenceFirstCollectionCurrentOriginalRoundedComparison.roundedGap
        rate rewards C_star C_h u t S z
  let curA := fun z : SourceInput p =>
    ∑ u : Fin p.T, ∑ t : Fin p.T,
      ReferenceFirstCollectionCurrentOriginalRoundedComparison.rawGap
        rate rewards C_star C_h u t S z
  let curF := fun z : SourceInput p =>
    ∑ u : Fin p.T, ∑ t : Fin p.T,
      ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
        rate rewards C_star C_h u t S z
  have hLiveRI : Integrable liveR μ := by
    exact integrable_finsetSum Finset.univ (fun t _ =>
      ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarRoundedGap
        rate rewards C_star C_h t S control0)
  have hLiveAI : Integrable liveA μ := by
    exact integrable_finsetSum Finset.univ (fun t _ =>
      ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarRawGap
        rate rewards C_star C_h t S control0)
  have hLiveFI : Integrable liveF μ := by
    exact integrable_finsetSum Finset.univ (fun t _ =>
      ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarFloorLoss
        rate rewards C_star C_h t S control0)
  have hOldRI : Integrable oldR μ := by
    exact integrable_finsetSum Finset.univ (fun t _ =>
      oldRoundedGap_integrable rate rewards C_star C_h control0 t S)
  have hOldAI : Integrable oldA μ := by
    exact integrable_finsetSum Finset.univ (fun t _ =>
      oldRawGap_integrable rate rewards C_star C_h control0 t S)
  have hOldFI : Integrable oldF μ := by
    exact integrable_finsetSum Finset.univ (fun t _ =>
      ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_floor_loss_integrable
        rate rewards C_star C_h control0 t S)
  have hCurRI : Integrable curR μ := by
    exact integrable_finsetSum Finset.univ (fun u _ =>
      integrable_finsetSum Finset.univ (fun t _ =>
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.roundedGap_integrable
          rate rewards C_star C_h control0 u t S))
  have hCurAI : Integrable curA μ := by
    exact integrable_finsetSum Finset.univ (fun u _ =>
      integrable_finsetSum Finset.univ (fun t _ =>
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.rawGap_integrable
          rate rewards C_star C_h control0 u t S))
  have hCurFI : Integrable curF μ := by
    exact integrable_finsetSum Finset.univ (fun u _ =>
      integrable_finsetSum Finset.univ (fun t _ =>
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss_integrable
          rate rewards C_star C_h control0 u t S))
  have hLive : (∫ z, liveR z ∂μ) ≤ (∫ z, liveA z ∂μ) + ∫ z, liveF z ∂μ := by
    have hR := integral_finsetSum Finset.univ (fun t _ =>
      ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarRoundedGap
        rate rewards C_star C_h t S control0)
    have hA := integral_finsetSum Finset.univ (fun t _ =>
      ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarRawGap
        rate rewards C_star C_h t S control0)
    have hF := integral_finsetSum Finset.univ (fun t _ =>
      ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarFloorLoss
        rate rewards C_star C_h t S control0)
    rw [hR, hA, hF]
    calc
      _ ≤ ∑ t : Fin p.T,
          ((∫ z, ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarRawGap
                rate rewards C_star C_h t S z ∂μ) +
            ∫ z, ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
                rate rewards C_star C_h t S z ∂μ) :=
        Finset.sum_le_sum fun t _ =>
          ReferenceFirstLiveOriginalCalendarRoundedComparison.integral_calendarRoundedGap_le_raw_add_floor
            rate rewards C_star C_h t S control0
      _ = _ := Finset.sum_add_distrib
  have hOld : (∫ z, oldR z ∂μ) ≤ (∫ z, oldA z ∂μ) + ∫ z, oldF z ∂μ := by
    have hR := integral_finsetSum Finset.univ (fun t _ =>
      oldRoundedGap_integrable rate rewards C_star C_h control0 t S)
    have hA := integral_finsetSum Finset.univ (fun t _ =>
      oldRawGap_integrable rate rewards C_star C_h control0 t S)
    have hF := integral_finsetSum Finset.univ (fun t _ =>
      ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_floor_loss_integrable
        rate rewards C_star C_h control0 t S)
    rw [hR, hA, hF]
    calc
      _ ≤ ∑ t : Fin p.T,
          ((∫ z, oldRawGap rate rewards C_star C_h t S z ∂μ) +
            ∫ z, ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
                rate rewards C_star C_h t S z ∂μ) :=
        Finset.sum_le_sum fun t _ =>
          integral_oldRoundedGap_le_raw_add_floor rate rewards C_star C_h control0 t S
      _ = _ := Finset.sum_add_distrib
  have hCur : (∫ z, curR z ∂μ) ≤ (∫ z, curA z ∂μ) + ∫ z, curF z ∂μ := by
    have hR := integral_finsetSum Finset.univ (fun u _ =>
      integrable_finsetSum Finset.univ (fun t _ =>
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.roundedGap_integrable
          rate rewards C_star C_h control0 u t S))
    have hA := integral_finsetSum Finset.univ (fun u _ =>
      integrable_finsetSum Finset.univ (fun t _ =>
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.rawGap_integrable
          rate rewards C_star C_h control0 u t S))
    have hF := integral_finsetSum Finset.univ (fun u _ =>
      integrable_finsetSum Finset.univ (fun t _ =>
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss_integrable
          rate rewards C_star C_h control0 u t S))
    have hRinner (u : Fin p.T) :
        (∫ z, ∑ t : Fin p.T,
          ReferenceFirstCollectionCurrentOriginalRoundedComparison.roundedGap
            rate rewards C_star C_h u t S z ∂μ) =
          ∑ t : Fin p.T, ∫ z,
            ReferenceFirstCollectionCurrentOriginalRoundedComparison.roundedGap
              rate rewards C_star C_h u t S z ∂μ := by
      rw [integral_finsetSum Finset.univ (fun t _ =>
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.roundedGap_integrable
          rate rewards C_star C_h control0 u t S)]
    have hAinner (u : Fin p.T) :
        (∫ z, ∑ t : Fin p.T,
          ReferenceFirstCollectionCurrentOriginalRoundedComparison.rawGap
            rate rewards C_star C_h u t S z ∂μ) =
          ∑ t : Fin p.T, ∫ z,
            ReferenceFirstCollectionCurrentOriginalRoundedComparison.rawGap
              rate rewards C_star C_h u t S z ∂μ := by
      rw [integral_finsetSum Finset.univ (fun t _ =>
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.rawGap_integrable
          rate rewards C_star C_h control0 u t S)]
    have hFinner (u : Fin p.T) :
        (∫ z, ∑ t : Fin p.T,
          ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
            rate rewards C_star C_h u t S z ∂μ) =
          ∑ t : Fin p.T, ∫ z,
            ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
              rate rewards C_star C_h u t S z ∂μ := by
      rw [integral_finsetSum Finset.univ (fun t _ =>
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss_integrable
          rate rewards C_star C_h control0 u t S)]
    have hCurU (u : Fin p.T) :
        (∫ z, ∑ t : Fin p.T,
          ReferenceFirstCollectionCurrentOriginalRoundedComparison.roundedGap
            rate rewards C_star C_h u t S z ∂μ) ≤
          (∫ z, ∑ t : Fin p.T,
            ReferenceFirstCollectionCurrentOriginalRoundedComparison.rawGap
              rate rewards C_star C_h u t S z ∂μ) +
            ∫ z, ∑ t : Fin p.T,
              ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
                rate rewards C_star C_h u t S z ∂μ := by
      rw [hRinner u, hAinner u, hFinner u, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun t _ =>
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.integral_roundedGap_le_rawGap_add_floorLoss
          rate rewards C_star C_h control0 u t S
    rw [hR, hA, hF, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun u _ => hCurU u
  have hroundEq : originalCalendarRoundedGap rate rewards C_star C_h S =
      fun z => liveR z + oldR z + curR z := by funext z; rfl
  have hrawEq : originalCalendarRawGap rate rewards C_star C_h S =
      fun z => liveA z + oldA z + curA z := by funext z; rfl
  have hfloorEq : originalCalendarFloorLoss rate rewards C_star C_h S =
      fun z => liveF z + oldF z + curF z := by funext z; rfl
  have hRoundTotal :
      (∫ z, (liveR z + oldR z) + curR z ∂μ) =
        (∫ z, liveR z ∂μ) + (∫ z, oldR z ∂μ) + ∫ z, curR z ∂μ := by
    calc
      _ = (∫ z, liveR z + oldR z ∂μ) + ∫ z, curR z ∂μ :=
        integral_add (hLiveRI.add hOldRI) hCurRI
      _ = _ := by rw [integral_add hLiveRI hOldRI]
  have hRawTotal :
      (∫ z, (liveA z + oldA z) + curA z ∂μ) =
        (∫ z, liveA z ∂μ) + (∫ z, oldA z ∂μ) + ∫ z, curA z ∂μ := by
    calc
      _ = (∫ z, liveA z + oldA z ∂μ) + ∫ z, curA z ∂μ :=
        integral_add (hLiveAI.add hOldAI) hCurAI
      _ = _ := by rw [integral_add hLiveAI hOldAI]
  have hFloorTotal :
      (∫ z, (liveF z + oldF z) + curF z ∂μ) =
        (∫ z, liveF z ∂μ) + (∫ z, oldF z ∂μ) + ∫ z, curF z ∂μ := by
    calc
      _ = (∫ z, liveF z + oldF z ∂μ) + ∫ z, curF z ∂μ :=
        integral_add (hLiveFI.add hOldFI) hCurFI
      _ = _ := by rw [integral_add hLiveFI hOldFI]
  rw [hroundEq, hrawEq, hfloorEq]
  change (∫ z, (liveR z + oldR z) + curR z ∂μ) ≤
    (∫ z, (liveA z + oldA z) + curA z ∂μ) +
      ∫ z, (liveF z + oldF z) + curF z ∂μ
  rw [hRoundTotal, hRawTotal, hFloorTotal]
  linarith

/-- The three actual floor contributions share the original per-date source
budget, so their total charge is one finite-horizon normalization. -/
theorem integral_originalCalendarFloorLoss_le_horizon
    (control0 : TimeControl p) (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z, originalCalendarFloorLoss rate rewards C_star C_h S z ∂μ) ≤
      (p.m : ℝ) * (p.T : ℝ) /
        (rate.eta.val * (ConstructorDimensions.D p : ℝ)) := by
  let c := (p.m : ℝ) / (rate.eta.val * (ConstructorDimensions.D p : ℝ))
  let liveSum := fun z : SourceInput p =>
    ∑ t : Fin p.T,
      ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
        rate rewards C_star C_h t S z
  let oldSum := fun z : SourceInput p =>
    ∑ t : Fin p.T,
      ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
        rate rewards C_star C_h t S z
  let currentSum := fun z : SourceInput p =>
    ∑ u : Fin p.T, ∑ t : Fin p.T,
      ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
        rate rewards C_star C_h u t S z
  have hc : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) (le_of_lt
    (mul_pos rate.eta.property (by exact_mod_cast ConstructorDimensions.D_pos p)))
  have hdate (t : Fin p.T) :
      ((∫ z, ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
          rate rewards C_star C_h t S z ∂μ) +
        ∫ z, ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
          rate rewards C_star C_h t S z ∂μ) +
        ∑ u : Fin p.T, ∫ z,
          ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
            rate rewards C_star C_h u t S z ∂μ ≤ c := by
    have hLive := integral_calendarFloorLoss_le_sourceCellMass
      rate rewards C_star C_h control0 t S
    have hOld :=
      ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_floor_loss_integral_le_gate_mass
        rate rewards C_star C_h control0 t S
    have hCurrent :
        (∑ u : Fin p.T, ∫ z,
          ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
            rate rewards C_star C_h u t S z ∂μ) ≤
          c * ∑ u : Fin p.T, (sourceInputLaw p).real
            (ReferenceFirstCollectionCurrentRetainedGate.G
              rate rewards C_star C_h u t) := by
      calc
        _ ≤ ∑ u : Fin p.T, c * (sourceInputLaw p).real
            (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t) :=
          Finset.sum_le_sum fun u _ =>
            integral_currentFloorLoss_le_gateMass rate rewards C_star C_h control0 u t S
        _ = _ := by rw [← Finset.mul_sum]
    have hbudget :=
      ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass_oldG_currentRetainedGate_le_one
        rate rewards C_star C_h t control0
    calc
      _ ≤
          (c * ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
            rate rewards C_star C_h t control0) +
          c * (sourceInputLaw p).real
            (ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h t) +
          c * ∑ u : Fin p.T, (sourceInputLaw p).real
            (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t) := by
        exact add_le_add (add_le_add hLive hOld) hCurrent
      _ = c * (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
            rate rewards C_star C_h t control0 +
          (sourceInputLaw p).real
            (ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h t) +
          ∑ u : Fin p.T, (sourceInputLaw p).real
            (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t)) := by ring
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left hbudget hc
      _ = c := by ring
  have hLiveI : Integrable liveSum μ :=
    integrable_finsetSum Finset.univ fun t _ =>
      ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarFloorLoss
        rate rewards C_star C_h t S control0
  have hOldI : Integrable oldSum μ :=
    integrable_finsetSum Finset.univ fun t _ =>
      ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_floor_loss_integrable
        rate rewards C_star C_h control0 t S
  have hCurI : Integrable currentSum μ :=
    integrable_finsetSum Finset.univ fun u _ =>
      integrable_finsetSum Finset.univ fun t _ =>
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss_integrable
          rate rewards C_star C_h control0 u t S
  have hCurrentExchange :
      (∫ z, ∑ u : Fin p.T, ∑ t : Fin p.T,
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
          rate rewards C_star C_h u t S z ∂μ) =
      ∑ t : Fin p.T, ∑ u : Fin p.T, ∫ z,
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
          rate rewards C_star C_h u t S z ∂μ := by
    calc
      _ = ∑ u : Fin p.T, ∑ t : Fin p.T, ∫ z,
          ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
            rate rewards C_star C_h u t S z ∂μ := by
        rw [integral_finsetSum Finset.univ (fun u _ =>
          integrable_finsetSum Finset.univ (fun t _ =>
            ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss_integrable
              rate rewards C_star C_h control0 u t S))]
        apply Finset.sum_congr rfl
        intro u hu
        exact integral_finsetSum Finset.univ (fun t _ =>
          ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss_integrable
            rate rewards C_star C_h control0 u t S)
      _ = _ := Finset.sum_comm
  have hFloorTotal :
      (∫ z, (liveSum z + oldSum z) + currentSum z ∂μ) =
        (∫ z, liveSum z ∂μ) + (∫ z, oldSum z ∂μ) + ∫ z, currentSum z ∂μ := by
    calc
      _ = (∫ z, liveSum z + oldSum z ∂μ) + ∫ z, currentSum z ∂μ :=
        integral_add (hLiveI.add hOldI) hCurI
      _ = _ := by rw [integral_add hLiveI hOldI]
  have hdef : originalCalendarFloorLoss rate rewards C_star C_h S =
      fun z => (liveSum z + oldSum z) + currentSum z := by
    funext z
    rfl
  have htotal :
      (∫ z, originalCalendarFloorLoss rate rewards C_star C_h S z ∂μ) =
        ∑ t : Fin p.T,
          (((∫ z, ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
              rate rewards C_star C_h t S z ∂μ) +
            ∫ z, ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
              rate rewards C_star C_h t S z ∂μ) +
            ∑ u : Fin p.T, ∫ z,
              ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
                rate rewards C_star C_h u t S z ∂μ) := by
    have hLsum := integral_finsetSum Finset.univ (fun t _ =>
      ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarFloorLoss
        rate rewards C_star C_h t S control0)
    have hOsum := integral_finsetSum Finset.univ (fun t _ =>
      ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_floor_loss_integrable
        rate rewards C_star C_h control0 t S)
    rw [hdef, hFloorTotal, hLsum, hOsum, hCurrentExchange]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  calc
    _ = ∑ t : Fin p.T,
        (((∫ z, ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
            rate rewards C_star C_h t S z ∂μ) +
          ∫ z, ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
            rate rewards C_star C_h t S z ∂μ) +
          ∑ u : Fin p.T, ∫ z,
            ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
              rate rewards C_star C_h u t S z ∂μ) := htotal
    _ ≤ ∑ _t : Fin p.T, c := Finset.sum_le_sum fun t _ => hdate t
    _ = (p.m : ℝ) * (p.T : ℝ) /
        (rate.eta.val * (ConstructorDimensions.D p : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [c]
      ring

/-- The original-calendar rounded-gap transfer with its single horizon floor
charge, alongside the preceding theorem that retains the exact floor sum. -/
theorem integral_originalCalendarRoundedGap_le_raw_add_horizon
    (control0 : TimeControl p) (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z, originalCalendarRoundedGap rate rewards C_star C_h S z ∂μ) ≤
      (∫ z, originalCalendarRawGap rate rewards C_star C_h S z ∂μ) +
        (p.m : ℝ) * (p.T : ℝ) /
          (rate.eta.val * (ConstructorDimensions.D p : ℝ)) := by
  calc
    _ ≤ (∫ z, originalCalendarRawGap rate rewards C_star C_h S z ∂μ) +
        ∫ z, originalCalendarFloorLoss rate rewards C_star C_h S z ∂μ :=
      integral_originalCalendarRoundedGap_le_raw_add_floorLoss
        rate rewards C_star C_h control0 S
    _ ≤ _ := by
      have hfloor := integral_originalCalendarFloorLoss_le_horizon
        rate rewards C_star C_h control0 S
      linarith

end Bandits.Support.ReferenceFirstCollectionOriginalCalendarRoundingJoin

end
