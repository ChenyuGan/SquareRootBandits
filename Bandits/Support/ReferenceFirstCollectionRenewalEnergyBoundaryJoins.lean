/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift
public import Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep
public import Bandits.Support.ReferenceFirstCollectionRenewalFutureWeightedEnergyStep

import Mathlib.Tactic

/-!
# Same-source first-renewal energy boundary joins

These results identify the whole-cell and immediate next-date energy on the
existing renewal source, then compare that actual next-date boundary with the
first strict-future optional prefix. Any energy lost when that supported tail
does not continue remains as an explicit nonnegative term.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical
open Bandits.Support ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionRenewalEnergyBoundaryJoins

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

abbrev Source :=
  ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
    rate rewards C_star C_h u t

local notation "Z" => Source rate rewards C_star C_h u t
local notation "ν" =>
  ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
    rate rewards C_star C_h u t
local notation "E" =>
  ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.E
    rate rewards C_star C_h u t
local notation "BW" =>
  ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Bminus
    rate rewards C_star C_h u t
local notation "VNin" =>
  ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Vminus
    rate rewards C_star C_h u t
local notation "VWout" =>
  ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus
    rate rewards C_star C_h u t
local notation "G" =>
  ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
    rate rewards C_star C_h u t
local notation "BN" =>
  ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus
    rate rewards C_star C_h u t
local notation "VNout" =>
  ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus
    rate rewards C_star C_h u t
local notation "Cnext" =>
  ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.priorCost
    rate rewards C_star C_h u t

/-- The whole-marker energy is exactly the incoming energy of the same
immediate next-date run. Both scalar energies use the literal register
formulas: the whole-post readout is the existing current state's readout. -/
theorem whole_next_energy_join (z : Z) :
    VWout z =
      ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vminus
        rate rewards C_star C_h u t z := by
  have hread := ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState_readout rate rewards C_star C_h u t z
  have hregisters := congrArg Prod.fst hread
  change (ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState rate rewards C_star C_h u t z).registers =
    (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
      rate rewards C_star C_h u t z).1 at hregisters
  rw [ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus_eq_energyFromWholePost]
  change ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters rate
      ((ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
        rate rewards C_star C_h u t z).1) =
    ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters rate
      (ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState rate rewards C_star C_h u t z).registers
  rw [hregisters]

private theorem numericalEncoding_injective :
    Function.Injective
      (ReferenceCompleteNumericalBranchObservation.encodeNumerical
        (p := p)) := by
  intro a b hab
  cases a with
  | mk ae aa ar arate arp arl atp =>
    cases b with
    | mk be ba br brate brp brl btp =>
      simp only [ReferenceCompleteNumericalBranchObservation.encodeNumerical,
        ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates] at hab
      cases hab
      rfl

private theorem optionNumericalEncoding_injective :
    Function.Injective
      (fun cell : Option (RecordedQueueRun.RoundInput p.K) =>
        cell.map (ReferenceCompleteNumericalBranchObservation.encodeNumerical
          (p := p))) := by
  intro left right h
  cases left with
  | none => cases right <;> simp_all
  | some a =>
    cases right with
    | none => simp at h
    | some b =>
      simp only [Option.map_some] at h
      congr 1
      exact numericalEncoding_injective (Option.some.inj h)

private theorem calendarCells_eq_actualNextAppend
    (hq : t.val + 1 < p.T) (z : Z) :
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t (t.val + 2) z =
    (ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
      rate rewards C_star C_h u t z).map some ++
        [ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell rate rewards C_star C_h u t z hq] := by
  have hlen : t.val + 2 ≤ p.T := by omega
  have hcodes :
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t (t.val + 2) z).map
          (Option.map (ReferenceCompleteNumericalBranchObservation.encodeNumerical
            (p := p))) =
        ((ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
            rate rewards C_star C_h u t z).map some ++
          [ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell rate rewards C_star C_h u t z hq]).map
          (Option.map (ReferenceCompleteNumericalBranchObservation.encodeNumerical
            (p := p))) := by
    calc
      _ = ReferenceFirstCollectionRenewalNextPhysicalPrefix.rawJoinedPrefix rate rewards C_star C_h u t z (t.val + 2) :=
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells_existingRawJoinedPrefix rate rewards C_star C_h u t
          (t.val + 2) hlen z
      _ = (ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells rate rewards C_star C_h u t z).map
            (fun c => some (ReferenceCompleteNumericalBranchObservation.encodeNumerical c)) ++
          [(ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell rate rewards C_star C_h u t z hq).map
            ReferenceCompleteNumericalBranchObservation.encodeNumerical] := by
        rw [ReferenceFirstCollectionRenewalNextPhysicalPrefix.rawJoinedPrefix_next rate rewards C_star C_h u t z hq]
      _ = _ := by
        simp only [List.map_append, List.map_map, Function.comp_def,
          Option.map_some, List.map_cons, List.map_nil]
  exact (List.map_injective_iff.mpr optionNumericalEncoding_injective) hcodes

private theorem optionalPrefixCells_map_some
    (cells : List (RecordedQueueRun.RoundInput p.K)) :
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
      (cells.map some) = some cells := by
  induction cells with
  | nil => rfl
  | cons c cells ih =>
      change (List.map some cells).mapM id = some cells at ih
      change (some c :: List.map some cells).mapM id = some (c :: cells)
      simp [List.mapM_cons, ih]

/-- The full natural-date `t+2` option readout is the actual one-cell
successor of the whole current prefix. Absence is dated and stays `none`;
presence keeps registers, overflow, and accepted histories in the same
first-detecting-update run. The natural readout also covers `t+2 = T`. -/
theorem futurePrefixReadout_nextDate (hq : t.val + 1 < p.T) (z : Z) :
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout rate rewards C_star C_h u t (t.val + 2) z =
      match ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell rate rewards C_star C_h u t z hq with
      | none => none
      | some c => some
          (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.step
              (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState rate rewards C_star C_h u t z) c)) := by
  have hcalendar := calendarCells_eq_actualNextAppend rate rewards C_star C_h u t hq z
  change ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout rate
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t (t.val + 2) z) = _
  rw [hcalendar, ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout_append rate
    ((ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
      rate rewards C_star C_h u t z).map some)
    (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell rate rewards C_star C_h u t z hq),
    optionalPrefixCells_map_some]
  cases hc : ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell rate rewards C_star C_h u t z hq <;>
    simp [ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState]

/-- Literal energy discarded only when the supported first strict-future
prefix fails to continue from the actual next-date run. -/
def boundaryLoss (qfirst : Fin p.T)
    (hdate : qfirst.val = t.val + 2) (z : Z) : ℝ :=
  ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus rate rewards C_star C_h u t
      (by omega) z -
    ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyMinus rate rewards C_star C_h u t qfirst
      (by omega) z

/-- On the actual future queue support, the future incoming energy is the
same register energy as the immediate next-date outgoing state. -/
theorem futureEnergy_eq_next_outgoing_of_support
    (qfirst : Fin p.T) (hdate : qfirst.val = t.val + 2) (z : Z)
    (hz : ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueSupport
      rate rewards C_star C_h u t qfirst (by omega) z) :
    ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyMinus rate rewards C_star C_h u t qfirst
        (by omega) z =
      ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus rate rewards C_star C_h u t
        (by omega) z := by
  have hqfirst := qfirst.isLt
  have hnext : t.val + 1 < p.T := by omega
  have hfuture : t.val + 1 < qfirst.val := by omega
  obtain ⟨inputs, c, _, _, hprior, _, henergy, _, _, _, _, _⟩ :=
    ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureReadouts_same_run_step rate rewards C_star C_h u t
      qfirst hfuture z hz
  have hread :
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout rate rewards C_star C_h u t qfirst.val z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) inputs)) := by
    exact hprior
  rw [hdate, futurePrefixReadout_nextDate rate rewards C_star C_h u t hnext z] at hread
  generalize hcell : ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
    rate rewards C_star C_h u t z hnext = actualCell at hread
  cases actualCell with
  | none =>
      cases hread
  | some cell =>
      have hstate := Option.some.inj hread
      have hregs :
          (RecordedQueueRun.run
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) inputs).registers =
            (RecordedQueueRun.step
              (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState rate rewards C_star C_h u t z) cell).registers := by
        exact (congrArg Prod.fst hstate).symm
      have henergyRun :
          ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters rate
            (RecordedQueueRun.run
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) inputs).registers =
          ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters rate
            (RecordedQueueRun.step
              (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState rate rewards C_star C_h u t z) cell).registers :=
        congrArg (ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters rate)
          hregs
      calc
        ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyMinus rate rewards C_star C_h u t qfirst hfuture z =
            ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters rate
              (RecordedQueueRun.run
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) inputs).registers :=
          henergy
        _ = ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters rate
              (RecordedQueueRun.step
                (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                (ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState rate rewards C_star C_h u t z) cell).registers := henergyRun
        _ = ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus rate rewards C_star C_h u t hnext z :=
          (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus_some rate rewards C_star C_h u t hnext z cell hcell).symm

/-- The literal next-to-future boundary loss is nonnegative everywhere,
including where the optional strict-future prefix is absent. -/
theorem boundaryLoss_nonneg (qfirst : Fin p.T)
    (hdate : qfirst.val = t.val + 2) (z : Z) :
    0 ≤ boundaryLoss rate rewards C_star C_h u t qfirst hdate z := by
  have hqfirst := qfirst.isLt
  have hfuture : t.val + 1 < qfirst.val := by omega
  by_cases hz : ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueSupport
      rate rewards C_star C_h u t qfirst hfuture z
  · rw [boundaryLoss,
      (futureEnergy_eq_next_outgoing_of_support rate rewards C_star C_h u t
        qfirst hdate z hz)]
    exact sub_nonneg.mpr le_rfl
  · have hout := ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus_bounds
      rate rewards C_star C_h u t (by omega) z
    have hzero :
        ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyMinus
          rate rewards C_star C_h u t qfirst hfuture z = 0 := by
      change (ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueSupport
        rate rewards C_star C_h u t qfirst hfuture).indicator _ z = 0
      apply Set.indicator_apply_eq_zero.mpr
      intro hmem
      exact False.elim (hz hmem)
    rw [boundaryLoss, hzero]
    simpa using hout.1

/-- The actual future incoming energy never exceeds the immediate next-date
outgoing energy; any shortfall is retained in `boundaryLoss`. -/
theorem futureEnergy_le_next_outgoing (qfirst : Fin p.T)
    (hdate : qfirst.val = t.val + 2) (z : Z) :
    ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyMinus rate rewards C_star C_h u t qfirst
        (by omega) z ≤
      ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus rate rewards C_star C_h u t
        (by omega) z := by
  have hloss := boundaryLoss_nonneg rate rewards C_star C_h u t qfirst hdate z
  unfold boundaryLoss at hloss
  linarith only [hloss]

/-- The boundary loss vanishes exactly on the actual supported strict-future
prefix; points off that support retain the nonnegative residual. -/
theorem boundaryLoss_eq_zero_of_future_support (qfirst : Fin p.T)
    (hdate : qfirst.val = t.val + 2) (z : Z)
    (hz : ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueSupport
      rate rewards C_star C_h u t qfirst (by omega) z) :
    boundaryLoss rate rewards C_star C_h u t qfirst hdate z = 0 := by
  have hqfirst := qfirst.isLt
  rw [boundaryLoss,
    (futureEnergy_eq_next_outgoing_of_support rate rewards C_star C_h u t
      qfirst hdate z hz)]
  simp

/-- The pointwise boundary loss is Borel on the same original source. -/
theorem measurable_boundaryLoss (control : ContinuousLearningRows.TimeControl p)
    (qfirst : Fin p.T)
    (hdate : qfirst.val = t.val + 2) :
    Measurable (boundaryLoss rate rewards C_star C_h u t qfirst hdate) := by
  have hqfirst := qfirst.isLt
  have hnext := ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.measurable_Vplus rate rewards C_star C_h u t control
    (by omega)
  have hfutureField := ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.measurable_futureWeightedEnergyMinus
    rate rewards C_star C_h u t control qfirst (by omega)
  have hfuture := hfutureField.mono
    (ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
      rate rewards C_star C_h u t control qfirst (by omega)) le_rfl
  exact hnext.sub hfuture

/-- The boundary loss is integrable under the original finite, possibly-zero
renewal source measure. -/
theorem integrable_boundaryLoss (control : ContinuousLearningRows.TimeControl p)
    (qfirst : Fin p.T)
    (hdate : qfirst.val = t.val + 2) :
    Integrable (boundaryLoss rate rewards C_star C_h u t qfirst hdate) ν := by
  have hqfirst := qfirst.isLt
  exact (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus_integrable rate rewards C_star C_h u t control (by omega)).sub
    (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedEnergyMinus rate rewards C_star C_h u t qfirst
      (by omega) control)

/-- Splitting the actual next-date outgoing energy into the first-future
incoming energy and the literal boundary loss uses only their established L1
integrability. -/
theorem integral_next_outgoing_eq_future_plus_loss
    (control : ContinuousLearningRows.TimeControl p) (qfirst : Fin p.T)
    (hdate : qfirst.val = t.val + 2) :
    (∫ z : Z, ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus rate rewards C_star C_h u t
      (by omega) z ∂ν) =
      (∫ z : Z, ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyMinus rate rewards C_star C_h u t qfirst
        (by omega) z ∂ν) +
      ∫ z : Z, boundaryLoss rate rewards C_star C_h u t qfirst hdate z ∂ν := by
  have hqfirst := qfirst.isLt
  have hpoint :
      (fun z : Z => ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus rate rewards C_star C_h u t
          (by omega) z) =
        fun z => ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyMinus rate rewards C_star C_h u t qfirst
          (by omega) z + boundaryLoss rate rewards C_star C_h u t qfirst hdate z := by
    funext z
    simp only [boundaryLoss]
    ring
  rw [hpoint, integral_add
    (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedEnergyMinus rate rewards C_star C_h u t qfirst
      (by omega) control)
    (integrable_boundaryLoss rate rewards C_star C_h u t control qfirst hdate)]

/-- Literal-cost accounting across the whole cell and its immediate next
date. The shared actual boundary cancels, while incoming energy is retained. -/
theorem whole_next_weightedEnergy_accounting
    (control : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) :
    (11 / 2 : ℝ) *
        (∫ z : Z, (E).indicator BW z + (G hq).indicator BN z ∂ν) +
      ∫ z : Z, VNout hq z ∂ν ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          (ν).real (E) +
        ∫ z : Z, (G hq).indicator
          (fun z => Cnext hq z + (33 / 2 : ℝ) * p.m) z ∂ν +
        ∫ z : Z, VNin z ∂ν := by
  have hEset := ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.measurableSet_E rate rewards C_star C_h u t
  have hGfield := ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.measurableSet_G rate rewards C_star C_h u t control hq
  have hGset := ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
    rate rewards C_star C_h u t control _ hGfield
  have hEint : Integrable ((E).indicator BW) ν :=
    (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.integrable_Bminus rate rewards C_star C_h u t control).indicator hEset
  have hGint : Integrable ((G hq).indicator BN) ν :=
    (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus_integrable rate rewards C_star C_h u t control).indicator hGset
  have hcostSum :
      (∫ z : Z, (E).indicator BW z + (G hq).indicator BN z ∂ν) =
        (∫ z : Z, (E).indicator BW z ∂ν) +
          ∫ z : Z, (G hq).indicator BN z ∂ν :=
    integral_add hEint hGint
  have hwhole := ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.weightedCost_integral_le rate rewards C_star C_h u t control
  have hnext := ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.weightedEnergyAccounting rate rewards C_star C_h u t control hq
  have hboundary :
      (∫ z : Z, ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus rate rewards C_star C_h u t z ∂ν) =
        ∫ z : Z, ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vminus rate rewards C_star C_h u t z ∂ν := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z =>
      whole_next_energy_join rate rewards C_star C_h u t z
  have hwhole' :
      (11 / 2 : ℝ) * (∫ z : Z, (E).indicator BW z ∂ν) ≤
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) * (ν).real E +
          (∫ z : Z, VNin z ∂ν) - ∫ z : Z, VWout z ∂ν := hwhole
  have hnext' :
      (11 / 2 : ℝ) * (∫ z : Z, (G hq).indicator BN z ∂ν) ≤
        (∫ z : Z, (G hq).indicator
          (fun z => Cnext hq z + (33 / 2 : ℝ) * p.m) z ∂ν) +
          (∫ z : Z,
            ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vminus rate rewards C_star C_h u t z ∂ν) -
          ∫ z : Z, VNout hq z ∂ν := hnext
  have hsum := add_le_add hwhole' hnext'
  rw [hboundary] at hsum
  calc
    _ =
        (11 / 2 : ℝ) *
            ((∫ z : Z, (E).indicator BW z ∂ν) +
              ∫ z : Z, (G hq).indicator BN z ∂ν) +
          ∫ z : Z, ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus rate rewards C_star C_h u t hq z ∂ν := by
      rw [hcostSum]
    _ ≤
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
            (ν).real E +
          ∫ z : Z, (G hq).indicator
            (fun z => Cnext hq z + (33 / 2 : ℝ) * p.m) z ∂ν +
          ∫ z : Z, VNin z ∂ν := by
      linarith only [hsum]

/-- If a first strict-future date exists, the same literal-cost inequality
retains both its incoming energy and the nonnegative boundary loss. -/
theorem whole_next_future_weightedEnergy_accounting
    (control : ContinuousLearningRows.TimeControl p)
    (qfirst : Fin p.T)
    (hdate : qfirst.val = t.val + 2) :
    (11 / 2 : ℝ) *
        (∫ z : Z, (E).indicator BW z +
          (G (by omega)).indicator BN z ∂ν) +
    (∫ z : Z, ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyMinus rate rewards C_star C_h u t qfirst
        (by omega) z ∂ν) +
      ∫ z : Z, boundaryLoss rate rewards C_star C_h u t qfirst hdate z ∂ν ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          (ν).real (E) +
        ∫ z : Z, (G (by omega)).indicator
          (fun z => Cnext (by omega) z +
            (33 / 2 : ℝ) * p.m) z ∂ν +
        ∫ z : Z, VNin z ∂ν := by
  have hqfirst := qfirst.isLt
  have hnext : t.val + 1 < p.T := by omega
  have hbase := whole_next_weightedEnergy_accounting rate rewards C_star C_h u t
    control hnext
  have hsplit := integral_next_outgoing_eq_future_plus_loss rate rewards C_star C_h u t
    control qfirst hdate
  calc
    _ =
        (11 / 2 : ℝ) *
            (∫ z : Z, (E).indicator BW z +
              (G (by omega)).indicator BN z ∂ν) +
          ((∫ z : Z, ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyMinus
              rate rewards C_star C_h u t qfirst (by omega) z ∂ν) +
            ∫ z : Z, boundaryLoss rate rewards C_star C_h u t qfirst hdate z ∂ν) := by
      exact add_assoc _ _ _
    _ =
        (11 / 2 : ℝ) *
            (∫ z : Z, (E).indicator BW z +
              (G (by omega)).indicator BN z ∂ν) +
          ∫ z : Z, VNout hnext z ∂ν := by
      rw [← hsplit]
    _ ≤ _ := hbase

/-- With no next date, keep precisely the accepted whole-marker accounting
and the actual terminal prefix; no next action or `Fin p.T` at time `T` is
introduced. -/
theorem terminal_whole_weightedEnergy_boundary
    (control : ContinuousLearningRows.TimeControl p) (z : Z)
    (hterminal : t.val + 1 = p.T) :
    ((11 / 2 : ℝ) *
        (∫ z : Z, (E).indicator BW z ∂ν) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          (ν).real E +
        (∫ z : Z, VNin z ∂ν) - ∫ z : Z, VWout z ∂ν) ∧
      (ReferenceCompleteObservationPrefixInformation.datePrefix rate p.T
          (ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation
            rate rewards C_star C_h u t z) =
          ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation
            rate rewards C_star C_h u t z ∧
        ReferenceFirstCollectionRenewalNextPhysicalPrefix.rawJoinedPrefix
            rate rewards C_star C_h u t z p.T =
          (ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
            rate rewards C_star C_h u t z).map (fun c => some
              (ReferenceCompleteNumericalBranchObservation.encodeNumerical c))) := by
  exact ⟨ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.weightedCost_integral_le rate rewards C_star C_h u t control,
    ReferenceFirstCollectionRenewalNextPhysicalPrefix.terminal_physical_prefix rate rewards C_star C_h u t z hterminal⟩

end Bandits.Support.ReferenceFirstCollectionRenewalEnergyBoundaryJoins

end
