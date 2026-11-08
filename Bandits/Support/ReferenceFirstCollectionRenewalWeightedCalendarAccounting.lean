/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalEnergyBoundaryJoins
public import Bandits.Support.ReferenceFirstCollectionRenewalNextDateRWeightedAccounting
public import Bandits.Support.ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget

import Mathlib.Tactic

/-!
# Same-source first-call weighted calendar accounting

This module joins the already established whole-call, immediate next-date,
and supported strict-future estimates on the original renewal source law.
Incoming energy and every actual boundary, terminal, and support loss remain
visible in the calendar budget.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical
open Bandits.Support ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionRenewalWeightedCalendarAccounting

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

/-- Backlog charged strictly after the already-paid whole date. -/
def afterCallBacklog : Z → ℝ := fun z =>
  (if hnext : t.val + 1 < p.T then
    (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t hnext).indicator
      (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus rate rewards C_star C_h u t) z
  else 0) +
    ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog rate rewards C_star C_h u t z

/-- Total backlog on the calendar beginning at the whole date. -/
def wholeCalendarBacklog : Z → ℝ := fun z =>
  (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.E rate rewards C_star C_h u t).indicator
    (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Bminus rate rewards C_star C_h u t) z +
      afterCallBacklog rate rewards C_star C_h u t z

/-- Actual retained gate mass strictly after the whole date. -/
def afterCallGateMass (rate0 : ReferenceActivePhysicalStep.RateInput p)
    (rewards0 : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star0 C_h0 : ℝ) (u0 t0 : Fin p.T) : ℝ :=
  (if hnext : t0.val + 1 < p.T then
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
      rate0 rewards0 C_star0 C_h0 u0 t0).real
        (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
          rate0 rewards0 C_star0 C_h0 u0 t0 hnext)
  else 0) +
    ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
      rate0 rewards0 C_star0 C_h0 u0 t0

/-- Actual retained gate mass beginning at the whole date. -/
def wholeCalendarGateMass (rate0 : ReferenceActivePhysicalStep.RateInput p)
    (rewards0 : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star0 C_h0 : ℝ) (u0 t0 : Fin p.T) : ℝ :=
  (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
    rate0 rewards0 C_star0 C_h0 u0 t0).real
      (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.E
        rate0 rewards0 C_star0 C_h0 u0 t0) +
    afterCallGateMass rate0 rewards0 C_star0 C_h0 u0 t0

/-- The actual terminal energy after the call, selecting the strict-future
terminal, the immediate next-date output, or the whole-date output at `T`. -/
def terminalEnergy (z : Z) : ℝ :=
  if _hfuture : t.val + 2 < p.T then
    ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureTerminalEnergy rate rewards C_star C_h u t z
  else if hnext : t.val + 1 < p.T then
    ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus rate rewards C_star C_h u t hnext z
  else
    ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus rate rewards C_star C_h u t z

/-- Boundary energy lost before the supported strict-future calendar, plus
all adjacent losses inside that supported calendar. -/
def supportLoss (z : Z) : ℝ :=
  if hfuture : t.val + 2 < p.T then
    let qfirst : Fin p.T := ⟨t.val + 2, hfuture⟩
    ReferenceFirstCollectionRenewalEnergyBoundaryJoins.boundaryLoss rate rewards C_star C_h u t qfirst (by simp [qfirst]) z +
      ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss rate rewards C_star C_h u t z
  else 0

private theorem futureEnergyMinusAt_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) :
    Measurable
      (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyMinusAt rate rewards C_star C_h u t n) := by
  by_cases hq : n < p.T
  · by_cases hf : t.val + 1 < n
    · let q : Fin p.T := ⟨n, hq⟩
      have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
        rate rewards C_star C_h u t control0 q (by simp [q]; omega)
      have hminus :=
        ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.measurable_futureWeightedEnergyMinus
          rate rewards C_star C_h u t control0 q hf
      have hminus' := hminus.mono hfield le_rfl
      simpa [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyMinusAt, q, hq, hf] using hminus'
    · have hzero : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyMinusAt
          rate rewards C_star C_h u t n = 0 := by
        simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyMinusAt, hq, hf]
      rw [hzero]
      exact measurable_const
  · have hzero : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyMinusAt
        rate rewards C_star C_h u t n = 0 := by
      simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyMinusAt, hq]
    rw [hzero]
    exact measurable_const

private theorem futureEnergyPlusAt_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) :
    Measurable
      (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyPlusAt rate rewards C_star C_h u t n) := by
  by_cases hq : n < p.T
  · by_cases hf : t.val + 1 < n
    · let q : Fin p.T := ⟨n, hq⟩
      have hplus :=
        ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.measurable_futureWeightedEnergyPlus
          rate rewards C_star C_h u t q hf control0
      simpa [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyPlusAt, q, hq, hf] using hplus
    · have hzero : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyPlusAt
          rate rewards C_star C_h u t n = 0 := by
        simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyPlusAt, hq, hf]
      rw [hzero]
      exact measurable_const
  · have hzero : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyPlusAt
        rate rewards C_star C_h u t n = 0 := by
      simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyPlusAt, hq]
    rw [hzero]
    exact measurable_const

private theorem futureAdjacentLossAt_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) :
    Measurable
      (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLossAt rate rewards C_star C_h u t n) := by
  by_cases hq : n < p.T
  · by_cases hf : t.val + 1 < n
    · by_cases hnext : n + 1 < p.T
      · have hplus := futureEnergyPlusAt_measurable rate rewards C_star C_h u t control0 n
        have hminus := futureEnergyMinusAt_measurable rate rewards C_star C_h u t control0 (n + 1)
        have hfnext : t.val + 1 < n + 1 := by omega
        simpa [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLossAt,
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyPlusAt,
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyMinusAt,
          hq, hf, hnext, hfnext] using hplus.sub hminus
      · have hzero : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLossAt
            rate rewards C_star C_h u t n = 0 := by
          simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLossAt, hq, hf, hnext]
        rw [hzero]
        exact measurable_const
    · have hzero : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLossAt
          rate rewards C_star C_h u t n = 0 := by
        simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLossAt, hq, hf]
      rw [hzero]
      exact measurable_const
  · have hzero : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLossAt
        rate rewards C_star C_h u t n = 0 := by
      simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLossAt, hq]
    rw [hzero]
    exact measurable_const

private theorem measurable_supportedFutureBacklog
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog rate rewards C_star C_h u t) := by
  unfold ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog
  change Measurable (fun z : Z =>
    ∑ n ∈ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t,
      ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklogAt
        rate rewards C_star C_h u t n z)
  exact Finset.measurable_fun_sum
      (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t)
      (f := fun n z =>
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklogAt
          rate rewards C_star C_h u t n z)
      (fun n hn => by
        have hn' := Finset.mem_Ico.mp hn
        have hq : n < p.T := hn'.2
        have hf : t.val + 1 < n := by omega
        let q : Fin p.T := ⟨n, hq⟩
        have hG0 := ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurableSet_Gfuture
          rate rewards C_star C_h u t q hf control0
        have htq : t.val < q.val := by simp [q]; omega
        have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
          rate rewards C_star C_h u t control0 q htq
        have hG : MeasurableSet
            (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
              rate rewards C_star C_h u t q hf) := hfield _ hG0
        have hbacklog :=
          ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.measurable_futureWeightedBacklog
            rate rewards C_star C_h u t control0 q hf
        have hbacklog' := hbacklog.mono hfield le_rfl
        simpa [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklogAt, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureBacklogAt,
          q, hq, hf] using hbacklog'.indicator hG)

private theorem futureEnergyMinusAt_integrable
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) :
    Integrable
      (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyMinusAt rate rewards C_star C_h u t n) ν := by
  by_cases hq : n < p.T
  · by_cases hf : t.val + 1 < n
    · let q : Fin p.T := ⟨n, hq⟩
      have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
        rate rewards C_star C_h u t control0 q (by simp [q]; omega)
      have hminus :=
        ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedEnergyMinus
          rate rewards C_star C_h u t q hf control0
      simpa [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyMinusAt, q, hq, hf] using hminus
    · simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyMinusAt, hq, hf]
  · simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyMinusAt, hq]

private theorem futureEnergyPlusAt_integrable
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) :
    Integrable
      (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyPlusAt rate rewards C_star C_h u t n) ν := by
  by_cases hq : n < p.T
  · by_cases hf : t.val + 1 < n
    · let q : Fin p.T := ⟨n, hq⟩
      have hplus :=
        ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedEnergyPlus
          rate rewards C_star C_h u t q hf control0
      simpa [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyPlusAt, q, hq, hf] using hplus
    · simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyPlusAt, hq, hf]
  · simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyPlusAt, hq]

private theorem futureAdjacentLossAt_integrable
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) :
    Integrable
      (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLossAt rate rewards C_star C_h u t n) ν := by
  by_cases hq : n < p.T
  · by_cases hf : t.val + 1 < n
    · by_cases hnext : n + 1 < p.T
      · have hplus := futureEnergyPlusAt_integrable rate rewards C_star C_h u t control0 n
        have hminus := futureEnergyMinusAt_integrable rate rewards C_star C_h u t control0 (n + 1)
        have hfnext : t.val + 1 < n + 1 := by omega
        simpa [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLossAt,
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyPlusAt,
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyMinusAt,
          hq, hf, hnext, hfnext] using hplus.sub hminus
      · simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLossAt, hq, hf, hnext]
    · simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLossAt, hq, hf]
  · simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLossAt, hq]

private theorem futureAdjacentLoss_integrable
    (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss rate rewards C_star C_h u t) ν := by
  unfold ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss
  simpa only [← Finset.sum_apply] using
    (integrable_finsetSum (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLossDates t)
      (fun n hn => futureAdjacentLossAt_integrable rate rewards C_star C_h u t control0 n))

private theorem futureAdjacentLoss_measurable
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss rate rewards C_star C_h u t) := by
  unfold ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss
  simpa only [← Finset.sum_apply] using
    (Finset.measurable_fun_sum (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLossDates t)
      (fun n hn => futureAdjacentLossAt_measurable rate rewards C_star C_h u t control0 n))

private theorem nextBacklog_integrable
    (control0 : ContinuousLearningRows.TimeControl p)
    (hnext : t.val + 1 < p.T) :
    Integrable
      ((ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t hnext).indicator
        (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus rate rewards C_star C_h u t)) ν :=
  (ReferenceFirstCollectionRenewalNextDateRWeightedAccounting.actualTermIntegrability
    rate rewards C_star C_h u t control0 hnext).2.1

private theorem nextBacklog_measurable
    (control0 : ContinuousLearningRows.TimeControl p)
    (hnext : t.val + 1 < p.T) :
    Measurable
      ((ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t hnext).indicator
        (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus rate rewards C_star C_h u t)) := by
  have hG0 := ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.measurableSet_G rate rewards C_star C_h u t control0 hnext
  have hfield := ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
    rate rewards C_star C_h u t control0
  have hG : MeasurableSet
      (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t hnext) := hfield _ hG0
  exact (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.measurable_Bminus rate rewards C_star C_h u t control0).mono hfield le_rfl |>.indicator hG

private theorem wholeBacklog_measurable :
    Measurable ((ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.E rate rewards C_star C_h u t).indicator
      (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Bminus rate rewards C_star C_h u t)) := by
  exact (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.measurable_Bminus rate rewards C_star C_h u t).indicator
    (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.measurableSet_E rate rewards C_star C_h u t)

private theorem wholeBacklog_integrable
    (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable ((ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.E rate rewards C_star C_h u t).indicator
      (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Bminus rate rewards C_star C_h u t)) ν :=
  (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.integrable_Bminus rate rewards C_star C_h u t control0).indicator
    (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.measurableSet_E rate rewards C_star C_h u t)

theorem afterCallBacklog_measurable
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (afterCallBacklog rate rewards C_star C_h u t) := by
  by_cases hnext : t.val + 1 < p.T
  · have hEq : afterCallBacklog rate rewards C_star C_h u t = fun z =>
        (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
          rate rewards C_star C_h u t hnext).indicator
            (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus
              rate rewards C_star C_h u t) z +
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog
            rate rewards C_star C_h u t z := by
      funext z
      simp [afterCallBacklog, hnext]
    rw [hEq]
    exact (nextBacklog_measurable rate rewards C_star C_h u t control0 hnext).add
      (measurable_supportedFutureBacklog rate rewards C_star C_h u t control0)
  · have hEq : afterCallBacklog rate rewards C_star C_h u t =
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog
          rate rewards C_star C_h u t := by
      funext z
      simp [afterCallBacklog, hnext]
    rw [hEq]
    exact measurable_supportedFutureBacklog rate rewards C_star C_h u t control0

theorem afterCallBacklog_integrable
    (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (afterCallBacklog rate rewards C_star C_h u t) ν := by
  by_cases hnext : t.val + 1 < p.T
  · have hEq : afterCallBacklog rate rewards C_star C_h u t = fun z =>
        (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
          rate rewards C_star C_h u t hnext).indicator
            (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus
              rate rewards C_star C_h u t) z +
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog
            rate rewards C_star C_h u t z := by
      funext z
      simp [afterCallBacklog, hnext]
    rw [hEq]
    exact (nextBacklog_integrable rate rewards C_star C_h u t control0 hnext).add
      (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.integrable_total_supported_future_backlog rate rewards C_star C_h u t control0)
  · have hEq : afterCallBacklog rate rewards C_star C_h u t =
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog
          rate rewards C_star C_h u t := by
      funext z
      simp [afterCallBacklog, hnext]
    rw [hEq]
    exact ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.integrable_total_supported_future_backlog
      rate rewards C_star C_h u t control0

theorem wholeCalendarBacklog_measurable
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (wholeCalendarBacklog rate rewards C_star C_h u t) := by
  exact (wholeBacklog_measurable rate rewards C_star C_h u t).add
    (afterCallBacklog_measurable rate rewards C_star C_h u t control0)

theorem wholeCalendarBacklog_integrable
    (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (wholeCalendarBacklog rate rewards C_star C_h u t) ν :=
  (wholeBacklog_integrable rate rewards C_star C_h u t control0).add
    (afterCallBacklog_integrable rate rewards C_star C_h u t control0)

theorem terminalEnergy_measurable
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (terminalEnergy rate rewards C_star C_h u t) := by
  by_cases hfuture : t.val + 2 < p.T
  · have hT := p.one_le_T
    let q : Fin p.T := ⟨p.T - 1, by omega⟩
    have hf : t.val + 1 < q.val := by simp [q]; omega
    have hm :=
      ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.measurable_futureWeightedEnergyPlus
        rate rewards C_star C_h u t q hf control0
    have hEq : terminalEnergy rate rewards C_star C_h u t =
        fun z => ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyPlus
          rate rewards C_star C_h u t q hf z := by
      funext z
      simp [terminalEnergy,
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureTerminalEnergy,
        hfuture, q]
    exact hEq ▸ hm
  · by_cases hnext : t.val + 1 < p.T
    · have hEq : terminalEnergy rate rewards C_star C_h u t =
          ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus
            rate rewards C_star C_h u t hnext := by
        funext z
        simp [terminalEnergy, hfuture, hnext]
      exact hEq ▸
        (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.measurable_Vplus
          rate rewards C_star C_h u t control0 hnext)
    · have hEq : terminalEnergy rate rewards C_star C_h u t =
          ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus
            rate rewards C_star C_h u t := by
        funext z
        simp [terminalEnergy, hfuture, hnext]
      exact hEq ▸
        (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.measurable_VwholePlus
          rate rewards C_star C_h u t)

theorem terminalEnergy_integrable
    (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (terminalEnergy rate rewards C_star C_h u t) ν := by
  by_cases hfuture : t.val + 2 < p.T
  · have hT := p.one_le_T
    let q : Fin p.T := ⟨p.T - 1, by omega⟩
    have hf : t.val + 1 < q.val := by simp [q]; omega
    have hi :=
      ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedEnergyPlus
        rate rewards C_star C_h u t q hf control0
    have hEq : terminalEnergy rate rewards C_star C_h u t =
        fun z => ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyPlus
          rate rewards C_star C_h u t q hf z := by
      funext z
      simp [terminalEnergy,
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureTerminalEnergy,
        hfuture, q]
    exact hEq ▸ hi
  · by_cases hnext : t.val + 1 < p.T
    · have hEq : terminalEnergy rate rewards C_star C_h u t =
          ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus
            rate rewards C_star C_h u t hnext := by
        funext z
        simp [terminalEnergy, hfuture, hnext]
      exact hEq ▸
        (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus_integrable
          rate rewards C_star C_h u t control0 hnext)
    · have hEq : terminalEnergy rate rewards C_star C_h u t =
          ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus
            rate rewards C_star C_h u t := by
        funext z
        simp [terminalEnergy, hfuture, hnext]
      exact hEq ▸
        (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.integrable_VwholePlus
          rate rewards C_star C_h u t control0)

theorem supportLoss_measurable
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (supportLoss rate rewards C_star C_h u t) := by
  by_cases hfuture : t.val + 2 < p.T
  · let qfirst : Fin p.T := ⟨t.val + 2, hfuture⟩
    have hdate : qfirst.val = t.val + 2 := by simp [qfirst]
    have hEq : supportLoss rate rewards C_star C_h u t = fun z =>
        ReferenceFirstCollectionRenewalEnergyBoundaryJoins.boundaryLoss
          rate rewards C_star C_h u t qfirst hdate z +
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss
          rate rewards C_star C_h u t z := by
      funext z
      simp [supportLoss, hfuture, qfirst]
    exact hEq ▸
      ((ReferenceFirstCollectionRenewalEnergyBoundaryJoins.measurable_boundaryLoss
        rate rewards C_star C_h u t control0 qfirst hdate).add
      (futureAdjacentLoss_measurable rate rewards C_star C_h u t control0))
  · have hEq : supportLoss rate rewards C_star C_h u t = fun _ => 0 := by
      funext z
      simp [supportLoss, hfuture]
    rw [hEq]
    exact (measurable_const : Measurable (fun _ : Z => (0 : ℝ)))

theorem supportLoss_integrable
    (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (supportLoss rate rewards C_star C_h u t) ν := by
  by_cases hfuture : t.val + 2 < p.T
  · let qfirst : Fin p.T := ⟨t.val + 2, hfuture⟩
    have hdate : qfirst.val = t.val + 2 := by simp [qfirst]
    have hEq : supportLoss rate rewards C_star C_h u t = fun z =>
        ReferenceFirstCollectionRenewalEnergyBoundaryJoins.boundaryLoss
          rate rewards C_star C_h u t qfirst hdate z +
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss
          rate rewards C_star C_h u t z := by
      funext z
      simp [supportLoss, hfuture, qfirst]
    exact hEq ▸
      ((ReferenceFirstCollectionRenewalEnergyBoundaryJoins.integrable_boundaryLoss
        rate rewards C_star C_h u t control0 qfirst hdate).add
      (futureAdjacentLoss_integrable rate rewards C_star C_h u t control0))
  · have hEq : supportLoss rate rewards C_star C_h u t = fun _ => 0 := by
      funext z
      simp [supportLoss, hfuture]
    rw [hEq]
    exact integrable_zero Z ℝ ν

private theorem futureAdjacentLoss_nonneg (z : Z) :
    0 ≤ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss rate rewards C_star C_h u t z := by
  unfold ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss
  apply Finset.sum_nonneg
  intro n hn
  exact ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLossAt_nonneg rate rewards C_star C_h u t n hn z

private theorem supportedFutureBacklog_nonneg (z : Z) :
    0 ≤ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog rate rewards C_star C_h u t z := by
  unfold ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog
  apply Finset.sum_nonneg
  intro n hn
  have hn' := Finset.mem_Ico.mp hn
  have hq : n < p.T := hn'.2
  have hf : t.val + 1 < n := by omega
  let q : Fin p.T := ⟨n, hq⟩
  by_cases hz : z ∈ ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
      rate rewards C_star C_h u t q hf
  · simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklogAt, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureBacklogAt,
      q, hq, hf, hz]
    exact (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedBacklog_bounds
      rate rewards C_star C_h u t q hf z).1
  · simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklogAt, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureBacklogAt,
      q, hq, hf, hz]

private theorem weightFromRegisters_pos (registers : Fin p.K → ℕ × ℕ)
    (j : Fin p.K) :
    0 < ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters
      rate j registers := by
  have hD : 0 < (ReferenceFirstLaunchNumericalCell.queueParameters rate).D := by
    rw [ReferenceFirstLaunchNumericalCell.queueParameters]
    exact ConstructorDimensions.D_pos p
  have hD' : 0 < ((ReferenceFirstLaunchNumericalCell.queueParameters rate).D : ℝ) :=
    Nat.cast_pos.mpr hD
  change 0 < ScoreWeights.scoreWeight
    (1 + 1 / ((ReferenceFirstLaunchNumericalCell.queueParameters rate).D : ℝ))
      (registers j).1
  exact ScoreWeights.scoreWeight_pos (by positivity) _

private theorem thetaFromRegisters_nonneg (registers : Fin p.K → ℕ × ℕ)
    (j : Fin p.K) :
    0 ≤ ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
      rate j registers := by
  unfold ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
  exact (ProductSetLaw.theta_pos
    (fun i => ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters
      rate i registers)
    j (ConstructorDimensions.m_pos p) p.m_lt_K
    (weightFromRegisters_pos rate registers)).le

private theorem energyFromRegisters_nonneg
    (registers : Fin p.K → ℕ × ℕ) :
    0 ≤ ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
      rate registers := by
  unfold ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (thetaFromRegisters_nonneg rate registers j) (sq_nonneg _)

private theorem wholeBacklog_nonneg (z : Z) :
    0 ≤ (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.E rate rewards C_star C_h u t).indicator
      (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Bminus rate rewards C_star C_h u t) z := by
  by_cases hz : z ∈ ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.E rate rewards C_star C_h u t
  · simp only [Set.indicator_of_mem hz]
    unfold ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Bminus ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.thetaMinus ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.bMinus
    apply Finset.sum_nonneg
    intro j hj
    apply mul_nonneg
    · exact thetaFromRegisters_nonneg rate
        (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Aminus
          rate rewards C_star C_h u t z) j
    · have hn : 0 < rate.n := ActiveFollowerDownAcceptance.rate_n_pos p rate
      unfold ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters
      positivity
  · simp only [Set.indicator_of_notMem hz]
    exact le_rfl

private theorem futureGateMass_nonneg :
    0 ≤ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass rate rewards C_star C_h u t := by
  unfold ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
  apply Finset.sum_nonneg
  intro n hn
  have hn' := Finset.mem_Ico.mp hn
  have hq : n < p.T := hn'.2
  have hf : t.val + 1 < n := by omega
  simp only [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMassAt, dite_eq_left hq, dite_eq_left hf]
  exact measureReal_nonneg

theorem afterCallBacklog_nonneg (z : Z) :
    0 ≤ afterCallBacklog rate rewards C_star C_h u t z := by
  by_cases hnext : t.val + 1 < p.T
  · have hEq : afterCallBacklog rate rewards C_star C_h u t z =
        (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
          rate rewards C_star C_h u t hnext).indicator
            (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus
              rate rewards C_star C_h u t) z +
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog
            rate rewards C_star C_h u t z := by
      simp [afterCallBacklog, hnext]
    rw [hEq]
    exact add_nonneg
      (Set.indicator_nonneg
        (fun x _ =>
          (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus_bounds
            rate rewards C_star C_h u t x).1) z)
      (supportedFutureBacklog_nonneg rate rewards C_star C_h u t z)
  · have hEq : afterCallBacklog rate rewards C_star C_h u t z =
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog
          rate rewards C_star C_h u t z := by
      simp [afterCallBacklog, hnext]
    rw [hEq]
    exact supportedFutureBacklog_nonneg rate rewards C_star C_h u t z

theorem wholeCalendarBacklog_nonneg (z : Z) :
    0 ≤ wholeCalendarBacklog rate rewards C_star C_h u t z := by
  exact add_nonneg (wholeBacklog_nonneg rate rewards C_star C_h u t z)
    (afterCallBacklog_nonneg rate rewards C_star C_h u t z)

theorem terminalEnergy_nonneg (z : Z) :
    0 ≤ terminalEnergy rate rewards C_star C_h u t z := by
  by_cases hfuture : t.val + 2 < p.T
  · have hT := p.one_le_T
    let q : Fin p.T := ⟨p.T - 1, by omega⟩
    have hf : t.val + 1 < q.val := by simp [q]; omega
    simpa [terminalEnergy, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureTerminalEnergy, hfuture, q, hf] using
      (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyPlus_bounds
        rate rewards C_star C_h u t q hf z).1
  · by_cases hnext : t.val + 1 < p.T
    · simpa [terminalEnergy, hfuture, hnext] using
        (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus_bounds rate rewards C_star C_h u t hnext z).1
    · have hterminal : terminalEnergy rate rewards C_star C_h u t z =
          ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus
            rate rewards C_star C_h u t z := by
        simp [terminalEnergy, hfuture, hnext]
      rw [hterminal]
      change 0 ≤ ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters rate
        (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Aplus
          rate rewards C_star C_h u t z)
      exact energyFromRegisters_nonneg (p := p) rate
        (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Aplus
          rate rewards C_star C_h u t z)

theorem supportLoss_nonneg (z : Z) :
    0 ≤ supportLoss rate rewards C_star C_h u t z := by
  by_cases hfuture : t.val + 2 < p.T
  · let qfirst : Fin p.T := ⟨t.val + 2, hfuture⟩
    have hdate : qfirst.val = t.val + 2 := by simp [qfirst]
    simp only [supportLoss, hfuture, ↓reduceDIte]
    exact add_nonneg
      (ReferenceFirstCollectionRenewalEnergyBoundaryJoins.boundaryLoss_nonneg rate rewards C_star C_h u t qfirst hdate z)
      (futureAdjacentLoss_nonneg rate rewards C_star C_h u t z)
  · simp [supportLoss, hfuture]

theorem afterCallGateMass_nonneg :
    0 ≤ afterCallGateMass rate rewards C_star C_h u t := by
  by_cases hnext : t.val + 1 < p.T
  · have hEq : afterCallGateMass rate rewards C_star C_h u t =
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t).real
            (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
              rate rewards C_star C_h u t hnext) +
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
            rate rewards C_star C_h u t := by
      simp [afterCallGateMass, hnext]
    rw [hEq]
    exact add_nonneg measureReal_nonneg
      (futureGateMass_nonneg rate rewards C_star C_h u t)
  · have hEq : afterCallGateMass rate rewards C_star C_h u t =
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
          rate rewards C_star C_h u t := by
      simp [afterCallGateMass, hnext]
    rw [hEq]
    exact futureGateMass_nonneg rate rewards C_star C_h u t

theorem wholeCalendarGateMass_nonneg :
    0 ≤ wholeCalendarGateMass rate rewards C_star C_h u t := by
  unfold wholeCalendarGateMass
  exact add_nonneg measureReal_nonneg
    (afterCallGateMass_nonneg rate rewards C_star C_h u t)

theorem calendarCost_nonneg :
    0 ≤ CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ) := by
  have hmK : (p.m : ℝ) < (p.K : ℝ) := Nat.cast_lt.mpr p.m_lt_K
  have hmpos : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
  unfold CanonicalRecordingRates.R
  nlinarith only [hmK, hmpos]

theorem afterCall_weighted_calendar_accounting
    (control0 : ContinuousLearningRows.TimeControl p) :
    (11 / 2 : ℝ) *
        (∫ z : Z, afterCallBacklog rate rewards C_star C_h u t z ∂ν) +
      (∫ z : Z, terminalEnergy rate rewards C_star C_h u t z ∂ν) +
      ∫ z : Z, supportLoss rate rewards C_star C_h u t z ∂ν ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        afterCallGateMass rate rewards C_star C_h u t +
      ∫ z : Z, ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus rate rewards C_star C_h u t z ∂ν := by
  by_cases hnext : t.val + 1 < p.T
  · by_cases hfuture : t.val + 2 < p.T
    · let qfirst : Fin p.T := ⟨t.val + 2, hfuture⟩
      have hdate : qfirst.val = t.val + 2 := by simp [qfirst]
      have hR :=
        ReferenceFirstCollectionRenewalNextDateRWeightedAccounting.actualRWeightedEnergyAccounting
          rate rewards C_star C_h u t control0 (by omega)
      have hH := ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supported_future_weighted_budget rate rewards C_star C_h u t control0
      have hboundary := ReferenceFirstCollectionRenewalEnergyBoundaryJoins.integral_next_outgoing_eq_future_plus_loss
        rate rewards C_star C_h u t control0 qfirst hdate
      have hinitial : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureInitialEnergy rate rewards C_star C_h u t =
          fun z => ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyMinus
            rate rewards C_star C_h u t qfirst (by
              simp [qfirst]) z := by
        funext z
        simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureInitialEnergy, hfuture, qfirst]
      have hjoin :
          (∫ z : Z, ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus rate rewards C_star C_h u t z ∂ν) =
            ∫ z : Z, ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vminus rate rewards C_star C_h u t z ∂ν := by
        apply integral_congr_ae
        filter_upwards [] with z
        exact ReferenceFirstCollectionRenewalEnergyBoundaryJoins.whole_next_energy_join rate rewards C_star C_h u t z
      have hnextBacklog := nextBacklog_integrable rate rewards C_star C_h u t control0 (by omega)
      have hfutureBacklog := ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.integrable_total_supported_future_backlog
        rate rewards C_star C_h u t control0
      have hbacklog :
          (∫ z : Z, afterCallBacklog rate rewards C_star C_h u t z ∂ν) =
            (∫ z : Z, (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t (by omega)).indicator
              (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus rate rewards C_star C_h u t) z ∂ν) +
              ∫ z : Z, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog rate rewards C_star C_h u t z ∂ν := by
        rw [show afterCallBacklog rate rewards C_star C_h u t = fun z =>
          (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t (by omega)).indicator
            (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus rate rewards C_star C_h u t) z +
            ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog rate rewards C_star C_h u t z by
              funext z; simp [afterCallBacklog, hnext]]
        exact integral_add hnextBacklog hfutureBacklog
      have hloss :
          (∫ z : Z, supportLoss rate rewards C_star C_h u t z ∂ν) =
            (∫ z : Z, ReferenceFirstCollectionRenewalEnergyBoundaryJoins.boundaryLoss rate rewards C_star C_h u t qfirst hdate z ∂ν) +
              ∫ z : Z, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss rate rewards C_star C_h u t z ∂ν := by
        rw [show supportLoss rate rewards C_star C_h u t = fun z =>
          ReferenceFirstCollectionRenewalEnergyBoundaryJoins.boundaryLoss rate rewards C_star C_h u t qfirst hdate z +
            ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss rate rewards C_star C_h u t z by
              funext z; simp [supportLoss, hfuture, qfirst]]
        exact integral_add
          (ReferenceFirstCollectionRenewalEnergyBoundaryJoins.integrable_boundaryLoss rate rewards C_star C_h u t control0 qfirst hdate)
          (futureAdjacentLoss_integrable rate rewards C_star C_h u t control0)
      have hterm :
          (∫ z : Z, terminalEnergy rate rewards C_star C_h u t z ∂ν) =
            ∫ z : Z, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureTerminalEnergy rate rewards C_star C_h u t z ∂ν := by
        apply integral_congr_ae
        filter_upwards [] with z
        simp [terminalEnergy, hfuture]
      have hgate :
          afterCallGateMass rate rewards C_star C_h u t =
            (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t (by omega)) +
              ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass rate rewards C_star C_h u t := by
        simp [afterCallGateMass, hnext]
      have hsum := add_le_add hR hH
      rw [← hjoin, hinitial] at hsum
      rw [hbacklog, hloss, hterm, hgate]
      rw [hboundary] at hsum
      linarith only [hsum]
    · have hlast : t.val + 2 = p.T := by omega
      have hdates : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates
          t = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro n hn
        have hn' := Finset.mem_Ico.mp hn
        omega
      have hlossDates : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLossDates
          t = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro n hn
        have hn' := Finset.mem_Ico.mp hn
        omega
      have hemptyBacklog : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog rate rewards C_star C_h u t =
          fun _ => 0 := by
        funext z
        simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog, hdates]
      have hemptyMass : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass rate rewards C_star C_h u t = 0 := by
        simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass, hdates]
      have hemptyTerminal : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureTerminalEnergy rate rewards C_star C_h u t =
          fun _ => 0 := by
        funext z
        simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureTerminalEnergy, hfuture]
      have hemptyInitial : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureInitialEnergy rate rewards C_star C_h u t =
          fun _ => 0 := by
        funext z
        simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureInitialEnergy, hfuture]
      have hemptyLoss : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss rate rewards C_star C_h u t =
          fun _ => 0 := by
        funext z
        simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss, hlossDates]
      have hR :=
        ReferenceFirstCollectionRenewalNextDateRWeightedAccounting.actualRWeightedEnergyAccounting
          rate rewards C_star C_h u t control0 hnext
      have hjoin :
          (∫ z : Z, ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus rate rewards C_star C_h u t z ∂ν) =
            ∫ z : Z, ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vminus rate rewards C_star C_h u t z ∂ν := by
        apply integral_congr_ae
        filter_upwards [] with z
        exact ReferenceFirstCollectionRenewalEnergyBoundaryJoins.whole_next_energy_join rate rewards C_star C_h u t z
      have hbacklog :
          (∫ z : Z, afterCallBacklog rate rewards C_star C_h u t z ∂ν) =
            (∫ z : Z, (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t hnext).indicator
              (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus rate rewards C_star C_h u t) z ∂ν) := by
        rw [show afterCallBacklog rate rewards C_star C_h u t = fun z =>
          (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t hnext).indicator
            (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus rate rewards C_star C_h u t) z by
              funext z; simp [afterCallBacklog, hnext, hemptyBacklog]]
      have hterm :
          (∫ z : Z, terminalEnergy rate rewards C_star C_h u t z ∂ν) =
            ∫ z : Z, ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus rate rewards C_star C_h u t hnext z ∂ν := by
        apply integral_congr_ae
        filter_upwards [] with z
        simp [terminalEnergy, hfuture, hnext]
      have hloss :
          (∫ z : Z, supportLoss rate rewards C_star C_h u t z ∂ν) = 0 := by
        rw [show supportLoss rate rewards C_star C_h u t = fun _ => 0 by
          funext z; simp [supportLoss, hfuture]]
        simp
      have hgate : afterCallGateMass rate rewards C_star C_h u t =
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t hnext) := by
        simp [afterCallGateMass, hnext, hemptyMass]
      have hR' := hR
      rw [← hjoin] at hR'
      rw [hbacklog, hterm, hloss, hgate]
      simpa only [add_zero] using hR'
  · have hlast : t.val + 1 = p.T := by omega
    have hfuture : ¬ t.val + 2 < p.T := by omega
    have hdates : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates
        t = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hn' := Finset.mem_Ico.mp hn
      omega
    have hlossDates : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLossDates
        t = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hn' := Finset.mem_Ico.mp hn
      omega
    have hemptyBacklog : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog rate rewards C_star C_h u t =
        fun _ => 0 := by
      funext z
      simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog, hdates]
    have hemptyMass : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass rate rewards C_star C_h u t = 0 := by
      simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass, hdates]
    have hemptyLoss : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss rate rewards C_star C_h u t =
        fun _ => 0 := by
      funext z
      simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss, hlossDates]
    have hbacklog :
        (∫ z : Z, afterCallBacklog rate rewards C_star C_h u t z ∂ν) = 0 := by
      rw [show afterCallBacklog rate rewards C_star C_h u t = fun _ => 0 by
        funext z; simp [afterCallBacklog, hnext, hemptyBacklog]]
      simp
    have hterm :
        (∫ z : Z, terminalEnergy rate rewards C_star C_h u t z ∂ν) =
          ∫ z : Z, ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus rate rewards C_star C_h u t z ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp [terminalEnergy, hfuture, hnext]
    have hloss :
        (∫ z : Z, supportLoss rate rewards C_star C_h u t z ∂ν) = 0 := by
      rw [show supportLoss rate rewards C_star C_h u t = fun _ => 0 by
        funext z; simp [supportLoss, hfuture]]
      simp
    have hgate : afterCallGateMass rate rewards C_star C_h u t = 0 := by
      simp [afterCallGateMass, hnext, hemptyMass]
    rw [hbacklog, hterm, hloss, hgate]
    linarith

theorem wholeCalendar_weighted_accounting
    (control0 : ContinuousLearningRows.TimeControl p) :
    (11 / 2 : ℝ) *
        (∫ z : Z, wholeCalendarBacklog rate rewards C_star C_h u t z ∂ν) +
      (∫ z : Z, terminalEnergy rate rewards C_star C_h u t z ∂ν) +
      ∫ z : Z, supportLoss rate rewards C_star C_h u t z ∂ν ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        wholeCalendarGateMass rate rewards C_star C_h u t +
      ∫ z : Z, ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Vminus rate rewards C_star C_h u t z ∂ν := by
  have hwhole := ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.weightedCost_integral_le rate rewards C_star C_h u t control0
  have hafter := afterCall_weighted_calendar_accounting rate rewards C_star C_h u t control0
  have hsplit :
      (∫ z : Z, wholeCalendarBacklog rate rewards C_star C_h u t z ∂ν) =
        (∫ z : Z, (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.E rate rewards C_star C_h u t).indicator
          (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Bminus rate rewards C_star C_h u t) z ∂ν) +
        ∫ z : Z, afterCallBacklog rate rewards C_star C_h u t z ∂ν := by
    rw [show wholeCalendarBacklog rate rewards C_star C_h u t = fun z =>
      (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.E rate rewards C_star C_h u t).indicator
        (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Bminus rate rewards C_star C_h u t) z +
          afterCallBacklog rate rewards C_star C_h u t z by
            funext z; rfl]
    exact integral_add
      (wholeBacklog_integrable rate rewards C_star C_h u t control0)
      (afterCallBacklog_integrable rate rewards C_star C_h u t control0)
  have hmass : wholeCalendarGateMass rate rewards C_star C_h u t =
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.E rate rewards C_star C_h u t) +
        afterCallGateMass rate rewards C_star C_h u t := rfl
  rw [hsplit, hmass]
  linarith only [hwhole, hafter]

theorem afterCallGateMass_le_horizon :
    afterCallGateMass rate rewards C_star C_h u t ≤
      ((p.T - (t.val + 1) : ℕ) : ℝ) * (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real Set.univ := by
  by_cases hnext : t.val + 1 < p.T
  · have hnextMass :
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t hnext) ≤
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real Set.univ :=
      measureReal_mono (Set.subset_univ _) (by finiteness)
    have hfuture := ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass_le_horizon rate rewards C_star C_h u t
    have hcount : 1 + (p.T - (t.val + 2)) = p.T - (t.val + 1) := by omega
    have hcountReal :
        (1 : ℝ) + ((p.T - (t.val + 2) : ℕ) : ℝ) =
          ((p.T - (t.val + 1) : ℕ) : ℝ) := by
      exact_mod_cast hcount
    unfold afterCallGateMass
    rw [dite_eq_left hnext]
    calc
      _ ≤ (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real Set.univ +
          ((p.T - (t.val + 2) : ℕ) : ℝ) * (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real Set.univ :=
        add_le_add hnextMass hfuture
      _ = ((p.T - (t.val + 1) : ℕ) : ℝ) * (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real Set.univ := by
        calc
          _ = ((1 : ℝ) + ((p.T - (t.val + 2) : ℕ) : ℝ)) *
              (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real Set.univ := by ring
          _ = _ := by rw [hcountReal]
  · have hlast : t.val + 1 = p.T := by omega
    have hdates : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates
        t = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hn' := Finset.mem_Ico.mp hn
      omega
    have hfutureZero : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass rate rewards C_star C_h u t = 0 := by
      simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass, hdates]
    simp [afterCallGateMass, hfutureZero, hlast]

theorem wholeCalendarGateMass_le_horizon :
    wholeCalendarGateMass rate rewards C_star C_h u t ≤
      ((p.T - t.val : ℕ) : ℝ) * (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real Set.univ := by
  have hwhole : (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.E rate rewards C_star C_h u t) ≤ (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real Set.univ :=
    measureReal_mono (Set.subset_univ _) (by finiteness)
  have hafter := afterCallGateMass_le_horizon rate rewards C_star C_h u t
  have hcount : 1 + (p.T - (t.val + 1)) = p.T - t.val := by omega
  have hcountReal :
      (1 : ℝ) + ((p.T - (t.val + 1) : ℕ) : ℝ) =
        ((p.T - t.val : ℕ) : ℝ) := by
    exact_mod_cast hcount
  unfold wholeCalendarGateMass
  calc
    _ ≤ (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real Set.univ +
        ((p.T - (t.val + 1) : ℕ) : ℝ) * (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real Set.univ :=
      add_le_add hwhole hafter
    _ = ((p.T - t.val : ℕ) : ℝ) * (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real Set.univ := by
      calc
        _ = ((1 : ℝ) + ((p.T - (t.val + 1) : ℕ) : ℝ)) *
            (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real Set.univ := by ring
        _ = _ := by rw [hcountReal]

theorem afterCall_weighted_calendar_accounting_horizon
    (control0 : ContinuousLearningRows.TimeControl p) :
    (11 / 2 : ℝ) *
        (∫ z : Z, afterCallBacklog rate rewards C_star C_h u t z ∂ν) +
      (∫ z : Z, terminalEnergy rate rewards C_star C_h u t z ∂ν) +
      ∫ z : Z, supportLoss rate rewards C_star C_h u t z ∂ν ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (((p.T - (t.val + 1) : ℕ) : ℝ) * (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real Set.univ) +
      ∫ z : Z, ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus rate rewards C_star C_h u t z ∂ν := by
  have h := afterCall_weighted_calendar_accounting rate rewards C_star C_h u t control0
  have hmass := afterCallGateMass_le_horizon rate rewards C_star C_h u t
  have hmul := mul_le_mul_of_nonneg_left hmass
    (calendarCost_nonneg (p := p))
  exact h.trans (add_le_add hmul le_rfl)

theorem wholeCalendar_weighted_accounting_horizon
    (control0 : ContinuousLearningRows.TimeControl p) :
    (11 / 2 : ℝ) *
        (∫ z : Z, wholeCalendarBacklog rate rewards C_star C_h u t z ∂ν) +
      (∫ z : Z, terminalEnergy rate rewards C_star C_h u t z ∂ν) +
      ∫ z : Z, supportLoss rate rewards C_star C_h u t z ∂ν ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (((p.T - t.val : ℕ) : ℝ) * (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real Set.univ) +
      ∫ z : Z, ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Vminus rate rewards C_star C_h u t z ∂ν := by
  have h := wholeCalendar_weighted_accounting rate rewards C_star C_h u t control0
  have hmass := wholeCalendarGateMass_le_horizon rate rewards C_star C_h u t
  have hmul := mul_le_mul_of_nonneg_left hmass
    (calendarCost_nonneg (p := p))
  exact h.trans (add_le_add hmul le_rfl)

theorem afterCall_backlog_budget_horizon
    (control0 : ContinuousLearningRows.TimeControl p) :
    (11 / 2 : ℝ) *
        (∫ z : Z, afterCallBacklog rate rewards C_star C_h u t z ∂ν) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (((p.T - (t.val + 1) : ℕ) : ℝ) * (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real Set.univ) +
      ∫ z : Z, ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus rate rewards C_star C_h u t z ∂ν := by
  have h := afterCall_weighted_calendar_accounting_horizon rate rewards C_star C_h u t control0
  have hnonneg :
      0 ≤ (∫ z : Z, terminalEnergy rate rewards C_star C_h u t z ∂ν) +
        ∫ z : Z, supportLoss rate rewards C_star C_h u t z ∂ν :=
    add_nonneg
      (integral_nonneg (fun z => terminalEnergy_nonneg rate rewards C_star C_h u t z))
      (integral_nonneg (fun z => supportLoss_nonneg rate rewards C_star C_h u t z))
  linarith only [h, hnonneg]

theorem wholeCalendar_backlog_budget_horizon
    (control0 : ContinuousLearningRows.TimeControl p) :
    (11 / 2 : ℝ) *
        (∫ z : Z, wholeCalendarBacklog rate rewards C_star C_h u t z ∂ν) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (((p.T - t.val : ℕ) : ℝ) * (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real Set.univ) +
      ∫ z : Z, ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Vminus rate rewards C_star C_h u t z ∂ν := by
  have h := wholeCalendar_weighted_accounting_horizon rate rewards C_star C_h u t control0
  have hnonneg :
      0 ≤ (∫ z : Z, terminalEnergy rate rewards C_star C_h u t z ∂ν) +
        ∫ z : Z, supportLoss rate rewards C_star C_h u t z ∂ν :=
    add_nonneg
      (integral_nonneg (fun z => terminalEnergy_nonneg rate rewards C_star C_h u t z))
      (integral_nonneg (fun z => supportLoss_nonneg rate rewards C_star C_h u t z))
  linarith only [h, hnonneg]

end Bandits.Support.ReferenceFirstCollectionRenewalWeightedCalendarAccounting

end
