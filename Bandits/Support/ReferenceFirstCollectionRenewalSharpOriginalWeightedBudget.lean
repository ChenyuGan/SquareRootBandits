/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalOriginalCalendarMassBudget
public import Bandits.Support.ReferenceFirstCollectionRenewalOriginalWeightedContinuation

import Mathlib.Tactic

/-!
# Sharp original-source weighted budget across the first renewal

The actual pre-call, first-call, and after-call weighted energies share the
joint datewise source-mass partition and therefore pay one calendar horizon.
-/

public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical
open Bandits.Support.ConstructorDimensions (Parameters)
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open Bandits.Support.ActualInitializationPhysicalStep (GridRewardTable)
open Bandits.Support.ContinuousLearningRows (TimeControl)

namespace Bandits.Support.ReferenceFirstCollectionRenewalSharpOriginalWeightedBudget

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)

local notation "S" => SourceInput p
local notation "μ" => sourceInputLaw p
local notation "Phi" =>
  ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.oldPotential
    rate rewards C_star C_h
local notation "LIVE" =>
  ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
    rate rewards C_star C_h
local notation "OLD" =>
  ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.costOld
    rate rewards C_star C_h

/-- The coefficient of the original-calendar weighted budget. -/
@[expose] public def originalCalendarCost : ℝ :=
  CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)

/-- The exact combined pre-call and actual first-call readout is integrable. -/
public theorem originalPreCallWeightedCost_integrable
    (control0 : TimeControl p) :
    Integrable
      (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalPreCallWeightedCost
        rate rewards C_star C_h) μ := by
  unfold ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalPreCallWeightedCost
  exact (integrable_finsetSum Finset.univ fun t _ =>
      (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.integrable_retainedWeightedBacklogCost
        rate rewards C_star C_h t control0).add
      (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_readouts_regular
        rate rewards C_star C_h control0 t).2.2.2).add
    (ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog_integrable
      rate rewards C_star C_h control0)

/-- The sum of the actual pre-call and after-call backlog readouts is
integrable under the unrestricted original source law. -/
public theorem originalPreCallAfterCallWeightedCost_integrable
    (control0 : TimeControl p) :
    Integrable
      (fun z : S =>
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalPreCallWeightedCost
            rate rewards C_star C_h z +
          ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog
            rate rewards C_star C_h z) μ := by
  exact (originalPreCallWeightedCost_integrable rate rewards C_star C_h control0).add
    (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog_integrable
      rate rewards C_star C_h control0)

/-- The actual first-call outgoing energy and retained pre-call cost are paid
by their exact original-source date masses and the retained first-call mass. -/
public theorem integral_preCall_firstCall_weighted_energy_le_actual_mass
    (control0 : TimeControl p) :
    (∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
        rate rewards C_star C_h z ∂μ) +
      (11 / 2 : ℝ) *
        (∫ z,
          ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalPreCallWeightedCost
            rate rewards C_star C_h z ∂μ) ≤
      originalCalendarCost (p := p) *
        ((∑ t : Fin p.T,
            (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
                rate rewards C_star C_h t control0 +
              (sourceInputLaw p).real
                (ReferenceFirstCollectionOldCalendarExponentialStep.G
                  rate rewards C_star C_h t))) +
          (sourceInputLaw p).real
            (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
              rate rewards C_star C_h)) := by
  have hsum0 := Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) =>
    ReferenceFirstCollectionPrecallActualCallWeightedEnergyJoin.integral_preCallPotential_calendar_step_le_sourceCellMass
      rate rewards C_star C_h t control0
  have hsumExpanded :
      (∑ t : Fin p.T,
        ∫ z, Phi (t.val + 1) z - Phi t.val z ∂μ) +
        (11 / 2 : ℝ) *
          (∑ t : Fin p.T, ∫ z, LIVE t z + OLD t z ∂μ) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        ∑ t : Fin p.T,
          (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
              rate rewards C_star C_h t control0 +
            (sourceInputLaw p).real
              (ReferenceFirstCollectionOldCalendarExponentialStep.G
                rate rewards C_star C_h t)) := by
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using hsum0
  have hPreCost : Integrable
      (fun z : S => ∑ t : Fin p.T, (LIVE t z + OLD t z)) μ :=
    integrable_finsetSum Finset.univ fun t _ =>
      (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.integrable_retainedWeightedBacklogCost
        rate rewards C_star C_h t control0).add
      (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_readouts_regular
        rate rewards C_star C_h control0 t).2.2.2
  have hPreCostIntegral :
      (∫ z, ∑ t : Fin p.T, (LIVE t z + OLD t z) ∂μ) =
        ∑ t : Fin p.T, ∫ z, LIVE t z + OLD t z ∂μ :=
    integral_finsetSum Finset.univ fun t _ =>
      (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.integrable_retainedWeightedBacklogCost
        rate rewards C_star C_h t control0).add
      (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_readouts_regular
        rate rewards C_star C_h control0 t).2.2.2
  have hPrePotential :
      (∫ z, Phi p.T z ∂μ) +
        (11 / 2 : ℝ) *
          (∫ z, ∑ t : Fin p.T, (LIVE t z + OLD t z) ∂μ) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        ∑ t : Fin p.T,
          (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
              rate rewards C_star C_h t control0 +
            (sourceInputLaw p).real
              (ReferenceFirstCollectionOldCalendarExponentialStep.G
                rate rewards C_star C_h t)) := by
    have h := hsumExpanded
    rw [← ReferenceFirstCollectionPrecallWeightedBacklogBound.integral_preCallPotential_telescope
        rate rewards C_star C_h,
      ← hPreCostIntegral] at h
    exact h
  have hIncoming :
      (∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus
        rate rewards C_star C_h z ∂μ) ≤ (∫ z, Phi p.T z ∂μ) := by
    apply integral_mono_ae
    · exact ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus_integrable
        rate rewards C_star C_h control0
    · exact (ReferenceFirstCollectionPrecallWeightedBacklogBound.precallPotential_regular
        rate rewards C_star C_h p.T (Nat.le_refl _)).2
    · exact Filter.Eventually.of_forall fun z =>
        ReferenceFirstCollectionPrecallActualCallWeightedEnergyJoin.callVMinus_le_preCallPotential_terminal
          rate rewards C_star C_h z
  have hPreEnergy :
      (∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus
        rate rewards C_star C_h z ∂μ) +
        (11 / 2 : ℝ) *
          (∫ z, ∑ t : Fin p.T, (LIVE t z + OLD t z) ∂μ) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        ∑ t : Fin p.T,
          (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
              rate rewards C_star C_h t control0 +
            (sourceInputLaw p).real
              (ReferenceFirstCollectionOldCalendarExponentialStep.G
                rate rewards C_star C_h t)) :=
    (add_le_add hIncoming le_rfl).trans hPrePotential
  have hCallEnergy :=
    ReferenceFirstCollectionActualCallWeightedEnergy.integral_call_energy_and_weighted_cost_le_incoming_add_mass
      rate rewards C_star C_h control0
  have hCallCost : Integrable
      (ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
        rate rewards C_star C_h) μ :=
    ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog_integrable
      rate rewards C_star C_h control0
  have hPreCallCombined := add_le_add hPreEnergy hCallEnergy
  have hPreCallRaw :
      (∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
        rate rewards C_star C_h z ∂μ) +
        (11 / 2 : ℝ) *
          ((∫ z, ∑ t : Fin p.T, (LIVE t z + OLD t z) ∂μ) +
            ∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
              rate rewards C_star C_h z ∂μ) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          ∑ t : Fin p.T,
            (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
                rate rewards C_star C_h t control0 +
              (sourceInputLaw p).real
                (ReferenceFirstCollectionOldCalendarExponentialStep.G
                  rate rewards C_star C_h t)) +
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          (sourceInputLaw p).real
            (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
              rate rewards C_star C_h) := by
    calc
      _ =
          ((∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus
              rate rewards C_star C_h z ∂μ) +
            (11 / 2 : ℝ) *
              (∫ z, ∑ t : Fin p.T, (LIVE t z + OLD t z) ∂μ)) +
          ((∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
              rate rewards C_star C_h z ∂μ) +
            (11 / 2 : ℝ) *
              ∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
                rate rewards C_star C_h z ∂μ) -
          (∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus
            rate rewards C_star C_h z ∂μ) := by ring
      _ ≤
          ((CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
              ∑ t : Fin p.T,
                (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
                    rate rewards C_star C_h t control0 +
                  (sourceInputLaw p).real
                    (ReferenceFirstCollectionOldCalendarExponentialStep.G
                      rate rewards C_star C_h t)) +
            ((∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus
                rate rewards C_star C_h z ∂μ) +
              (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
                (sourceInputLaw p).real
                  (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
                    rate rewards C_star C_h))) -
          (∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus
            rate rewards C_star C_h z ∂μ) :=
        sub_le_sub_right hPreCallCombined _
      _ = _ := by ring
  have hOriginalPreCostIntegral :
      (∫ z, ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalPreCallWeightedCost
        rate rewards C_star C_h z ∂μ) =
        (∫ z, ∑ t : Fin p.T, (LIVE t z + OLD t z) ∂μ) +
          ∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
            rate rewards C_star C_h z ∂μ := by
    unfold ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalPreCallWeightedCost
    rw [integral_add hPreCost hCallCost, hPreCostIntegral]
  have hPreCall :
      (∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
        rate rewards C_star C_h z ∂μ) +
        (11 / 2 : ℝ) *
          (∫ z, ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalPreCallWeightedCost
            rate rewards C_star C_h z ∂μ) ≤
      originalCalendarCost (p := p) *
        ((∑ t : Fin p.T,
            (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
                rate rewards C_star C_h t control0 +
              (sourceInputLaw p).real
                (ReferenceFirstCollectionOldCalendarExponentialStep.G
                  rate rewards C_star C_h t))) +
          (sourceInputLaw p).real
            (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
              rate rewards C_star C_h)) := by
    rw [originalCalendarCost]
    calc
      _ =
          (∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
            rate rewards C_star C_h z ∂μ) +
            (11 / 2 : ℝ) *
              ((∫ z, ∑ t : Fin p.T, (LIVE t z + OLD t z) ∂μ) +
                ∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
                  rate rewards C_star C_h z ∂μ) := by
        rw [hOriginalPreCostIntegral]
      _ ≤ _ := hPreCallRaw
      _ = _ := by ring
  rw [originalCalendarCost]
  exact hPreCall

/-- The actual after-call continuation mass is the same retained successor
mass plus strict-future mass counted by the sharp joint calendar partition. -/
theorem afterCallGateMass_eq_joint_postGateMass
    (u t : Fin p.T) :
    (∑ q : Fin p.T,
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t).real
        (ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGate
          rate rewards C_star C_h u t q)) =
      ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
        rate rewards C_star C_h u t := by
  rw [ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateMass_sum_eq]
  rfl

/-- The exact actual original-source energy and weighted backlog readouts fit
one calendar horizon using the joint pre/call/post datewise mass partition. -/
public theorem original_preCall_afterCall_weighted_energy_join_sharp
    (control0 : TimeControl p) :
    (11 / 2 : ℝ) *
        ((∫ z : S,
            ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalPreCallWeightedCost
              rate rewards C_star C_h z ∂μ) +
          ∫ z : S,
            ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog
              rate rewards C_star C_h z ∂μ) +
      (∫ z : S,
          ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalTerminalEnergy
            rate rewards C_star C_h z ∂μ) +
      ∫ z : S,
          ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalSupportLoss
            rate rewards C_star C_h z ∂μ ≤
      originalCalendarCost (p := p) * (p.T : ℝ) := by
  let preMass : ℝ :=
    ∑ t : Fin p.T,
      (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
          rate rewards C_star C_h t control0 +
        (sourceInputLaw p).real
          (ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h t))
  let firstCallMass : ℝ :=
    (sourceInputLaw p).real
      (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
        rate rewards C_star C_h)
  let afterCallMass : ℝ :=
    ∑ u : Fin p.T, ∑ t : Fin p.T,
      ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
        rate rewards C_star C_h u t
  have hpre :=
    integral_preCall_firstCall_weighted_energy_le_actual_mass
      rate rewards C_star C_h control0
  have hpre' :
      (∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
          rate rewards C_star C_h z ∂μ) +
        (11 / 2 : ℝ) *
          (∫ z, ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalPreCallWeightedCost
            rate rewards C_star C_h z ∂μ) ≤
      originalCalendarCost (p := p) * (preMass + firstCallMass) := by
    simpa only [preMass, firstCallMass] using hpre
  have hafterRaw :=
    ReferenceFirstCollectionRenewalOriginalWeightedContinuation.afterCall_weighted_calendar_accounting_sum_wholeSource
      rate rewards C_star C_h control0
  rw [← ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog_integral
        rate rewards C_star C_h control0,
      ← ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalTerminalEnergy_integral
        rate rewards C_star C_h control0,
      ← ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalSupportLoss_integral
        rate rewards C_star C_h control0] at hafterRaw
  have hafter :
      (11 / 2 : ℝ) *
          (∫ z : S,
            ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog
              rate rewards C_star C_h z ∂μ) +
        (∫ z : S,
          ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalTerminalEnergy
            rate rewards C_star C_h z ∂μ) +
        ∫ z : S,
          ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalSupportLoss
            rate rewards C_star C_h z ∂μ ≤
      originalCalendarCost (p := p) * afterCallMass +
        ∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
          rate rewards C_star C_h z ∂μ := by
    simpa only [originalCalendarCost, afterCallMass] using hafterRaw
  have hjoined :
      (11 / 2 : ℝ) *
          ((∫ z : S,
              ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalPreCallWeightedCost
                rate rewards C_star C_h z ∂μ) +
            ∫ z : S,
              ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog
                rate rewards C_star C_h z ∂μ) +
        (∫ z : S,
          ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalTerminalEnergy
            rate rewards C_star C_h z ∂μ) +
        ∫ z : S,
          ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalSupportLoss
            rate rewards C_star C_h z ∂μ ≤
      originalCalendarCost (p := p) * ((preMass + firstCallMass) + afterCallMass) := by
    have hadd := add_le_add hpre' hafter
    calc
      _ =
          ((∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
              rate rewards C_star C_h z ∂μ) +
            (11 / 2 : ℝ) *
              (∫ z, ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalPreCallWeightedCost
                rate rewards C_star C_h z ∂μ)) +
          ((11 / 2 : ℝ) *
              (∫ z, ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog
                rate rewards C_star C_h z ∂μ) +
            (∫ z, ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalTerminalEnergy
              rate rewards C_star C_h z ∂μ) +
            ∫ z, ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalSupportLoss
              rate rewards C_star C_h z ∂μ) -
          (∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
            rate rewards C_star C_h z ∂μ) := by ring
      _ ≤
          (originalCalendarCost (p := p) * (preMass + firstCallMass) +
            (originalCalendarCost (p := p) * afterCallMass +
              ∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
                rate rewards C_star C_h z ∂μ)) -
          (∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
            rate rewards C_star C_h z ∂μ) :=
        sub_le_sub_right hadd _
      _ = _ := by ring
  have hpostMass :
      afterCallMass =
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ((if hnext : t.val + 1 < p.T then
              (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t).real
                (ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
                  rate rewards C_star C_h u t hnext)
            else 0) +
            ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
              rate rewards C_star C_h u t) := by
    unfold afterCallMass
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro t _
    calc
      ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
          rate rewards C_star C_h u t =
        ∑ q : Fin p.T,
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t).real
            (ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGate
              rate rewards C_star C_h u t q) :=
          (afterCallGateMass_eq_joint_postGateMass
            rate rewards C_star C_h u t).symm
      _ =
          (if hnext : t.val + 1 < p.T then
              (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t).real
                (ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
                  rate rewards C_star C_h u t hnext)
            else 0) +
            ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
              rate rewards C_star C_h u t :=
        ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateMass_sum_eq
          rate rewards C_star C_h u t
  have hmass :=
    ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.sum_sourceDateMass_le_horizon
      rate rewards C_star C_h control0
  rw [← hpostMass] at hmass
  have hmass' : preMass + firstCallMass + afterCallMass ≤ (p.T : ℝ) := by
    simpa only [preMass, firstCallMass, afterCallMass] using hmass
  have hcostNonneg :=
    ReferenceFirstCollectionRenewalWeightedCalendarAccounting.calendarCost_nonneg
      (p := p)
  have hscaled :=
    mul_le_mul_of_nonneg_left hmass' hcostNonneg
  calc
    _ ≤ originalCalendarCost (p := p) * ((preMass + firstCallMass) + afterCallMass) :=
      hjoined
    _ ≤ originalCalendarCost (p := p) * (p.T : ℝ) := hscaled

/-- Removing the already proved nonnegative terminal energy and support loss
gives the backlog-only consequence with the same single horizon. -/
public theorem original_preCall_afterCall_weighted_backlog_budget_sharp
    (control0 : TimeControl p) :
    (11 / 2 : ℝ) *
        ((∫ z : S,
            ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalPreCallWeightedCost
              rate rewards C_star C_h z ∂μ) +
          ∫ z : S,
            ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog
              rate rewards C_star C_h z ∂μ) ≤
      originalCalendarCost (p := p) * (p.T : ℝ) := by
  have h := original_preCall_afterCall_weighted_energy_join_sharp
    rate rewards C_star C_h control0
  have hterm :=
    ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalTerminalEnergy_integral_nonneg
      rate rewards C_star C_h
  have hloss :=
    ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalSupportLoss_integral_nonneg
      rate rewards C_star C_h
  linarith only [h, hterm, hloss]

end Bandits.Support.ReferenceFirstCollectionRenewalSharpOriginalWeightedBudget

end
