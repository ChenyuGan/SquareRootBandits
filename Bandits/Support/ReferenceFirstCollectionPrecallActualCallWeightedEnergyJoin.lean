/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionPrecallWeightedBacklogBound
public import Bandits.Support.ReferenceFirstCollectionPrecallFirstCallMassBudget

import Mathlib.Tactic

/-!
# Original-source pre-call and first-invocation energy join

The terminal optional pre-call queue is the incoming queue of the same first
sampler invocation. The sharp datewise source-cell budgets and the retained
first-call mass then fit one calendar horizon.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open Bandits.Support.ActualInitializationPhysicalStep (GridRewardTable)
open Bandits.Support.ContinuousLearningRows (TimeControl)
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionPrecallActualCallWeightedEnergyJoin

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

/-- The incoming energy of the actual first invocation is the terminal readout
of the same optional pre-call prefix. The absent-call branch uses the literal
zero call observation and retains the terminal potential on the whole source. -/
public theorem callVMinus_le_preCallPotential_terminal (z : S) :
    ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus
        rate rewards C_star C_h z ≤ Phi p.T z := by
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none =>
      have hzero :=
        ReferenceFirstCollectionActualCallWeightedEnergy.callObservations_eq_zero_of_firstCollectionCall_none
          rate rewards C_star C_h z hcall
      rw [hzero.1]
      exact ReferenceFirstCollectionPrecallWeightedBacklogBound.precallPotential_terminal_nonneg
        rate rewards C_star C_h z
  | some call =>
      rcases call with ⟨u, t, theta⟩
      have hcall' : ReferenceFirstCollectionSamplerCall.firstCollectionCall
          rate rewards C_star C_h z = some (u, (t, theta)) := by
        simpa using hcall
      obtain ⟨L, c, hpast, hcurrent, henabled, hbefore, hafter,
        hthetaMinus, hthetaPlus, hminus, hplus, hbacklog⟩ :=
        ReferenceFirstCollectionActualCallWeightedEnergy.callEnergy_actual_run_readouts_of_firstCollectionCall
          rate rewards C_star C_h z u t theta hcall'
      have hfirstCell : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
          rate rewards C_star C_h u t := by
        change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
          rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) = some (u, t)
        rw [hcall']
        rfl
      have hprefix :=
        ReferenceFirstCollectionPrecallCalendarSupport.precallCells_at_or_after_firstCell
          rate rewards C_star C_h u t p.T (Nat.le_of_lt t.isLt) z hfirstCell
      have hterminalCells :
          ReferenceFirstCollectionPrecallCalendarSupport.precallCells?
            rate rewards C_star C_h p.T z = some L := by
        rw [hprefix, hpast]
      have hincoming :
          ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus
              rate rewards C_star C_h z = Phi p.T z := by
        simpa only [
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.oldPotential,
          hterminalCells,
          RecordedWeightedDrift.weightedSquarePotential,
          StoppedQueueBound.normalizedBacklog] using hminus
      rw [hincoming]

/-- The actual per-date pre-call energy increment retains the full original
birth, continuing and empty source-cell mass, together with the accepted OLD
mass. No phase-union enlargement is made. -/
public theorem integral_preCallPotential_calendar_step_le_sourceCellMass
    (t : Fin p.T) (control0 : TimeControl p) :
    (∫ z, Phi (t.val + 1) z - Phi t.val z ∂μ) +
      (11 / 2 : ℝ) * (∫ z, LIVE t z + OLD t z ∂μ) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
          rate rewards C_star C_h t control0 +
          (sourceInputLaw p).real (ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h t)) := by
  let V := ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt
    rate rewards C_star C_h
  have hPhi := ReferenceFirstCollectionPrecallWeightedBacklogBound.precallPotential_regular
    rate rewards C_star C_h (t.val + 1) (Nat.succ_le_of_lt t.isLt)
  have hPhi0 := ReferenceFirstCollectionPrecallWeightedBacklogBound.precallPotential_regular
    rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt)
  have hDelta : Integrable (fun z : S => Phi (t.val + 1) z - Phi t.val z) μ :=
    hPhi.2.sub hPhi0.2
  have hOld := ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_readouts_regular
    rate rewards C_star C_h control0 t
  have hD : Integrable
      (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld
        rate rewards C_star C_h t) μ := hOld.2.1
  have hOldCost : Integrable (OLD t) μ := hOld.2.2.2
  have hLive : Integrable (LIVE t) μ :=
    ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.integrable_retainedWeightedBacklogCost
      rate rewards C_star C_h t control0
  have hV : Integrable (fun z : S => V (t.val + 1) z - V t.val z) μ := by
    have heq : (fun z : S => V (t.val + 1) z - V t.val z) =
        fun z => (Phi (t.val + 1) z - Phi t.val z) -
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld
            rate rewards C_star C_h t z := by
      funext z
      rw [ReferenceFirstCollectionPrecallWeightedBacklogBound.precallPotential_calendar_increment
        rate rewards C_star C_h t z]
      ring
    rw [heq]
    exact hDelta.sub hD
  have hIntegralIdentity :
      (∫ z, Phi (t.val + 1) z - Phi t.val z ∂μ) =
        (∫ z, V (t.val + 1) z - V t.val z ∂μ) +
          ∫ z, ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld
            rate rewards C_star C_h t z ∂μ := by
    calc
      _ = ∫ z, (V (t.val + 1) z - V t.val z) +
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld
            rate rewards C_star C_h t z ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        exact ReferenceFirstCollectionPrecallWeightedBacklogBound.precallPotential_calendar_increment
          rate rewards C_star C_h t z
      _ = _ := integral_add hV hD
  have hLiveStep :=
    ReferenceFirstCollectionPrecallWeightedBacklogBound.firstLive_cell_mass_bound
      rate rewards C_star C_h t control0
  have hLiveCombinedRaw :
      (∫ z, V (t.val + 1) z - V t.val z ∂μ) +
        (11 / 2 : ℝ) * (∫ z, LIVE t z ∂μ) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        ((∑ q : Fin (ConstructorDimensions.M p),
          (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards
            C_star C_h t
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)).real
            Set.univ) +
          ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
            ((ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards
              C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ +
             (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ)) := by
    linarith only [hLiveStep]
  have hLiveCombined :
      (∫ z, V (t.val + 1) z - V t.val z ∂μ) +
        (11 / 2 : ℝ) * (∫ z, LIVE t z ∂μ) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
          rate rewards C_star C_h t control0 := by
    simpa only [ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass]
      using hLiveCombinedRaw
  have hOldCombined :
      (∫ z, ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld
        rate rewards C_star C_h t z ∂μ) +
        (11 / 2 : ℝ) * (∫ z, OLD t z ∂μ) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (sourceInputLaw p).real (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t) :=
    ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.sourceIntegral_weighted_cost
      rate rewards C_star C_h control0 t
  have hCostIntegral :
      (∫ z, LIVE t z + OLD t z ∂μ) =
        (∫ z, LIVE t z ∂μ) + (∫ z, OLD t z ∂μ) := integral_add hLive hOldCost
  change (∫ z, Phi (t.val + 1) z - Phi t.val z ∂μ) +
      (11 / 2 : ℝ) * (∫ z, LIVE t z + OLD t z ∂μ) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
          rate rewards C_star C_h t control0 +
          (sourceInputLaw p).real (ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h t))
  rw [hIntegralIdentity, hCostIntegral]
  calc
    _ = ((∫ z, V (t.val + 1) z - V t.val z ∂μ) +
          (11 / 2 : ℝ) * (∫ z, LIVE t z ∂μ)) +
        ((∫ z, ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld
          rate rewards C_star C_h t z ∂μ) +
          (11 / 2 : ℝ) * (∫ z, OLD t z ∂μ)) := by ring
    _ ≤ (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
            rate rewards C_star C_h t control0 +
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          (sourceInputLaw p).real (ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h t) :=
      add_le_add hLiveCombined hOldCombined
    _ = _ := by ring

/-- The original calendar pre-call energy and actual first-call energy join
with the retained weighted costs on the same sharp horizon. -/
public theorem integral_preCall_firstCall_weighted_energy_join
    (control0 : TimeControl p) :
    (∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
        rate rewards C_star C_h z ∂μ) +
      (11 / 2 : ℝ) *
        (∫ z,
          (∑ t : Fin p.T, (LIVE t z + OLD t z)) +
            ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
              rate rewards C_star C_h z ∂μ) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) * (p.T : ℝ) := by
  have hsum0 := Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) =>
    integral_preCallPotential_calendar_step_le_sourceCellMass
      rate rewards C_star C_h t control0
  have hsum :
      (∑ t : Fin p.T,
        ((∫ z, Phi (t.val + 1) z - Phi t.val z ∂μ) +
          (11 / 2 : ℝ) *
            (∫ z, (LIVE t z + OLD t z) ∂μ))) ≤
        ∑ t : Fin p.T,
          (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
            (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
              rate rewards C_star C_h t control0 +
              (sourceInputLaw p).real (ReferenceFirstCollectionOldCalendarExponentialStep.G
                rate rewards C_star C_h t)) := by
    exact hsum0
  have hCostTotal : Integrable
      (fun z : S => ∑ t : Fin p.T, (LIVE t z + OLD t z)) μ :=
    integrable_finsetSum Finset.univ fun t _ =>
      (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.integrable_retainedWeightedBacklogCost
        rate rewards C_star C_h t control0).add
      (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_readouts_regular
        rate rewards C_star C_h control0 t).2.2.2
  have hcostInt :
      (∫ z, ∑ t : Fin p.T, (LIVE t z + OLD t z) ∂μ) =
        ∑ t : Fin p.T, ∫ z, LIVE t z + OLD t z ∂μ :=
    integral_finsetSum Finset.univ fun t _ =>
      (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.integrable_retainedWeightedBacklogCost
        rate rewards C_star C_h t control0).add
      (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_readouts_regular
        rate rewards C_star C_h control0 t).2.2.2
  have hsumExpanded :
      (∑ t : Fin p.T,
        ∫ z, Phi (t.val + 1) z - Phi t.val z ∂μ) +
        (11 / 2 : ℝ) *
          (∑ t : Fin p.T, ∫ z, LIVE t z + OLD t z ∂μ) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        ∑ t : Fin p.T,
          (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
            rate rewards C_star C_h t control0 +
            (sourceInputLaw p).real (ReferenceFirstCollectionOldCalendarExponentialStep.G
              rate rewards C_star C_h t)) := by
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using hsum
  have hPreCall :
      (∫ z, Phi p.T z ∂μ) +
        (11 / 2 : ℝ) *
          (∫ z, ∑ t : Fin p.T, (LIVE t z + OLD t z) ∂μ) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        ∑ t : Fin p.T,
          (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
            rate rewards C_star C_h t control0 +
            (sourceInputLaw p).real (ReferenceFirstCollectionOldCalendarExponentialStep.G
              rate rewards C_star C_h t)) := by
    have hsum' := hsumExpanded
    rw [← ReferenceFirstCollectionPrecallWeightedBacklogBound.integral_preCallPotential_telescope
        rate rewards C_star C_h,
      ← hcostInt] at hsum'
    exact hsum'
  have hIncoming :
      (∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus
        rate rewards C_star C_h z ∂μ) ≤ (∫ z, Phi p.T z ∂μ) := by
    apply integral_mono_ae
    · exact ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus_integrable
        rate rewards C_star C_h control0
    · exact (ReferenceFirstCollectionPrecallWeightedBacklogBound.precallPotential_regular
        rate rewards C_star C_h p.T (Nat.le_refl _)).2
    · exact Filter.Eventually.of_forall fun z =>
        callVMinus_le_preCallPotential_terminal rate rewards C_star C_h z
  have hCallEnergy :=
    ReferenceFirstCollectionActualCallWeightedEnergy.integral_call_energy_and_weighted_cost_le_incoming_add_mass
      rate rewards C_star C_h control0
  have hCallEnergy' :
      (∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
        rate rewards C_star C_h z ∂μ) +
        (11 / 2 : ℝ) *
          ∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
            rate rewards C_star C_h z ∂μ ≤
      (∫ z, Phi p.T z ∂μ) +
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          (sourceInputLaw p).real (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
            rate rewards C_star C_h) :=
    hCallEnergy.trans (add_le_add hIncoming le_rfl)
  have hCallCost : Integrable
      (ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
        rate rewards C_star C_h) μ :=
    ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog_integrable
      rate rewards C_star C_h control0
  have hcombinedSeparate :
      (∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
        rate rewards C_star C_h z ∂μ) +
        (11 / 2 : ℝ) *
          (∫ z, ∑ t : Fin p.T, (LIVE t z + OLD t z) ∂μ) +
        (11 / 2 : ℝ) *
          ∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
            rate rewards C_star C_h z ∂μ ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          ∑ t : Fin p.T,
            (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
              rate rewards C_star C_h t control0 +
              (sourceInputLaw p).real (ReferenceFirstCollectionOldCalendarExponentialStep.G
                rate rewards C_star C_h t)) +
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          (sourceInputLaw p).real
            (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
              rate rewards C_star C_h) := by
    linarith only [hPreCall, hCallEnergy']
  have hmass :=
    ReferenceFirstCollectionPrecallFirstCallMassBudget.sum_sourceCellMass_oldG_add_retainedFirstCall_le_horizon
      rate rewards C_star C_h control0
  have hC : 0 ≤ CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ) := by
    have hmK : (p.m : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast p.m_lt_K.le
    have hsub : 0 ≤ 2 * (p.K : ℝ) - (p.m : ℝ) := by linarith
    dsimp [CanonicalRecordingRates.R]
    positivity
  have hmassScaled := mul_le_mul_of_nonneg_left hmass hC
  have hjoin :
      (∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
        rate rewards C_star C_h z ∂μ) +
        (11 / 2 : ℝ) *
          ((∫ z, ∑ t : Fin p.T, (LIVE t z + OLD t z) ∂μ) +
            ∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
              rate rewards C_star C_h z ∂μ) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) * (p.T : ℝ) := by
    calc
      _ = (∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
            rate rewards C_star C_h z ∂μ) +
          (11 / 2 : ℝ) *
            (∫ z, ∑ t : Fin p.T, (LIVE t z + OLD t z) ∂μ) +
          (11 / 2 : ℝ) *
            ∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
              rate rewards C_star C_h z ∂μ := by ring
      _ ≤ (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          ((∑ t : Fin p.T,
            (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
              rate rewards C_star C_h t control0 +
                (sourceInputLaw p).real (ReferenceFirstCollectionOldCalendarExponentialStep.G
                rate rewards C_star C_h t))) +
              (sourceInputLaw p).real (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
              rate rewards C_star C_h)) := by
        calc
          _ ≤ (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
              ∑ t : Fin p.T,
                (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
                  rate rewards C_star C_h t control0 +
                (sourceInputLaw p).real (ReferenceFirstCollectionOldCalendarExponentialStep.G
                    rate rewards C_star C_h t)) +
              (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
                (sourceInputLaw p).real (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
                  rate rewards C_star C_h) := hcombinedSeparate
          _ = _ := by ring
      _ ≤ _ := hmassScaled
  have hcostAdd :
      (∫ z, (∑ t : Fin p.T, (LIVE t z + OLD t z)) +
        ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
          rate rewards C_star C_h z ∂μ) =
        (∫ z, ∑ t : Fin p.T, (LIVE t z + OLD t z) ∂μ) +
          ∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
            rate rewards C_star C_h z ∂μ :=
    integral_add hCostTotal hCallCost
  simpa only [hcostAdd] using hjoin

/-- Dropping the nonnegative actual outgoing energy gives the backlog bound
for the same combined pre-call and first-invocation cost. -/
public theorem integral_preCall_firstCall_weighted_backlog_join
    (control0 : TimeControl p) :
    (11 / 2 : ℝ) *
      (∫ z,
        (∑ t : Fin p.T, (LIVE t z + OLD t z)) +
          ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
            rate rewards C_star C_h z ∂μ) ≤
    (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) * (p.T : ℝ) := by
  have hstrong := integral_preCall_firstCall_weighted_energy_join
    rate rewards C_star C_h control0
  have hout : 0 ≤
      ∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
        rate rewards C_star C_h z ∂μ :=
    integral_nonneg (fun z =>
      ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus_nonneg
        rate rewards C_star C_h z)
  linarith only [hstrong, hout]

end Bandits.Support.ReferenceFirstCollectionPrecallActualCallWeightedEnergyJoin

end
