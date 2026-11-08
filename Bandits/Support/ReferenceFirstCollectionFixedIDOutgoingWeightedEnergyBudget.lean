/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Bandits Lean Project contributors
-/
module

public import Bandits.Support.ReferenceFirstCollectionFixedIDWeightedCostBudget

import Mathlib.Tactic

/-!
# Fixed-ID pre-call and outgoing energy budget

The pre-call calendar drift and the actual outgoing energy remain localized
on the same unrestricted fixed-ID source cylinder. Their local source-cell
masses are kept datewise.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionFixedIDOutgoingWeightedEnergyBudget

open ConstructorDimensions (Parameters)
open ReferenceActivePhysicalStep (RateInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open ContinuousLearningRows (TimeControl)
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)

variable {p : Parameters}
  (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (control0 : TimeControl p)
  (ids : CompletePublicTable.IDArray p)

local notation "S" => SourceInput p
local notation "mu" => sourceInputLaw p
local notation "D" => ReferenceFixedIDSourceSection.fixedIDSourceSection ids
local notation "c" => CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)
local notation "Phi" => ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.oldPotential
  rate rewards C_star C_h
local notation "LIVE" => ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
  rate rewards C_star C_h
local notation "OLD" => ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.costOld
  rate rewards C_star C_h
local notation "VP" => ReferenceFirstCollectionCurrentQueueEnergy.VPlus rate rewards C_star C_h
local notation "VM" => ReferenceFirstCollectionCurrentQueueEnergy.VMinus rate rewards C_star C_h
local notation "G" => ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h
local notation "B" => ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog rate rewards C_star C_h
local notation "CP" => ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
  rate rewards C_star C_h
local notation "CM" => ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus
  rate rewards C_star C_h

private theorem sum_calendar_sub (b : ℕ → ℝ) (n : ℕ) :
    (∑ t : Fin n, (b (t.val + 1) - b t.val)) = b n - b 0 := by
  induction n with
  | zero => simp only [Fin.sum_univ_zero, sub_self]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    ring

include control0 in
/-- The literal actual outgoing first-call energy and first-invocation cost
are bounded by the uncollapsed pre-call source-cell mass on the fixed-ID
cylinder. -/
public theorem fixedIDOutgoingEnergyBudget :
    (∫ z in D, CP z ∂mu) +
      (11 / 2 : ℝ) *
        (∫ z in D,
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
            rate rewards C_star C_h z ∂mu) ≤
      c * ∑ t : Fin p.T,
        ((mu).real (D ∩
            (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
              ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
              ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4)) +
          (mu).real (D ∩
            ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h t) +
          ∑ u : Fin p.T, (mu).real (D ∩
            ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t)) := by
  have hPhi (n : ℕ) (hn : n ≤ p.T) :=
    (ReferenceFirstCollectionPrecallWeightedBacklogBound.precallPotential_regular
      rate rewards C_star C_h n hn).2
  have hpre (t : Fin p.T) :
      (∫ z in D, Phi (t.val + 1) z - Phi t.val z ∂mu) +
        (11 / 2 : ℝ) * (∫ z in D, LIVE t z + OLD t z ∂mu) ≤
      c * ((mu).real (D ∩
          (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
            ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
            ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4)) +
        (mu).real (D ∩ ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h t)) := by
    have hl := ReferenceFirstCollectionFixedIDWeightedCostBudget.fixedIDLiveEnergyBudget
      rate rewards C_star C_h control0 ids t
    have ho := ReferenceFirstCollectionFixedIDWeightedCostBudget.fixedIDOldEnergyBudget
      rate rewards C_star C_h control0 ids t
    have heq : (fun z : SourceInput p => Phi (t.val + 1) z - Phi t.val z) =
        fun z => (ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt
          rate rewards C_star C_h (t.val + 1) z -
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt
            rate rewards C_star C_h t.val z) +
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld
            rate rewards C_star C_h t z := by
      funext z
      exact ReferenceFirstCollectionPrecallWeightedBacklogBound.precallPotential_calendar_increment
        rate rewards C_star C_h t z
    rw [heq, integral_add (f := fun z =>
        ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt
          rate rewards C_star C_h (t.val + 1) z -
        ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt
          rate rewards C_star C_h t.val z)
      ((ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowPotentialAt
        rate rewards C_star C_h (t.val + 1)).sub
        (ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowPotentialAt
          rate rewards C_star C_h t.val)).integrableOn
      (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_readouts_regular
        rate rewards C_star C_h control0 t).2.1.integrableOn,
      integral_add
        (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.integrable_retainedWeightedBacklogCost
          rate rewards C_star C_h t control0).integrableOn
        (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_readouts_regular
          rate rewards C_star C_h control0 t).2.2.2.integrableOn]
    linarith only [hl, ho]
  have hstep (t : Fin p.T) :
      ((∫ z in D, Phi (t.val + 1) z - Phi t.val z ∂mu) +
        ∑ u : Fin p.T, ∫ z in D, VP u t z - VM u t z ∂mu) +
      (11 / 2 : ℝ) * ((∫ z in D, LIVE t z + OLD t z ∂mu) +
        ∑ u : Fin p.T, ∫ z in D, (G u t).indicator (B u t) z ∂mu) ≤
      c * ((mu).real (D ∩
          (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
            ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
            ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4)) +
        (mu).real (D ∩ ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h t) +
        ∑ u : Fin p.T, (mu).real
          (D ∩ ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t)) := by
    have hc := Finset.sum_le_sum fun (u : Fin p.T) (_ : u ∈ Finset.univ) =>
      ReferenceFirstCollectionFixedIDWeightedCostBudget.fixedIDCurrentEnergyBudget
        rate rewards C_star C_h control0 ids u t
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hc
    linarith only [hpre t, hc]
  have hsum := Finset.sum_le_sum fun (t : Fin p.T) (_ : t ∈ Finset.univ) => hstep t
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have htel :
      (∑ t : Fin p.T, ∫ z in D, Phi (t.val + 1) z - Phi t.val z ∂mu) =
        ∫ z in D, Phi p.T z ∂mu := by
    rw [← integral_finsetSum Finset.univ
      (f := fun (t : Fin p.T) z => Phi (t.val + 1) z - Phi t.val z)
      (fun t _ => ((hPhi _ (Nat.succ_le_of_lt t.isLt)).sub
        (hPhi _ t.isLt.le)).integrableOn)]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [sum_calendar_sub (fun n => Phi n z) p.T,
      ReferenceFirstCollectionPrecallWeightedBacklogBound.precallPotential_zero
        rate rewards C_star C_h z,
      sub_zero]
  have hP (u t : Fin p.T) := ReferenceFirstCollectionCurrentQueueEnergy.VPlus_integrable
    rate rewards C_star C_h control0 u t
  have hM (u t : Fin p.T) := ReferenceFirstCollectionCurrentQueueEnergy.VMinus_integrable
    rate rewards C_star C_h control0 u t
  have hcur :
      (∑ t : Fin p.T, ∑ u : Fin p.T,
        ∫ z in D, VP u t z - VM u t z ∂mu) =
      ∫ z in D, CP z - CM z ∂mu := by
    simp_rw [← integral_finsetSum Finset.univ
      (f := fun (u : Fin p.T) z => VP u _ z - VM u _ z)
      (fun u _ => ((hP u _).sub (hM u _)).integrableOn)]
    rw [← integral_finsetSum Finset.univ
      (f := fun (t : Fin p.T) z => ∑ u : Fin p.T, (VP u t z - VM u t z))
      (fun t _ => integrable_finsetSum Finset.univ
        (fun u _ => ((hP u t).sub (hM u t)).integrableOn))]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [Finset.sum_comm]
    simp only [ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus,
      ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus,
      Finset.sum_sub_distrib]
  have hB (u t : Fin p.T) : Integrable ((G u t).indicator (B u t)) mu :=
    (ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog_integrable
      rate rewards C_star C_h control0 u t).indicator
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
        (t.val + 1) _ (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
          rate rewards C_star C_h control0 u t))
  have hPastInt : Integrable (fun z : SourceInput p =>
      ∑ t : Fin p.T, (LIVE t z + OLD t z)) mu := by
    apply integrable_finsetSum
    intro t ht
    exact (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.integrable_retainedWeightedBacklogCost
        rate rewards C_star C_h t control0).add
      (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_readouts_regular
        rate rewards C_star C_h control0 t).2.2.2
  have hCurrentInt : Integrable (fun z : SourceInput p =>
      ∑ t : Fin p.T, ∑ u : Fin p.T, (G u t).indicator (B u t) z) mu := by
    apply integrable_finsetSum
    intro t ht
    apply integrable_finsetSum
    intro u hu
    exact hB u t
  have hPastIntegral :
      (∑ t : Fin p.T, ∫ z in D, LIVE t z + OLD t z ∂mu) =
        ∫ z in D, (∑ t : Fin p.T, (LIVE t z + OLD t z)) ∂mu := by
    exact (integral_finsetSum Finset.univ
      (f := fun (t : Fin p.T) z => LIVE t z + OLD t z)
      (fun t _ =>
        ((ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.integrable_retainedWeightedBacklogCost
          rate rewards C_star C_h t control0).add
        (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_readouts_regular
          rate rewards C_star C_h control0 t).2.2.2).integrableOn)).symm
  have hCurrentIntegral :
      (∑ t : Fin p.T, ∑ u : Fin p.T,
        ∫ z in D, (G u t).indicator (B u t) z ∂mu) =
        ∫ z in D, (∑ t : Fin p.T, ∑ u : Fin p.T,
          (G u t).indicator (B u t) z) ∂mu := by
    calc
      _ = ∑ t : Fin p.T, ∫ z in D,
          (∑ u : Fin p.T, (G u t).indicator (B u t) z) ∂mu := by
        apply Finset.sum_congr rfl
        intro t ht
        exact (integral_finsetSum Finset.univ
          (f := fun (u : Fin p.T) z => (G u t).indicator (B u t) z)
          (fun u _ => (hB u t).integrableOn)).symm
      _ = ∫ z in D, (∑ t : Fin p.T, ∑ u : Fin p.T,
          (G u t).indicator (B u t) z) ∂mu :=
        (integral_finsetSum Finset.univ
          (f := fun (t : Fin p.T) z =>
            ∑ u : Fin p.T, (G u t).indicator (B u t) z)
          (fun t _ =>
            (integrable_finsetSum Finset.univ (fun u _ => hB u t)).integrableOn)).symm
  have hcost :
      (∑ t : Fin p.T, ∫ z in D, LIVE t z + OLD t z ∂mu) +
        (∑ t : Fin p.T, ∑ u : Fin p.T,
          ∫ z in D, (G u t).indicator (B u t) z ∂mu) =
      ∫ z in D,
        ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
          rate rewards C_star C_h z ∂mu := by
    calc
      _ = (∫ z in D, (∑ t : Fin p.T, (LIVE t z + OLD t z)) ∂mu) +
          ∫ z in D, (∑ t : Fin p.T, ∑ u : Fin p.T,
            (G u t).indicator (B u t) z) ∂mu := by
        rw [hPastIntegral, hCurrentIntegral]
      _ = ∫ z in D,
          (∑ t : Fin p.T, (LIVE t z + OLD t z)) +
            (∑ t : Fin p.T, ∑ u : Fin p.T, (G u t).indicator (B u t) z) ∂mu :=
        (integral_add hPastInt.integrableOn hCurrentInt.integrableOn).symm
      _ = ∫ z in D,
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
            rate rewards C_star C_h z ∂mu := by
        apply setIntegral_congr_fun
          (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids)
        intro z hz
        rw [ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationCost_eq_energyIntegrand
          rate rewards C_star C_h z]
        dsimp only [ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog]
        congr 1
        rw [Finset.sum_comm]
  rw [htel, hcur, hcost] at hsum
  have hCP := ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus_integrable
    rate rewards C_star C_h control0
  have hCM := ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus_integrable
    rate rewards C_star C_h control0
  have hIncoming :
      (∫ z in D, CM z ∂mu) ≤ (∫ z in D, Phi p.T z ∂mu) := by
    apply setIntegral_mono_on hCM.integrableOn (hPhi _ le_rfl).integrableOn
      (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids)
    intro z hz
    exact ReferenceFirstCollectionPrecallActualCallWeightedEnergyJoin.callVMinus_le_preCallPotential_terminal
      rate rewards C_star C_h z
  have hmass :
      (∑ t : Fin p.T,
        ((mu).real (D ∩
            (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
              ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
              ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4)) +
          (mu).real (D ∩
            ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h t) +
          ∑ u : Fin p.T, (mu).real (D ∩
            ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t))) =
        (∑ t : Fin p.T, (mu).real (D ∩
          (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
            ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
            ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4))) +
        (∑ t : Fin p.T, (mu).real (D ∩
          ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h t)) +
        (∑ t : Fin p.T, ∑ u : Fin p.T, (mu).real (D ∩
          ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t)) := by
    simp only [Finset.sum_add_distrib]
  rw [hmass]
  rw [integral_sub hCP.integrableOn hCM.integrableOn] at hsum
  linarith only [hIncoming, hsum]

end Bandits.Support.ReferenceFirstCollectionFixedIDOutgoingWeightedEnergyBudget

end
