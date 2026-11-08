/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCurrentConditionalWeightedDrift
public import Bandits.Support.ReferenceFirstCollectionActualCallExponentialQueueEstimate

import Mathlib.Tactic

/-!
# Actual first collection-call weighted queue energy

The literal finite sums below join the disjoint cutoff/date cells of one
original sampler invocation. The outgoing queue energy remains visible at the
first update that detects overflow; only the retained weighted cost is gated.

Sources: `04_slow_fast_learner.tex:140-188,245-318`,
`05_binary_transport.tex:352-431`, and `06_interruptions.tex:355-426` under
`sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open Bandits.Support.ActualInitializationPhysicalStep (GridRewardTable)
open Bandits.Support.ContinuousLearningRows (TimeControl)
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration (sourcePrefixFiltration)
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionActualCallWeightedEnergy

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)

local notation "q" => ReferenceFirstLaunchNumericalCell.queueParameters rate

local instance sourceInputMeasurableSpace : MeasurableSpace (SourceInput p) :=
  @ReferenceFirstCollectionCurrentQueueEnergy.sourceInputMeasurableSpace p

local notation "mu" => sourceInputLaw p

/-- Literal incoming quadratic-energy observations, summed over cutoff/date
cells of the original source space. -/
public def callVMinus (rate0 : ReferenceActivePhysicalStep.RateInput p)
    (rewards0 : GridRewardTable p) (C_star0 C_h0 : ℝ) : SourceInput p → ℝ :=
  fun z => ∑ u : Fin p.T, ∑ t : Fin p.T,
    ReferenceFirstCollectionCurrentQueueEnergy.VMinus
      rate0 rewards0 C_star0 C_h0 u t z

/-- Literal outgoing quadratic-energy observations, summed over cutoff/date
cells of the original source space. -/
public def callVPlus (rate0 : ReferenceActivePhysicalStep.RateInput p)
    (rewards0 : GridRewardTable p) (C_star0 C_h0 : ℝ) : SourceInput p → ℝ :=
  fun z => ∑ u : Fin p.T, ∑ t : Fin p.T,
    ReferenceFirstCollectionCurrentQueueEnergy.VPlus
      rate0 rewards0 C_star0 C_h0 u t z

/-- Literal retained weighted-backlog observations, with the same original
strict-past gate on every cutoff/date cell. -/
public def callWeightedBacklog
    (rate0 : ReferenceActivePhysicalStep.RateInput p)
    (rewards0 : GridRewardTable p) (C_star0 C_h0 : ℝ) : SourceInput p → ℝ :=
  fun z => ∑ u : Fin p.T, ∑ t : Fin p.T,
    (ReferenceFirstCollectionCurrentRetainedGate.G
      rate0 rewards0 C_star0 C_h0 u t).indicator
      (ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog
        rate0 rewards0 C_star0 C_h0 u t) z

private theorem G_measurable_ambient (control0 : TimeControl p)
    (u t : Fin p.T) : MeasurableSet (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t) := by
  exact (sourcePrefixFiltration control0).le' (t.val + 1) _
    (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
      rate rewards C_star C_h control0 u t)

theorem callVMinus_measurable (control0 : TimeControl p) :
    Measurable (callVMinus rate rewards C_star C_h) := by
  apply Finset.measurable_fun_sum
  intro u hu
  apply Finset.measurable_fun_sum
  intro t ht
  exact Measurable.mono
    (ReferenceFirstCollectionCurrentQueueEnergy.measurable_VMinus
      rate rewards C_star C_h control0 u t)
    ((sourcePrefixFiltration control0).le' (t.val + 1)) le_rfl

theorem callVPlus_measurable (control0 : TimeControl p) :
    Measurable (callVPlus rate rewards C_star C_h) := by
  apply Finset.measurable_fun_sum
  intro u hu
  apply Finset.measurable_fun_sum
  intro t ht
  exact ReferenceFirstCollectionCurrentQueueEnergy.measurable_VPlus
    rate rewards C_star C_h control0 u t

theorem callWeightedBacklog_measurable (control0 : TimeControl p) :
    Measurable (callWeightedBacklog rate rewards C_star C_h) := by
  apply Finset.measurable_fun_sum
  intro u hu
  apply Finset.measurable_fun_sum
  intro t ht
  exact (Measurable.mono
    (ReferenceFirstCollectionCurrentQueueEnergy.measurable_weightedBacklog
      rate rewards C_star C_h control0 u t)
    ((sourcePrefixFiltration control0).le' (t.val + 1)) le_rfl).indicator
      (G_measurable_ambient rate rewards C_star C_h control0 u t)

theorem callVMinus_integrable (control0 : TimeControl p) :
    Integrable (callVMinus rate rewards C_star C_h) mu := by
  apply integrable_finsetSum
  intro u hu
  apply integrable_finsetSum
  intro t ht
  exact ReferenceFirstCollectionCurrentQueueEnergy.VMinus_integrable
    rate rewards C_star C_h control0 u t

theorem callVPlus_integrable (control0 : TimeControl p) :
    Integrable (callVPlus rate rewards C_star C_h) mu := by
  apply integrable_finsetSum
  intro u hu
  apply integrable_finsetSum
  intro t ht
  exact ReferenceFirstCollectionCurrentQueueEnergy.VPlus_integrable
    rate rewards C_star C_h control0 u t

theorem callWeightedBacklog_integrable (control0 : TimeControl p) :
    Integrable (callWeightedBacklog rate rewards C_star C_h) mu := by
  apply integrable_finsetSum
  intro u hu
  apply integrable_finsetSum
  intro t ht
  exact (ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog_integrable
    rate rewards C_star C_h control0 u t).indicator
      (G_measurable_ambient rate rewards C_star C_h control0 u t)

theorem callVMinus_nonneg (z : SourceInput p) :
    0 ≤ callVMinus rate rewards C_star C_h z := by
  apply Finset.sum_nonneg
  intro u hu
  apply Finset.sum_nonneg
  intro t ht
  exact (ReferenceFirstCollectionCurrentQueueEnergy.VMinus_bounds
    rate rewards C_star C_h u t z).1

theorem callVPlus_nonneg (z : SourceInput p) :
    0 ≤ callVPlus rate rewards C_star C_h z := by
  apply Finset.sum_nonneg
  intro u hu
  apply Finset.sum_nonneg
  intro t ht
  exact (ReferenceFirstCollectionCurrentQueueEnergy.VPlus_bounds
    rate rewards C_star C_h u t z).1

theorem callWeightedBacklog_nonneg (z : SourceInput p) :
    0 ≤ callWeightedBacklog rate rewards C_star C_h z := by
  apply Finset.sum_nonneg
  intro u hu
  apply Finset.sum_nonneg
  intro t ht
  by_cases hg : z ∈ ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t
  · rw [Set.indicator_of_mem hg]
    exact (ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog_bounds
      rate rewards C_star C_h u t z).1
  · simp [Set.indicator_of_notMem hg]

private theorem integral_callVMinus_eq_sum (control0 : TimeControl p) :
    (∫ z, callVMinus rate rewards C_star C_h z ∂mu) =
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z, ReferenceFirstCollectionCurrentQueueEnergy.VMinus
          rate rewards C_star C_h u t z ∂mu := by
  unfold callVMinus
  rw [integral_finsetSum Finset.univ (fun u hu =>
    integrable_finsetSum Finset.univ (fun t ht =>
      ReferenceFirstCollectionCurrentQueueEnergy.VMinus_integrable
        rate rewards C_star C_h control0 u t))]
  apply Finset.sum_congr rfl
  intro u hu
  rw [integral_finsetSum Finset.univ (fun t ht =>
    ReferenceFirstCollectionCurrentQueueEnergy.VMinus_integrable
      rate rewards C_star C_h control0 u t)]

private theorem integral_callVPlus_eq_sum (control0 : TimeControl p) :
    (∫ z, callVPlus rate rewards C_star C_h z ∂mu) =
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z, ReferenceFirstCollectionCurrentQueueEnergy.VPlus
          rate rewards C_star C_h u t z ∂mu := by
  unfold callVPlus
  rw [integral_finsetSum Finset.univ (fun u hu =>
    integrable_finsetSum Finset.univ (fun t ht =>
      ReferenceFirstCollectionCurrentQueueEnergy.VPlus_integrable
        rate rewards C_star C_h control0 u t))]
  apply Finset.sum_congr rfl
  intro u hu
  rw [integral_finsetSum Finset.univ (fun t ht =>
    ReferenceFirstCollectionCurrentQueueEnergy.VPlus_integrable
      rate rewards C_star C_h control0 u t)]

private theorem integral_callWeightedBacklog_eq_sum (control0 : TimeControl p) :
    (∫ z, callWeightedBacklog rate rewards C_star C_h z ∂mu) =
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z, (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t).indicator
          (ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog
            rate rewards C_star C_h u t) z ∂mu := by
  unfold callWeightedBacklog
  rw [integral_finsetSum Finset.univ (fun u hu =>
    integrable_finsetSum Finset.univ (fun t ht =>
      (ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog_integrable
        rate rewards C_star C_h control0 u t).indicator
        (G_measurable_ambient rate rewards C_star C_h control0 u t)))]
  apply Finset.sum_congr rfl
  intro u hu
  rw [integral_finsetSum Finset.univ (fun t ht =>
    (ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog_integrable
      rate rewards C_star C_h control0 u t).indicator
      (G_measurable_ambient rate rewards C_star C_h control0 u t))]

private theorem firstCell_unique_pair (z : SourceInput p)
    (u₁ u₂ t₁ t₂ : Fin p.T)
    (h₁ : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u₁ t₁)
    (h₂ : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u₂ t₂) : u₁ = u₂ ∧ t₁ = t₂ := by
  change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) = some (u₁, t₁) at h₁
  change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) = some (u₂, t₂) at h₂
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none => simp [hcall] at h₁
  | some call =>
      simp [hcall] at h₁ h₂
      exact ⟨h₁.1.symm.trans h₂.1, h₁.2.symm.trans h₂.2⟩

private theorem finite_pair_sum_eq_selected
    (P : Fin p.T → Fin p.T → Prop)
    (f : Fin p.T → Fin p.T → ℝ)
    (hunique : ∀ u₁ u₂ t₁ t₂, P u₁ t₁ → P u₂ t₂ →
      u₁ = u₂ ∧ t₁ = t₂)
    (hzero : ∀ u t, ¬ P u t → f u t = 0)
    (u t : Fin p.T) (hP : P u t) :
    (∑ u₀ : Fin p.T, ∑ t₀ : Fin p.T, f u₀ t₀) = f u t := by
  have hinner (u₀ : Fin p.T) :
      (∑ t₀ : Fin p.T, f u₀ t₀) =
        if u₀ = u then f u t else 0 := by
    by_cases hu : u₀ = u
    · subst u₀
      rw [Finset.sum_eq_single t]
      · simp
      · intro t₀ ht₀ htt
        apply hzero u t₀
        intro hp
        exact htt (hunique u u t t₀ hP hp).2.symm
      · intro hmem
        exact (hmem (Finset.mem_univ t)).elim
    · have hzeroAll : ∀ t₀ : Fin p.T, f u₀ t₀ = 0 := by
        intro t₀
        apply hzero u₀ t₀
        intro hp
        exact hu (hunique u u₀ t t₀ hP hp).1.symm
      simp_rw [hzeroAll]
      simp [hu]
  rw [show (∑ u₀ : Fin p.T, ∑ t₀ : Fin p.T, f u₀ t₀) =
      ∑ u₀ : Fin p.T, (if u₀ = u then f u t else 0) by
        apply Finset.sum_congr rfl
        intro u₀ hu
        exact hinner u₀]
  rw [Finset.sum_ite_eq' Finset.univ u]
  simp

private theorem VMinus_zero_of_not_firstCell (z : SourceInput p)
    (u t : Fin p.T)
    (hz : z ∉ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t) :
    ReferenceFirstCollectionCurrentQueueEnergy.VMinus
      rate rewards C_star C_h u t z = 0 := by
  have htheta : ∀ a,
      ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
        rate rewards C_star C_h u t a z = 0 := by
    intro a
    simp [ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus, hz]
  simp [ReferenceFirstCollectionCurrentQueueEnergy.VMinus, htheta]

private theorem VPlus_zero_of_not_firstCell (z : SourceInput p)
    (u t : Fin p.T)
    (hz : z ∉ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t) :
    ReferenceFirstCollectionCurrentQueueEnergy.VPlus
      rate rewards C_star C_h u t z = 0 := by
  have htheta : ∀ a,
      ReferenceFirstCollectionCurrentQueueEnergy.thetaPlus
        rate rewards C_star C_h u t a z = 0 := by
    intro a
    simp [ReferenceFirstCollectionCurrentQueueEnergy.thetaPlus, hz]
  simp [ReferenceFirstCollectionCurrentQueueEnergy.VPlus, htheta]

private theorem retainedWeighted_zero_of_not_G (z : SourceInput p)
    (u t : Fin p.T) (hz : z ∉ ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t) :
    (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t).indicator
      (ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog
        rate rewards C_star C_h u t) z = 0 := by
  simp [Set.indicator_of_notMem hz]

private theorem G_unique_pair (z : SourceInput p)
    (u₁ u₂ t₁ t₂ : Fin p.T)
    (h₁ : z ∈ ReferenceFirstCollectionCurrentRetainedGate.G
      rate rewards C_star C_h u₁ t₁)
    (h₂ : z ∈ ReferenceFirstCollectionCurrentRetainedGate.G
      rate rewards C_star C_h u₂ t₂) :
    u₁ = u₂ ∧ t₁ = t₂ :=
  firstCell_unique_pair rate rewards C_star C_h z u₁ u₂ t₁ t₂ h₁.1 h₂.1

private theorem not_G_anywhere_of_firstCell_not_G (z : SourceInput p)
    (u t u₀ t₀ : Fin p.T)
    (hE : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t)
    (hnot : z ∉ ReferenceFirstCollectionCurrentRetainedGate.G
      rate rewards C_star C_h u t) :
    z ∉ ReferenceFirstCollectionCurrentRetainedGate.G
      rate rewards C_star C_h u₀ t₀ := by
  intro hG
  obtain ⟨hu, ht⟩ := firstCell_unique_pair rate rewards C_star C_h z
    u u₀ t t₀ hE hG.1
  subst u₀
  subst t₀
  exact hnot hG

private theorem not_firstCell_of_no_call (z : SourceInput p)
    (hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z = none) (u t : Fin p.T) :
    z ∉ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t := by
  change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
    rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) ≠ some (u, t)
  simp [hcall]

private theorem firstCell_of_firstCollectionCall (z : SourceInput p)
    (u t : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
    (hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z = some (u, (t, theta))) :
    z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t := by
  change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) = some (u, t)
  rw [hcall]
  rfl

/-- The finite scalar sums select the original actual invocation's cell. The
retained cost keeps the same strict-past gate used by the one-cell drift. -/
public theorem callObservations_eq_actual_cell_of_firstCollectionCall
    (z : SourceInput p) (u t : Fin p.T)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z = some (u, (t, theta))) :
    callVMinus rate rewards C_star C_h z =
        ReferenceFirstCollectionCurrentQueueEnergy.VMinus
          rate rewards C_star C_h u t z ∧
      callVPlus rate rewards C_star C_h z =
        ReferenceFirstCollectionCurrentQueueEnergy.VPlus
          rate rewards C_star C_h u t z ∧
      callWeightedBacklog rate rewards C_star C_h z =
        (ReferenceFirstCollectionCurrentRetainedGate.G
          rate rewards C_star C_h u t).indicator
          (ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog
            rate rewards C_star C_h u t) z := by
  have hE := firstCell_of_firstCollectionCall
    rate rewards C_star C_h z u t theta hcall
  have hminus := finite_pair_sum_eq_selected
    (fun u₀ t₀ => z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u₀ t₀)
    (fun u₀ t₀ => ReferenceFirstCollectionCurrentQueueEnergy.VMinus
      rate rewards C_star C_h u₀ t₀ z)
    (fun u₁ u₂ t₁ t₂ h₁ h₂ =>
      firstCell_unique_pair rate rewards C_star C_h z u₁ u₂ t₁ t₂ h₁ h₂)
    (fun u₀ t₀ hnot => VMinus_zero_of_not_firstCell
      rate rewards C_star C_h z u₀ t₀ hnot)
    u t hE
  have hplus := finite_pair_sum_eq_selected
    (fun u₀ t₀ => z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u₀ t₀)
    (fun u₀ t₀ => ReferenceFirstCollectionCurrentQueueEnergy.VPlus
      rate rewards C_star C_h u₀ t₀ z)
    (fun u₁ u₂ t₁ t₂ h₁ h₂ =>
      firstCell_unique_pair rate rewards C_star C_h z u₁ u₂ t₁ t₂ h₁ h₂)
    (fun u₀ t₀ hnot => VPlus_zero_of_not_firstCell
      rate rewards C_star C_h z u₀ t₀ hnot)
    u t hE
  have hcost : callWeightedBacklog rate rewards C_star C_h z =
      (ReferenceFirstCollectionCurrentRetainedGate.G
        rate rewards C_star C_h u t).indicator
        (ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog
          rate rewards C_star C_h u t) z := by
    by_cases hg : z ∈ ReferenceFirstCollectionCurrentRetainedGate.G
        rate rewards C_star C_h u t
    · exact finite_pair_sum_eq_selected
        (fun u₀ t₀ => z ∈ ReferenceFirstCollectionCurrentRetainedGate.G
          rate rewards C_star C_h u₀ t₀)
        (fun u₀ t₀ => (ReferenceFirstCollectionCurrentRetainedGate.G
          rate rewards C_star C_h u₀ t₀).indicator
          (ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog
            rate rewards C_star C_h u₀ t₀) z)
        (fun u₁ u₂ t₁ t₂ h₁ h₂ =>
          G_unique_pair rate rewards C_star C_h z u₁ u₂ t₁ t₂ h₁ h₂)
        (fun u₀ t₀ hnot => retainedWeighted_zero_of_not_G
          rate rewards C_star C_h z u₀ t₀ hnot)
        u t hg
    · have hnotG (u₀ t₀ : Fin p.T) :
          z ∉ ReferenceFirstCollectionCurrentRetainedGate.G
            rate rewards C_star C_h u₀ t₀ :=
        not_G_anywhere_of_firstCell_not_G
          rate rewards C_star C_h z u t u₀ t₀ hE hg
      rw [retainedWeighted_zero_of_not_G
        rate rewards C_star C_h z u t hg]
      unfold callWeightedBacklog
      apply Finset.sum_eq_zero
      intro u₀ hu
      apply Finset.sum_eq_zero
      intro t₀ ht
      exact retainedWeighted_zero_of_not_G
        rate rewards C_star C_h z u₀ t₀ (hnotG u₀ t₀)
  exact ⟨by simpa [callVMinus] using hminus,
    by simpa [callVPlus] using hplus, hcost⟩

/-- With no actual sampler invocation, all three scalar observations are zero.
This is only the literal empty finite sum, not an operational state default. -/
public theorem callObservations_eq_zero_of_firstCollectionCall_none
    (z : SourceInput p)
    (hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z = none) :
    callVMinus rate rewards C_star C_h z = 0 ∧
      callVPlus rate rewards C_star C_h z = 0 ∧
      callWeightedBacklog rate rewards C_star C_h z = 0 := by
  have hminus : callVMinus rate rewards C_star C_h z = 0 := by
    unfold callVMinus
    apply Finset.sum_eq_zero
    intro u hu
    apply Finset.sum_eq_zero
    intro t ht
    exact VMinus_zero_of_not_firstCell rate rewards C_star C_h z u t
      (not_firstCell_of_no_call rate rewards C_star C_h z hcall u t)
  have hplus : callVPlus rate rewards C_star C_h z = 0 := by
    unfold callVPlus
    apply Finset.sum_eq_zero
    intro u hu
    apply Finset.sum_eq_zero
    intro t ht
    exact VPlus_zero_of_not_firstCell rate rewards C_star C_h z u t
      (not_firstCell_of_no_call rate rewards C_star C_h z hcall u t)
  have hcost : callWeightedBacklog rate rewards C_star C_h z = 0 := by
    unfold callWeightedBacklog
    apply Finset.sum_eq_zero
    intro u hu
    apply Finset.sum_eq_zero
    intro t ht
    apply retainedWeighted_zero_of_not_G
    intro hg
    exact not_firstCell_of_no_call rate rewards C_star C_h z hcall u t hg.1
  exact ⟨hminus, hplus, hcost⟩

/-- At an actual but unretained call, both energy observations remain the
actual incoming and outgoing energies, while the gated retained cost is zero. -/
public theorem callObservations_eq_actual_cell_of_unretained_firstCollectionCall
    (z : SourceInput p) (u t : Fin p.T)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z = some (u, (t, theta)))
    (hnotG : z ∉ ReferenceFirstCollectionCurrentRetainedGate.G
      rate rewards C_star C_h u t) :
    callVMinus rate rewards C_star C_h z =
        ReferenceFirstCollectionCurrentQueueEnergy.VMinus
          rate rewards C_star C_h u t z ∧
      callVPlus rate rewards C_star C_h z =
        ReferenceFirstCollectionCurrentQueueEnergy.VPlus
          rate rewards C_star C_h u t z ∧
      callWeightedBacklog rate rewards C_star C_h z = 0 := by
  obtain ⟨hminus, hplus, hcost⟩ := callObservations_eq_actual_cell_of_firstCollectionCall
    rate rewards C_star C_h z u t theta hcall
  rw [hcost, Set.indicator_of_notMem hnotG]
  exact ⟨hminus, hplus, rfl⟩

/-- The actual call's incoming and outgoing energies are the energies of the
same original queue run and its current step. The queue readouts and product
set marginals use the shared `L,c` witnesses from the admitted readout and
score-marginal producers. -/
public theorem callEnergy_actual_run_readouts_of_firstCollectionCall
    (z : SourceInput p) (u t : Fin p.T)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z = some (u, (t, theta))) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (c : RecordedQueueRun.RoundInput p.K),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells?
        rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell
        rate rewards C_star C_h t z = some c ∧
      c.enabled = true ∧
      ReferenceFirstCollectionCurrentQueueReadout.before?
        rate rewards C_star C_h t z = some
          (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.run q L)) ∧
      ReferenceFirstCollectionCurrentQueueReadout.after?
        rate rewards C_star C_h t z = some
          (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.step q (RecordedQueueRun.run q L) c)) ∧
      (∀ a : Fin p.K,
        ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
          rate rewards C_star C_h u t a z =
          ProductSetLaw.theta p.m
            (RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L)) a) ∧
      (∀ a : Fin p.K,
        ReferenceFirstCollectionCurrentQueueEnergy.thetaPlus
          rate rewards C_star C_h u t a z =
          ProductSetLaw.theta p.m
            (RecordedQueueRun.scoreWeight q
              (RecordedQueueRun.step q (RecordedQueueRun.run q L) c)) a) ∧
      callVMinus rate rewards C_star C_h z =
        ∑ a : Fin p.K,
          ProductSetLaw.theta p.m
            (RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L)) a *
            ((((RecordedQueueRun.run q L).registers a).2 : ℝ) /
              ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) ^ 2 ∧
      callVPlus rate rewards C_star C_h z =
        ∑ a : Fin p.K,
          ProductSetLaw.theta p.m
            (RecordedQueueRun.scoreWeight q
              (RecordedQueueRun.step q (RecordedQueueRun.run q L) c)) a *
            ((((RecordedQueueRun.step q (RecordedQueueRun.run q L) c).registers a).2 : ℝ) /
              ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) ^ 2 ∧
      callWeightedBacklog rate rewards C_star C_h z =
        (ReferenceFirstCollectionCurrentRetainedGate.G
          rate rewards C_star C_h u t).indicator
          (ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog
            rate rewards C_star C_h u t) z := by
  have hE := firstCell_of_firstCollectionCall
    rate rewards C_star C_h z u t theta hcall
  let arm0 : Fin p.K := ⟨0, ConstructorDimensions.K_pos p⟩
  obtain ⟨L, c, hL, hc, henabled, hbefore, hafter, _, _, _, _⟩ :=
    ReferenceFirstCollectionCurrentQueueReadout.firstCell_actual_queue_readouts
      rate rewards C_star C_h u t arm0 z hE
  obtain ⟨Lscore, cscore, hLscore, hcscore, _, _, _,
      hthetaMinus, hthetaPlus⟩ :=
    ReferenceFirstCollectionCurrentQueueEnergy.firstCell_actual_score_marginals
      rate rewards C_star C_h u t z hE
  have hLsame : Lscore = L := Option.some.inj (hLscore.symm.trans hL)
  have hcsame : cscore = c := Option.some.inj (hcscore.symm.trans hc)
  subst Lscore
  subst cscore
  have hthetaMinus' (a : Fin p.K) :
      ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
          rate rewards C_star C_h u t a z =
        ProductSetLaw.theta p.m
          (RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L)) a :=
    congrFun hthetaMinus a
  have hthetaPlus' (a : Fin p.K) :
      ReferenceFirstCollectionCurrentQueueEnergy.thetaPlus
          rate rewards C_star C_h u t a z =
        ProductSetLaw.theta p.m
          (RecordedQueueRun.scoreWeight q
            (RecordedQueueRun.step q (RecordedQueueRun.run q L) c)) a :=
    congrFun hthetaPlus a
  have hbMinus (a : Fin p.K) :
      ReferenceFirstCollectionCurrentQueueReadout.bMinus
        rate rewards C_star C_h u t a z =
        ((((RecordedQueueRun.run q L).registers a).2 : ℝ) /
          ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) := by
    simp [ReferenceFirstCollectionCurrentQueueReadout.bMinus,
      Set.indicator_of_mem hE, hbefore,
      ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog,
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout]
  have hbPlus (a : Fin p.K) :
      ReferenceFirstCollectionCurrentQueueReadout.bPlus
        rate rewards C_star C_h u t a z =
        ((((RecordedQueueRun.step q (RecordedQueueRun.run q L) c).registers a).2 : ℝ) /
          ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) := by
    simp [ReferenceFirstCollectionCurrentQueueReadout.bPlus,
      Set.indicator_of_mem hE, hafter,
      ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog,
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout]
  have hVMinus :
      ReferenceFirstCollectionCurrentQueueEnergy.VMinus
        rate rewards C_star C_h u t z =
        ∑ a : Fin p.K,
          ProductSetLaw.theta p.m
            (RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L)) a *
            ((((RecordedQueueRun.run q L).registers a).2 : ℝ) /
              ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) ^ 2 := by
    unfold ReferenceFirstCollectionCurrentQueueEnergy.VMinus
    apply Finset.sum_congr rfl
    intro a ha
    rw [hthetaMinus' a, hbMinus a]
  have hVPlus :
      ReferenceFirstCollectionCurrentQueueEnergy.VPlus
        rate rewards C_star C_h u t z =
        ∑ a : Fin p.K,
          ProductSetLaw.theta p.m
            (RecordedQueueRun.scoreWeight q
              (RecordedQueueRun.step q (RecordedQueueRun.run q L) c)) a *
            ((((RecordedQueueRun.step q (RecordedQueueRun.run q L) c).registers a).2 : ℝ) /
              ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) ^ 2 := by
    unfold ReferenceFirstCollectionCurrentQueueEnergy.VPlus
    apply Finset.sum_congr rfl
    intro a ha
    rw [hthetaPlus' a, hbPlus a]
  obtain ⟨hcallMinus, hcallPlus, hcallCost⟩ :=
    callObservations_eq_actual_cell_of_firstCollectionCall
      rate rewards C_star C_h z u t theta hcall
  refine ⟨L, c, hL, hc, henabled, hbefore, hafter, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun a => hthetaMinus' a
  · exact fun a => hthetaPlus' a
  · exact hcallMinus.trans hVMinus
  · exact hcallPlus.trans hVPlus
  · exact hcallCost

private theorem mul_pair_sum
    (f : Fin p.T → Fin p.T → ℝ) (c : ℝ) :
    c * (∑ u : Fin p.T, ∑ t : Fin p.T, f u t) =
      ∑ u : Fin p.T, ∑ t : Fin p.T, c * f u t := by
  calc
    _ = ∑ u : Fin p.T, c * (∑ t : Fin p.T, f u t) := by
      rw [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mul_sum]

private theorem pair_sum_add
    (f g : Fin p.T → Fin p.T → ℝ) (c : ℝ) :
    (∑ u : Fin p.T, ∑ t : Fin p.T, f u t) +
        ∑ u : Fin p.T, ∑ t : Fin p.T, c * g u t =
      ∑ u : Fin p.T, ∑ t : Fin p.T, (f u t + c * g u t) := by
  calc
    _ = ∑ u : Fin p.T,
          ((∑ t : Fin p.T, f u t) + ∑ t : Fin p.T, c * g u t) := by
      rw [← Finset.sum_add_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [← Finset.sum_add_distrib]

private theorem C_nonneg :
    0 ≤ CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ) := by
  have hm : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
  have hmk : (p.m : ℝ) < (p.K : ℝ) := by exact_mod_cast p.m_lt_K
  have hfactor : 0 < 2 * (p.K : ℝ) - (p.m : ℝ) := by linarith
  unfold CanonicalRecordingRates.R
  positivity

/-- Main one-invocation energy/backlog inequality under the original source
law. The mass is exactly that of the retained first-call cells. -/
public theorem integral_call_energy_weighted_cost (control0 : TimeControl p) :
    (∫ z, callVPlus rate rewards C_star C_h z -
        callVMinus rate rewards C_star C_h z ∂mu) +
      (11 / 2 : ℝ) *
        ∫ z, callWeightedBacklog rate rewards C_star C_h z ∂mu ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (sourceInputLaw p).real (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
          rate rewards C_star C_h) := by
  have hplus := integral_callVPlus_eq_sum rate rewards C_star C_h control0
  have hminus := integral_callVMinus_eq_sum rate rewards C_star C_h control0
  have hcost := integral_callWeightedBacklog_eq_sum
    rate rewards C_star C_h control0
  have hsub : (∫ z, callVPlus rate rewards C_star C_h z -
      callVMinus rate rewards C_star C_h z ∂mu) =
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z, ReferenceFirstCollectionCurrentQueueEnergy.VPlus
          rate rewards C_star C_h u t z -
        ReferenceFirstCollectionCurrentQueueEnergy.VMinus
          rate rewards C_star C_h u t z ∂mu := by
    rw [integral_sub (callVPlus_integrable rate rewards C_star C_h control0)
      (callVMinus_integrable rate rewards C_star C_h control0), hplus, hminus]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    exact integral_sub
      (ReferenceFirstCollectionCurrentQueueEnergy.VPlus_integrable
        rate rewards C_star C_h control0 u t)
      (ReferenceFirstCollectionCurrentQueueEnergy.VMinus_integrable
        rate rewards C_star C_h control0 u t) |>.symm
  rw [hsub, hcost]
  have hcell (u t : Fin p.T) :
      (∫ z, ReferenceFirstCollectionCurrentQueueEnergy.VPlus
          rate rewards C_star C_h u t z -
        ReferenceFirstCollectionCurrentQueueEnergy.VMinus
          rate rewards C_star C_h u t z ∂mu) +
        (11 / 2 : ℝ) *
          ∫ z, (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t).indicator
            (ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog
              rate rewards C_star C_h u t) z ∂mu ≤
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          (sourceInputLaw p).real (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t) :=
    ReferenceFirstCollectionCurrentConditionalWeightedDrift.sourceIntegral_weighted_cost
      rate rewards C_star C_h control0 u t
  calc
    (∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z, ReferenceFirstCollectionCurrentQueueEnergy.VPlus
          rate rewards C_star C_h u t z -
        ReferenceFirstCollectionCurrentQueueEnergy.VMinus
          rate rewards C_star C_h u t z ∂mu) +
      (11 / 2 : ℝ) *
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z, (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t).indicator
            (ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog
              rate rewards C_star C_h u t) z ∂mu =
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ((∫ z, ReferenceFirstCollectionCurrentQueueEnergy.VPlus
            rate rewards C_star C_h u t z -
          ReferenceFirstCollectionCurrentQueueEnergy.VMinus
            rate rewards C_star C_h u t z ∂mu) +
          (11 / 2 : ℝ) *
            ∫ z, (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t).indicator
              (ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog
                rate rewards C_star C_h u t) z ∂mu) := by
        rw [mul_pair_sum
          (fun u t => ∫ z, (ReferenceFirstCollectionCurrentRetainedGate.G
            rate rewards C_star C_h u t).indicator
            (ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog
              rate rewards C_star C_h u t) z ∂mu) (11 / 2 : ℝ)]
        exact pair_sum_add
          (fun u t => ∫ z,
            ReferenceFirstCollectionCurrentQueueEnergy.VPlus
              rate rewards C_star C_h u t z -
            ReferenceFirstCollectionCurrentQueueEnergy.VMinus
              rate rewards C_star C_h u t z ∂mu)
          (fun u t => ∫ z, (ReferenceFirstCollectionCurrentRetainedGate.G
            rate rewards C_star C_h u t).indicator
            (ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog
              rate rewards C_star C_h u t) z ∂mu) (11 / 2 : ℝ)
    _ ≤ ∑ u : Fin p.T, ∑ t : Fin p.T,
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          (sourceInputLaw p).real (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t) := by
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro t ht
        exact hcell u t
    _ = (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (sourceInputLaw p).real (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
          rate rewards C_star C_h) := by
        calc
          _ = (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
              (∑ u : Fin p.T, ∑ t : Fin p.T,
                (sourceInputLaw p).real
                  (ReferenceFirstCollectionCurrentRetainedGate.G
                    rate rewards C_star C_h u t)) :=
            (mul_pair_sum
              (fun u t => (sourceInputLaw p).real
                (ReferenceFirstCollectionCurrentRetainedGate.G
                  rate rewards C_star C_h u t))
              (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ))).symm
          _ = _ := congrArg
            (fun x : ℝ =>
              (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) * x)
            (ReferenceFirstCollectionActualCallExponentialQueueEstimate.sum_retainedGate_measures_eq_retainedFirstCall_measure
              rate rewards C_star C_h control0)

/-- Separated-energy form: outgoing energy plus retained weighted backlog is
paid by incoming energy and the exact retained first-call mass. -/
public theorem integral_call_energy_and_weighted_cost_le_incoming_add_mass
    (control0 : TimeControl p) :
    (∫ z, callVPlus rate rewards C_star C_h z ∂mu) +
        (11 / 2 : ℝ) *
          ∫ z, callWeightedBacklog rate rewards C_star C_h z ∂mu ≤
      (∫ z, callVMinus rate rewards C_star C_h z ∂mu) +
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          (sourceInputLaw p).real
            (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
              rate rewards C_star C_h) := by
  have hmain := integral_call_energy_weighted_cost rate rewards C_star C_h control0
  have hminus := callVMinus_integrable rate rewards C_star C_h control0
  have hplus := callVPlus_integrable rate rewards C_star C_h control0
  rw [integral_sub hplus hminus] at hmain
  linarith

/-- Removing the nonnegative outgoing energy gives the backlog-only form with
the same exact retained first-call mass. -/
public theorem integral_call_weighted_cost_le_incoming_energy_add_mass
    (control0 : TimeControl p) :
    (11 / 2 : ℝ) *
        ∫ z, callWeightedBacklog rate rewards C_star C_h z ∂mu ≤
      (∫ z, callVMinus rate rewards C_star C_h z ∂mu) +
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          (sourceInputLaw p).real (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
            rate rewards C_star C_h) := by
  have hmain := integral_call_energy_and_weighted_cost_le_incoming_add_mass
    rate rewards C_star C_h control0
  have hout : 0 ≤ ∫ z, callVPlus rate rewards C_star C_h z ∂mu :=
    integral_nonneg (fun z => callVPlus_nonneg rate rewards C_star C_h z)
  linarith

/-- Probability-at-most-one consequence of the separated-energy estimate. -/
public theorem integral_call_weighted_cost_le_incoming_energy_add_constant
    (control0 : TimeControl p) :
    (11 / 2 : ℝ) *
        ∫ z, callWeightedBacklog rate rewards C_star C_h z ∂mu ≤
      (∫ z, callVMinus rate rewards C_star C_h z ∂mu) +
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) := by
  have hmass := integral_call_weighted_cost_le_incoming_energy_add_mass
    rate rewards C_star C_h control0
  have hprob :=
    ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall_measure_le_one
      rate rewards C_star C_h
  have hC := C_nonneg (p := p)
  have hconst :
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          (sourceInputLaw p).real
            (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
              rate rewards C_star C_h) ≤
        CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ) := by
    calc
      _ ≤ (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hprob hC
      _ = _ := by ring
  have hadd := add_le_add_left hconst
    (∫ z, callVMinus rate rewards C_star C_h z ∂mu)
  exact hmass.trans (by linarith)

end Bandits.Support.ReferenceFirstCollectionActualCallWeightedEnergy

end
