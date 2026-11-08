/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualCompleteReferenceErrorRowComparison
public import Bandits.Support.ReferenceCompleteCombinedErrorRowCost
public import Bandits.Support.GeneratedSelectedIndexForwardBound

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Ring

/-!
# Actual regret on one complete public-good output

The public event is fixed before the reward grid and original private
expectation. On it, the actual regret is controlled by the same-ID combined
complete-row mean, with one row-concentration allowance and the original
selected-index forward-test probability.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.BootstrapPrivateRoundStreams

namespace Bandits.Support.ActualCompletePublicGoodGridRegret

variable {p : ConstructorDimensions.Parameters}

/-- The literal public event used by the actual regret composition: the
all-grid combined-row event intersected with the accepted common numeric
public-good set. -/
def actualCompletePublicGoodEvent
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (C_star C_h : ℝ) : Set (PublishedOutput p) :=
  ReferenceCompleteCombinedErrorRowCost.actualCombinedErrorPublicGoodEvent
      rate C_star C_h ∩
    BootstrapContextPassingTail.commonNumericPublicGoodSet p

theorem measurableSet_actualCompletePublicGoodEvent
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (C_star C_h : ℝ) :
    MeasurableSet (actualCompletePublicGoodEvent rate C_star C_h) := by
  exact (ReferenceCompleteCombinedErrorRowCost.measurableSet_actualCombinedErrorPublicGoodEvent
    rate C_star C_h).inter
      (BootstrapContextPassingTail.measurableSet_commonNumericPublicGoodSet p)

private theorem falseForwardPrivateMass_le_inv_Bboot
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : PublishedOutput p)
    (hgood : published ∈ BootstrapContextPassingTail.commonNumericPublicGoodSet p) :
    ActualCompleteReferenceErrorRowComparison.falseForwardPrivateMass
        rate rewards C_star C_h published ≤ 1 / (B_boot p : ℝ) := by
  have hevent :
      ActualCompleteReferenceErrorRowComparison.falseForwardPrivateEvent
          rate rewards C_star C_h published =
        GeneratedSelectedIndexForwardBound.actualSelectedIndexAnyFalseForwardPrefixPassSection
          C_star C_h rate.eta rewards published := by
    ext e
    change ((published, e) ∈
        GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
          C_star C_h rate.eta rewards
          (ActualInitializationPhysicalStep.selectedRowIndex p (published, e))) ↔
      ((published, e) ∈
        GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
          C_star C_h rate.eta rewards
          (PrivateSourceStreams.coordinatorIndex p e.1.2))
    rfl
  rw [ActualCompleteReferenceErrorRowComparison.falseForwardPrivateMass,
    hevent]
  exact GeneratedSelectedIndexForwardBound.actualSelectedIndexAnyFalseForwardPrefixPassSection_real_le_inv_Bboot
    C_star C_h rate.eta rewards published hgood

/-- At one fixed complete public output in the public event, every whole grid
reward table obeys the actual original-private expected-regret bound by the
same-ID combined row average plus one `2V` and one bootstrap-forward penalty.
-/
theorem actualPrivateExpectedRegret_le_sameIdMean_on_actualCompletePublicGoodEvent
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : PublishedOutput p)
    (hgood : published ∈ actualCompletePublicGoodEvent rate C_star C_h) :
    ActualCompleteReferenceErrorRowComparison.actualPrivateExpectedRegret
        rate rewards C_star C_h published ≤
      ReferenceCompleteCombinedErrorRowCost.meanActualCombinedErrorRowCost
          rate rewards C_star C_h published.1 +
        2 * PublicGridConcentration.rowConcentrationScale p +
        (2 * (p.m : ℝ) * (p.T : ℝ)) / (B_boot p : ℝ) := by
  have hcombined := hgood.1
  have hnumeric := hgood.2
  have hrowBound :=
    ReferenceCompleteCombinedErrorRowCost.actualCombinedErrorPublicGoodEvent_bound_at
      rate C_star C_h published hcombined rewards
  rw [← ReferenceCompleteCombinedErrorRowCost.actualCombinedErrorRowAverage_eq_original_private_expression
    rate rewards C_star C_h published] at hrowBound
  have hforward := falseForwardPrivateMass_le_inv_Bboot
    rate rewards C_star C_h published hnumeric
  have hrowAverage :
      (1 / (ConstructorDimensions.M p : ℝ)) *
        ∑ j : Fin (ConstructorDimensions.M p),
          (ReferenceCompleteSelectedRowExpectation.fixedRowPrivateExpectedRegret
              rate rewards C_star C_h published.1 j (published.2 j) +
            (2 * (p.m : ℝ) * (p.T : ℝ)) *
              ReferenceCompleteErrorSelectedRowProbability.completeErrorFixedRowProbability
                rate rewards C_star C_h published.1 j (published.2 j)) =
        ReferenceCompleteCombinedErrorRowCost.actualCombinedErrorRowAverage
          rate rewards C_star C_h published := by
    rfl
  have hcoef : 0 ≤ 2 * (p.m : ℝ) * (p.T : ℝ) := by
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  calc
    _ ≤
        (1 / (ConstructorDimensions.M p : ℝ)) *
          ∑ j : Fin (ConstructorDimensions.M p),
            (ReferenceCompleteSelectedRowExpectation.fixedRowPrivateExpectedRegret
                rate rewards C_star C_h published.1 j (published.2 j) +
              (2 * (p.m : ℝ) * (p.T : ℝ)) *
                ReferenceCompleteErrorSelectedRowProbability.completeErrorFixedRowProbability
                  rate rewards C_star C_h published.1 j (published.2 j)) +
          (2 * (p.m : ℝ) * (p.T : ℝ)) *
            ActualCompleteReferenceErrorRowComparison.falseForwardPrivateMass
              rate rewards C_star C_h published :=
      ActualCompleteReferenceErrorRowComparison.actualPrivateExpectedRegret_le_fixedRowAverage
        rate rewards C_star C_h published
    _ = ReferenceCompleteCombinedErrorRowCost.actualCombinedErrorRowAverage
          rate rewards C_star C_h published +
        (2 * (p.m : ℝ) * (p.T : ℝ)) *
          ActualCompleteReferenceErrorRowComparison.falseForwardPrivateMass
            rate rewards C_star C_h published := by
      rw [hrowAverage]
    _ ≤ ReferenceCompleteCombinedErrorRowCost.meanActualCombinedErrorRowCost
          rate rewards C_star C_h published.1 +
        2 * PublicGridConcentration.rowConcentrationScale p +
        (2 * (p.m : ℝ) * (p.T : ℝ)) *
          ActualCompleteReferenceErrorRowComparison.falseForwardPrivateMass
            rate rewards C_star C_h published := by
      exact add_le_add hrowBound le_rfl
    _ ≤ ReferenceCompleteCombinedErrorRowCost.meanActualCombinedErrorRowCost
          rate rewards C_star C_h published.1 +
        2 * PublicGridConcentration.rowConcentrationScale p +
        (2 * (p.m : ℝ) * (p.T : ℝ)) * (1 / (B_boot p : ℝ)) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hforward hcoef)
    _ = _ := by
      congr 1
      ring

/-- The same on-event estimate with the accepted SAME-ID decomposition of the
combined mean into reference regret and the complete-error mean. -/
theorem actualPrivateExpectedRegret_le_sameIdComponents_on_actualCompletePublicGoodEvent
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : PublishedOutput p)
    (hgood : published ∈ actualCompletePublicGoodEvent rate C_star C_h) :
    ActualCompleteReferenceErrorRowComparison.actualPrivateExpectedRegret
        rate rewards C_star C_h published ≤
      ReferenceCompleteRegretRowConcentration.meanReferenceRegret
          rate C_star C_h rewards published.1 +
        2 * (p.m : ℝ) * (p.T : ℝ) *
          ReferenceCompleteErrorSelectedRowProbability.completeErrorMean
            rate rewards C_star C_h published.1 +
        2 * PublicGridConcentration.rowConcentrationScale p +
        (2 * (p.m : ℝ) * (p.T : ℝ)) / (B_boot p : ℝ) := by
  calc
    _ ≤ ReferenceCompleteCombinedErrorRowCost.meanActualCombinedErrorRowCost
          rate rewards C_star C_h published.1 +
        2 * PublicGridConcentration.rowConcentrationScale p +
        (2 * (p.m : ℝ) * (p.T : ℝ)) / (B_boot p : ℝ) :=
      actualPrivateExpectedRegret_le_sameIdMean_on_actualCompletePublicGoodEvent
        rate rewards C_star C_h published hgood
    _ = _ := by
      rw [ReferenceCompleteCombinedErrorRowCost.meanActualCombinedErrorRowCost_eq_components]

/-- A universal threshold for the single complete public-good event gives
its measurability, its `3/(2N)` failure estimate, and the actual original-
private regret bound for every whole grid reward table on that same event. -/
theorem exists_universal_N0_actualCompletePublicGoodEvent_and_actualRegret_bound :
    ∃ N₀ : ℕ, ∀ p : ConstructorDimensions.Parameters, N₀ ≤ N p →
      (16 : ℝ) * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 < (p.T : ℝ) →
      ∀ rate : ActualCompleteHistoryRewardReadouts.RateInput p,
        ∀ C_star C_h : ℝ,
          MeasurableSet (actualCompletePublicGoodEvent rate C_star C_h) ∧
          (CompletePublicTable.publishedOutputMeasure p).real
            (actualCompletePublicGoodEvent rate C_star C_h)ᶜ ≤
              3 / (2 * (N p : ℝ)) ∧
          ∀ published : PublishedOutput p,
            published ∈ actualCompletePublicGoodEvent rate C_star C_h →
            ∀ rewards : ActualInitializationPhysicalStep.GridRewardTable p,
              ActualCompleteReferenceErrorRowComparison.actualPrivateExpectedRegret
                  rate rewards C_star C_h published ≤
                ReferenceCompleteRegretRowConcentration.meanReferenceRegret
                    rate C_star C_h rewards published.1 +
                  2 * (p.m : ℝ) * (p.T : ℝ) *
                    ReferenceCompleteErrorSelectedRowProbability.completeErrorMean
                      rate rewards C_star C_h published.1 +
                  2 * PublicGridConcentration.rowConcentrationScale p +
                  (2 * (p.m : ℝ) * (p.T : ℝ)) / (B_boot p : ℝ) := by
  obtain ⟨N₀, hN₀⟩ :=
    GeneratedSelectedIndexForwardBound.exists_universal_N0_commonGoodSet_and_actualSelectedIndexForward_bound
  refine ⟨N₀, ?_⟩
  intro p hN branch rate C_star C_h
  rcases hN₀ p hN branch with ⟨_hmeasNumeric, hnumericFailure, _hforwardBound⟩
  have hfailureCombined :=
    ReferenceCompleteCombinedErrorRowCost.actualCombinedErrorPublicGoodEvent_failure_prob_le
      rate C_star C_h
  have hfailure :
      (CompletePublicTable.publishedOutputMeasure p).real
          (actualCompletePublicGoodEvent rate C_star C_h)ᶜ ≤
        3 / (2 * (N p : ℝ)) := by
    let μ := CompletePublicTable.publishedOutputMeasure p
    have hsubset :
        (actualCompletePublicGoodEvent rate C_star C_h)ᶜ ⊆
          (ReferenceCompleteCombinedErrorRowCost.actualCombinedErrorPublicGoodEvent
              rate C_star C_h)ᶜ ∪
            (BootstrapContextPassingTail.commonNumericPublicGoodSet p)ᶜ := by
      intro x hx
      change x ∉
        ReferenceCompleteCombinedErrorRowCost.actualCombinedErrorPublicGoodEvent
          rate C_star C_h ∩
        BootstrapContextPassingTail.commonNumericPublicGoodSet p at hx
      simp only [Set.mem_inter_iff, not_and_or] at hx
      simp only [Set.mem_union, Set.mem_compl_iff]
      exact hx
    calc
      μ.real (actualCompletePublicGoodEvent rate C_star C_h)ᶜ ≤
          μ.real ((ReferenceCompleteCombinedErrorRowCost.actualCombinedErrorPublicGoodEvent
              rate C_star C_h)ᶜ ∪
            (BootstrapContextPassingTail.commonNumericPublicGoodSet p)ᶜ) :=
        MeasureTheory.measureReal_mono hsubset
      _ ≤
          μ.real (ReferenceCompleteCombinedErrorRowCost.actualCombinedErrorPublicGoodEvent
              rate C_star C_h)ᶜ +
            μ.real (BootstrapContextPassingTail.commonNumericPublicGoodSet p)ᶜ :=
        MeasureTheory.measureReal_union_le _ _
      _ ≤ 1 / (2 * (N p : ℝ)) + 1 / (N p : ℝ) :=
        add_le_add hfailureCombined hnumericFailure
      _ = 3 / (2 * (N p : ℝ)) := by
        have hNpos : 0 < (N p : ℝ) :=
          Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
        field_simp [ne_of_gt hNpos]
        ; ring
  refine ⟨measurableSet_actualCompletePublicGoodEvent rate C_star C_h,
    hfailure, ?_⟩
  intro published hgood rewards
  exact actualPrivateExpectedRegret_le_sameIdComponents_on_actualCompletePublicGoodEvent
    rate rewards C_star C_h published hgood

end Bandits.Support.ActualCompletePublicGoodGridRegret

end
