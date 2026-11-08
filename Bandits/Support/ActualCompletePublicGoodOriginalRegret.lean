/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualCompletePublicGoodGridRegret
public import Bandits.Support.ActualCompleteOriginalRewardRounding
public import Bandits.Support.ReferenceCompleteFixedIDErrorMeanBound

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Actual original-payoff regret on a strengthened public-good event

The event is the existing simultaneous identification-good event intersected
with the existing actual complete public-good event. On each such published
output, the literal original physical payoff is compared with the accepted
same-ID row mean and its complete-error mean, before taking the original
private expectation. No source-facing regret theorem is claimed here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.BootstrapPrivateRoundStreams

namespace Bandits.Support.ActualCompletePublicGoodOriginalRegret

variable {p : ConstructorDimensions.Parameters}

/-- The identification-good public event intersected with the actual
complete public-good event, both on the same published-output carrier. -/
def identificationAndActualCompletePublicGoodEvent
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (C_star C_h : ℝ) : Set (PublishedOutput p) :=
  IdentificationGoodEvent.identificationPublicGoodEvent p ∩
    ActualCompletePublicGoodGridRegret.actualCompletePublicGoodEvent rate C_star C_h

theorem measurableSet_identificationAndActualCompletePublicGoodEvent
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (C_star C_h : ℝ) :
    MeasurableSet (identificationAndActualCompletePublicGoodEvent rate C_star C_h) := by
  change MeasurableSet (IdentificationGoodEvent.identificationPublicGoodEvent p ∩
    ActualCompletePublicGoodGridRegret.actualCompletePublicGoodEvent rate C_star C_h)
  exact (IdentificationGoodEvent.measurableSet_identificationPublicGoodEvent p).inter
    (ActualCompletePublicGoodGridRegret.measurableSet_actualCompletePublicGoodEvent
      rate C_star C_h)

private theorem gridRewardMatrix_code_eq_rounded
    (original : FiniteBanditModel.RewardMatrix p.T p.K) :
    ReferenceCompleteSelectedRowExpectation.gridRewardMatrix p
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original) =
      RoundedLocalRollout.roundedRewardMatrix (D p) (D_pos p) original := by
  cases hleft : ReferenceCompleteSelectedRowExpectation.gridRewardMatrix p
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original) with
  | mk leftReward leftBound =>
    cases hright : RoundedLocalRollout.roundedRewardMatrix (D p) (D_pos p) original with
    | mk rightReward rightBound =>
      have hreward : leftReward = rightReward := by
        funext t a
        have hvalue := RoundedLocalRollout.roundedRewardMatrixCode_equiv_value
          (D p) (D_pos p) original t a
        calc
          leftReward t a =
              (ReferenceCompleteSelectedRowExpectation.gridRewardMatrix p
                (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)).reward
                t a := by rw [hleft]
          _ = (RealRewardGridCount.realRewardMatrixEncodingEquiv
                (D p) p.K p.T (D_pos p)
                (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
                t a).val := rfl
          _ = rightReward t a := by simpa only [hright] using hvalue
      subst rightReward
      have hbound : leftBound = rightBound := Subsingleton.elim _ _
      subst rightBound
      rfl

/-- On the actual public-good event, the real original-payoff expected regret
is bounded by the actual same-ID combined row mean, one whole-row allowance,
one bootstrap allowance, and the literal physical-reward rounding cost. -/
theorem fixedPublicOriginalExpectedRegret_le_sameIdMean_on_actualCompletePublicGoodEvent
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (C_star C_h : ℝ) (published : PublishedOutput p)
    (hgood : published ∈
      ActualCompletePublicGoodGridRegret.actualCompletePublicGoodEvent rate C_star C_h) :
    ∀ original : FiniteBanditModel.RewardMatrix p.T p.K,
      FiniteBanditModel.bestFixedMSetComparator (m_pos p) (Nat.le_of_lt p.m_lt_K)
          original -
        (∫ e, ActualCompleteOriginalRewardRounding.fixedPublicSourceInitializedOriginalTotalReward
          p rate C_star C_h original published e ∂extendedPrivateLaw p) ≤
      ReferenceCompleteCombinedErrorRowCost.meanActualCombinedErrorRowCost rate
          (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
          C_star C_h published.1 +
        2 * PublicGridConcentration.rowConcentrationScale p +
        (2 * (p.m : ℝ) * (p.T : ℝ)) / (B_boot p : ℝ) +
        (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) := by
  intro original
  let g : ActualInitializationPhysicalStep.GridRewardTable p :=
    RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original
  have hmatrix :
      ReferenceCompleteSelectedRowExpectation.gridRewardMatrix p g =
        RoundedLocalRollout.roundedRewardMatrix (D p) (D_pos p) original := by
    exact gridRewardMatrix_code_eq_rounded original
  have hround := ActualCompleteOriginalRewardRounding.fixedPublicOriginalExpectedRegret_rounding_le
    p rate C_star C_h published original
  have hround' :
      FiniteBanditModel.bestFixedMSetComparator (m_pos p) (Nat.le_of_lt p.m_lt_K)
          original -
        (∫ e, ActualCompleteOriginalRewardRounding.fixedPublicSourceInitializedOriginalTotalReward
          p rate C_star C_h original published e ∂extendedPrivateLaw p) ≤
      ActualCompleteReferenceErrorRowComparison.actualPrivateExpectedRegret
          rate g C_star C_h published +
        (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) := by
    simpa only [ActualCompleteReferenceErrorRowComparison.actualPrivateExpectedRegret,
      ReferenceCompleteSelectedRowExpectation.gridComparator, g, ← hmatrix] using hround
  have hprivate :=
    ActualCompletePublicGoodGridRegret.actualPrivateExpectedRegret_le_sameIdMean_on_actualCompletePublicGoodEvent
      rate g C_star C_h published hgood
  calc
    _ ≤ ActualCompleteReferenceErrorRowComparison.actualPrivateExpectedRegret
          rate g C_star C_h published +
        (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) := hround'
    _ ≤ ReferenceCompleteCombinedErrorRowCost.meanActualCombinedErrorRowCost
          rate g C_star C_h published.1 +
        2 * PublicGridConcentration.rowConcentrationScale p +
        (2 * (p.m : ℝ) * (p.T : ℝ)) / (B_boot p : ℝ) +
        (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) :=
      add_le_add_left hprivate ((p.m : ℝ) * (p.T : ℝ) / (D p : ℝ))

/-- The same original-payoff estimate with the accepted SAME-ID decomposition
of the combined mean into reference regret and the complete-error mean. -/
theorem fixedPublicOriginalExpectedRegret_le_sameIdComponents_on_actualCompletePublicGoodEvent
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (C_star C_h : ℝ) (published : PublishedOutput p)
    (hgood : published ∈
      ActualCompletePublicGoodGridRegret.actualCompletePublicGoodEvent rate C_star C_h) :
    ∀ original : FiniteBanditModel.RewardMatrix p.T p.K,
      FiniteBanditModel.bestFixedMSetComparator (m_pos p) (Nat.le_of_lt p.m_lt_K)
          original -
        (∫ e, ActualCompleteOriginalRewardRounding.fixedPublicSourceInitializedOriginalTotalReward
          p rate C_star C_h original published e ∂extendedPrivateLaw p) ≤
      ReferenceCompleteRegretRowConcentration.meanReferenceRegret rate C_star C_h
          (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
          published.1 +
        2 * (p.m : ℝ) * (p.T : ℝ) *
          ReferenceCompleteErrorSelectedRowProbability.completeErrorMean rate
            (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
            C_star C_h published.1 +
        2 * PublicGridConcentration.rowConcentrationScale p +
        (2 * (p.m : ℝ) * (p.T : ℝ)) / (B_boot p : ℝ) +
        (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) := by
  intro original
  let g : ActualInitializationPhysicalStep.GridRewardTable p :=
    RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original
  have hmatrix :
      ReferenceCompleteSelectedRowExpectation.gridRewardMatrix p g =
        RoundedLocalRollout.roundedRewardMatrix (D p) (D_pos p) original := by
    exact gridRewardMatrix_code_eq_rounded original
  have hround := ActualCompleteOriginalRewardRounding.fixedPublicOriginalExpectedRegret_rounding_le
    p rate C_star C_h published original
  have hround' :
      FiniteBanditModel.bestFixedMSetComparator (m_pos p) (Nat.le_of_lt p.m_lt_K)
          original -
        (∫ e, ActualCompleteOriginalRewardRounding.fixedPublicSourceInitializedOriginalTotalReward
          p rate C_star C_h original published e ∂extendedPrivateLaw p) ≤
      ActualCompleteReferenceErrorRowComparison.actualPrivateExpectedRegret
          rate g C_star C_h published +
        (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) := by
    simpa only [ActualCompleteReferenceErrorRowComparison.actualPrivateExpectedRegret,
      ReferenceCompleteSelectedRowExpectation.gridComparator, g, ← hmatrix] using hround
  have hprivate :=
    ActualCompletePublicGoodGridRegret.actualPrivateExpectedRegret_le_sameIdComponents_on_actualCompletePublicGoodEvent
      rate g C_star C_h published hgood
  calc
    _ ≤ ActualCompleteReferenceErrorRowComparison.actualPrivateExpectedRegret
          rate g C_star C_h published +
        (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) := hround'
    _ ≤ ReferenceCompleteRegretRowConcentration.meanReferenceRegret rate C_star C_h g
          published.1 +
        2 * (p.m : ℝ) * (p.T : ℝ) *
          ReferenceCompleteErrorSelectedRowProbability.completeErrorMean rate g C_star C_h
            published.1 +
        2 * PublicGridConcentration.rowConcentrationScale p +
        (2 * (p.m : ℝ) * (p.T : ℝ)) / (B_boot p : ℝ) +
        (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) :=
      add_le_add_left hprivate ((p.m : ℝ) * (p.T : ℝ) / (D p : ℝ))

/-- One universal threshold precedes the parameter, rate, unrestricted
constants, good published output, every original reward matrix, and the
original private expectation. The event is the literal identification-good
and actual complete public-good intersection. -/
theorem exists_universal_N0_identificationAndActualCompletePublicGoodEvent_and_originalRegret_bound :
    ∃ N₀ : ℕ, ∀ p : ConstructorDimensions.Parameters, N₀ ≤ N p →
      (16 : ℝ) * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 < (p.T : ℝ) →
      ∀ rate : ActualCompleteHistoryRewardReadouts.RateInput p,
        ∀ C_star C_h : ℝ, (4096 : ℝ) ≤ C_h → (2 : ℝ) ^ 20 ≤ C_star →
          MeasurableSet (identificationAndActualCompletePublicGoodEvent rate C_star C_h) ∧
          (publishedOutputMeasure p).real
            (identificationAndActualCompletePublicGoodEvent rate C_star C_h)ᶜ ≤
              9 / (2 * (N p : ℝ)) ∧
          (publishedOutputMeasure p).real
            (identificationAndActualCompletePublicGoodEvent rate C_star C_h)ᶜ ≤
              5 / (N p : ℝ) ∧
          ∀ published : PublishedOutput p,
            published ∈ identificationAndActualCompletePublicGoodEvent rate C_star C_h →
            ∀ original : FiniteBanditModel.RewardMatrix p.T p.K,
              FiniteBanditModel.bestFixedMSetComparator (m_pos p) (Nat.le_of_lt p.m_lt_K)
                  original -
                (∫ e, ActualCompleteOriginalRewardRounding.fixedPublicSourceInitializedOriginalTotalReward
                  p rate C_star C_h original published e ∂extendedPrivateLaw p) ≤
              ReferenceCompleteRegretRowConcentration.meanReferenceRegret rate C_star C_h
                  (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
                  published.1 +
                13 * (p.m : ℝ) * (p.T : ℝ) /
                  (2 * (N p : ℝ) ^ 2) +
                2 * PublicGridConcentration.rowConcentrationScale p +
                (2 * (p.m : ℝ) * (p.T : ℝ)) / (B_boot p : ℝ) +
                (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) := by
  obtain ⟨N₀, hPall⟩ :=
    ActualCompletePublicGoodGridRegret.exists_universal_N0_actualCompletePublicGoodEvent_and_actualRegret_bound
  refine ⟨N₀, ?_⟩
  intro p hN branch rate C_star C_h hC_h hCstar
  rcases hPall p hN branch rate C_star C_h with
    ⟨hPmeas, hPfailure, _hPbound⟩
  have hbranch : IdentificationColumnBalance.constructionBranchBound 16 p := by
    simpa only [IdentificationColumnBalance.constructionBranchBound] using branch
  have hIDfailure := IdentificationGoodEvent.identificationPublicGoodEvent_compl_measure_le
    16 p (by norm_num) hbranch
  have hmeas :
      MeasurableSet (identificationAndActualCompletePublicGoodEvent rate C_star C_h) := by
    change MeasurableSet (IdentificationGoodEvent.identificationPublicGoodEvent p ∩
      ActualCompletePublicGoodGridRegret.actualCompletePublicGoodEvent rate C_star C_h)
    exact (IdentificationGoodEvent.measurableSet_identificationPublicGoodEvent p).inter hPmeas
  have hfailure :
      (publishedOutputMeasure p).real
          (identificationAndActualCompletePublicGoodEvent rate C_star C_h)ᶜ ≤
        9 / (2 * (N p : ℝ)) := by
    let μ := publishedOutputMeasure p
    have hsubset :
        (identificationAndActualCompletePublicGoodEvent rate C_star C_h)ᶜ ⊆
          (IdentificationGoodEvent.identificationPublicGoodEvent p)ᶜ ∪
            (ActualCompletePublicGoodGridRegret.actualCompletePublicGoodEvent
              rate C_star C_h)ᶜ := by
      intro y hy
      change y ∉ IdentificationGoodEvent.identificationPublicGoodEvent p ∩
        ActualCompletePublicGoodGridRegret.actualCompletePublicGoodEvent rate C_star C_h at hy
      simp only [Set.mem_inter_iff, not_and_or] at hy
      simp only [Set.mem_union, Set.mem_compl_iff]
      exact hy
    have hNpos : 0 < (N p : ℝ) :=
      Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
    have hNne : (N p : ℝ) ≠ 0 := ne_of_gt hNpos
    calc
      μ.real (identificationAndActualCompletePublicGoodEvent rate C_star C_h)ᶜ ≤
          μ.real ((IdentificationGoodEvent.identificationPublicGoodEvent p)ᶜ ∪
            (ActualCompletePublicGoodGridRegret.actualCompletePublicGoodEvent
              rate C_star C_h)ᶜ) :=
        MeasureTheory.measureReal_mono hsubset
      _ ≤ μ.real (IdentificationGoodEvent.identificationPublicGoodEvent p)ᶜ +
          μ.real (ActualCompletePublicGoodGridRegret.actualCompletePublicGoodEvent
            rate C_star C_h)ᶜ := MeasureTheory.measureReal_union_le _ _
      _ ≤ 3 / (N p : ℝ) + 3 / (2 * (N p : ℝ)) :=
        add_le_add hIDfailure hPfailure
      _ = 9 / (2 * (N p : ℝ)) := by
        field_simp [hNne]
        ; ring
  have hfailureFive :
      (publishedOutputMeasure p).real
          (identificationAndActualCompletePublicGoodEvent rate C_star C_h)ᶜ ≤
        5 / (N p : ℝ) := by
    have hNpos : 0 < (N p : ℝ) :=
      Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
    have h2Npos : 0 < 2 * (N p : ℝ) := mul_pos (by norm_num) hNpos
    calc
      _ ≤ 9 / (2 * (N p : ℝ)) := hfailure
      _ ≤ 5 / (N p : ℝ) := by
        field_simp [ne_of_gt hNpos, ne_of_gt h2Npos]
        ; norm_num
  refine ⟨hmeas, hfailure, hfailureFive, ?_⟩
  intro published hgood original
  have hIDgood :
      published.1 ∈ IdentificationGoodEvent.identificationGoodEvent p := by
    exact (IdentificationGoodEvent.mem_identificationPublicGoodEvent_iff
      p published).mp hgood.1
  have hPgood :
      published ∈ ActualCompletePublicGoodGridRegret.actualCompletePublicGoodEvent
        rate C_star C_h := hgood.2
  let g : ActualInitializationPhysicalStep.GridRewardTable p :=
    RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original
  let control0 : ContinuousLearningRows.TimeControl p :=
    (fun _ => ⟨0, by constructor <;> norm_num⟩,
      fun _ => (fun _ => 0, 0))
  have herr := ReferenceCompleteFixedIDErrorMeanBound.completeErrorMean_le_13_over_four_N_sq
    rate g C_star C_h control0 published.1 hIDgood hC_h hCstar
  have hcoef : 0 ≤ 2 * (p.m : ℝ) * (p.T : ℝ) := by
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_left herr hcoef
  have herrorParts :
      2 * (p.m : ℝ) * (p.T : ℝ) *
          ReferenceCompleteErrorSelectedRowProbability.completeErrorMean
            rate g C_star C_h published.1 +
        2 * PublicGridConcentration.rowConcentrationScale p +
        (2 * (p.m : ℝ) * (p.T : ℝ)) / (B_boot p : ℝ) ≤
      2 * (p.m : ℝ) * (p.T : ℝ) *
          (13 / (4 * (N p : ℝ) ^ 2)) +
        2 * PublicGridConcentration.rowConcentrationScale p +
        (2 * (p.m : ℝ) * (p.T : ℝ)) / (B_boot p : ℝ) := by
    exact add_le_add_left
      (add_le_add_left hscaled (2 * PublicGridConcentration.rowConcentrationScale p))
      ((2 * (p.m : ℝ) * (p.T : ℝ)) / (B_boot p : ℝ))
  have hround :=
    fixedPublicOriginalExpectedRegret_le_sameIdComponents_on_actualCompletePublicGoodEvent
      rate C_star C_h published hPgood original
  calc
    _ ≤ ReferenceCompleteRegretRowConcentration.meanReferenceRegret rate C_star C_h g
          published.1 +
        2 * (p.m : ℝ) * (p.T : ℝ) *
          ReferenceCompleteErrorSelectedRowProbability.completeErrorMean
            rate g C_star C_h published.1 +
        2 * PublicGridConcentration.rowConcentrationScale p +
        (2 * (p.m : ℝ) * (p.T : ℝ)) / (B_boot p : ℝ) +
        (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) := hround
    _ ≤ ReferenceCompleteRegretRowConcentration.meanReferenceRegret rate C_star C_h g
          published.1 +
        2 * (p.m : ℝ) * (p.T : ℝ) *
          (13 / (4 * (N p : ℝ) ^ 2)) +
        2 * PublicGridConcentration.rowConcentrationScale p +
        (2 * (p.m : ℝ) * (p.T : ℝ)) / (B_boot p : ℝ) +
        (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) := by
      simpa only [add_assoc] using
        (add_le_add_left
          (add_le_add_right herrorParts
            (ReferenceCompleteRegretRowConcentration.meanReferenceRegret
              rate C_star C_h g published.1))
          ((p.m : ℝ) * (p.T : ℝ) / (D p : ℝ)))
    _ = ReferenceCompleteRegretRowConcentration.meanReferenceRegret rate C_star C_h g
          published.1 +
        13 * (p.m : ℝ) * (p.T : ℝ) /
          (2 * (N p : ℝ) ^ 2) +
        2 * PublicGridConcentration.rowConcentrationScale p +
        (2 * (p.m : ℝ) * (p.T : ℝ)) / (B_boot p : ℝ) +
        (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) := by
      congr 1
      have hNpos : 0 < (N p : ℝ) :=
        Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
      have hN2pos : 0 < (N p : ℝ) ^ 2 := pow_pos hNpos 2
      field_simp [ne_of_gt hN2pos]
      ; ring

end Bandits.Support.ActualCompletePublicGoodOriginalRegret

end
