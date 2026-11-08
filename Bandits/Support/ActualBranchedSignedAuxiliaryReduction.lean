/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualBranchedFiniteHorizonLocalPolicy
public import Bandits.Support.ReferenceCompleteOriginalFixedIDAccountingMean

import Mathlib.MeasureTheory.Integral.Prod

/-!
# Actual branched regret reduced to the full signed auxiliary expectation

This internal reduction joins the accepted complete-row mean to the original
fixed-ID source law, chooses a maximizing fixed set from the whole rounded
table before source randomness, and applies the accepted physical accounting.
It preserves the existing actual local policy, role-private law, public event,
and complementary branch. The full signed auxiliary expectation remains
explicit; no auxiliary learning estimate or main regret bound is asserted.

Sources: `08_main_theorem.tex:29-75,78-130`,
`07_public_setup.tex:123-164`, `04_slow_fast_learner.tex:323-390`, and
`06_interruptions.tex:391-426`, under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferenceCompleteSelectedRowExpectation
open Bandits.Support.ReferenceCompleteRegretRowConcentration
open Bandits.Support.ActualBranchedFiniteHorizonLocalPolicy

namespace Bandits.Support.ActualBranchedSignedAuxiliaryReduction

variable {p : ConstructorDimensions.Parameters}

local instance roleProfileMeasurableSpace :
    MeasurableSpace (FiniteHorizonRolePrivateLaw.Profile p) := by
  change MeasurableSpace ((i : Fin p.m) → FiniteHorizonRolePrivateLaw.Role p i)
  infer_instance

/-- The existing row mean is exactly the comparator minus complete physical
reward under the original fixed-ID source law. Whole rows and every original
private coordinate, including the uniform original index, are preserved. -/
theorem meanReferenceRegret_eq_gridComparator_sub_fixedID_expectation
    (rate : ReferenceActivePhysicalStep.RateInput p) (C_star C_h : ℝ)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (ids : IDArray p) :
    meanReferenceRegret rate C_star C_h rewards ids =
      gridComparator p rewards -
        (∫ z : BootstrapPrivateRoundStreams.SourceInput p,
          ReferenceCompletePhysicalRewards.completeReward rate z rewards C_star C_h
          ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) := by
  let f : BootstrapPrivateRoundStreams.SourceInput p → ℝ := fun z =>
    ReferenceCompletePhysicalRewards.completeReward rate z rewards C_star C_h
  have hfmeas : Measurable f :=
    ReferenceCompleteRewardMeasurability.measurable_completeReward_source
      rate rewards C_star C_h
  have hfint : Integrable f
      (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) := by
    apply Integrable.of_mem_Icc 0 ((p.m : ℝ) * (p.T : ℝ)) hfmeas.aemeasurable
    exact ae_of_all _ fun z =>
      ReferenceCompletePhysicalRewards.completeReward_bounds rate z rewards C_star C_h
  have hinsertInt : Integrable
      (f ∘ ReferenceFixedIDSourceSection.fixedIDSourceInsertion (p := p) ids)
      ((completeRowsMeasure p).prod (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) :=
    hfint.comp_measurable
      (ReferenceFixedIDSourceSection.measurable_fixedIDSourceInsertion (p := p) ids)
  have hsource :
      (∫ z : BootstrapPrivateRoundStreams.SourceInput p,
        ReferenceCompletePhysicalRewards.completeReward rate z rewards C_star C_h
        ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) =
      ∫ rows : CompleteRows p,
        ∫ e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p,
          ReferenceCompletePhysicalRewards.completeReward rate ((ids, rows), e)
            rewards C_star C_h ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p
        ∂completeRowsMeasure p := by
    calc
      _ = ∫ w, f (ReferenceFixedIDSourceSection.fixedIDSourceInsertion (p := p) ids w)
          ∂(completeRowsMeasure p).prod
            (BootstrapPrivateRoundStreams.extendedPrivateLaw p) :=
        ReferenceFixedIDSourceSection.fixedIDSourceLaw_integral_eq_insertion ids f hfint
      _ = _ := integral_prod _ hinsertInt
  rw [meanReferenceRegret_eq_comparator_sub_iterated_original_expectation, hsource]

/-- A whole rounded table has a deterministic maximizing product-support set.
This existential depends only on the table and dimensions, before any rate,
execution constants, ID array, initial control, or source randomness. -/
theorem exists_gridComparator_productSet
    (p : ConstructorDimensions.Parameters)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    ∃ S0 : ProductSetLaw.ProductSet p.K p.m,
      (∑ q : Fin p.T, ∑ a ∈ S0.val,
        ((rewards q a).val : ℝ) / (D p : ℝ)) = gridComparator p rewards := by
  classical
  obtain ⟨S, _hmem, hmax⟩ := Finset.exists_mem_eq_sup'
    (FiniteBanditModel.fixedMSetSupport_nonempty (m_pos p) p.m_lt_K.le)
    (fun S : FiniteBanditModel.FixedMSet p.m p.K =>
      FiniteBanditModel.fixedMSetReward (gridRewardMatrix p rewards) S.val)
  have hsupport : S.val ∈ ProductSetLaw.support p.K p.m := by
    simp only [ProductSetLaw.support, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    exact S.property.1
  refine ⟨⟨S.val, hsupport⟩, ?_⟩
  exact hmax.symm

/-- For the same deterministic maximizing set, every original fixed ID and
initial control satisfies the physical reduction. No good-ID event or lower
bound on the execution constants is needed. The auxiliary expectation is the
full signed archive readout of the existing exhaustive terminal law. -/
theorem exists_gridMaximizer_meanReferenceRegret_le_signedGap
    (p : ConstructorDimensions.Parameters)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    ∃ S0 : ProductSetLaw.ProductSet p.K p.m,
      (∑ q : Fin p.T, ∑ a ∈ S0.val,
        ((rewards q a).val : ℝ) / (D p : ℝ)) = gridComparator p rewards ∧
      ∀ (rate : ReferenceActivePhysicalStep.RateInput p) (C_star C_h : ℝ)
        (ids : IDArray p) (control0 : ContinuousLearningRows.TimeControl p),
        meanReferenceRegret rate C_star C_h rewards ids ≤
          (∫ w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h,
            ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap rate rewards S0
              (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout
                rate rewards C_star C_h control0 w).2.2
            ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw
              rate rewards C_star C_h control0 ids) +
          128 * (4 * (BootstrapStartupCostScale.Q C_star C_h p : ℝ) +
            (p.K : ℝ) * (BootstrapDimensions.B_boot p : ℝ) +
            (p.m : ℝ) * (p.K : ℝ) * (BootstrapDimensions.B_boot p : ℝ) *
              (4 * (b_N p : ℝ))) +
          (p.m : ℝ) * (p.T : ℝ) / (N p : ℝ) ^ 2 +
          ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) *
            ((4 * (p.m : ℝ) + 128) * rate.eta.val * (p.T : ℝ) + 2) +
          4 * (p.m : ℝ) * (p.T : ℝ) / (N p : ℝ) ^ 2 := by
  obtain ⟨S0, hmax⟩ := exists_gridComparator_productSet p rewards
  refine ⟨S0, hmax, ?_⟩
  intro rate C_star C_h ids control0
  rw [meanReferenceRegret_eq_gridComparator_sub_fixedID_expectation, ← hmax]
  exact ReferenceCompleteOriginalFixedIDAccountingMean.fixedID_physical_expected_regret_le_signedGap
    rate rewards C_star C_h control0 ids S0

/-- One universal threshold gives the existing reward-independent public event
and actual own-local private-regret bound. On construction, each original reward
matrix uses its actual rounded table and the deterministic maximizer above,
uniformly in the initial control. All accepted physical and public accounting
costs are displayed. The complementary branch keeps its accepted bound.

The downstream main-regret assembly must still prove and apply a full signed
auxiliary estimate to this same set, rounded table, ID, and terminal law. -/
theorem exists_universal_Nmin_branchedPublicGood_and_signedAuxiliary_reduction :
    ∃ Nmin : ℕ, ∀ N₀ : ℕ, Nmin ≤ N₀ → ∀ C_b C_star C_h : ℝ,
      16 ≤ C_b → (4096 : ℝ) ≤ C_h → (2 : ℝ) ^ 20 ≤ C_star →
      ∀ p : ConstructorDimensions.Parameters,
        ∀ rate : ActualSampledBoundedCoordinatorDecision.RateInput p,
          MeasurableSet (branchedPublicGoodEvent rate C_star C_h C_b N₀) ∧
          (publishedOutputMeasure p).real
            (branchedPublicGoodEvent rate C_star C_h C_b N₀)ᶜ ≤ 5 / (N p : ℝ) ∧
          ∀ published : PublishedOutput p,
            published ∈ branchedPublicGoodEvent rate C_star C_h C_b N₀ →
            ((constructionBranch C_b N₀ p →
              ∀ rewards : FiniteBanditModel.RewardMatrix p.T p.K,
                let rounded :=
                  RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) rewards
                ∃ S0 : ProductSetLaw.ProductSet p.K p.m,
                  (∑ q : Fin p.T, ∑ a ∈ S0.val,
                    ((rounded q a).val : ℝ) / (D p : ℝ)) = gridComparator p rounded ∧
                  ∀ control0 : ContinuousLearningRows.TimeControl p,
                    FiniteHorizonBoundedLocalRollout.expectedPrivateRegret p
                      (actualBranchedDecision rate C_star C_h C_b N₀)
                      (FiniteHorizonRolePrivateLaw.nu p) rewards published ≤
                    (∫ w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega
                        rate rounded C_star C_h,
                      ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap rate rounded S0
                        (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout
                          rate rounded C_star C_h control0 w).2.2
                      ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw
                        rate rounded C_star C_h control0 published.1) +
                    128 * (4 * (BootstrapStartupCostScale.Q C_star C_h p : ℝ) +
                      (p.K : ℝ) * (BootstrapDimensions.B_boot p : ℝ) +
                      (p.m : ℝ) * (p.K : ℝ) * (BootstrapDimensions.B_boot p : ℝ) *
                        (4 * (b_N p : ℝ))) +
                    (p.m : ℝ) * (p.T : ℝ) / (N p : ℝ) ^ 2 +
                    ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) *
                      ((4 * (p.m : ℝ) + 128) * rate.eta.val * (p.T : ℝ) + 2) +
                    4 * (p.m : ℝ) * (p.T : ℝ) / (N p : ℝ) ^ 2 +
                    13 * (p.m : ℝ) * (p.T : ℝ) / (2 * (N p : ℝ) ^ 2) +
                    2 * PublicGridConcentration.rowConcentrationScale p +
                    (2 * (p.m : ℝ) * (p.T : ℝ)) /
                      (BootstrapDimensions.B_boot p : ℝ) +
                    (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ)) ∧
             (¬ constructionBranch C_b N₀ p →
              ∀ rewards : FiniteBanditModel.RewardMatrix p.T p.K,
                FiniteHorizonBoundedLocalRollout.expectedPrivateRegret p
                  (actualBranchedDecision rate C_star C_h C_b N₀)
                  (FiniteHorizonRolePrivateLaw.nu p) rewards published ≤
                  max (Real.sqrt C_b) (N₀ : ℝ) *
                    PublicGridConcentration.rowConcentrationScale p)) := by
  obtain ⟨Nmin, haccepted⟩ :=
    exists_universal_Nmin_branchedPublicGood_and_regret_bound
  refine ⟨Nmin, ?_⟩
  intro N₀ hNmin C_b C_star C_h hC_b hC_h hC_star p rate
  obtain ⟨hmeas, hfailure, hpublic⟩ :=
    haccepted N₀ hNmin C_b C_star C_h hC_b hC_h hC_star p rate
  refine ⟨hmeas, hfailure, ?_⟩
  intro published hgood
  obtain ⟨hconstruction, hcomplement⟩ := hpublic published hgood
  refine ⟨?_, hcomplement⟩
  intro hbranch rewards
  let rounded := RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) rewards
  obtain ⟨S0, hmax, hfixed⟩ :=
    exists_gridMaximizer_meanReferenceRegret_le_signedGap p rounded
  refine ⟨S0, hmax, ?_⟩
  intro control0
  have hmean := hfixed rate C_star C_h published.1 control0
  have hactual := hconstruction hbranch rewards
  exact hactual.trans
    (add_le_add (add_le_add (add_le_add (add_le_add hmean le_rfl) le_rfl) le_rfl) le_rfl)

end Bandits.Support.ActualBranchedSignedAuxiliaryReduction

end
