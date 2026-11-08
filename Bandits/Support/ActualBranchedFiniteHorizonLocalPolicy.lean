/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualFiniteHorizonLocalPolicyMembership
public import Bandits.Support.SmallRegimeAbsorption
public import Bandits.Support.ActualCompletePublicGoodOriginalRegret

/-!
# Source-parameter-branched actual finite-horizon local policy

The source chooses the construction strategy exactly when
`T > C_b * m * K * b_N^2` and `N₀ ≤ N`; on the complement, each player uses
its fixed, distinct cast arm. Both constants precede the constructor parameters.
The construction strategy is the accepted actual local policy on every path,
including its failure, overflow, and terminal cases. This module composes that
strategy with the fixed assignment and the already proved public comparison.
It does not construct a hidden-history coupling or close the manuscript regret
bound. Sources: `07_public_setup.tex:5-12`, `08_main_theorem.tex:67-75,154-175`,
and the model clauses in `01_introduction.tex:20-52`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.FiniteBanditModel
open Bandits.Support.CompletePublicTable
open Bandits.Support.ActualFiniteHorizonLocalPolicyMembership
open Bandits.Support.FixedAssignmentRegret
open Bandits.Support.PublicGridConcentration

namespace Bandits.Support.ActualBranchedFiniteHorizonLocalPolicy

variable {p : ConstructorDimensions.Parameters}

local instance roleProfileMeasurableSpace :
    MeasurableSpace (FiniteHorizonRolePrivateLaw.Profile p) := by
  change MeasurableSpace ((i : Fin p.m) → FiniteHorizonRolePrivateLaw.Role p i)
  infer_instance

/-- The literal source parameter branch. `N₀` and `C_b` are fixed before `p`.
The real cast expresses the source's integer comparison `N₀ ≤ N` in the same
carrier as the accepted absorption estimate. -/
def constructionBranch (C_b : ℝ) (N₀ : ℕ)
    (p : ConstructorDimensions.Parameters) : Prop :=
  IdentificationColumnBalance.constructionBranchBound C_b p ∧
    (N₀ : ℝ) ≤ N p

/-- The source fixed assignment on each player's existing role-specific local
input and bounded strict-past history. It ignores all of those inputs. -/
def fixedAssignmentDecision (p : ConstructorDimensions.Parameters) :
    FiniteHorizonBoundedLocalRollout.FiniteBoundedLocalDecision p
      (FiniteHorizonRolePrivateLaw.Role p) :=
  fun i _ _ => Fin.castLE (Nat.le_of_lt p.m_lt_K) i

/-- One literal finite-horizon decision: the accepted actual policy on the
source construction branch, and the distinct fixed cast arms otherwise. -/
def actualBranchedDecision
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p)
    (C_star C_h C_b : ℝ) (N₀ : ℕ) :
    FiniteHorizonBoundedLocalRollout.FiniteBoundedLocalDecision p
      (FiniteHorizonRolePrivateLaw.Role p) := by
  classical
  exact fun i t x =>
    if constructionBranch C_b N₀ p then
      actualDecision rate C_star C_h i t x
    else
      Fin.castLE (Nat.le_of_lt p.m_lt_K) i

/-- The public event uses the accepted identification-and-actual-good event on
the construction branch and all published outputs on the complement. -/
def branchedPublicGoodEvent
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (C_star C_h C_b : ℝ) (N₀ : ℕ) : Set (PublishedOutput p) := by
  classical
  exact if constructionBranch C_b N₀ p then
      ActualCompletePublicGoodOriginalRegret.identificationAndActualCompletePublicGoodEvent
        rate C_star C_h
    else
      Set.univ

theorem actualBranchedDecision_eq_actual_on_construction
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p)
    (C_star C_h C_b : ℝ) (N₀ : ℕ)
    (hbranch : constructionBranch C_b N₀ p) :
    actualBranchedDecision rate C_star C_h C_b N₀ = actualDecision rate C_star C_h := by
  classical
  funext i t x
  simp [actualBranchedDecision, hbranch]

theorem actualBranchedDecision_eq_fixed_on_complement
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p)
    (C_star C_h C_b : ℝ) (N₀ : ℕ)
    (hbranch : ¬ constructionBranch C_b N₀ p) :
    actualBranchedDecision rate C_star C_h C_b N₀ = fixedAssignmentDecision p := by
  classical
  funext i t x
  simp [actualBranchedDecision, fixedAssignmentDecision, hbranch]

theorem branchedPublicGoodEvent_eq_actual_on_construction
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (C_star C_h C_b : ℝ) (N₀ : ℕ)
    (hbranch : constructionBranch C_b N₀ p) :
    branchedPublicGoodEvent rate C_star C_h C_b N₀ =
      ActualCompletePublicGoodOriginalRegret.identificationAndActualCompletePublicGoodEvent
        rate C_star C_h := by
  classical
  simp [branchedPublicGoodEvent, hbranch]

theorem branchedPublicGoodEvent_eq_univ_on_complement
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (C_star C_h C_b : ℝ) (N₀ : ℕ)
    (hbranch : ¬ constructionBranch C_b N₀ p) :
    branchedPublicGoodEvent rate C_star C_h C_b N₀ = Set.univ := by
  classical
  simp [branchedPublicGoodEvent, hbranch]

/-- Joint Borel measurability on each existing player's own-input and
bounded-history carrier follows by branch composition. -/
theorem measurable_actualBranchedDecision
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p)
    (C_star C_h C_b : ℝ) (N₀ : ℕ) (i : Fin p.m) (t : Fin p.T) :
    Measurable (actualBranchedDecision rate C_star C_h C_b N₀ i t) := by
  classical
  by_cases hbranch : constructionBranch C_b N₀ p
  · rw [actualBranchedDecision_eq_actual_on_construction rate C_star C_h C_b N₀ hbranch]
    exact measurable_actualDecision rate C_star C_h i t
  · rw [actualBranchedDecision_eq_fixed_on_complement rate C_star C_h C_b N₀ hbranch]
    exact measurable_const

/-- On the construction branch, every bounded prefix is exactly the accepted
actual-policy prefix, for every `n ≤ T`. -/
theorem boundedLocalPrefix_eq_actual_on_construction
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p)
    (C_star C_h C_b : ℝ) (N₀ : ℕ)
    (hbranch : constructionBranch C_b N₀ p)
    (published : PublishedOutput p) (rho : FiniteHorizonRolePrivateLaw.Profile p)
    (rewards : RewardMatrix p.T p.K) :
    ∀ n hn,
      (FiniteHorizonBoundedLocalRollout.boundedLocalPrefix p
        (actualBranchedDecision rate C_star C_h C_b N₀) published rho rewards n hn).val =
      (FiniteHorizonBoundedLocalRollout.boundedLocalPrefix p
        (actualDecision rate C_star C_h) published rho rewards n hn).val := by
  intro n hn
  rw [actualBranchedDecision_eq_actual_on_construction rate C_star C_h C_b N₀ hbranch]

/-- The construction-branch local recursion is the existing physical actual
execution prefix, preserving the role-specific private inputs and all feedback. -/
theorem boundedLocalPrefix_eq_actualPrefix_on_construction
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p)
    (C_star C_h C_b : ℝ) (N₀ : ℕ)
    (hbranch : constructionBranch C_b N₀ p)
    (rewards : RewardMatrix p.T p.K)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    ∀ n hn,
      (FiniteHorizonBoundedLocalRollout.boundedLocalPrefix p
        (actualBranchedDecision rate C_star C_h C_b N₀) source.1
        (FiniteHorizonRolePrivateLaw.phi p source) rewards n hn).val =
      actualPrefix rate C_star C_h rewards source n hn := by
  intro n hn
  rw [actualBranchedDecision_eq_actual_on_construction rate C_star C_h C_b N₀ hbranch]
  exact boundedLocalPrefix_eq_actualPrefix rate C_star C_h rewards source n hn

/-- Every complementary-branch bounded prefix equals the deterministic
fixed-assignment prefix, including the empty and complete prefixes. -/
theorem boundedLocalPrefix_eq_fixedAssignmentPrefix_on_complement
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p)
    (C_star C_h C_b : ℝ) (N₀ : ℕ)
    (hbranch : ¬ constructionBranch C_b N₀ p)
    (published : PublishedOutput p)
    (rho : FiniteHorizonBoundedLocalRollout.PrivateProfile p
      (FiniteHorizonRolePrivateLaw.Role p))
    (rewards : RewardMatrix p.T p.K) :
    ∀ n hn,
      (FiniteHorizonBoundedLocalRollout.boundedLocalPrefix p
        (actualBranchedDecision rate C_star C_h C_b N₀) published rho rewards n hn).val =
      deterministicRolloutPrefix (fixedAssignmentPolicy (Nat.le_of_lt p.m_lt_K)) ()
        (fun _ : Fin p.m => ()) rewards n hn := by
  rw [actualBranchedDecision_eq_fixed_on_complement rate C_star C_h C_b N₀ hbranch]
  let hmK : p.m ≤ p.K := Nat.le_of_lt p.m_lt_K
  intro n hn
  change (FiniteHorizonBoundedLocalRollout.boundedLocalPrefix p
      (fixedAssignmentDecision p) published rho rewards n hn).val =
    deterministicRolloutPrefix (fixedAssignmentPolicy hmK) ()
      (fun _ : Fin p.m => ()) rewards n hn
  have hprefix : ∀ n (hn : n ≤ p.T),
      (FiniteHorizonBoundedLocalRollout.boundedLocalPrefix p
        (fixedAssignmentDecision p) published rho rewards n hn).val =
      deterministicRolloutPrefix (fixedAssignmentPolicy hmK) ()
        (fun _ : Fin p.m => ()) rewards n hn := by
    intro n
    induction n with
    | zero =>
        intro hn
        rfl
    | succ n ih =>
        intro hn
        apply congrArg₂ (fun a f => (⟨a, f⟩ : RunPrefix p.m p.K (n + 1)))
        · funext s i
          cases s using Fin.lastCases with
          | cast s =>
              simp only [Fin.snoc_castSucc]
              exact congrArg (fun q : RunPrefix p.m p.K n => q.action s i) (ih (Nat.le_of_succ_le hn))
          | last =>
              simp only [Fin.snoc_last, fixedAssignmentDecision,
                FixedAssignmentRegret.fixedAssignmentPolicy]
        · funext s i
          cases s using Fin.lastCases with
          | cast s =>
              simp only [Fin.snoc_castSucc]
              exact congrArg (fun q : RunPrefix p.m p.K n => q.feedback s i)
                (ih (Nat.le_of_succ_le hn))
          | last =>
              simp only [Fin.snoc_last, fixedAssignmentDecision,
                FixedAssignmentRegret.fixedAssignmentPolicy]
              have ht :
                  (⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩ : Fin p.T) =
                    Fin.castLE hn (Fin.last n) := by
                apply Fin.ext
                rfl
              rw [ht]
  exact hprefix n hn

/-- The complete complementary-branch physical run is the deterministic
rollout of the accepted injective fixed assignment. -/
theorem boundedLocalPrefix_eq_fixedAssignmentRollout
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p)
    (C_star C_h C_b : ℝ) (N₀ : ℕ)
    (hbranch : ¬ constructionBranch C_b N₀ p)
    (published : PublishedOutput p)
    (rho : FiniteHorizonBoundedLocalRollout.PrivateProfile p
      (FiniteHorizonRolePrivateLaw.Role p))
    (rewards : RewardMatrix p.T p.K) :
    (FiniteHorizonBoundedLocalRollout.boundedLocalPrefix p
      (actualBranchedDecision rate C_star C_h C_b N₀) published rho rewards p.T
      (Nat.le_refl p.T)).val =
    deterministicRollout (fixedAssignmentPolicy (Nat.le_of_lt p.m_lt_K)) ()
      (fun _ : Fin p.m => ()) rewards := by
  simpa only [FiniteBanditModel.deterministicRollout] using
    (boundedLocalPrefix_eq_fixedAssignmentPrefix_on_complement rate C_star C_h C_b N₀
      hbranch published rho rewards p.T (Nat.le_refl p.T))

/-- Every player takes its source's fixed cast arm throughout the complete
complementary-branch execution. -/
theorem boundedLocalPrefix_action_eq_cast_on_complement
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p)
    (C_star C_h C_b : ℝ) (N₀ : ℕ)
    (hbranch : ¬ constructionBranch C_b N₀ p)
    (published : PublishedOutput p)
    (rho : FiniteHorizonBoundedLocalRollout.PrivateProfile p
      (FiniteHorizonRolePrivateLaw.Role p))
    (rewards : RewardMatrix p.T p.K) (t : Fin p.T) (i : Fin p.m) :
    (FiniteHorizonBoundedLocalRollout.boundedLocalPrefix p
      (actualBranchedDecision rate C_star C_h C_b N₀) published rho rewards p.T
      (Nat.le_refl p.T)).val.action t i = Fin.castLE (Nat.le_of_lt p.m_lt_K) i := by
  rw [boundedLocalPrefix_eq_fixedAssignmentRollout rate C_star C_h C_b N₀
    hbranch published rho rewards]
  exact FixedAssignmentRegret.deterministicRollout_action_eq_fixedAssignment
    (Nat.le_of_lt p.m_lt_K) () (fun _ : Fin p.m => ()) rewards t i

/-- The complementary-branch physical action profile is injective at every
round, by the distinct fixed cast-arm assignment. -/
theorem boundedLocalPrefix_action_injective_on_complement
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p)
    (C_star C_h C_b : ℝ) (N₀ : ℕ)
    (hbranch : ¬ constructionBranch C_b N₀ p)
    (published : PublishedOutput p)
    (rho : FiniteHorizonBoundedLocalRollout.PrivateProfile p
      (FiniteHorizonRolePrivateLaw.Role p))
    (rewards : RewardMatrix p.T p.K) (t : Fin p.T) :
    Function.Injective (fun i =>
      (FiniteHorizonBoundedLocalRollout.boundedLocalPrefix p
        (actualBranchedDecision rate C_star C_h C_b N₀) published rho rewards p.T
        (Nat.le_refl p.T)).val.action t i) := by
  rw [boundedLocalPrefix_eq_fixedAssignmentRollout rate C_star C_h C_b N₀
    hbranch published rho rewards]
  exact FixedAssignmentRegret.deterministicRollout_action_injective
    (Nat.le_of_lt p.m_lt_K) () (fun _ : Fin p.m => ()) rewards t

/-- Construction-branch expected private regret is exactly the original
physical expected regret. The physical integral retains the original rewards,
all original private coordinates including the sampled `J`, and the fixed
published output. -/
theorem expectedPrivateRegret_eq_original_physical_on_construction
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p)
    (C_star C_h C_b : ℝ) (N₀ : ℕ)
    (hbranch : constructionBranch C_b N₀ p)
    (published : PublishedOutput p) (rewards : RewardMatrix p.T p.K) :
    FiniteHorizonBoundedLocalRollout.expectedPrivateRegret p
      (actualBranchedDecision rate C_star C_h C_b N₀)
      (FiniteHorizonRolePrivateLaw.nu p) rewards published =
    bestFixedMSetComparator (ConstructorDimensions.m_pos p) p.m_lt_K.le rewards -
      (∫ e, ActualCompleteOriginalRewardRounding.fixedPublicSourceInitializedOriginalTotalReward
        p rate C_star C_h rewards published e
        ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p) := by
  rw [actualBranchedDecision_eq_actual_on_construction rate C_star C_h C_b N₀ hbranch]
  exact (fixedPublic_actualRegret_eq_expectedPrivateRegret rate C_star C_h published rewards).symm

/-- On the complementary branch, expectation under the actual role-product
law equals the deterministic fixed-assignment regret. The ignored common
carrier is `Unit`; the actual dependent role carriers and product law remain
unchanged in the left-hand side. -/
theorem expectedPrivateRegret_eq_fixedAssignmentRegret_on_complement
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p)
    (C_star C_h C_b : ℝ) (N₀ : ℕ)
    (hbranch : ¬ constructionBranch C_b N₀ p)
    (published : PublishedOutput p) (rewards : RewardMatrix p.T p.K) :
    FiniteHorizonBoundedLocalRollout.expectedPrivateRegret p
      (actualBranchedDecision rate C_star C_h C_b N₀)
      (FiniteHorizonRolePrivateLaw.nu p) rewards published =
    bestFixedMSetComparator (ConstructorDimensions.m_pos p) p.m_lt_K.le rewards -
      pathwiseCumulativeReward
        (deterministicRollout (fixedAssignmentPolicy (Nat.le_of_lt p.m_lt_K)) ()
          (fun _ : Fin p.m => ()) rewards) := by
  rw [actualBranchedDecision_eq_fixed_on_complement rate C_star C_h C_b N₀ hbranch]
  have hrun (rho : FiniteHorizonBoundedLocalRollout.PrivateProfile p
      (FiniteHorizonRolePrivateLaw.Role p)) :
      (FiniteHorizonBoundedLocalRollout.boundedLocalPrefix p
        (fixedAssignmentDecision p) published rho rewards p.T (Nat.le_refl p.T)).val =
        deterministicRollout (fixedAssignmentPolicy (Nat.le_of_lt p.m_lt_K)) ()
          (fun _ : Fin p.m => ()) rewards := by
    have h := boundedLocalPrefix_eq_fixedAssignmentRollout rate C_star C_h C_b N₀
      hbranch published rho rewards
    rw [actualBranchedDecision_eq_fixed_on_complement rate C_star C_h C_b N₀ hbranch] at h
    exact h
  have hpoint : ∀ rho : FiniteHorizonBoundedLocalRollout.PrivateProfile p
      (FiniteHorizonRolePrivateLaw.Role p),
      FiniteHorizonBoundedLocalRollout.pathwiseRegret p (fixedAssignmentDecision p)
        published rho rewards =
        bestFixedMSetComparator (ConstructorDimensions.m_pos p) p.m_lt_K.le rewards -
          pathwiseCumulativeReward
            (deterministicRollout (fixedAssignmentPolicy (Nat.le_of_lt p.m_lt_K)) ()
              (fun _ : Fin p.m => ()) rewards) := by
    intro rho
    change bestFixedMSetComparator (ConstructorDimensions.m_pos p) p.m_lt_K.le rewards -
        pathwiseCumulativeReward
          (FiniteHorizonBoundedLocalRollout.boundedLocalPrefix p
            (fixedAssignmentDecision p) published rho rewards p.T (Nat.le_refl p.T)).val = _
    rw [hrun rho]
  unfold FiniteHorizonBoundedLocalRollout.expectedPrivateRegret
  calc
    (∫ rho, FiniteHorizonBoundedLocalRollout.pathwiseRegret p (fixedAssignmentDecision p)
        published rho rewards ∂FiniteHorizonBoundedLocalRollout.privateProfileLaw p
          (FiniteHorizonRolePrivateLaw.nu p)) =
      ∫ _rho : FiniteHorizonBoundedLocalRollout.PrivateProfile p
          (FiniteHorizonRolePrivateLaw.Role p),
        (bestFixedMSetComparator (ConstructorDimensions.m_pos p) p.m_lt_K.le rewards -
          pathwiseCumulativeReward
            (deterministicRollout (fixedAssignmentPolicy (Nat.le_of_lt p.m_lt_K)) ()
              (fun _ : Fin p.m => ()) rewards))
          ∂FiniteHorizonBoundedLocalRollout.privateProfileLaw p
            (FiniteHorizonRolePrivateLaw.nu p) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = bestFixedMSetComparator (ConstructorDimensions.m_pos p) p.m_lt_K.le rewards -
        pathwiseCumulativeReward
          (deterministicRollout (fixedAssignmentPolicy (Nat.le_of_lt p.m_lt_K)) ()
            (fun _ : Fin p.m => ()) rewards) := by
      simp

/-- For every public output and original reward matrix on the complement,
actual private expectation satisfies the accepted fixed-assignment absorption
bound. Only nonnegativity of `C_b` is needed; in particular this includes
`N < N₀`, with unrestricted construction-policy constants. -/
theorem expectedPrivateRegret_le_complementary_branch_mul_rowConcentrationScale
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p)
    (C_star C_h C_b : ℝ) (N₀ : ℕ) (hC_b : 0 ≤ C_b)
    (hbranch : ¬ constructionBranch C_b N₀ p)
    (published : PublishedOutput p) (rewards : RewardMatrix p.T p.K) :
    FiniteHorizonBoundedLocalRollout.expectedPrivateRegret p
      (actualBranchedDecision rate C_star C_h C_b N₀)
      (FiniteHorizonRolePrivateLaw.nu p) rewards published ≤
    max (Real.sqrt C_b) (N₀ : ℝ) * PublicGridConcentration.rowConcentrationScale p := by
  rw [expectedPrivateRegret_eq_fixedAssignmentRegret_on_complement
    rate C_star C_h C_b N₀ hbranch published rewards]
  exact SmallRegimeAbsorption.bestFixedMSetComparator_regret_le_complementary_branch_mul_rowConcentrationScale
    C_b (N₀ : ℝ) hC_b (Nat.cast_nonneg N₀) p hbranch
    rewards () (fun _ : Fin p.m => ())

/-- The exact literal source horizon condition at `C_b ≥ 16` implies the
accepted construction comparison's threshold-16 condition. -/
private theorem constructionBranch16_of_ge
    (C_b : ℝ) (hC_b : 16 ≤ C_b) (p : ConstructorDimensions.Parameters)
    (hbranch : IdentificationColumnBalance.constructionBranchBound C_b p) :
    (16 : ℝ) * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 < (p.T : ℝ) := by
  have hfactor : 0 ≤ ((p.m : ℝ) * (p.K : ℝ)) * (b_N p : ℝ) ^ 2 :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _)
  calc
    (16 : ℝ) * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 =
        16 * (((p.m : ℝ) * (p.K : ℝ)) * (b_N p : ℝ) ^ 2) := by ring
    _ ≤ C_b * (((p.m : ℝ) * (p.K : ℝ)) * (b_N p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hC_b hfactor
    _ = C_b * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 := by ring
    _ < (p.T : ℝ) := hbranch

/-- A single threshold is selected before the parameters. For every larger
fixed `N₀`, unrestricted `C_b,C_star,C_h` satisfying the source lower bounds,
the branched public-good event is measurable with failure at most `5/(N p)`.
On it, every original reward matrix obeys the exact accepted construction RHS
or the fixed-assignment complementary scale, according to the same branch. -/
theorem exists_universal_Nmin_branchedPublicGood_and_regret_bound :
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
              ∀ rewards : RewardMatrix p.T p.K,
                FiniteHorizonBoundedLocalRollout.expectedPrivateRegret p
                  (actualBranchedDecision rate C_star C_h C_b N₀)
                  (FiniteHorizonRolePrivateLaw.nu p) rewards published ≤
                  ReferenceCompleteRegretRowConcentration.meanReferenceRegret rate
                    C_star C_h
                    (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) rewards)
                    published.1 +
                  13 * (p.m : ℝ) * (p.T : ℝ) / (2 * (N p : ℝ) ^ 2) +
                  2 * PublicGridConcentration.rowConcentrationScale p +
                  (2 * (p.m : ℝ) * (p.T : ℝ)) /
                    (BootstrapDimensions.B_boot p : ℝ) +
                  (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ)) ∧
             (¬ constructionBranch C_b N₀ p →
              ∀ rewards : RewardMatrix p.T p.K,
                FiniteHorizonBoundedLocalRollout.expectedPrivateRegret p
                  (actualBranchedDecision rate C_star C_h C_b N₀)
                  (FiniteHorizonRolePrivateLaw.nu p) rewards published ≤
                  max (Real.sqrt C_b) (N₀ : ℝ) *
                    PublicGridConcentration.rowConcentrationScale p)) := by
  obtain ⟨Nmin, haccepted⟩ :=
    ActualCompletePublicGoodOriginalRegret.exists_universal_N0_identificationAndActualCompletePublicGoodEvent_and_originalRegret_bound
  refine ⟨Nmin, ?_⟩
  intro N₀ hNmin C_b C_star C_h hC_b hC_h hC_star p rate
  by_cases hbranch : constructionBranch C_b N₀ p
  · have hN₀ : N₀ ≤ N p := Nat.cast_le.mp hbranch.2
    have h16 := constructionBranch16_of_ge C_b hC_b p hbranch.1
    obtain ⟨hmeas, _hfailure9, hfailure5, hregret⟩ :=
      haccepted p (Nat.le_trans hNmin hN₀) h16 rate C_star C_h hC_h hC_star
    have heventMeas : MeasurableSet (branchedPublicGoodEvent rate C_star C_h C_b N₀) := by
      rw [branchedPublicGoodEvent_eq_actual_on_construction rate C_star C_h C_b N₀ hbranch]
      exact hmeas
    have heventFailure : (publishedOutputMeasure p).real
        (branchedPublicGoodEvent rate C_star C_h C_b N₀)ᶜ ≤ 5 / (N p : ℝ) := by
      rw [branchedPublicGoodEvent_eq_actual_on_construction rate C_star C_h C_b N₀ hbranch]
      exact hfailure5
    refine ⟨heventMeas, heventFailure, ?_⟩
    intro published hgood
    constructor
    · intro _branch rewards
      have hgoodActual : published ∈
          ActualCompletePublicGoodOriginalRegret.identificationAndActualCompletePublicGoodEvent
            rate C_star C_h := by
        rw [← branchedPublicGoodEvent_eq_actual_on_construction
          rate C_star C_h C_b N₀ hbranch]
        exact hgood
      have hphysical := hregret published hgoodActual rewards
      calc
        FiniteHorizonBoundedLocalRollout.expectedPrivateRegret p
            (actualBranchedDecision rate C_star C_h C_b N₀)
            (FiniteHorizonRolePrivateLaw.nu p) rewards published =
          bestFixedMSetComparator (ConstructorDimensions.m_pos p) p.m_lt_K.le rewards -
            (∫ e, ActualCompleteOriginalRewardRounding.fixedPublicSourceInitializedOriginalTotalReward
              p rate C_star C_h rewards published e
              ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p) :=
          expectedPrivateRegret_eq_original_physical_on_construction
            rate C_star C_h C_b N₀ hbranch published rewards
        _ ≤ _ := hphysical
    · intro hnotbranch rewards
      exact expectedPrivateRegret_le_complementary_branch_mul_rowConcentrationScale
        rate C_star C_h C_b N₀ (le_trans (by norm_num : (0 : ℝ) ≤ 16) hC_b)
        hnotbranch published rewards
  · have heventMeas : MeasurableSet (branchedPublicGoodEvent rate C_star C_h C_b N₀) := by
      rw [branchedPublicGoodEvent_eq_univ_on_complement rate C_star C_h C_b N₀ hbranch]
      exact MeasurableSet.univ
    have heventFailure : (publishedOutputMeasure p).real
        (branchedPublicGoodEvent rate C_star C_h C_b N₀)ᶜ ≤ 5 / (N p : ℝ) := by
      rw [branchedPublicGoodEvent_eq_univ_on_complement rate C_star C_h C_b N₀ hbranch]
      simp
      positivity
    refine ⟨heventMeas, heventFailure, ?_⟩
    intro published hgood
    constructor
    · intro hbranch' rewards
      exact (hbranch hbranch').elim
    · intro _hnotbranch rewards
      exact expectedPrivateRegret_le_complementary_branch_mul_rowConcentrationScale
        rate C_star C_h C_b N₀ (le_trans (by norm_num : (0 : ℝ) ≤ 16) hC_b)
        hbranch published rewards

end Bandits.Support.ActualBranchedFiniteHorizonLocalPolicy

end
