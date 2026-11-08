/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarAuxiliaryExpectation
public import Bandits.Support.ActualBranchedSignedAuxiliaryReduction
public import Bandits.Support.ReferenceLearningTransportRateDomination

/-!
# Same-rate promotion of the actual finite-horizon local policy

All tuning and execution constants are chosen before the constructor parameters.
The decision below is the accepted actual policy at the canonical source rate
on the literal construction branch, and the distinct fixed assignment on its
complement. A rate input is constructed only on the construction branch.

Sources: `01_introduction.tex:20-52`, `07_public_setup.tex:5-12`, and
`08_main_theorem.tex:4-24,67-175` in `sources/zip4/manuscript/`.
These are internal provider results awaiting independent exact-statement review;
this module neither approves nor seals a manuscript anchor.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ActualBranchedFiniteHorizonLocalPolicy

namespace Bandits.Support.ActualMainRegretLocalPolicyPromotion

local instance roleProfileMeasurableSpace {p : Parameters} :
    MeasurableSpace (FiniteHorizonRolePrivateLaw.Profile p) := by
  change MeasurableSpace ((i : Fin p.m) → FiniteHorizonRolePrivateLaw.Role p i)
  infer_instance

/-- A universal branch coefficient supplied by tuning at this same `C1`. -/
def tuningBranchConstant (C1 : ℝ) (hC1 : 0 < C1) : ℝ :=
  (SourceDyadicTuning.sourceRate_uniform_tuning C1 hC1).choose

/-- The corresponding universal size threshold; it has no parameter input. -/
def tuningThreshold (C1 : ℝ) (hC1 : 0 < C1) : ℕ :=
  (SourceDyadicTuning.sourceRate_uniform_tuning C1 hC1).choose_spec.choose

/-- Enlarge a universal branch coefficient before receiving any parameters. -/
def branchConstant (C1 : ℝ) (hC1 : 0 < C1) (Cb : ℝ) : ℝ :=
  max Cb (tuningBranchConstant C1 hC1)

/-- Enlarge a universal size threshold before receiving any parameters. -/
def sizeThreshold (C1 : ℝ) (hC1 : 0 < C1) (N0 : ℕ) : ℕ :=
  max N0 (tuningThreshold C1 hC1)

/-- Enlarging either source branch constant only shrinks its construction
branch; the learning rate is not changed. -/
theorem constructionBranch_mono {Cb Cb' : ℝ} {N0 N0' : ℕ}
    (hCb : Cb ≤ Cb') (hN0 : N0 ≤ N0') (p : Parameters)
    (hbranch : constructionBranch Cb' N0' p) :
    constructionBranch Cb N0 p := by
  refine ⟨?_, ?_⟩
  · change Cb * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 < (p.T : ℝ)
    have hmul : Cb * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 ≤
        Cb' * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 := by
      gcongr
    exact hmul.trans_lt hbranch.1
  · exact (Nat.cast_le.mpr hN0).trans hbranch.2

/-- The positive integer code of the canonical source rate exists on the
enlarged branch, by the original joint tuning theorem. -/
theorem sourceRate_integer_on_construction
    (C1 : ℝ) (hC1 : 0 < C1) (Cb : ℝ) (N0 : ℕ) (p : Parameters)
    (hbranch : constructionBranch (branchConstant C1 hC1 Cb)
      (sizeThreshold C1 hC1 N0) p) :
    ∃ n : ℕ, 0 < n ∧
      (n : ℝ) = SourceDyadicTuning.sourceRate C1 hC1 p * (D p : ℝ) := by
  have htune :=
    (SourceDyadicTuning.sourceRate_uniform_tuning C1 hC1).choose_spec.choose_spec
  have hsmall := constructionBranch_mono
    (le_max_right Cb (tuningBranchConstant C1 hC1))
    (le_max_right N0 (tuningThreshold C1 hC1)) p hbranch
  exact (htune.2.2 p hsmall.1 (Nat.cast_le.mp hsmall.2)).2.2.2.2.1

/-- The original rate carrier, built from the positive integer witness only
where that witness is available. Its real learning rate is literally the
canonical source rate, with its original source cap. -/
def constructionRate (C1 : ℝ) (hC1 : 0 < C1) (Cb : ℝ) (N0 : ℕ)
    (p : Parameters)
    (hbranch : constructionBranch (branchConstant C1 hC1 Cb)
      (sizeThreshold C1 hC1 N0) p) : ReferenceActivePhysicalStep.RateInput p where
  eta := ⟨SourceDyadicTuning.sourceRate C1 hC1 p,
    SourceDyadicTuning.sourceRate_pos C1 hC1 p⟩
  sourceCap := (SourceDyadicTuning.sourceRate_admissible C1 hC1 p).1
  n := (sourceRate_integer_on_construction C1 hC1 Cb N0 p hbranch).choose
  n_scale := (sourceRate_integer_on_construction C1 hC1 Cb N0 p hbranch).choose_spec.2

theorem constructionRate_eta (C1 : ℝ) (hC1 : 0 < C1) (Cb : ℝ) (N0 : ℕ)
    (p : Parameters)
    (hbranch : constructionBranch (branchConstant C1 hC1 Cb)
      (sizeThreshold C1 hC1 N0) p) :
    (constructionRate C1 hC1 Cb N0 p hbranch).eta.val =
      SourceDyadicTuning.sourceRate C1 hC1 p := rfl

theorem constructionRate_n_pos (C1 : ℝ) (hC1 : 0 < C1) (Cb : ℝ) (N0 : ℕ)
    (p : Parameters)
    (hbranch : constructionBranch (branchConstant C1 hC1 Cb)
      (sizeThreshold C1 hC1 N0) p) :
    0 < (constructionRate C1 hC1 Cb N0 p hbranch).n :=
  (sourceRate_integer_on_construction C1 hC1 Cb N0 p hbranch).choose_spec.1

/-- The literal source-branched own-local policy. On the complement no rate
input is selected or required. All input and history carriers are unchanged. -/
def decision (C1 : ℝ) (hC1 : 0 < C1) (C_star C_h Cb : ℝ) (N0 : ℕ)
    (p : Parameters) : FiniteHorizonBoundedLocalRollout.FiniteBoundedLocalDecision p
      (FiniteHorizonRolePrivateLaw.Role p) := by
  classical
  exact if hbranch : constructionBranch (branchConstant C1 hC1 Cb)
      (sizeThreshold C1 hC1 N0) p then
    ActualFiniteHorizonLocalPolicyMembership.actualDecision
      (constructionRate C1 hC1 Cb N0 p hbranch) C_star C_h
  else fixedAssignmentDecision p

/-- The reward-independent public event on the original complete continuous
published-output carrier, and the whole carrier on the complementary branch. -/
def goodPublicEvent (C1 : ℝ) (hC1 : 0 < C1) (C_star C_h Cb : ℝ)
    (N0 : ℕ) (p : Parameters) : Set (PublishedOutput p) := by
  classical
  exact if hbranch : constructionBranch (branchConstant C1 hC1 Cb)
      (sizeThreshold C1 hC1 N0) p then
    branchedPublicGoodEvent (constructionRate C1 hC1 Cb N0 p hbranch)
      C_star C_h (branchConstant C1 hC1 Cb) (sizeThreshold C1 hC1 N0)
  else Set.univ

theorem decision_eq_actual_on_construction
    (C1 : ℝ) (hC1 : 0 < C1) (C_star C_h Cb : ℝ) (N0 : ℕ) (p : Parameters)
    (hbranch : constructionBranch (branchConstant C1 hC1 Cb)
      (sizeThreshold C1 hC1 N0) p) :
    decision C1 hC1 C_star C_h Cb N0 p =
      ActualFiniteHorizonLocalPolicyMembership.actualDecision
        (constructionRate C1 hC1 Cb N0 p hbranch) C_star C_h := by
  classical
  simp only [decision, dite_eq_left hbranch]

theorem decision_eq_branched_on_construction
    (C1 : ℝ) (hC1 : 0 < C1) (C_star C_h Cb : ℝ) (N0 : ℕ) (p : Parameters)
    (hbranch : constructionBranch (branchConstant C1 hC1 Cb)
      (sizeThreshold C1 hC1 N0) p) :
    decision C1 hC1 C_star C_h Cb N0 p =
      actualBranchedDecision (constructionRate C1 hC1 Cb N0 p hbranch)
        C_star C_h (branchConstant C1 hC1 Cb) (sizeThreshold C1 hC1 N0) := by
  rw [decision_eq_actual_on_construction C1 hC1 C_star C_h Cb N0 p hbranch,
    actualBranchedDecision_eq_actual_on_construction _ _ _ _ _ hbranch]

theorem decision_eq_fixed_on_complement
    (C1 : ℝ) (hC1 : 0 < C1) (C_star C_h Cb : ℝ) (N0 : ℕ) (p : Parameters)
    (hbranch : ¬ constructionBranch (branchConstant C1 hC1 Cb)
      (sizeThreshold C1 hC1 N0) p) :
    decision C1 hC1 C_star C_h Cb N0 p = fixedAssignmentDecision p := by
  classical
  simp only [decision, dite_eq_right hbranch]

theorem goodPublicEvent_eq_branched_on_construction
    (C1 : ℝ) (hC1 : 0 < C1) (C_star C_h Cb : ℝ) (N0 : ℕ) (p : Parameters)
    (hbranch : constructionBranch (branchConstant C1 hC1 Cb)
      (sizeThreshold C1 hC1 N0) p) :
    goodPublicEvent C1 hC1 C_star C_h Cb N0 p =
      branchedPublicGoodEvent (constructionRate C1 hC1 Cb N0 p hbranch)
        C_star C_h (branchConstant C1 hC1 Cb) (sizeThreshold C1 hC1 N0) := by
  classical
  simp only [goodPublicEvent, dite_eq_left hbranch]

theorem goodPublicEvent_eq_univ_on_complement
    (C1 : ℝ) (hC1 : 0 < C1) (C_star C_h Cb : ℝ) (N0 : ℕ) (p : Parameters)
    (hbranch : ¬ constructionBranch (branchConstant C1 hC1 Cb)
      (sizeThreshold C1 hC1 N0) p) :
    goodPublicEvent C1 hC1 C_star C_h Cb N0 p = Set.univ := by
  classical
  simp only [goodPublicEvent, dite_eq_right hbranch]

/-- Joint Borel measurability in the accepted own-private-input and strict
action/observation-history carrier. -/
theorem measurable_decision (C1 : ℝ) (hC1 : 0 < C1)
    (C_star C_h Cb : ℝ) (N0 : ℕ) (p : Parameters) (i : Fin p.m) (t : Fin p.T) :
    Measurable (decision C1 hC1 C_star C_h Cb N0 p i t) := by
  classical
  by_cases hbranch : constructionBranch (branchConstant C1 hC1 Cb)
      (sizeThreshold C1 hC1 N0) p
  · rw [decision_eq_actual_on_construction C1 hC1 C_star C_h Cb N0 p hbranch]
    exact ActualFiniteHorizonLocalPolicyMembership.measurable_actualDecision _ _ _ i t
  · rw [decision_eq_fixed_on_complement C1 hC1 C_star C_h Cb N0 p hbranch]
    exact measurable_const

/-- A literal strict-prefix filler for the auxiliary expectation. It is an
administrative value, not a new execution or a random input. -/
def zeroControl (p : Parameters) : ContinuousLearningRows.TimeControl p :=
  ⟨fun _ => ⟨0, le_rfl, zero_lt_one⟩, fun _ => (fun _ => 0, 0)⟩

/-- The two explicit bootstrap arm costs are bounded by the same actual launch
budget. No startup or learning estimate is assumed. -/
theorem startup_terms_le (C_b C_h C_star : ℝ) (p : Parameters)
    (hC_b : 16 ≤ C_b) (hC_h : 0 ≤ C_h) (hC_star : 2 ≤ C_star)
    (hbranch : C_b * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 < (p.T : ℝ)) :
    128 * (4 * (BootstrapStartupCostScale.Q C_star C_h p : ℝ) +
      (p.K : ℝ) * (BootstrapDimensions.B_boot p : ℝ) +
      (p.m : ℝ) * (p.K : ℝ) * (BootstrapDimensions.B_boot p : ℝ) *
        (4 * (b_N p : ℝ))) ≤
      768 * (C_star * (5 + 8 * C_h + (4 * C_h + 1) / Real.sqrt C_b)) *
        BootstrapStartupCostScale.Q_boot p := by
  have harmNat := BootstrapStartupCostScale.bootstrap_arm_budget_le_Q C_h C_star p hC_star
  have hfactor : 1 ≤ p.m * (4 * b_N p) := Nat.succ_le_of_lt
    (Nat.mul_pos (ConstructorDimensions.m_pos p)
      (Nat.mul_pos (by decide) (ConstructorDimensions.b_N_pos p)))
  have hsmallNat : p.K * BootstrapDimensions.B_boot p ≤
      p.m * p.K * BootstrapDimensions.B_boot p * (4 * b_N p) := by
    calc
      p.K * BootstrapDimensions.B_boot p =
          1 * (p.K * BootstrapDimensions.B_boot p) := by omega
      _ ≤ (p.m * (4 * b_N p)) * (p.K * BootstrapDimensions.B_boot p) :=
        Nat.mul_le_mul_right _ hfactor
      _ = p.m * p.K * BootstrapDimensions.B_boot p * (4 * b_N p) := by ring
  have harm : (p.m : ℝ) * (p.K : ℝ) * (BootstrapDimensions.B_boot p : ℝ) *
      (4 * (b_N p : ℝ)) ≤ (BootstrapStartupCostScale.Q C_star C_h p : ℝ) := by
    exact_mod_cast harmNat
  have hsmall : (p.K : ℝ) * (BootstrapDimensions.B_boot p : ℝ) ≤
      (BootstrapStartupCostScale.Q C_star C_h p : ℝ) := by
    exact_mod_cast hsmallNat.trans harmNat
  have hQ := BootstrapStartupCostScale.Q_le_cost_scale
    C_b C_h C_star p hC_b hC_h hC_star hbranch
  calc
    _ ≤ 768 * (BootstrapStartupCostScale.Q C_star C_h p : ℝ) := by
      linarith only [harm, hsmall]
    _ ≤ 768 * (C_star * (5 + 8 * C_h + (4 * C_h + 1) / Real.sqrt C_b) *
        BootstrapStartupCostScale.Q_boot p) :=
      mul_le_mul_of_nonneg_left hQ (by norm_num)
    _ = _ := by ring

/-- Every remaining error from the auxiliary mean, physical accounting,
public comparison and original-reward rounding is retained here. -/
theorem numerical_errors_le (p : Parameters) :
    (p.m : ℝ) * (p.T : ℝ) / (N p : ℝ) ^ 2 +
      (p.m : ℝ) * (p.T : ℝ) / (N p : ℝ) ^ 2 +
      4 * (p.m : ℝ) * (p.T : ℝ) / (N p : ℝ) ^ 2 +
      13 * (p.m : ℝ) * (p.T : ℝ) / (2 * (N p : ℝ) ^ 2) +
      2 * PublicGridConcentration.rowConcentrationScale p +
      (2 * (p.m : ℝ) * (p.T : ℝ)) / (BootstrapDimensions.B_boot p : ℝ) +
      (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) ≤
      18 * BootstrapStartupCostScale.Q_boot p := by
  have hV := TunedNumericalRemainder.rowConcentrationScale_le_Q_boot p
  have hOne : 1 ≤ BootstrapStartupCostScale.Q_boot p :=
    (SmallRegimeAbsorption.one_le_rowConcentrationScale p).trans hV
  have hSeven := TunedNumericalRemainder.m_mul_T_mul_seven_div_N_sq_le_seven p
  have hfrac : (p.m : ℝ) * (p.T : ℝ) / (N p : ℝ) ^ 2 ≤ 1 := by
    have heq : (p.m : ℝ) * (p.T : ℝ) * (7 / (N p : ℝ) ^ 2) =
        7 * ((p.m : ℝ) * (p.T : ℝ) / (N p : ℝ) ^ 2) := by ring
    rw [heq] at hSeven
    linarith only [hSeven]
  have hb : 1 ≤ (b_N p : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.b_N_pos p)
  have hroot : (p.m : ℝ) * Real.sqrt (p.m : ℝ) *
      Real.sqrt ((p.K : ℝ) * (p.T : ℝ)) ≤
      PublicGridConcentration.rowConcentrationScale p := by
    change _ ≤ _ * (b_N p : ℝ)
    exact le_mul_of_one_le_right (by positivity) hb
  have hblock := (TunedNumericalRemainder.m_mul_T_div_B_boot_le_root_scale p).trans
    (hroot.trans hV)
  have hround := (TunedNumericalRemainder.m_mul_T_div_D_le_one p).trans hOne
  have hfracQ := hfrac.trans hOne
  have hfrac0 : 0 ≤ (p.m : ℝ) * (p.T : ℝ) / (N p : ℝ) ^ 2 := by positivity
  have hnormal :
      4 * (p.m : ℝ) * (p.T : ℝ) / (N p : ℝ) ^ 2 =
        4 * ((p.m : ℝ) * (p.T : ℝ) / (N p : ℝ) ^ 2) ∧
      13 * (p.m : ℝ) * (p.T : ℝ) / (2 * (N p : ℝ) ^ 2) =
        (13 / 2 : ℝ) * ((p.m : ℝ) * (p.T : ℝ) / (N p : ℝ) ^ 2) ∧
      (2 * (p.m : ℝ) * (p.T : ℝ)) / (BootstrapDimensions.B_boot p : ℝ) =
        2 * ((p.m : ℝ) * (p.T : ℝ) / (BootstrapDimensions.B_boot p : ℝ)) := by
    constructor
    · ring
    constructor <;> ring
  rw [hnormal.1, hnormal.2.1, hnormal.2.2]
  linarith only [hfracQ, hfrac0, hV, hblock, hround]

/-- The original fixed decision has the deterministic fixed-assignment run
on every role-private profile, without requiring any rate input. -/
theorem fixedAssignmentPrefix_eq (p : Parameters) (published : PublishedOutput p)
    (rho : FiniteHorizonRolePrivateLaw.Profile p)
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) :
    ∀ n hn,
      (FiniteHorizonBoundedLocalRollout.boundedLocalPrefix p
        (fixedAssignmentDecision p) published rho rewards n hn).val =
      FiniteBanditModel.deterministicRolloutPrefix
        (FixedAssignmentRegret.fixedAssignmentPolicy (Nat.le_of_lt p.m_lt_K)) ()
        (fun _ : Fin p.m => ()) rewards n hn := by
  intro n
  induction n with
  | zero =>
      intro hn
      rfl
  | succ n ih =>
      intro hn
      apply congrArg₂ (fun a f => (⟨a, f⟩ : FiniteBanditModel.RunPrefix p.m p.K (n + 1)))
      · funext s i
        cases s using Fin.lastCases with
        | cast s =>
            simp only [Fin.snoc_castSucc]
            exact congrArg (fun q : FiniteBanditModel.RunPrefix p.m p.K n => q.action s i)
              (ih (Nat.le_of_succ_le hn))
        | last =>
            simp only [Fin.snoc_last, fixedAssignmentDecision,
              FixedAssignmentRegret.fixedAssignmentPolicy]
      · funext s i
        cases s using Fin.lastCases with
        | cast s =>
            simp only [Fin.snoc_castSucc]
            exact congrArg (fun q : FiniteBanditModel.RunPrefix p.m p.K n => q.feedback s i)
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

/-- The complementary decision has precisely the fixed-assignment regret
under the original role-private product law, also for sizes below the threshold. -/
theorem expectedPrivateRegret_fixedAssignment (p : Parameters)
    (published : PublishedOutput p) (rewards : FiniteBanditModel.RewardMatrix p.T p.K) :
    FiniteHorizonBoundedLocalRollout.expectedPrivateRegret p
      (fixedAssignmentDecision p) (FiniteHorizonRolePrivateLaw.nu p) rewards published =
    FiniteBanditModel.bestFixedMSetComparator (ConstructorDimensions.m_pos p) p.m_lt_K.le rewards -
      FiniteBanditModel.pathwiseCumulativeReward
        (FiniteBanditModel.deterministicRollout
          (FixedAssignmentRegret.fixedAssignmentPolicy (Nat.le_of_lt p.m_lt_K)) ()
          (fun _ : Fin p.m => ()) rewards) := by
  have hpoint (rho : FiniteHorizonBoundedLocalRollout.PrivateProfile p
      (FiniteHorizonRolePrivateLaw.Role p)) :
      FiniteHorizonBoundedLocalRollout.pathwiseRegret p
        (fixedAssignmentDecision p) published rho rewards =
      FiniteBanditModel.bestFixedMSetComparator (ConstructorDimensions.m_pos p) p.m_lt_K.le rewards -
        FiniteBanditModel.pathwiseCumulativeReward
          (FiniteBanditModel.deterministicRollout
            (FixedAssignmentRegret.fixedAssignmentPolicy (Nat.le_of_lt p.m_lt_K)) ()
            (fun _ : Fin p.m => ()) rewards) := by
    change _ - FiniteBanditModel.pathwiseCumulativeReward
      (FiniteHorizonBoundedLocalRollout.boundedLocalPrefix p
        (fixedAssignmentDecision p) published rho rewards p.T (Nat.le_refl p.T)).val = _
    rw [fixedAssignmentPrefix_eq p published rho rewards p.T (Nat.le_refl p.T)]
    rfl
  unfold FiniteHorizonBoundedLocalRollout.expectedPrivateRegret
  calc
    _ = ∫ _rho : FiniteHorizonBoundedLocalRollout.PrivateProfile p
        (FiniteHorizonRolePrivateLaw.Role p),
        (FiniteBanditModel.bestFixedMSetComparator (ConstructorDimensions.m_pos p)
          p.m_lt_K.le rewards - FiniteBanditModel.pathwiseCumulativeReward
            (FiniteBanditModel.deterministicRollout
              (FixedAssignmentRegret.fixedAssignmentPolicy (Nat.le_of_lt p.m_lt_K)) ()
              (fun _ : Fin p.m => ()) rewards))
          ∂FiniteHorizonBoundedLocalRollout.privateProfileLaw p
            (FiniteHorizonRolePrivateLaw.nu p) := by
      apply integral_congr_ae
      exact ae_of_all _ hpoint
    _ = _ := by simp only [integral_const, probReal_univ, one_smul]

/-- Exact coefficient normalization: the full signed learning coefficients
plus the literal stopped-transport budget are the accepted combined budget. -/
theorem learning_transport_eq_combinedBudget (p : Parameters) (eta : ℝ) :
    (2 * Real.log (Nat.choose p.K p.m : ℝ) + (p.m : ℝ) / 16) / eta +
      (16 * (p.m : ℝ) ^ 2 + (16 / 11 : ℝ) * CanonicalRecordingRates.R p +
        32 * (p.m : ℝ) + 1024 * ((p.K - p.m + 1 : ℕ) : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ)) * eta * p.T +
      ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) *
        ((4 * (p.m : ℝ) + 128) * eta * p.T + 2) =
      ReferenceLearningTransportRateDomination.combinedBudget p eta := by
  unfold ReferenceLearningTransportRateDomination.combinedBudget
    CanonicalRecordingRates.gamma CanonicalRecordingRates.beta
  ring

/-- One choice of universal constants gives a measurable own-local policy and
a reward-independent public event on the original complete continuous law.
Every output in that event works simultaneously for every original oblivious
reward matrix. There are no rate, mean, law, history, or large-size premises.

The literal source constants in the branch are `branchConstant C1 hC1 Cb`
and `sizeThreshold C1 hC1 N0`; their exposed bodies take universal maxima
before `p`, without modifying the canonical source rate. -/
theorem exists_uniform_actual_main_regret_bound :
    ∃ C1 : ℝ, ∃ hC1 : 0 < C1, ∃ Cb : ℝ, ∃ N0 : ℕ, ∃ C_star C_h C : ℝ,
      16 ≤ Cb ∧ (2 : ℝ) ^ 20 ≤ C_star ∧ (4096 : ℝ) ≤ C_h ∧ 0 < C ∧
      ∀ p : Parameters,
        (∀ (i : Fin p.m) (t : Fin p.T),
          Measurable (decision C1 hC1 C_star C_h Cb N0 p i t)) ∧
        MeasurableSet (goodPublicEvent C1 hC1 C_star C_h Cb N0 p) ∧
        (publishedOutputMeasure p).real
          (goodPublicEvent C1 hC1 C_star C_h Cb N0 p)ᶜ ≤ 5 / (N p : ℝ) ∧
        ∀ published : PublishedOutput p,
          published ∈ goodPublicEvent C1 hC1 C_star C_h Cb N0 p →
          ∀ rewards : FiniteBanditModel.RewardMatrix p.T p.K,
            FiniteHorizonBoundedLocalRollout.expectedPrivateRegret p
              (decision C1 hC1 C_star C_h Cb N0 p)
              (FiniteHorizonRolePrivateLaw.nu p) rewards published ≤
              C * BootstrapStartupCostScale.Q_boot p := by
  classical
  obtain ⟨C1, hC1, Cb, Nbudget, Cbudget, hCb, hCbudget, hbudget⟩ :=
    ReferenceLearningTransportRateDomination.exists_uniform_tuned_combinedBudget_bound
  obtain ⟨Nmin, hreduce⟩ :=
    ActualBranchedSignedAuxiliaryReduction.exists_universal_Nmin_branchedPublicGood_and_signedAuxiliary_reduction
  let N0 : ℕ := max Nbudget Nmin
  let C_b : ℝ := branchConstant C1 hC1 Cb
  let N₀ : ℕ := sizeThreshold C1 hC1 N0
  let C_star : ℝ := 2 ^ 20
  let C_h : ℝ := 4096
  let A : ℝ := C_star * (5 + 8 * C_h + (4 * C_h + 1) / Real.sqrt C_b)
  let Cconstruction : ℝ := Cbudget + 768 * A + 18
  let Ccomplement : ℝ := max (Real.sqrt C_b) (N₀ : ℝ)
  let C : ℝ := Cconstruction + Ccomplement
  have hC_b : 16 ≤ C_b := hCb.trans (le_max_left _ _)
  have hC_star : (2 : ℝ) ^ 20 ≤ C_star := le_rfl
  have hC_h : (4096 : ℝ) ≤ C_h := le_rfl
  have hC_star2 : 2 ≤ C_star := by norm_num [C_star]
  have hC_h0 : 0 ≤ C_h := by norm_num [C_h]
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hCconstruction : 0 < Cconstruction := by
    dsimp [Cconstruction]
    linarith only [hCbudget, hA]
  have hCcomplement : 0 ≤ Ccomplement :=
    (Real.sqrt_nonneg C_b).trans (le_max_left _ _)
  have hC : 0 < C := add_pos_of_pos_of_nonneg hCconstruction hCcomplement
  have hCcons : Cconstruction ≤ C := le_add_of_nonneg_right hCcomplement
  have hCcomp : Ccomplement ≤ C := le_add_of_nonneg_left hCconstruction.le
  have hNmin : Nmin ≤ N₀ :=
    (le_max_right Nbudget Nmin).trans (le_max_left _ _)
  refine ⟨C1, hC1, Cb, N0, C_star, C_h, C, hCb, hC_star, hC_h, hC, ?_⟩
  intro p
  refine ⟨measurable_decision C1 hC1 C_star C_h Cb N0 p, ?_⟩
  have hQnonneg : 0 ≤ BootstrapStartupCostScale.Q_boot p := by
    unfold BootstrapStartupCostScale.Q_boot
    positivity
  by_cases hbranch : constructionBranch C_b N₀ p
  · let rate := constructionRate C1 hC1 Cb N0 p hbranch
    obtain ⟨hmeas, hfail, hpublic⟩ :=
      hreduce N₀ hNmin C_b C_star C_h hC_b hC_h hC_star p rate
    have hevent := goodPublicEvent_eq_branched_on_construction
      C1 hC1 C_star C_h Cb N0 p hbranch
    have hdecision := decision_eq_branched_on_construction
      C1 hC1 C_star C_h Cb N0 p hbranch
    rw [hevent]
    refine ⟨hmeas, hfail, ?_⟩
    intro published hgood rewards
    rw [hdecision]
    let rounded := RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) rewards
    obtain ⟨S0, _hmax, hphysical⟩ := (hpublic published hgood).1 hbranch rewards
    have hactual := hphysical (zeroControl p)
    have haux :=
      (ReferenceGeneratedCalendarAuxiliaryExpectation.fixedID_integral_signedGap_le_auxiliaryLearningBound
          rate rounded C_star C_h (zeroControl p) published.1 S0).2
    have hauxCombined :
        (∫ w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rounded C_star C_h,
          ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap rate rounded S0
            (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout
              rate rounded C_star C_h (zeroControl p) w).2.2
          ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw
            rate rounded C_star C_h (zeroControl p) published.1) +
          ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) *
            ((4 * (p.m : ℝ) + 128) * rate.eta.val * p.T + 2) ≤
        ReferenceLearningTransportRateDomination.combinedBudget p rate.eta.val +
          (p.m : ℝ) * p.T / (rate.eta.val * D p) +
          (p.m : ℝ) * p.T / (N p : ℝ) ^ 2 := by
      rw [← learning_transport_eq_combinedBudget p rate.eta.val]
      linarith only [haux]
    have hsmall := constructionBranch_mono
      (le_max_left Cb (tuningBranchConstant C1 hC1))
      ((le_max_left Nbudget Nmin).trans (le_max_left N0 (tuningThreshold C1 hC1))) p hbranch
    have hbudgetp := hbudget p hsmall.1 (Nat.cast_le.mp hsmall.2)
    have hbudgetRate :
        ReferenceLearningTransportRateDomination.combinedBudget p rate.eta.val +
          (p.m : ℝ) * p.T / (rate.eta.val * D p) ≤
          Cbudget * BootstrapStartupCostScale.Q_boot p := hbudgetp
    have hstartup := startup_terms_le C_b C_h C_star p hC_b hC_h0 hC_star2 hbranch.1
    have herr := numerical_errors_le p
    have hassembled :
        FiniteHorizonBoundedLocalRollout.expectedPrivateRegret p
          (actualBranchedDecision rate C_star C_h C_b N₀)
          (FiniteHorizonRolePrivateLaw.nu p) rewards published ≤
          Cconstruction * BootstrapStartupCostScale.Q_boot p := by
      dsimp only [Cconstruction]
      change _ ≤ (Cbudget + 768 *
        (C_star * (5 + 8 * C_h + (4 * C_h + 1) / Real.sqrt C_b)) + 18) *
          BootstrapStartupCostScale.Q_boot p
      linarith only [hactual, hauxCombined, hbudgetRate, hstartup, herr]
    exact hassembled.trans (mul_le_mul_of_nonneg_right hCcons hQnonneg)
  · rw [goodPublicEvent_eq_univ_on_complement C1 hC1 C_star C_h Cb N0 p hbranch]
    refine ⟨MeasurableSet.univ, ?_, ?_⟩
    · simp only [Set.compl_univ, measureReal_empty]
      positivity
    · intro published _hgood rewards
      rw [decision_eq_fixed_on_complement C1 hC1 C_star C_h Cb N0 p hbranch,
        expectedPrivateRegret_fixedAssignment]
      have hfixed :=
        SmallRegimeAbsorption.bestFixedMSetComparator_regret_le_complementary_branch_mul_rowConcentrationScale
            C_b (N₀ : ℝ) (by linarith only [hC_b]) (Nat.cast_nonneg N₀)
            p hbranch rewards () (fun _ : Fin p.m => ())
      exact hfixed.trans
        ((mul_le_mul_of_nonneg_left
          (TunedNumericalRemainder.rowConcentrationScale_le_Q_boot p) hCcomplement).trans
          (mul_le_mul_of_nonneg_right hCcomp hQnonneg))

end Bandits.Support.ActualMainRegretLocalPolicyPromotion

end
