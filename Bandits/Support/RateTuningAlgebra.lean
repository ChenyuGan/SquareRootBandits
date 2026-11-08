module

public import Bandits.Support.ConstructorDimensions
public import Mathlib.Analysis.Real.Sqrt

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Conditional scalar algebra for the main regret estimate.

The rate objective follows from the dyadic tuning interval in
`sources/zip4/manuscript/08_main_theorem.tex:4-24`; its use in the main proof,
including the `m T / (η D)` comparison, is at
`sources/zip4/manuscript/08_main_theorem.tex:147-155`. These are internal
conditional inequalities: this module does not construct the source rate or
prove the main regret bound.
-/

public section

namespace Bandits.Support.RateTuningAlgebra

open Bandits.Support.ConstructorDimensions

/-- The square-root product identity for the manuscript's rate scale. -/
theorem sqrt_rate_product_identity {J W T : ℝ}
    (hJ : 0 < J) (hW : 0 < W) (hT : 0 < T) :
    Real.sqrt (J / (W * T)) * (W * T) = Real.sqrt (J * W * T) := by
  have hWT : 0 < W * T := mul_pos hW hT
  have hsWT : 0 < Real.sqrt (W * T) := Real.sqrt_pos.2 hWT
  calc
    Real.sqrt (J / (W * T)) * (W * T) =
        (Real.sqrt J / Real.sqrt (W * T)) * (W * T) := by
          rw [Real.sqrt_div hJ.le]
    _ = Real.sqrt J * Real.sqrt (W * T) := by
          have hroot_sq :
              Real.sqrt (W * T) * Real.sqrt (W * T) = W * T :=
            Real.mul_self_sqrt hWT.le
          calc
            (Real.sqrt J / Real.sqrt (W * T)) * (W * T) =
                (Real.sqrt J / Real.sqrt (W * T)) *
                  (Real.sqrt (W * T) * Real.sqrt (W * T)) := by
                    exact congrArg
                      (fun z => (Real.sqrt J / Real.sqrt (W * T)) * z)
                      hroot_sq.symm
            _ = Real.sqrt J * Real.sqrt (W * T) := by
              rw [div_eq_mul_inv]
              calc
                (Real.sqrt J * (Real.sqrt (W * T))⁻¹) *
                (Real.sqrt (W * T) * Real.sqrt (W * T)) =
                  Real.sqrt J * ((Real.sqrt (W * T))⁻¹ * Real.sqrt (W * T)) *
                    Real.sqrt (W * T) := by ring
                _ = Real.sqrt J * Real.sqrt (W * T) := by
                  rw [inv_mul_cancel₀ hsWT.ne', mul_one]
    _ = Real.sqrt (J * (W * T)) := (Real.sqrt_mul hJ.le (W * T)).symm
    _ = Real.sqrt (J * W * T) := by congr 1; ring

/-- If `η` lies in the source dyadic tuning interval, the two objective terms
sum to at most three times `sqrt (J W T)`. -/
theorem rate_objective_bound {J W T η : ℝ}
    (hJ : 0 < J) (hW : 0 < W) (hT : 0 < T) (hη : 0 < η)
    (hη_lower : (1 / 2 : ℝ) * Real.sqrt (J / (W * T)) < η)
    (hη_upper : η ≤ Real.sqrt (J / (W * T))) :
    J / η + W * η * T ≤ 3 * Real.sqrt (J * W * T) := by
  have hWT : 0 < W * T := mul_pos hW hT
  let q : ℝ := Real.sqrt (J / (W * T))
  let R : ℝ := Real.sqrt (J * W * T)
  have hq : 0 < q := by
    dsimp [q]
    exact Real.sqrt_pos.2 (div_pos hJ hWT)
  have hq_sq : q ^ 2 = J / (W * T) := by
    dsimp [q]
    exact Real.sq_sqrt (div_nonneg hJ.le hWT.le)
  have hscale : q * (W * T) = R := by
    dsimp [q, R]
    exact sqrt_rate_product_identity hJ hW hT
  have hηq : q < 2 * η := by
    change Real.sqrt (J / (W * T)) < 2 * η
    linarith [hη_lower]
  have hJ_decomp : J = q ^ 2 * (W * T) := by
    calc
      J = (J / (W * T)) * (W * T) := (div_mul_cancel₀ J hWT.ne').symm
      _ = q ^ 2 * (W * T) := by rw [← hq_sq]
  have hfirst_mul : J < (2 * R) * η := by
    have hqWT : 0 < q * (W * T) := mul_pos hq hWT
    calc
      J = q * (q * (W * T)) := by rw [hJ_decomp]; ring
      _ < (2 * η) * (q * (W * T)) := mul_lt_mul_of_pos_right hηq hqWT
      _ = (2 * R) * η := by rw [hscale]; ring
  have hfirst : J / η < 2 * R := (div_lt_iff₀ hη).2 hfirst_mul
  have hsecond : W * η * T ≤ R := by
    calc
      W * η * T = η * (W * T) := by ring
      _ ≤ q * (W * T) := mul_le_mul_of_nonneg_right hη_upper hWT.le
      _ = R := hscale
  calc
    J / η + W * η * T ≤ 2 * R + R := add_le_add hfirst.le hsecond
    _ = 3 * Real.sqrt (J * W * T) := by dsimp [R]; ring

/-- Scalar comparison used to remove the constructor's `m T / (η D)` term. -/
theorem penalty_comparison {m T η D J : ℝ}
    (hm : 0 ≤ m) (hT : 0 ≤ T) (hη : 0 < η) (hD : 0 < D)
    (hmT : m * T ≤ J * D) :
    m * T / (η * D) ≤ J / η := by
  have hMT : 0 ≤ m * T := mul_nonneg hm hT
  have hdiv : m * T / D ≤ J := (div_le_iff₀ hD).2 hmT
  have hdiv_nonneg : 0 ≤ m * T / D := div_nonneg hMT hD.le
  have hJ_nonneg : 0 ≤ J := hdiv_nonneg.trans hdiv
  calc
    m * T / (η * D) = (m * T / D) / η := by
      rw [mul_comm η D, ← div_div]
    _ ≤ J / η := div_le_div₀ hJ_nonneg hdiv hη le_rfl

/-- The accepted constructor dimensions and `J ≥ m` supply the comparison
premise internally, using the actual dyadic denominator `D` and the source
size relation `N < D`. -/
theorem parameter_penalty_comparison (p : Parameters) {J η : ℝ}
    (hJm : (p.m : ℝ) ≤ J) (hη : 0 < η) :
    (p.m : ℝ) * (p.T : ℝ) / (η * (D p : ℝ)) ≤ J / η := by
  have hm : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
  have hT : 0 < (p.T : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.T_pos p)
  have hD : 0 < (D p : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.D_pos p)
  have hfactor : 1 ≤ 2 * p.K := by
    calc
      1 ≤ 2 := by norm_num
      _ ≤ 2 * p.K := Nat.mul_le_mul_left 2
        (Nat.succ_le_of_lt (ConstructorDimensions.K_pos p))
  have hm_factor : p.m ≤ (2 * p.K) * p.m := by
    calc
      p.m = 1 * p.m := by simp
      _ ≤ (2 * p.K) * p.m := Nat.mul_le_mul_right p.m hfactor
  have hmT_le_N : p.m * p.T ≤ N p := by
    change p.m * p.T ≤ 2 * p.K * p.m * (p.T + 1)
    calc
      p.m * p.T ≤ p.m * (p.T + 1) :=
        Nat.mul_le_mul_left p.m (Nat.le_succ p.T)
      _ ≤ (2 * p.K * p.m) * (p.T + 1) :=
        Nat.mul_le_mul_right (p.T + 1) hm_factor
  have hmT_le_D_nat : p.m * p.T ≤ D p :=
    hmT_le_N.trans (ConstructorDimensions.N_lt_D p).le
  have hmT_le_D : (p.m : ℝ) * (p.T : ℝ) ≤ (D p : ℝ) := by
    exact_mod_cast hmT_le_D_nat
  have hm_one : (1 : ℝ) ≤ (p.m : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (ConstructorDimensions.m_pos p))
  have hJ_one : (1 : ℝ) ≤ J := hm_one.trans hJm
  have hD_le_JD : (D p : ℝ) ≤ J * (D p : ℝ) := by
    calc
      (D p : ℝ) = 1 * (D p : ℝ) := by ring
      _ ≤ J * (D p : ℝ) := mul_le_mul_of_nonneg_right hJ_one hD.le
  have hmT_le_JD :
      (p.m : ℝ) * (p.T : ℝ) ≤ J * (D p : ℝ) := hmT_le_D.trans hD_le_JD
  exact penalty_comparison hm.le hT.le hη hD hmT_le_JD

end Bandits.Support.RateTuningAlgebra
