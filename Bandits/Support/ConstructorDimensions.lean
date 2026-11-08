module

public import Mathlib.Analysis.SpecialFunctions.Log.Base

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Literal parameter dimensions for the public constructor.

The only input data are the source parameters `K`, `m`, and `T`, with
`2 ≤ m < K` and `1 ≤ T`. The dimensions themselves are defined here, rather
than carried as fields or supplied as hypotheses. Source: introduction,
`sources/zip4/manuscript/01_introduction.tex:20-40`; public table parameters,
`sources/zip4/manuscript/appendix_b_communication.tex:7-15`; and whole-row
counting bounds,
`sources/zip4/manuscript/08_main_theorem.tex:55-59`.
-/

public section

namespace Bandits.Support.ConstructorDimensions

/-- The manuscript's constructor domain, with no derived dimension fields.
Source: `sources/zip4/manuscript/01_introduction.tex:20`. -/
structure Parameters where
  K : ℕ
  m : ℕ
  T : ℕ
  two_le_m : 2 ≤ m
  m_lt_K : m < K
  one_le_T : 1 ≤ T

/-- The source's natural size parameter `N = 2 K m (T + 1)`.
Source: `sources/zip4/manuscript/01_introduction.tex:38-40`. -/
@[expose] def N (p : Parameters) : ℕ := 2 * p.K * p.m * (p.T + 1)

/-- The source's bit length, represented by the natural ceiling logarithm.
Source: `sources/zip4/manuscript/01_introduction.tex:38-40`. -/
@[expose] def b_N (p : Parameters) : ℕ := Nat.clog 2 (N p + 1)

/-- The source's dyadic score denominator `D = 2 ^ b_N`.
Source: `sources/zip4/manuscript/appendix_b_communication.tex:7-8`. -/
@[expose] def D (p : Parameters) : ℕ := 2 ^ b_N p

/-- The source's number of complete rows, using the actual natural ceiling.
Source: `sources/zip4/manuscript/appendix_b_communication.tex:13`. -/
@[expose] noncomputable def M (p : Parameters) : ℕ :=
  ⌈(8 : ℝ) * (p.T : ℝ) ^ 2 / ((p.m : ℝ) * (b_N p : ℝ))⌉₊

theorem K_pos (p : Parameters) : 0 < p.K := by
  exact lt_trans (lt_of_lt_of_le Nat.zero_lt_two p.two_le_m) p.m_lt_K

theorem m_pos (p : Parameters) : 0 < p.m :=
  Nat.zero_lt_two.trans_le p.two_le_m

theorem T_pos (p : Parameters) : 0 < p.T :=
  Nat.zero_lt_one.trans_le p.one_le_T

/-- `N` is positive throughout the manuscript parameter domain. -/
theorem N_pos (p : Parameters) : 0 < N p := by
  change 0 < 2 * p.K * p.m * (p.T + 1)
  exact Nat.mul_pos
    (Nat.mul_pos (Nat.mul_pos (by decide) (K_pos p)) (m_pos p))
    (Nat.zero_lt_succ p.T)

/-- `b_N` is positive, since `N + 1 > 1`. -/
theorem b_N_pos (p : Parameters) : 0 < b_N p := by
  change 0 < Nat.clog 2 (N p + 1)
  exact Nat.clog_pos (by decide) (Nat.succ_lt_succ (N_pos p))

/-- `D` is positive. -/
theorem D_pos (p : Parameters) : 0 < D p := by
  change 0 < 2 ^ b_N p
  exact Nat.pow_pos (by decide)

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow : 1 ≤ 2 ^ n := Nat.succ_le_of_lt (Nat.pow_pos (by decide))
      calc
        n + 1 ≤ 2 ^ n + 1 := Nat.add_le_add_right ih 1
        _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add_left hpow (2 ^ n)
        _ = 2 ^ (n + 1) := by rw [pow_succ, Nat.mul_two]

/-- The bit length is at most its dyadic denominator. -/
theorem b_N_le_D (p : Parameters) : b_N p ≤ D p := by
  change b_N p ≤ 2 ^ b_N p
  exact nat_le_two_pow _

/-- The source ceiling-log notation agrees with the natural ceiling of the
real logarithm. This is Mathlib's `Real.natCeil_logb_natCast` identity. -/
theorem b_N_eq_real_ceiling_log (p : Parameters) :
    b_N p = ⌈Real.logb 2 ((N p + 1 : ℕ) : ℝ)⌉₊ := by
  change Nat.clog 2 (N p + 1) =
    ⌈Real.logb 2 ((N p + 1 : ℕ) : ℝ)⌉₊
  exact (Real.natCeil_logb_natCast 2 (N p + 1)).symm

/-- The ceiling logarithm's defining power dominates `N + 1`, so in
particular `N < D`. -/
theorem N_lt_D (p : Parameters) : N p < D p := by
  have hpow : N p + 1 ≤ 2 ^ Nat.clog 2 (N p + 1) :=
    Nat.le_pow_clog (by decide) (N p + 1)
  change N p < 2 ^ Nat.clog 2 (N p + 1)
  exact Nat.lt_of_succ_le hpow

/-- The source constraints make the constructor's natural size dominate `K`.
Source: `sources/zip4/manuscript/01_introduction.tex:20,38-40`. -/
theorem K_le_N (p : Parameters) : p.K ≤ N p := by
  have hm : 1 ≤ p.m := (by decide : 1 ≤ 2).trans p.two_le_m
  have hT : 1 ≤ p.T + 1 := Nat.le_add_left 1 p.T
  change p.K ≤ 2 * p.K * p.m * (p.T + 1)
  calc
    p.K = 1 * p.K := by simp
    _ ≤ 2 * p.K := Nat.mul_le_mul_right p.K (by decide : 1 ≤ 2)
    _ ≤ (2 * p.K) * p.m := le_mul_of_one_le_right' hm
    _ ≤ ((2 * p.K) * p.m) * (p.T + 1) := le_mul_of_one_le_right' hT

/-- The source arm count fits below the dyadic denominator. -/
theorem K_le_D (p : Parameters) : p.K ≤ D p :=
  (K_le_N p).trans (N_lt_D p).le

private theorem rateNumerator_pos (p : Parameters) :
    0 < (8 : ℝ) * (p.T : ℝ) ^ 2 := by
  exact mul_pos (by norm_num) (pow_pos (Nat.cast_pos.mpr (T_pos p)) 2)

private theorem rateDenominator_pos (p : Parameters) :
    0 < (p.m : ℝ) * (b_N p : ℝ) := by
  exact mul_pos (Nat.cast_pos.mpr (m_pos p)) (Nat.cast_pos.mpr (b_N_pos p))

/-- The actual natural ceiling makes the row count positive. -/
theorem M_pos (p : Parameters) : 0 < M p := by
  have hrate :
      0 < (8 : ℝ) * (p.T : ℝ) ^ 2 / ((p.m : ℝ) * (b_N p : ℝ)) :=
    div_pos (rateNumerator_pos p) (rateDenominator_pos p)
  have hM : 1 ≤ M p := by
    change 1 ≤
      ⌈(8 : ℝ) * (p.T : ℝ) ^ 2 / ((p.m : ℝ) * (b_N p : ℝ))⌉₊
    rw [Nat.one_le_ceil_iff]
    exact hrate
  exact Nat.zero_lt_one.trans_le hM

/-- The source row count is at least its real rate before rounding, by the
defining lower-bound property of `Nat.ceil`. -/
theorem M_real_lower_bound (p : Parameters) :
    (8 : ℝ) * (p.T : ℝ) ^ 2 / ((p.m : ℝ) * (b_N p : ℝ)) ≤ (M p : ℝ) := by
  change (8 : ℝ) * (p.T : ℝ) ^ 2 / ((p.m : ℝ) * (b_N p : ℝ)) ≤
    (⌈(8 : ℝ) * (p.T : ℝ) ^ 2 / ((p.m : ℝ) * (b_N p : ℝ))⌉₊ : ℝ)
  exact Nat.le_ceil _

private theorem log_two_le_one : Real.log 2 ≤ 1 := by
  calc
    Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    _ = 1 := by norm_num

/-- The natural logarithm of `2D` is at most `2 b_N`. -/
theorem log_two_mul_D_le (p : Parameters) :
    Real.log (2 * (D p : ℝ)) ≤ 2 * (b_N p : ℝ) := by
  have hlogD : Real.log (D p : ℝ) = (b_N p : ℝ) * Real.log 2 := by
    rw [D, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  have hmul : Real.log (2 * (D p : ℝ)) =
      Real.log 2 + (b_N p : ℝ) * Real.log 2 := by
    rw [Real.log_mul (by norm_num) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D_pos p))), hlogD]
  calc
    Real.log (2 * (D p : ℝ)) = Real.log 2 + (b_N p : ℝ) * Real.log 2 := hmul
    _ ≤ 1 + (b_N p : ℝ) := by
      apply add_le_add log_two_le_one
      exact (mul_le_mul_of_nonneg_left log_two_le_one (Nat.cast_nonneg _)).trans_eq (by simp)
    _ ≤ 2 * (b_N p : ℝ) := by
      have hb : (1 : ℝ) ≤ (b_N p : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (b_N_pos p)
      linarith

/-- The source logarithm of `D + 1` is at most `2 b_N`.
Source: `sources/zip4/manuscript/08_main_theorem.tex:55-59`. -/
theorem log_D_add_one_le (p : Parameters) :
    Real.log ((D p : ℝ) + 1) ≤ 2 * (b_N p : ℝ) := by
  have hDpos : 0 < (D p : ℝ) := Nat.cast_pos.mpr (D_pos p)
  have hDge : 1 ≤ (D p : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (D_pos p)
  have harg : (D p : ℝ) + 1 ≤ 2 * (D p : ℝ) := by
    calc
      (D p : ℝ) + 1 ≤ (D p : ℝ) + (D p : ℝ) := add_le_add_right hDge _
      _ = 2 * (D p : ℝ) := by rw [two_mul]
  calc
    Real.log ((D p : ℝ) + 1) ≤ Real.log (2 * (D p : ℝ)) :=
      Real.log_le_log (add_pos hDpos zero_lt_one) harg
    _ ≤ 2 * (b_N p : ℝ) := log_two_mul_D_le p

/-- The source logarithm of `2N` is at most `2 b_N`.
Source: `sources/zip4/manuscript/08_main_theorem.tex:55-59`. -/
theorem log_two_mul_N_le (p : Parameters) :
    Real.log (2 * (N p : ℝ)) ≤ 2 * (b_N p : ℝ) := by
  have hNpos : 0 < (N p : ℝ) := Nat.cast_pos.mpr (N_pos p)
  have hND : (N p : ℝ) ≤ (D p : ℝ) := Nat.cast_le.mpr (N_lt_D p).le
  have harg : 2 * (N p : ℝ) ≤ 2 * (D p : ℝ) :=
    mul_le_mul_of_nonneg_left hND (by norm_num)
  calc
    Real.log (2 * (N p : ℝ)) ≤ Real.log (2 * (D p : ℝ)) :=
      Real.log_le_log (mul_pos (by norm_num) hNpos) harg
    _ ≤ 2 * (b_N p : ℝ) := log_two_mul_D_le p

/-- The source parameter domain implies `K T ≥ 1`, with casts made explicit. -/
theorem KT_ge_one (p : Parameters) : 1 ≤ (p.K : ℝ) * (p.T : ℝ) := by
  have hK : (1 : ℝ) ≤ (p.K : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (K_pos p)
  have hT : (1 : ℝ) ≤ (p.T : ℝ) := by
    exact_mod_cast p.one_le_T
  calc
    (1 : ℝ) = 1 * 1 := by norm_num
    _ ≤ (p.K : ℝ) * (p.T : ℝ) :=
      mul_le_mul hK hT (by norm_num) (by norm_num)

/-- The exact logarithmic counting input used by the whole-row union bound.
All casts are explicit, and `K T ≥ 1` is derived from the source domain.
Source: `sources/zip4/manuscript/08_main_theorem.tex:55-59`. -/
theorem whole_row_log_count_bound (p : Parameters) :
    ((p.K : ℝ) * (p.T : ℝ)) * Real.log ((D p : ℝ) + 1) +
        Real.log (2 * (N p : ℝ)) ≤
      4 * ((p.K : ℝ) * (p.T : ℝ)) * (b_N p : ℝ) := by
  have hKT := KT_ge_one p
  have hscale : 1 ≤ (p.K : ℝ) * (p.T : ℝ) := hKT
  have hb_nonneg : (0 : ℝ) ≤ 2 * (b_N p : ℝ) :=
    mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hfirst := mul_le_mul_of_nonneg_left (log_D_add_one_le p)
    (mul_nonneg (Nat.cast_nonneg p.K) (Nat.cast_nonneg p.T))
  have hsecond : 2 * (b_N p : ℝ) ≤
      ((p.K : ℝ) * (p.T : ℝ)) * (2 * (b_N p : ℝ)) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hscale hb_nonneg
  calc
    ((p.K : ℝ) * (p.T : ℝ)) * Real.log ((D p : ℝ) + 1) +
        Real.log (2 * (N p : ℝ)) ≤
      ((p.K : ℝ) * (p.T : ℝ)) * (2 * (b_N p : ℝ)) +
        ((p.K : ℝ) * (p.T : ℝ)) * (2 * (b_N p : ℝ)) :=
          add_le_add hfirst ((log_two_mul_N_le p).trans hsecond)
    _ = 4 * ((p.K : ℝ) * (p.T : ℝ)) * (b_N p : ℝ) := by ring

end Bandits.Support.ConstructorDimensions
