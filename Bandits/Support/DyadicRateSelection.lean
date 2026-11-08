/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.DyadicEnvelope

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Largest dyadic rate below a positive cutoff

This module provides a generic dyadic cutoff selector for the rational tuning
step in `sources/zip4/manuscript/08_main_theorem.tex:7-24`. It uses the accepted
dyadic ceiling at the reciprocal cutoff. The construction-branch feasibility
bound and the canonical `J` and `W` constants remain separate obligations.
-/

public section

namespace Bandits.Support.DyadicRateSelection

/-- A genuine positive real cutoff, so rate selection has no zero fallback. -/
abbrev PositiveCutoff := {x : ℝ // 0 < x}

/-- The reciprocal of the accepted dyadic ceiling at the reciprocal cutoff. -/
@[expose] noncomputable def dyadicRate (x : PositiveCutoff) : ℝ :=
  1 / DyadicEnvelope.dyadicCeiling (1 / x.1)

/-- The reciprocal-ceiling definition is exactly an integer power of two. -/
theorem dyadicRate_eq_intPower (x : PositiveCutoff) :
    dyadicRate x =
      (2 : ℝ) ^ (-Int.ceil (Real.logb 2 (1 / x.1))) := by
  change 1 / ((2 : ℝ) ^ (Int.ceil (Real.logb 2 (1 / x.1)) : ℝ)) = _
  rw [one_div, Real.rpow_intCast, zpow_neg]

/-- The selected rate lies strictly above half the cutoff and at or below it. -/
theorem dyadicRate_bounds (x : PositiveCutoff) :
    x.1 / 2 < dyadicRate x ∧ dyadicRate x ≤ x.1 := by
  let y : ℝ := 1 / x.1
  let c : ℝ := DyadicEnvelope.dyadicCeiling y
  have hy : 0 < y := by
    dsimp [y]
    exact one_div_pos.mpr x.2
  have hc := DyadicEnvelope.dyadicCeiling_bounds hy
  have hcpos : 0 < c := by
    dsimp [c]
    exact hy.trans_le hc.1
  have hleft : 1 / (2 * y) = x.1 / 2 := by
    dsimp [y]
    field_simp [ne_of_gt x.2]
  have hright : 1 / y = x.1 := by
    dsimp [y]
    exact one_div_one_div x.1
  constructor
  · change x.1 / 2 < 1 / c
    rw [← hleft]
    exact one_div_lt_one_div_of_lt hcpos hc.2
  · change 1 / c ≤ x.1
    rw [← hright]
    exact one_div_le_one_div_of_le hy hc.1

/-- Every integer power of two below the cutoff is at most the selected rate. -/
theorem dyadicRate_maximal (x : PositiveCutoff) (z : ℤ)
    (hz : (2 : ℝ) ^ z ≤ x.1) :
    (2 : ℝ) ^ z ≤ dyadicRate x := by
  let y : ℝ := 1 / x.1
  let c : ℝ := DyadicEnvelope.dyadicCeiling y
  let k : ℤ := Int.ceil (Real.logb 2 y)
  have hy : 0 < y := by
    dsimp [y]
    exact one_div_pos.mpr x.2
  have hc := DyadicEnvelope.dyadicCeiling_bounds hy
  have hcpos : 0 < c := by
    dsimp [c]
    exact hy.trans_le hc.1
  have hy_pow : y ≤ (2 : ℝ) ^ (-z) := by
    calc
      y = 1 / x.1 := rfl
      _ ≤ 1 / ((2 : ℝ) ^ z) :=
        one_div_le_one_div_of_le (zpow_pos (by norm_num) z) hz
      _ = (2 : ℝ) ^ (-z) := by rw [one_div, zpow_neg]
  have hlog : Real.logb 2 y ≤ ((-z : ℤ) : ℝ) :=
    (Real.logb_le_iff_le_rpow one_lt_two hy).2 <| by
      simpa only [Real.rpow_intCast] using hy_pow
  have hk : k ≤ -z := by
    dsimp [k]
    exact Int.ceil_le.mpr hlog
  have hc_eq : c = (2 : ℝ) ^ (k : ℝ) := by
    dsimp [c, k, DyadicEnvelope.dyadicCeiling]
  have hk_real : (k : ℝ) ≤ ((-z : ℤ) : ℝ) := by
    exact_mod_cast hk
  have hc_pow : c ≤ (2 : ℝ) ^ (-z) := by
    rw [hc_eq]
    rw [← Real.rpow_intCast]
    exact Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) one_lt_two.le hk_real
  have hinv : 1 / ((2 : ℝ) ^ (-z)) ≤ 1 / c :=
    one_div_le_one_div_of_le hcpos hc_pow
  change (2 : ℝ) ^ z ≤ 1 / c
  calc
    (2 : ℝ) ^ z = 1 / ((2 : ℝ) ^ (-z)) := by
      rw [one_div, zpow_neg, inv_inv]
    _ ≤ 1 / c := hinv

/-- If the cutoff is at least the reciprocal of `2^b`, then the selected
integer power becomes a natural number after multiplication by `2^b`.
The exponent lower bound is proved from the cutoff premise. -/
theorem dyadicRate_mul_pow_two_isNat (x : PositiveCutoff) (b : ℕ)
    (hx : 1 / ((2 ^ b : ℕ) : ℝ) ≤ x.1) :
    ∃ n : ℕ, dyadicRate x * ((2 ^ b : ℕ) : ℝ) = (n : ℝ) := by
  let y : ℝ := 1 / x.1
  let d : ℝ := ((2 ^ b : ℕ) : ℝ)
  let k : ℤ := Int.ceil (Real.logb 2 y)
  let q : ℤ := (b : ℤ) - k
  have hy : 0 < y := by
    dsimp [y]
    exact one_div_pos.mpr x.2
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hy_d : y ≤ d := by
    calc
      y = 1 / x.1 := rfl
      _ ≤ 1 / (1 / d) :=
        one_div_le_one_div_of_le (one_div_pos.mpr hd) hx
      _ = d := one_div_one_div d
  have hlog : Real.logb 2 y ≤ (b : ℝ) := by
    apply (Real.logb_le_iff_le_rpow one_lt_two hy).2
    calc
      y ≤ d := hy_d
      _ = (2 : ℝ) ^ b := by
        dsimp [d]
        norm_cast
      _ = (2 : ℝ) ^ (b : ℝ) := by rw [Real.rpow_natCast]
  have hk : k ≤ (b : ℤ) := by
    dsimp [k]
    exact Int.ceil_le.mpr hlog
  have hq : 0 ≤ q := by
    dsimp [q]
    exact sub_nonneg.mpr hk
  have heta : dyadicRate x = (2 : ℝ) ^ (-k) := by
    dsimp [k, y]
    exact dyadicRate_eq_intPower x
  have hd_pow : d = (2 : ℝ) ^ (b : ℤ) := by
    calc
      d = (2 : ℝ) ^ b := by
        dsimp [d]
        norm_cast
      _ = (2 : ℝ) ^ (b : ℤ) := by rw [zpow_natCast]
  have hproduct : dyadicRate x * d = (2 : ℝ) ^ q := by
    rw [heta, hd_pow]
    calc
      (2 : ℝ) ^ (-k) * (2 : ℝ) ^ (b : ℤ) =
          (2 : ℝ) ^ ((-k) + (b : ℤ)) := by
        rw [zpow_add₀ (by norm_num) (-k) (b : ℤ)]
      _ = (2 : ℝ) ^ q := by
        congr 1
        dsimp [q]
        ring
  have hnat : (2 : ℝ) ^ q = ((2 ^ q.toNat : ℕ) : ℝ) := by
    conv_lhs => rw [← Int.toNat_of_nonneg hq]
    rw [zpow_natCast]
    norm_cast
  refine ⟨2 ^ q.toNat, ?_⟩
  calc
    dyadicRate x * ((2 ^ b : ℕ) : ℝ) = (2 : ℝ) ^ q := by
      simpa only [d] using hproduct
    _ = ((2 ^ q.toNat : ℕ) : ℝ) := hnat

end Bandits.Support.DyadicRateSelection
