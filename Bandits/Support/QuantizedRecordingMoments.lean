/-
Copyright (c) 2026 Bandits formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Moments of a quantized recorded reward

The scalar estimate is the floor expression in
`sources/zip4/manuscript/04_slow_fast_learner.tex:151-155`. Its first and
second moment bounds are the arithmetic component of
`sources/zip4/manuscript/04_slow_fast_learner.tex:256-264`.

The finite Bernoulli sums below describe the scalar weighting of a recorded
value. They do not formalize the manuscript's conditional recording law.
-/

public section

namespace Bandits.Support.QuantizedRecordingMoments

open scoped BigOperators

/-- The exact natural-valued quantization index from the marker formula. -/
@[expose] noncomputable def quantizedIndex (D : ℕ) (eta xi r : ℝ) : ℕ :=
  Nat.floor (((D : ℝ) * eta * r) / xi)

/-- The quantized reward value before multiplication by the recording indicator. -/
@[expose] noncomputable def quantizedValue (D : ℕ) (eta xi r : ℝ) : ℝ :=
  (quantizedIndex D eta xi r : ℝ) / (eta * (D : ℝ))

/-- The two probabilities in a finite Bernoulli law, indexed by `Bool`. -/
@[expose] def bernoulliWeight (xi : ℝ) (recorded : Bool) : ℝ :=
  if recorded then xi else 1 - xi

/-- The scalar estimate produced by a Bernoulli recording indicator. -/
@[expose] def bernoulliRecordedValue (v : ℝ) (recorded : Bool) : ℝ :=
  if recorded then v else 0

/-- The finite Bernoulli-weighted first moment of a recorded value. -/
@[expose] def bernoulliFirstMoment (xi v : ℝ) : ℝ :=
  ∑ recorded : Bool, bernoulliWeight xi recorded * bernoulliRecordedValue v recorded

/-- The finite Bernoulli-weighted second moment of a recorded value. -/
@[expose] def bernoulliSecondMoment (xi v : ℝ) : ℝ :=
  ∑ recorded : Bool,
    bernoulliWeight xi recorded * (bernoulliRecordedValue v recorded) ^ 2

/-- The floor index lies below its argument and less than one above it. -/
theorem quantizedIndex_floorBounds (D : ℕ) (eta xi r : ℝ)
    (hD : 0 < D) (heta : 0 < eta) (hxi : 0 < xi) (hr : 0 ≤ r) :
    (quantizedIndex D eta xi r : ℝ) ≤ ((D : ℝ) * eta * r) / xi ∧
      ((D : ℝ) * eta * r) / xi < (quantizedIndex D eta xi r : ℝ) + 1 := by
  have hDreal : 0 < (D : ℝ) := Nat.cast_pos.mpr hD
  have hx : 0 ≤ ((D : ℝ) * eta * r) / xi :=
    div_nonneg (mul_nonneg (mul_nonneg hDreal.le heta.le) hr) hxi.le
  constructor
  · simpa [quantizedIndex] using Nat.floor_le hx
  · simpa [quantizedIndex] using Nat.lt_floor_add_one (((D : ℝ) * eta * r) / xi)

/-- Under the positive parameter assumptions, the scaled denominator is positive. -/
theorem quantizedDenominator_pos (D : ℕ) (eta : ℝ)
    (hD : 0 < D) (heta : 0 < eta) :
    0 < eta * (D : ℝ) :=
  mul_pos heta (Nat.cast_pos.mpr hD)

theorem quantizedValue_nonneg (D : ℕ) (eta xi r : ℝ) (heta : 0 < eta) :
    0 ≤ quantizedValue D eta xi r := by
  unfold quantizedValue
  exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg heta.le (Nat.cast_nonneg _))

private theorem quantizedValue_le_reward_div (D : ℕ) (eta xi r : ℝ)
    (hD : 0 < D) (heta : 0 < eta) (hxi : 0 < xi)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    quantizedValue D eta xi r ≤ r / xi := by
  have hden : 0 < eta * (D : ℝ) := quantizedDenominator_pos D eta hD heta
  have hfloor := quantizedIndex_floorBounds D eta xi r hD heta hxi hr.1
  calc
    quantizedValue D eta xi r ≤
        (((D : ℝ) * eta * r) / xi) / (eta * (D : ℝ)) :=
      div_le_div_of_nonneg_right hfloor.1 hden.le
    _ = r / xi := by
      field_simp [ne_of_gt hden, ne_of_gt hxi]

theorem quantizedValue_firstMoment_le (D : ℕ) (eta xi r : ℝ)
    (hD : 0 < D) (heta : 0 < eta) (hxi : 0 < xi)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    xi * quantizedValue D eta xi r ≤ r := by
  calc
    xi * quantizedValue D eta xi r ≤ xi * (r / xi) :=
      mul_le_mul_of_nonneg_left
        (quantizedValue_le_reward_div D eta xi r hD heta hxi hr) hxi.le
    _ = r := by
      field_simp [ne_of_gt hxi]

theorem quantizedValue_roundingError (D : ℕ) (eta xi r : ℝ)
    (hD : 0 < D) (heta : 0 < eta) (hxi : 0 < xi)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    r - xi / (eta * (D : ℝ)) ≤ xi * quantizedValue D eta xi r := by
  let k : ℕ := quantizedIndex D eta xi r
  let den : ℝ := eta * (D : ℝ)
  have hden : 0 < den := by
    dsimp [den]
    exact quantizedDenominator_pos D eta hD heta
  have hfloor := quantizedIndex_floorBounds D eta xi r hD heta hxi hr.1
  have hscaled : (D : ℝ) * eta * r < xi * ((k : ℝ) + 1) := by
    have h := (div_lt_iff₀ hxi).mp hfloor.2
    simpa [k, mul_comm] using h
  have hscaled_div :
      (((D : ℝ) * eta * r) / den) < (xi * ((k : ℝ) + 1)) / den :=
    div_lt_div_of_pos_right hscaled hden
  have hleft : ((D : ℝ) * eta * r) / den = r := by
    dsimp [den]
    field_simp [ne_of_gt (quantizedDenominator_pos D eta hD heta)]
  have hright : (xi * ((k : ℝ) + 1)) / den =
      xi * ((k : ℝ) / den) + xi / den := by
    dsimp [den]
    field_simp [ne_of_gt (quantizedDenominator_pos D eta hD heta)]
  have hsum : r < xi * ((k : ℝ) / den) + xi / den := by
    calc
      r = ((D : ℝ) * eta * r) / den := hleft.symm
      _ < (xi * ((k : ℝ) + 1)) / den := hscaled_div
      _ = xi * ((k : ℝ) / den) + xi / den := hright
  have hvalue : quantizedValue D eta xi r = (k : ℝ) / den := by
    simp [quantizedValue, k, den]
  rw [hvalue]
  linarith

theorem quantizedValue_secondMoment_le (D : ℕ) (eta xi r : ℝ)
    (hD : 0 < D) (heta : 0 < eta) (hxi : 0 < xi)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    xi * (quantizedValue D eta xi r) ^ 2 ≤ r ^ 2 / xi := by
  have hv_nonneg := quantizedValue_nonneg D eta xi r heta
  have hv_le := quantizedValue_le_reward_div D eta xi r hD heta hxi hr
  calc
    xi * (quantizedValue D eta xi r) ^ 2 =
        (xi * quantizedValue D eta xi r) * quantizedValue D eta xi r := by ring
    _ ≤ r * quantizedValue D eta xi r :=
      mul_le_mul_of_nonneg_right (quantizedValue_firstMoment_le D eta xi r
        hD heta hxi hr) hv_nonneg
    _ ≤ r * (r / xi) := mul_le_mul_of_nonneg_left hv_le hr.1
    _ = r ^ 2 / xi := by
      field_simp [ne_of_gt hxi]

theorem quantizedValue_le_inv_of_beta_le (D : ℕ) (eta xi r beta : ℝ)
    (hD : 0 < D) (heta : 0 < eta) (hxi : 0 < xi)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) (hbeta : 0 < beta) (hbetaxi : beta ≤ xi) :
    quantizedValue D eta xi r ≤ 1 / beta := by
  calc
    quantizedValue D eta xi r ≤ r / xi :=
      quantizedValue_le_reward_div D eta xi r hD heta hxi hr
    _ ≤ 1 / xi := div_le_div_of_nonneg_right hr.2 hxi.le
    _ ≤ 1 / beta := one_div_le_one_div_of_le hbeta hbetaxi

/-- A Bernoulli weight is nonnegative for a probability in `[0,1]`. -/
theorem bernoulliWeight_nonneg (xi : ℝ) (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (recorded : Bool) :
    0 ≤ bernoulliWeight xi recorded := by
  cases recorded <;> simp [bernoulliWeight] <;> linarith

/-- The two Bernoulli weights form a probability mass on `Bool`. -/
theorem bernoulliWeight_sum (xi : ℝ) :
    (∑ recorded : Bool, bernoulliWeight xi recorded) = 1 := by
  simp [bernoulliWeight]

/-- The finite Bernoulli-weighted first moment is exactly `xi * v`. -/
theorem bernoulliFirstMoment_eq (xi v : ℝ) :
    bernoulliFirstMoment xi v = xi * v := by
  simp [bernoulliFirstMoment, bernoulliWeight, bernoulliRecordedValue]

/-- The finite Bernoulli-weighted second moment is exactly `xi * v^2`. -/
theorem bernoulliSecondMoment_eq (xi v : ℝ) :
    bernoulliSecondMoment xi v = xi * v ^ 2 := by
  simp [bernoulliSecondMoment, bernoulliWeight, bernoulliRecordedValue]

/-- In the Bernoulli interpretation, the quantized first moment is bounded by `r`. -/
theorem bernoulliFirstMoment_quantized_le (D : ℕ) (eta xi r : ℝ)
    (hD : 0 < D) (heta : 0 < eta) (hxi : 0 < xi)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    bernoulliFirstMoment xi (quantizedValue D eta xi r) ≤ r := by
  rw [bernoulliFirstMoment_eq]
  exact quantizedValue_firstMoment_le D eta xi r hD heta hxi hr

/-- In the Bernoulli interpretation, the quantized second moment has the source bound. -/
theorem bernoulliSecondMoment_quantized_le (D : ℕ) (eta xi r : ℝ)
    (hD : 0 < D) (heta : 0 < eta) (hxi : 0 < xi)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    bernoulliSecondMoment xi (quantizedValue D eta xi r) ≤ r ^ 2 / xi := by
  rw [bernoulliSecondMoment_eq]
  exact quantizedValue_secondMoment_le D eta xi r hD heta hxi hr

end Bandits.Support.QuantizedRecordingMoments

end
