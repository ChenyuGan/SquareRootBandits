/- Deterministic bootstrap gain weights on the literal dyadic grid. -/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Grid-rounded bootstrap gain weights

Literal held-arm update from `sources/zip4/manuscript/07_public_setup.tex:27-38`
and its deterministic potential argument from
`sources/zip4/manuscript/appendix_b_communication.tex:524-568`.

The update permission includes activity and the stopping decision. Inputs are
natural block gains bounded by `B`; this module does not construct observations,
random draws, stopping times, or bootstrap success. Dimensions are internal
natural inputs, with no identification with the canonical constructor yet.
-/

public section

namespace Bandits.Support.BootstrapWeightPotential

open Finset

/-- Integer denominator of the weight grid. -/
@[expose] def scale (b : ℕ) : ℕ := 2 ^ (4 * b)

/-- The quantum `2^(-4b)`, written as a reciprocal natural power. -/
@[expose] noncomputable def epsilon (b : ℕ) : ℝ := 1 / (scale b : ℝ)

/-- Real weights represented by natural numerators on the dyadic grid. -/
@[expose] noncomputable def weight {K : ℕ} (b : ℕ) (n : Fin K → ℕ)
    (a : Fin K) : ℝ := epsilon b * n a

/-- Total current real weight. -/
@[expose] noncomputable def total {K : ℕ} (b : ℕ) (n : Fin K → ℕ) : ℝ :=
  ∑ a, weight b n a

/-- The actual held-arm mixture, formed from the constructed weights. -/
@[expose] noncomputable def probability {K : ℕ} (b : ℕ) (n : Fin K → ℕ)
    (a : Fin K) : ℝ := (weight b n a / total b n + 1 / K) / 2

/-- Explicit deterministic input to one block. `enabled` includes not having
stopped and being active; an arm is supplied even on disabled blocks. -/
structure Block (K B : ℕ) where
  enabled : Bool
  held : Fin K
  gain : ℕ
  gain_le : gain ≤ B

/-- Gains after activity/stopping has been applied. -/
@[expose] def effectiveGain {K B : ℕ} (s : Block K B) : ℕ :=
  if s.enabled then s.gain else 0

/-- Actual stopped importance gain for an arm. -/
@[expose] noncomputable def importance {K B : ℕ} (b : ℕ) (n : Fin K → ℕ)
    (s : Block K B) (a : Fin K) : ℝ :=
  if s.enabled = true ∧ s.held = a then (s.gain : ℝ) / probability b n a else 0

/-- Literal numerator update: floor only the enabled held arm. -/
@[expose] noncomputable def next {K B : ℕ} (b : ℕ) (n : Fin K → ℕ)
    (s : Block K B) (a : Fin K) : ℕ :=
  if s.enabled = true ∧ s.held = a then
    ⌊(n a : ℝ) * (1 + (s.gain : ℝ) / (4 * K * B * probability b n a))⌋₊
  else n a

/-- All-one initial weights, represented exactly on the grid. -/
@[expose] def initial (K b : ℕ) : Fin K → ℕ := fun _ => scale b

/-- Finite prefixes constructed recursively, never supplied as a recurrence
hypothesis. Only inputs before `r` are read by `numerators b input r`. -/
@[expose] noncomputable def numerators {K B : ℕ} (b : ℕ)
    (input : ℕ → Block K B) : ℕ → (Fin K → ℕ)
  | 0 => initial K b
  | r + 1 => next b (numerators b input r) (input r)

/-- A finite run computed by folding the literal update over the prefix. -/
@[expose] noncomputable def listNumerators {K B : ℕ} (b : ℕ)
    (blocks : List (Block K B)) (r : ℕ) : Fin K → ℕ :=
  (blocks.take r).foldl (fun n s => next b n s) (initial K b)

/-- Extend a finite input list by disabled zero-gain blocks after its end.
The supplied arm is immaterial after the end, since updates are disabled. -/
@[expose] def stoppedInput {K B : ℕ} (blocks : List (Block K B))
    (arm : Fin K) (s : ℕ) : Block K B :=
  if h : s < blocks.length then blocks[s]
  else ⟨false, arm, 0, Nat.zero_le B⟩

variable {K B b : ℕ}

theorem scale_pos (b : ℕ) : 0 < scale b := by
  exact pow_pos (by decide) _

theorem epsilon_pos (b : ℕ) : 0 < epsilon b := by
  exact one_div_pos.mpr (Nat.cast_pos.mpr (scale_pos b))

theorem epsilon_mul_scale (b : ℕ) : epsilon b * (scale b : ℝ) = 1 := by
  exact one_div_mul_cancel (Nat.cast_ne_zero.mpr (scale_pos b).ne')

theorem epsilon_eq_two_zpow (b : ℕ) :
    epsilon b = (2 : ℝ) ^ (-((4 * b : ℕ) : ℤ)) := by
  simp only [epsilon, scale, Nat.cast_pow, Nat.cast_ofNat, one_div,
    zpow_neg, zpow_natCast]

theorem weight_initial (a : Fin K) : weight b (initial K b) a = 1 := by
  exact epsilon_mul_scale b

theorem weight_nonneg (n : Fin K → ℕ) (a : Fin K) : 0 ≤ weight b n a := by
  exact mul_nonneg (epsilon_pos b).le (Nat.cast_nonneg _)

theorem weight_grid (n : Fin K → ℕ) (a : Fin K) :
    ∃ j : ℕ, weight b n a = epsilon b * j := ⟨n a, rfl⟩

theorem weight_le_total (n : Fin K → ℕ) (a : Fin K) :
    weight b n a ≤ total b n := by
  exact Finset.single_le_sum (fun i _ => weight_nonneg n i) (Finset.mem_univ a)

theorem total_pos (hK : 0 < K) (n : Fin K → ℕ)
    (hn : ∀ a, 1 ≤ weight b n a) : 0 < total b n := by
  exact lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one (hn ⟨0, hK⟩))
    (weight_le_total n ⟨0, hK⟩)

theorem probability_lower (_hK : 0 < K) (n : Fin K → ℕ) (a : Fin K) :
    1 / (2 * (K : ℝ)) ≤ probability b n a := by
  have h : 0 ≤ weight b n a / total b n :=
    div_nonneg (weight_nonneg n a) (Finset.sum_nonneg (fun i _ => weight_nonneg n i))
  unfold probability
  have heq : 1 / (2 * (K : ℝ)) = (1 / (K : ℝ)) / 2 := by ring
  rw [heq]
  linarith only [h]

theorem probability_pos (hK : 0 < K) (n : Fin K → ℕ) (a : Fin K) :
    0 < probability b n a := by
  exact lt_of_lt_of_le (by positivity) (probability_lower hK n a)

theorem weight_fraction_le (n : Fin K → ℕ) (a : Fin K) :
    weight b n a / total b n ≤ 2 * probability b n a := by
  have h : 0 ≤ 1 / (K : ℝ) := by positivity
  unfold probability
  linarith only [h]

theorem sum_probability (hK : 0 < K) (n : Fin K → ℕ)
    (hn : ∀ a, 1 ≤ weight b n a) : (∑ a, probability b n a) = 1 := by
  have hW := (total_pos hK n hn).ne'
  have hKr : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hK.ne'
  simp only [probability, ← Finset.sum_div, Finset.sum_add_distrib]
  change (total b n / total b n + _) / 2 = 1
  rw [div_self hW]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_one, div_self hKr]
  norm_num

theorem probability_le_one (hK : 0 < K) (n : Fin K → ℕ)
    (hn : ∀ a, 1 ≤ weight b n a) (a : Fin K) : probability b n a ≤ 1 := by
  rw [← sum_probability hK n hn]
  exact Finset.single_le_sum (fun i _ => (probability_pos hK n i).le)
    (Finset.mem_univ a)

theorem next_disabled (n : Fin K → ℕ) (s : Block K B) (hs : s.enabled = false) :
    next b n s = n := by
  funext a
  simp only [next, hs, Bool.false_eq_true, false_and, ↓reduceIte]

theorem next_other (n : Fin K → ℕ) (s : Block K B) (a : Fin K)
    (ha : s.held ≠ a) : next b n s a = n a := by
  simp only [next, ha, and_false, ↓reduceIte]

theorem next_mono (hK : 0 < K) (hB : 0 < B) (n : Fin K → ℕ)
    (s : Block K B) (a : Fin K) : n a ≤ next b n s a := by
  unfold next
  split_ifs with h
  · apply Nat.le_floor
    have hp := probability_pos (b := b) hK n a
    have hg : 0 ≤ (s.gain : ℝ) / (4 * K * B * probability b n a) := by
      positivity
    have hn0 : (0 : ℝ) ≤ n a := Nat.cast_nonneg _
    nlinarith only [hg, hn0]
  · exact le_rfl

theorem weight_next_mono (hK : 0 < K) (hB : 0 < B) (n : Fin K → ℕ)
    (s : Block K B) (a : Fin K) : weight b n a ≤ weight b (next b n s) a := by
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (next_mono hK hB n s a))
    (epsilon_pos b).le

theorem weight_ge_one (hK : 0 < K) (hB : 0 < B) (input : ℕ → Block K B)
    (r : ℕ) (a : Fin K) : 1 ≤ weight b (numerators b input r) a := by
  induction r with
  | zero => exact (weight_initial a).ge
  | succ r ih => exact ih.trans (weight_next_mono hK hB _ _ a)

theorem prefix_weight_pos (hK : 0 < K) (hB : 0 < B) (input : ℕ → Block K B)
    (r : ℕ) (a : Fin K) : 0 < weight b (numerators b input r) a := by
  exact lt_of_lt_of_le zero_lt_one (weight_ge_one hK hB input r a)

/-- Exactness for a zero integer gain, whether or not updating is enabled. -/
theorem next_gain_zero (n : Fin K → ℕ) (s : Block K B) (hs : s.gain = 0) :
    next b n s = n := by
  funext a
  simp only [next, hs, Nat.cast_zero, zero_div, add_zero, mul_one,
    Nat.floor_natCast, ite_self]

theorem importance_nonneg (hK : 0 < K) (n : Fin K → ℕ)
    (s : Block K B) (a : Fin K) : 0 ≤ importance b n s a := by
  unfold importance
  split_ifs
  · exact div_nonneg (Nat.cast_nonneg _) (probability_pos hK n a).le
  · exact le_rfl

theorem importance_le (hK : 0 < K) (n : Fin K → ℕ)
    (s : Block K B) (a : Fin K) : importance b n s a ≤ 2 * K * B := by
  unfold importance
  split_ifs
  · apply (div_le_iff₀ (probability_pos hK n a)).mpr
    have h := probability_lower (b := b) hK n a
    have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
    have h' : 1 ≤ 2 * (K : ℝ) * probability b n a := by
      simpa only [mul_comm] using
        (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K)).mp h
    have hg : (s.gain : ℝ) ≤ B := Nat.cast_le.mpr s.gain_le
    have hBr : (0 : ℝ) ≤ B := Nat.cast_nonneg _
    nlinarith only [h', hg, hBr]
  · positivity

theorem scaled_importance_bounds (hK : 0 < K) (hB : 0 < B)
    (n : Fin K → ℕ) (s : Block K B) (a : Fin K) :
    0 ≤ importance b n s a / (4 * K * B) ∧
      importance b n s a / (4 * K * B) ≤ 1 / 2 := by
  have hD : (0 : ℝ) < 4 * K * B := by positivity
  constructor
  · exact div_nonneg (importance_nonneg hK n s a) hD.le
  · apply (div_le_iff₀ hD).mpr
    nlinarith only [importance_le (b := b) hK n s a]

/-- The one-arm update, uniformly including unselected and disabled arms, in
the importance-gain form of appendix B. -/
theorem next_eq_floor (hK : 0 < K) (hB : 0 < B) (n : Fin K → ℕ)
    (s : Block K B) (a : Fin K) :
    next b n s a =
      ⌊(n a : ℝ) * (1 + importance b n s a / (4 * K * B))⌋₊ := by
  unfold next importance
  split_ifs with h
  · congr 1
    have hp := (probability_pos (b := b) hK n a).ne'
    have hKr : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hK.ne'
    have hBr : (B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hB.ne'
    field_simp
  · simp only [zero_div, add_zero, mul_one, Nat.floor_natCast]

/-- Exact real conversion of the update. Source: appendix B:536-543. -/
theorem weight_next_eq (hK : 0 < K) (hB : 0 < B) (n : Fin K → ℕ)
    (s : Block K B) (a : Fin K) :
    weight b (next b n s) a = epsilon b *
      (⌊weight b n a * (1 + importance b n s a / (4 * K * B)) / epsilon b⌋₊ : ℝ) := by
  rw [weight, next_eq_floor hK hB]
  congr 2
  rw [weight]
  field_simp [(epsilon_pos b).ne']

/-- Exact source 07:33-36 equation for the enabled held arm. -/
theorem weight_next_held (n : Fin K → ℕ)
    (s : Block K B) (hs : s.enabled = true) :
    weight b (next b n s) s.held = epsilon b *
      (⌊(scale b : ℝ) * weight b n s.held *
        (1 + (s.gain : ℝ) / (4 * K * B * probability b n s.held))⌋₊ : ℝ) := by
  simp only [weight, next, hs, and_self, ↓reduceIte]
  congr 2
  congr 1
  have he := epsilon_mul_scale b
  calc
    _ = (epsilon b * (scale b : ℝ)) *
        ((n s.held : ℝ) * (1 + (s.gain : ℝ) /
          (4 * K * B * probability b n s.held))) := by rw [he, one_mul]
    _ = _ := by ring

/-- Zero importance gain has no rounding loss, because numerators are integers. -/
theorem next_eq_of_importance_zero (hK : 0 < K) (hB : 0 < B)
    (n : Fin K → ℕ) (s : Block K B) (a : Fin K)
    (hzero : importance b n s a = 0) : next b n s a = n a := by
  rw [next_eq_floor hK hB, hzero, zero_div, add_zero, mul_one, Nat.floor_natCast]

theorem weight_next_upper (hK : 0 < K) (hB : 0 < B)
    (n : Fin K → ℕ) (s : Block K B) (a : Fin K) :
    weight b (next b n s) a ≤
      weight b n a * (1 + importance b n s a / (4 * K * B)) := by
  simp only [weight]
  rw [next_eq_floor hK hB]
  have hx := (scaled_importance_bounds (b := b) hK hB n s a).1
  have hf := Nat.floor_le (mul_nonneg (Nat.cast_nonneg (n a)) (by linarith :
    0 ≤ 1 + importance b n s a / (4 * K * B)))
  have h := mul_le_mul_of_nonneg_left hf (epsilon_pos b).le
  simpa only [weight, mul_assoc] using h

theorem weight_next_lower (hK : 0 < K) (hB : 0 < B)
    (n : Fin K → ℕ) (s : Block K B) (a : Fin K) :
    weight b n a * (1 + importance b n s a / (4 * K * B)) - epsilon b ≤
      weight b (next b n s) a := by
  simp only [weight]
  rw [next_eq_floor hK hB]
  have hf := (Nat.lt_floor_add_one
    ((n a : ℝ) * (1 + importance b n s a / (4 * K * B)))).le
  have h := mul_le_mul_of_nonneg_left hf (epsilon_pos b).le
  nlinarith only [h]

/-- The honest dimension inputs imply the rounding quantum bound used in
appendix B:546-550. No constructor dimensions are assumed here. -/
theorem epsilon_le {N : ℕ} (hK : 0 < K) (hB : 0 < B)
    (hN : 24 ≤ N) (hKB : K * B ≤ N) (hNb : N ≤ 2 ^ b) :
    epsilon b ≤ 1 / (16 * K * B) := by
  have ha : 24 ≤ 2 ^ b := hN.trans hNb
  have hp : 16 ≤ (2 ^ b) ^ 3 :=
    (by omega : 16 ≤ 2 ^ b).trans (le_self_pow (by omega : 1 ≤ 2 ^ b) (by decide))
  have hscale : 16 * K * B ≤ scale b := by
    calc
      16 * K * B = 16 * (K * B) := by ring
      _ ≤ (2 ^ b) ^ 3 * 2 ^ b := Nat.mul_le_mul hp (hKB.trans hNb)
      _ = (2 ^ b) ^ 4 := by ring
      _ = scale b := by rw [scale, ← pow_mul, Nat.mul_comm b 4]
  exact one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 16 * K * B)
    (by exact_mod_cast hscale)

/-- A strictly positive importance gain comes from an integer gain at least
one. This is the discrete input needed to absorb downward rounding. -/
theorem one_le_importance (hK : 0 < K) (n : Fin K → ℕ)
    (hn : ∀ a, 1 ≤ weight b n a) (s : Block K B) (a : Fin K)
    (hpos : 0 < importance b n s a) : 1 ≤ importance b n s a := by
  by_cases h : s.enabled = true ∧ s.held = a
  · rw [importance, ite_eq_left h] at hpos
    rw [importance, ite_eq_left h]
    have hg : 1 ≤ s.gain := by
      by_contra hg
      have hz : s.gain = 0 := by omega
      simp only [hz, Nat.cast_zero, zero_div, lt_self_iff_false] at hpos
    apply (le_div_iff₀ (probability_pos hK n a)).mpr
    have hprob := probability_le_one (b := b) hK n hn a
    have hgr : (1 : ℝ) ≤ s.gain := by exact_mod_cast hg
    simpa only [one_mul] using hprob.trans hgr
  · simp only [importance, h, ↓reduceIte, lt_self_iff_false] at hpos

/-- Scalar logarithm estimate, derived from Mathlib's actual real-log lower
bound; it is not an assumed potential estimate. -/
theorem log_ratio_lower {w v x e : ℝ} (hw : 1 ≤ w)
    (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) (he : e ≤ x / 4)
    (hv : w * (1 + x) - e ≤ v) : x / 2 ≤ Real.log (v / w) := by
  have hwpos : 0 < w := lt_of_lt_of_le zero_lt_one hw
  have hratio : 1 + 3 * x / 4 ≤ v / w := by
    apply (le_div_iff₀ hwpos).mpr
    nlinarith only [hw, hx, he, hv]
  have hy : 0 ≤ 3 * x / 4 := by positivity
  have hden : 0 < 3 * x / 4 + 2 := by positivity
  have hfrac : x / 2 ≤ 2 * (3 * x / 4) / (3 * x / 4 + 2) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith only [hx, hxhalf]
  exact hfrac.trans ((Real.le_log_one_add_of_nonneg hy).trans
    (Real.log_le_log (by positivity) hratio))

/-- Per-arm logarithmic gain, including zero-gain, inactive and stopped blocks.
Source: appendix B:540-556. -/
theorem importance_div_le_log_ratio {N : ℕ} (hK : 0 < K) (hB : 0 < B)
    (hN : 24 ≤ N) (hKB : K * B ≤ N) (hNb : N ≤ 2 ^ b)
    (n : Fin K → ℕ) (hn : ∀ a, 1 ≤ weight b n a)
    (s : Block K B) (a : Fin K) :
    importance b n s a / (8 * K * B) ≤
      Real.log (weight b (next b n s) a / weight b n a) := by
  by_cases hz : importance b n s a = 0
  · rw [hz, zero_div]
    have hweight : weight b (next b n s) a = weight b n a := by
      simp only [weight, next_eq_of_importance_zero hK hB n s a hz]
    rw [hweight]
    have hw : weight b n a ≠ 0 := (lt_of_lt_of_le zero_lt_one (hn a)).ne'
    rw [div_self hw, Real.log_one]
  · have hpos : 0 < importance b n s a :=
      lt_of_le_of_ne (importance_nonneg hK n s a) (Ne.symm hz)
    have hD : (0 : ℝ) < 4 * K * B := by positivity
    have hsmall : epsilon b ≤ (importance b n s a / (4 * K * B)) / 4 := by
      calc
        epsilon b ≤ 1 / (16 * K * B) := epsilon_le hK hB hN hKB hNb
        _ = (1 / (4 * K * B)) / 4 := by ring
        _ ≤ (importance b n s a / (4 * K * B)) / 4 := by
          exact div_le_div_of_nonneg_right
            (div_le_div_of_nonneg_right (one_le_importance hK n hn s a hpos) hD.le)
            (by norm_num)
    have hx := scaled_importance_bounds (b := b) hK hB n s a
    have hlog := log_ratio_lower (hn a) hx.1 hx.2 hsmall
      (weight_next_lower hK hB n s a)
    convert hlog using 1
    ring

/-- Summed contribution of the single held arm. All inputs remain explicit. -/
theorem sum_weight_importance (n : Fin K → ℕ) (s : Block K B) :
    (∑ a, weight b n a * importance b n s a / (4 * K * B)) =
      weight b n s.held * (effectiveGain s : ℝ) /
        (4 * K * B * probability b n s.held) := by
  have hs : (∑ a, weight b n a * importance b n s a / (4 * K * B)) =
      weight b n s.held * importance b n s s.held / (4 * K * B) := by
    apply Finset.sum_eq_single s.held
    · intro a _ ha
      simp only [importance, Ne.symm ha, and_false, ↓reduceIte, mul_zero, zero_div]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  rw [hs]
  cases he : s.enabled <;>
    simp only [importance, effectiveGain, he, Bool.false_eq_true, false_and,
      and_self, ↓reduceIte, Nat.cast_zero, mul_zero, zero_div]
  ring

/-- Total mass grows by at most the source factor, including stopped blocks.
Source: appendix B:557-561. -/
theorem total_next_le (hK : 0 < K) (hB : 0 < B) (n : Fin K → ℕ)
    (hn : ∀ a, 1 ≤ weight b n a) (s : Block K B) :
    total b (next b n s) ≤ total b n * (1 + (effectiveGain s : ℝ) / (2 * K * B)) := by
  have hW := total_pos hK n hn
  have hp := probability_pos (b := b) hK n s.held
  have hD : (0 : ℝ) < 4 * K * B := by positivity
  have hw : weight b n s.held ≤ 2 * probability b n s.held * total b n :=
    (div_le_iff₀ hW).mp (weight_fraction_le n s.held)
  have hcontrib : weight b n s.held * (effectiveGain s : ℝ) /
      (4 * K * B * probability b n s.held) ≤
      total b n * ((effectiveGain s : ℝ) / (2 * K * B)) := by
    calc
      _ ≤ (2 * probability b n s.held * total b n) * (effectiveGain s : ℝ) /
          (4 * K * B * probability b n s.held) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg _)) (mul_pos hD hp).le
      _ = _ := by field_simp; ring
  calc
    total b (next b n s) ≤
        ∑ a, weight b n a * (1 + importance b n s a / (4 * K * B)) := by
      exact Finset.sum_le_sum (fun a _ => weight_next_upper hK hB n s a)
    _ = total b n + ∑ a, weight b n a * importance b n s a / (4 * K * B) := by
      simp only [mul_add, mul_one, ← mul_div_assoc, Finset.sum_add_distrib, total]
    _ = total b n + weight b n s.held * (effectiveGain s : ℝ) /
        (4 * K * B * probability b n s.held) := by rw [sum_weight_importance]
    _ ≤ total b n + total b n * ((effectiveGain s : ℝ) / (2 * K * B)) :=
      by linarith only [hcontrib]
    _ = _ := by ring

/-- The total-mass logarithm upper bound uses Mathlib's `log t ≤ t - 1`. -/
theorem log_total_next_le (hK : 0 < K) (hB : 0 < B) (n : Fin K → ℕ)
    (hn : ∀ a, 1 ≤ weight b n a) (s : Block K B) :
    Real.log (total b (next b n s)) ≤
      Real.log (total b n) + (effectiveGain s : ℝ) / (2 * K * B) := by
  have hW := total_pos hK n hn
  have hnext : 0 < total b (next b n s) := total_pos hK _
    (fun a => (hn a).trans (weight_next_mono hK hB n s a))
  have hz : 0 ≤ (effectiveGain s : ℝ) / (2 * K * B) := by positivity
  have hf : 0 < 1 + (effectiveGain s : ℝ) / (2 * K * B) := by positivity
  calc
    Real.log (total b (next b n s)) ≤
        Real.log (total b n * (1 + (effectiveGain s : ℝ) / (2 * K * B))) :=
      Real.log_le_log hnext (total_next_le hK hB n hn s)
    _ = Real.log (total b n) +
        Real.log (1 + (effectiveGain s : ℝ) / (2 * K * B)) :=
      Real.log_mul hW.ne' hf.ne'
    _ ≤ Real.log (total b n) + (effectiveGain s : ℝ) / (2 * K * B) := by
      have h := Real.log_le_sub_one_of_pos hf
      linarith only [h]

theorem total_initial : total b (initial K b) = K := by
  simp only [total, weight_initial, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- Lower telescope, for every constructed finite prefix and every arm.
Source: appendix B:562-565. -/
theorem sum_importance_div_le_log {N : ℕ} (hK : 0 < K) (hB : 0 < B)
    (hN : 24 ≤ N) (hKB : K * B ≤ N) (hNb : N ≤ 2 ^ b)
    (input : ℕ → Block K B) (r : ℕ) (a : Fin K) :
    (∑ s ∈ Finset.range r, importance b (numerators b input s) (input s) a) /
        (8 * K * B) ≤ Real.log (weight b (numerators b input r) a) := by
  induction r with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_div,
      numerators, weight_initial, Real.log_one, le_refl]
  | succ r ih =>
    have hstep := importance_div_le_log_ratio hK hB hN hKB hNb
      (numerators b input r) (weight_ge_one hK hB input r) (input r) a
    have hw : 0 < weight b (numerators b input r) a :=
      lt_of_lt_of_le zero_lt_one (weight_ge_one hK hB input r a)
    have hw' : 0 < weight b (numerators b input (r + 1)) a :=
      lt_of_lt_of_le zero_lt_one (weight_ge_one hK hB input (r + 1) a)
    change _ ≤ Real.log (weight b (numerators b input (r + 1)) a /
      weight b (numerators b input r) a) at hstep
    rw [Real.log_div hw'.ne' hw.ne'] at hstep
    rw [Finset.sum_range_succ, add_div]
    linarith only [ih, hstep]

/-- Upper telescope for the constructed total mass. -/
theorem log_total_le (hK : 0 < K) (hB : 0 < B)
    (input : ℕ → Block K B) (r : ℕ) :
    Real.log (total b (numerators b input r)) ≤ Real.log (K : ℝ) +
      (∑ s ∈ Finset.range r, (effectiveGain (input s) : ℝ)) / (2 * K * B) := by
  induction r with
  | zero => simp only [numerators, total_initial, Finset.range_zero,
      Finset.sum_empty, zero_div, add_zero, le_refl]
  | succ r ih =>
    have hstep := log_total_next_le hK hB (numerators b input r)
      (weight_ge_one hK hB input r) (input r)
    change Real.log (total b (numerators b input (r + 1))) ≤ _ at hstep
    rw [Finset.sum_range_succ, add_div]
    linarith only [ih, hstep]

/-- Deterministic stopped bootstrap potential bound, with the exact constants
of appendix B:566-568. This asserts no probabilistic or manuscript closure.
The input stream is inspected only through its finite prefix of length `r`. -/
theorem bootstrap_potential_bound {N : ℕ} (hK : 0 < K) (hB : 0 < B)
    (hN : 24 ≤ N) (hKB : K * B ≤ N) (hNb : N ≤ 2 ^ b)
    (input : ℕ → Block K B) (r : ℕ) (a : Fin K) :
    (∑ s ∈ Finset.range r, importance b (numerators b input s) (input s) a) ≤
      4 * (∑ s ∈ Finset.range r, (effectiveGain (input s) : ℝ)) +
        8 * K * B * Real.log (K : ℝ) := by
  have hlo := sum_importance_div_le_log hK hB hN hKB hNb input r a
  have hw : 0 < weight b (numerators b input r) a :=
    lt_of_lt_of_le zero_lt_one (weight_ge_one hK hB input r a)
  have hmid := Real.log_le_log hw (weight_le_total (numerators b input r) a)
  have hhi := log_total_le (b := b) hK hB input r
  have hD : (0 : ℝ) < 8 * K * B := by positivity
  have h := (div_le_iff₀ hD).mp (hlo.trans (hmid.trans hhi))
  convert h using 1
  field_simp
  ring

theorem listNumerators_succ (blocks : List (Block K B)) (r : ℕ)
    (hr : r < blocks.length) :
    listNumerators b blocks (r + 1) = next b (listNumerators b blocks r) blocks[r] := by
  unfold listNumerators
  rw [List.take_succ_eq_append_getElem hr, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

/-- The recursive construction and literal finite-list fold agree. -/
theorem numerators_stoppedInput (blocks : List (Block K B)) (arm : Fin K)
    (r : ℕ) (hr : r ≤ blocks.length) :
    numerators b (stoppedInput blocks arm) r = listNumerators b blocks r := by
  induction r with
  | zero => simp only [numerators, listNumerators, List.take_zero, List.foldl_nil]
  | succ r ih =>
    have hlt : r < blocks.length := by omega
    rw [numerators, ih (Nat.le_of_lt hlt), listNumerators_succ blocks r hlt]
    rw [stoppedInput, dite_eq_left hlt]

/-- Finite-list version of the exact potential inequality, simultaneously
available for every prefix and arm. Its states are actual prefix folds.
Source: appendix B:524-568. -/
theorem finite_bootstrap_potential_bound {N : ℕ} (hK : 0 < K) (hB : 0 < B)
    (hN : 24 ≤ N) (hKB : K * B ≤ N) (hNb : N ≤ 2 ^ b)
    (blocks : List (Block K B)) (r : ℕ) (hr : r ≤ blocks.length) (a : Fin K) :
    (∑ s : Fin r, importance b (listNumerators b blocks s.val)
      (blocks.get ⟨s.val, lt_of_lt_of_le s.isLt hr⟩) a) ≤
      4 * (∑ s : Fin r, (effectiveGain
        (blocks.get ⟨s.val, lt_of_lt_of_le s.isLt hr⟩) : ℝ)) +
          8 * K * B * Real.log (K : ℝ) := by
  have h := bootstrap_potential_bound hK hB hN hKB hNb (stoppedInput blocks a) r a
  rw [Finset.sum_range, Finset.sum_range] at h
  have hnum (s : Fin r) : numerators b (stoppedInput blocks a) s.val =
      listNumerators b blocks s.val :=
    numerators_stoppedInput blocks a s.val (s.isLt.le.trans hr)
  have hin (s : Fin r) : stoppedInput blocks a s.val =
      blocks.get ⟨s.val, lt_of_lt_of_le s.isLt hr⟩ := by
    rw [stoppedInput, dite_eq_left (lt_of_lt_of_le s.isLt hr)]
    rw [List.get_eq_getElem]
  simpa only [hnum, hin] using h

end Bandits.Support.BootstrapWeightPotential

end
