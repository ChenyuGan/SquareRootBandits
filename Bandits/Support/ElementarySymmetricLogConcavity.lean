module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Basic.Real.Basic

import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Algebra.Order.BigOperators.Ring.Multiset
import Mathlib.Tactic.Ring

/-!
# Weak Newton inequality for nonnegative elementary symmetric coefficients

Internal mathematics for `sources/zip4/manuscript/04_slow_fast_learner.tex`,
lines 84–89, specifically the sign estimate on line 88. All coefficients are
Mathlib's canonical `Multiset.esymm`; no project elementary symmetric function
is introduced here.

We prove the stronger cross-product inequality by adjoining one nonnegative
weight. Its four expanded terms follow from four instances of the induction
hypothesis, so neither strict positivity nor a no-internal-zeros assumption is
needed. The weak Newton inequality includes every natural degree, including
degrees above the multiset's cardinality. This module does not formalize the
inclusion law or claim closure of a manuscript theorem.
-/

public section

namespace Bandits.Support.ElementarySymmetricLogConcavity

/-- Adjoining one coordinate to Mathlib's elementary symmetric coefficients. -/
theorem esymm_cons_succ {R : Type*} [CommSemiring R]
    (x : R) (s : Multiset R) (k : ℕ) :
    (x ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + x * s.esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add,
    Multiset.sum_add, Multiset.map_map, Function.comp_apply, Multiset.prod_cons,
    Multiset.sum_map_mul_left]

/-- Every elementary symmetric coefficient of nonnegative real weights is nonnegative. -/
theorem esymm_nonneg (s : Multiset ℝ) (hs : ∀ x ∈ s, 0 ≤ x) (k : ℕ) :
    0 ≤ s.esymm k := by
  unfold Multiset.esymm
  apply Multiset.sum_nonneg
  intro p hp
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hp
  apply Multiset.prod_nonneg
  intro x hx
  exact hs x (Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 hx)

/-- Cross-product inequality for nonnegative elementary symmetric coefficients.

The only weight hypothesis is coordinatewise nonnegativity. The degree shift
`c` and both degrees may be zero or exceed the multiset's cardinality. -/
theorem esymm_mul_le_esymm_mul (s : Multiset ℝ)
    (hs : ∀ x ∈ s, 0 ≤ x) (a b c : ℕ) (hab : a ≤ b) :
    s.esymm a * s.esymm (b + c) ≤ s.esymm (a + c) * s.esymm b := by
  induction s using Multiset.induction_on generalizing a b c with
  | empty =>
      cases b with
      | zero =>
          have ha : a = 0 := Nat.eq_zero_of_le_zero hab
          subst a
          simp only [Nat.zero_add, Multiset.esymm_zero, one_mul, mul_one, le_refl]
      | succ b =>
          have hb : (0 : Multiset ℝ).esymm (b + 1) = 0 :=
            Multiset.esymm_of_card_lt (by
              simpa only [Multiset.card_zero] using Nat.zero_lt_succ b)
          have hbc : (0 : Multiset ℝ).esymm (b + 1 + c) = 0 :=
            Multiset.esymm_of_card_lt (by
              simpa only [Multiset.card_zero] using Nat.add_pos_left (Nat.zero_lt_succ b) c)
          rw [hb, hbc, mul_zero, mul_zero]
  | cons x s ih =>
      have hx : 0 ≤ x := hs x (Multiset.mem_cons_self x s)
      have hs' : ∀ y ∈ s, 0 ≤ y := fun y hy => hs y (Multiset.mem_cons_of_mem hy)
      cases c with
      | zero =>
          simp only [Nat.add_zero, le_refl]
      | succ c =>
          cases a with
          | zero =>
              cases b with
              | zero =>
                  simp only [Nat.zero_add, Multiset.esymm_zero, one_mul, mul_one, le_refl]
              | succ b =>
                  have h₀ : s.esymm (b + 1 + c + 1) ≤
                      s.esymm (c + 1) * s.esymm (b + 1) := by
                    simpa only [Multiset.esymm_zero, Nat.zero_add, one_mul,
                      Nat.add_assoc] using
                      ih hs' 0 (b + 1) (c + 1) (Nat.zero_le _)
                  have h₁ : s.esymm (b + 1 + c) ≤ s.esymm c * s.esymm (b + 1) := by
                    simpa only [Multiset.esymm_zero, Nat.zero_add, one_mul] using
                      ih hs' 0 (b + 1) c (Nat.zero_le _)
                  simp only [Multiset.esymm_zero, Nat.zero_add, one_mul]
                  rw [← Nat.add_assoc (b + 1) c 1]
                  rw [esymm_cons_succ x s (b + 1 + c), esymm_cons_succ x s c,
                    esymm_cons_succ x s b]
                  calc
                    s.esymm (b + 1 + c + 1) + x * s.esymm (b + 1 + c)
                        ≤ s.esymm (c + 1) * s.esymm (b + 1) +
                            x * (s.esymm c * s.esymm (b + 1)) :=
                      add_le_add h₀ (mul_le_mul_of_nonneg_left h₁ hx)
                    _ = (s.esymm (c + 1) + x * s.esymm c) * s.esymm (b + 1) := by
                      ring
                    _ ≤ (s.esymm (c + 1) + x * s.esymm c) *
                        (s.esymm (b + 1) + x * s.esymm b) :=
                      mul_le_mul_of_nonneg_left
                        (le_add_of_nonneg_right (mul_nonneg hx (esymm_nonneg s hs' b)))
                        (add_nonneg (esymm_nonneg s hs' (c + 1))
                          (mul_nonneg hx (esymm_nonneg s hs' c)))
          | succ a =>
              cases b with
              | zero => exact (Nat.not_succ_le_zero a hab).elim
              | succ b =>
                  have hab' : a ≤ b := Nat.le_of_succ_le_succ hab
                  have h₀ := ih hs' (a + 1) (b + 1) (c + 1) hab
                  have h₁ := mul_le_mul_of_nonneg_left (ih hs' a b (c + 2) hab') hx
                  have h₂ := mul_le_mul_of_nonneg_left (ih hs' (a + 1) (b + 1) c hab) hx
                  have h₃ := mul_le_mul_of_nonneg_left (ih hs' a b (c + 1) hab')
                    (mul_nonneg hx hx)
                  simp only [Nat.add_assoc, Nat.add_left_comm 1 c,
                    Nat.add_comm 1 c] at h₀ h₁ h₂ h₃
                  rw [Nat.add_right_comm b 1 (c + 1), Nat.add_right_comm a 1 (c + 1),
                    esymm_cons_succ x s a, esymm_cons_succ x s (b + (c + 1)),
                    esymm_cons_succ x s (a + (c + 1)), esymm_cons_succ x s b]
                  calc
                    (s.esymm (a + 1) + x * s.esymm a) *
                        (s.esymm (b + (c + 1) + 1) + x * s.esymm (b + (c + 1)))
                        = s.esymm (a + 1) * s.esymm (b + (c + 2)) +
                            x * (s.esymm a * s.esymm (b + (c + 2))) +
                            x * (s.esymm (a + 1) * s.esymm (b + (c + 1))) +
                            (x * x) * (s.esymm a * s.esymm (b + (c + 1))) := by
                      simp only [Nat.add_assoc]
                      ring
                    _ ≤ s.esymm (a + (c + 2)) * s.esymm (b + 1) +
                            x * (s.esymm (a + (c + 2)) * s.esymm b) +
                            x * (s.esymm (a + (c + 1)) * s.esymm (b + 1)) +
                            (x * x) * (s.esymm (a + (c + 1)) * s.esymm b) :=
                      add_le_add (add_le_add (add_le_add h₀ h₁) h₂) h₃
                    _ = (s.esymm (a + (c + 1) + 1) + x * s.esymm (a + (c + 1))) *
                        (s.esymm (b + 1) + x * s.esymm b) := by
                      simp only [Nat.add_assoc]
                      ring

/-- Weak Newton inequality, including all boundary degrees and zero weights.

Source motivation: `sources/zip4/manuscript/04_slow_fast_learner.tex`,
lines 84–89, especially the coefficient inequality on line 88. This is an
internal coefficient theorem, not the manuscript's inclusion comparison. -/
theorem esymm_log_concave (s : Multiset ℝ) (hs : ∀ x ∈ s, 0 ≤ x) (k : ℕ) :
    s.esymm k * s.esymm (k + 2) ≤ (s.esymm (k + 1)) ^ 2 := by
  simpa only [pow_two, Nat.add_assoc] using
    esymm_mul_le_esymm_mul s hs k (k + 1) 1 (Nat.le_succ k)

/-- The nonpositive numerator in the other-coordinate derivative, in coefficient form. -/
theorem esymm_newton_difference_nonpos (s : Multiset ℝ)
    (hs : ∀ x ∈ s, 0 ≤ x) (k : ℕ) :
    s.esymm k * s.esymm (k + 2) - (s.esymm (k + 1)) ^ 2 ≤ 0 :=
  sub_nonpos.mpr (esymm_log_concave s hs k)

/-- List version, using the canonical coercion to Mathlib's multiset coefficients. -/
theorem list_esymm_log_concave (w : List ℝ) (hw : ∀ x ∈ w, 0 ≤ x) (k : ℕ) :
    (w : Multiset ℝ).esymm k * (w : Multiset ℝ).esymm (k + 2) ≤
      ((w : Multiset ℝ).esymm (k + 1)) ^ 2 :=
  esymm_log_concave (w : Multiset ℝ) (fun x hx => hw x (Multiset.mem_coe.mp hx)) k

end Bandits.Support.ElementarySymmetricLogConcavity
