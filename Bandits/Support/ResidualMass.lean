module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Basic.Real.Basic

/-!
Finite residual-mass and affine-correction identities for real-valued laws.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:174-186` and
`sources/zip4/manuscript/06_interruptions.tex:351-427`.
-/

public section
noncomputable section

open scoped BigOperators

namespace Bandits.Support.ResidualMass

/-- The residual law obtained by removing the common mass `(1 - h) * p`. -/
@[expose] def residual {α : Type*} (h : ℝ) (p q : α → ℝ) (x : α) : ℝ :=
  (q x - (1 - h) * p x) / h

/-- Pointwise domination makes every residual mass nonnegative. -/
theorem residual_nonneg {α : Type*} [Fintype α] (h : ℝ) (p q : α → ℝ)
    (hh : 0 < h) (hdom : ∀ x, (1 - h) * p x ≤ q x) :
    ∀ x, 0 ≤ residual h p q x := by
  intro x
  unfold residual
  exact div_nonneg (sub_nonneg.mpr (hdom x)) (le_of_lt hh)

/-- If `p` and `q` each have total mass one, the residual also has total mass one. -/
theorem residual_sum_eq_one {α : Type*} [Fintype α] (h : ℝ) (p q : α → ℝ)
    (hh : 0 < h) (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1) :
    ∑ x, residual h p q x = 1 := by
  classical
  have hnum : (∑ x, (q x - (1 - h) * p x)) = h := by
    calc
      (∑ x, (q x - (1 - h) * p x))
          = (∑ x, q x) - (1 - h) * (∑ x, p x) := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 1 - (1 - h) * 1 := by rw [hq, hp]
      _ = h := by simp
  change (∑ x, (q x - (1 - h) * p x) / h) = 1
  rw [← Finset.sum_div, hnum, div_self (ne_of_gt hh)]

/-- The source's affine correction of a law by a difference of two laws. -/
@[expose] def correctedLaw {α : Type*} (a h : ℝ) (n : ℕ)
    (Q_t Q_u Q_prev : α → ℝ) (x : α) : ℝ :=
  Q_t x + (a ^ (n + 1) / h) * (Q_u x - Q_prev x)

/-- An affine correction by a difference of normalized laws preserves total mass. -/
theorem correctedLaw_sum_eq_one {α : Type*} [Fintype α] (a h : ℝ) (n : ℕ)
    (Q_t Q_u Q_prev : α → ℝ)
    (ht : ∑ x, Q_t x = 1) (hu : ∑ x, Q_u x = 1)
    (hprev : ∑ x, Q_prev x = 1) :
    ∑ x, correctedLaw a h n Q_t Q_u Q_prev x = 1 := by
  classical
  change (∑ x, (Q_t x + (a ^ (n + 1) / h) * (Q_u x - Q_prev x))) = 1
  calc
    (∑ x, (Q_t x + (a ^ (n + 1) / h) * (Q_u x - Q_prev x)))
        = (∑ x, Q_t x) + (a ^ (n + 1) / h) *
            ((∑ x, Q_u x) - (∑ x, Q_prev x)) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
    _ = 1 + (a ^ (n + 1) / h) * (1 - 1) := by rw [ht, hu, hprev]
    _ = 1 := by simp

end Bandits.Support.ResidualMass
