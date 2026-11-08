module
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Internal scalar recurrence calculations used in the deferred collection-law argument.

The source calculation is in `sources/zip4/manuscript/06_interruptions.tex:399-405`;
its residual identity is defined in `sources/zip4/manuscript/04_slow_fast_learner.tex:177`.
-/

public section

namespace Bandits.Support.DeferredRecurrence

/-- If two scalar sequences have the same affine input at each step, their difference
is multiplied by `a` at every step. -/
theorem affineError (mu p rho : ℕ → ℝ) (a h : ℝ)
    (hmu : ∀ n, mu (Nat.succ n) = a * mu n + h * rho n)
    (hp : ∀ n, p (Nat.succ n) = a * p n + h * rho n) (n : ℕ) :
    mu n - p n = a ^ n * (mu 0 - p 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        mu (Nat.succ n) - p (Nat.succ n) = a * (mu n - p n) := by
          rw [hmu n, hp n]
          ring
        _ = a * (a ^ n * (mu 0 - p 0)) := by rw [ih]
        _ = a ^ Nat.succ n * (mu 0 - p 0) := by
          rw [pow_succ]
          ring

/-- The initial trigger sets the starting sequence to the preceding residual draw.
When `h * rhoPrev = p(0) - a * pPrev` and `a = 1-h`, the generic recurrence
therefore has the deferred error shown in the source calculation. -/
theorem initialTriggerError (mu p rho : ℕ → ℝ) (a h rhoPrev pPrev : ℝ)
    (hmu : ∀ n, mu (Nat.succ n) = a * mu n + h * rho n)
    (hp : ∀ n, p (Nat.succ n) = a * p n + h * rho n)
    (ha : a = 1 - h) (hh : h ≠ 0) (hmu0 : mu 0 = rhoPrev)
    (htrigger : h * rhoPrev = p 0 - a * pPrev) (n : ℕ) :
    mu n - p n = a ^ Nat.succ n / h * (p 0 - pPrev) := by
  have hbaseMul : h * (rhoPrev - p 0) = a * (p 0 - pPrev) := by
    calc
      h * (rhoPrev - p 0) = h * rhoPrev - h * p 0 := by ring
      _ = (p 0 - a * pPrev) - h * p 0 := by rw [htrigger]
      _ = a * p 0 - a * pPrev := by rw [ha]; ring
      _ = a * (p 0 - pPrev) := by ring
  have hbase : mu 0 - p 0 = a / h * (p 0 - pPrev) := by
    rw [hmu0]
    field_simp [hh]
    calc
      (rhoPrev - p 0) * h = h * (rhoPrev - p 0) := by ring
      _ = a * (p 0 - pPrev) := hbaseMul
  calc
    mu n - p n = a ^ n * (mu 0 - p 0) := affineError mu p rho a h hmu hp n
    _ = a ^ n * (a / h * (p 0 - pPrev)) := by rw [hbase]
    _ = a ^ Nat.succ n / h * (p 0 - pPrev) := by
      rw [pow_succ]
      ring

end Bandits.Support.DeferredRecurrence
