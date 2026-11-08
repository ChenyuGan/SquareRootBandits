module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Deterministic positivity bound for the corrected sampler.

Source: `sources/zip4/manuscript/06_interruptions.tex:351-427` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:66-77`.
-/

public section

namespace Bandits.Support.CorrectedPositivity

/-- Iterating a one-step lower bound gives the corresponding lower bound after `n` steps. -/
theorem iterateLowerBound {a : ℝ} (ha : 0 ≤ a) (q : ℕ → ℝ)
    (hstep : ∀ k, a * q k ≤ q (k + 1)) (k n : ℕ) :
    a ^ n * q k ≤ q (k + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        a ^ (n + 1) * q k = a * (a ^ n * q k) := by rw [pow_succ]; ring
        _ ≤ a * q (k + n) := mul_le_mul_of_nonneg_left ih ha
        _ ≤ q (k + n + 1) := hstep (k + n)

/--
The scalar corrected-sampler inequality. The exponent in the correction term is `n + 1`.
The hypotheses give the `n`-step lower bound at `Q_t` and the preceding one-step bound
at `Q_u`; the displayed corrected quantity is therefore at least a nonnegative quantity.
-/
theorem correctedSamplerBounds (h : ℝ) (n : ℕ) (Q_t Q_u Q_prev : ℝ)
    (hh : 0 < h) (hh_le : h ≤ 1)
    (ht : (1 - h) ^ n * Q_u ≤ Q_t)
    (hu : (1 - h) * Q_prev ≤ Q_u) :
    (1 - h) ^ n / h * (Q_u - (1 - h) * Q_prev) ≤
        Q_t + (1 - h) ^ (n + 1) / h * (Q_u - Q_prev) ∧
      0 ≤ (1 - h) ^ n / h * (Q_u - (1 - h) * Q_prev) := by
  have ha : 0 ≤ 1 - h := sub_nonneg.mpr hh_le
  have hbase : 0 ≤ Q_u - (1 - h) * Q_prev := sub_nonneg.mpr hu
  have hcorr : 0 ≤ (1 - h) ^ n / h * (Q_u - (1 - h) * Q_prev) :=
    mul_nonneg (div_nonneg (pow_nonneg ha n) hh.le) hbase
  have hres : 0 ≤ Q_t - (1 - h) ^ n * Q_u := sub_nonneg.mpr ht
  have hid :
      Q_t + (1 - h) ^ (n + 1) / h * (Q_u - Q_prev) =
        (Q_t - (1 - h) ^ n * Q_u) +
          ((1 - h) ^ n / h * (Q_u - (1 - h) * Q_prev)) := by
    field_simp [ne_of_gt hh]
    ring
  refine ⟨?_, hcorr⟩
  rw [hid]
  exact le_add_of_nonneg_left hres

end Bandits.Support.CorrectedPositivity
