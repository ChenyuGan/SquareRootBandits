module

public import Mathlib.Basic.Real.Basic
import Bandits.Support.CorrectedPositivity
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
Finite-window scalar domination and the corrected-sampler positivity bound.

Source: `sources/zip4/manuscript/06_interruptions.tex:376-408` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:66-77`.
-/

public section

namespace Bandits.Support.BoundedDomination

/--
Iterating a scalar lower bound over only the finite interval `[u, u + n)` gives
the corresponding `n`-step lower bound. No hypothesis is imposed after that
interval, so the final step may end at an episode boundary.
-/
theorem finiteWindowLowerBound {a : ℝ} (ha : 0 ≤ a) (q : ℕ → ℝ) (u n : ℕ)
    (hstep : ∀ k, u ≤ k → k < u + n → a * q k ≤ q (k + 1)) :
    a ^ n * q u ≤ q (u + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprefix : ∀ k, u ≤ k → k < u + n → a * q k ≤ q (k + 1) := by
        intro k hku hkn
        apply hstep k hku
        omega
      have hiter := ih hprefix
      have hlast : a * q (u + n) ≤ q (u + n + 1) := by
        apply hstep (u + n)
        · omega
        · omega
      calc
        a ^ (n + 1) * q u = a * (a ^ n * q u) := by rw [pow_succ]; ring
        _ ≤ a * q (u + n) := mul_le_mul_of_nonneg_left hiter ha
        _ ≤ q (u + n + 1) := hlast

/--
The corrected-sampler bound on a finite episode window. The one-step premise
from `Q (u - 1)` to `Q u` is stated separately; the iterated premise is needed
only for indices in `[u, u + n)`. The hypothesis `0 < u` makes `u - 1` the
actual preceding index. The exponent `n + 1` in the corrected term is retained,
including when `n = 0` or `h = 1`.
-/
theorem correctedSamplerBounds_of_finiteWindow (h : ℝ) (u n : ℕ) (Q : ℕ → ℝ)
    (hh : 0 < h) (hh_le : h ≤ 1) (hu : 0 < u)
    (hstep : ∀ k, u ≤ k → k < u + n → (1 - h) * Q k ≤ Q (k + 1))
    (hprev : (1 - h) * Q (u - 1) ≤ Q ((u - 1) + 1)) :
    (1 - h) ^ n / h * (Q u - (1 - h) * Q (u - 1)) ≤
        Q (u + n) + (1 - h) ^ (n + 1) / h * (Q u - Q (u - 1)) ∧
      0 ≤ (1 - h) ^ n / h * (Q u - (1 - h) * Q (u - 1)) := by
  have hiter : (1 - h) ^ n * Q u ≤ Q (u + n) :=
    finiteWindowLowerBound (sub_nonneg.mpr hh_le) Q u n hstep
  have hprev' : (1 - h) * Q (u - 1) ≤ Q u := by
    simpa only [Nat.sub_add_cancel hu] using hprev
  exact Bandits.Support.CorrectedPositivity.correctedSamplerBounds h n
    (Q (u + n)) (Q u) (Q (u - 1)) hh hh_le hiter hprev'

end Bandits.Support.BoundedDomination
