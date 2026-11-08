module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Helpers for the finite reward-table count and its deterministic row-cost envelope.

The source passage is `sources/zip4/manuscript/08_main_theorem.tex:38,46,55`:
`E_{j,r}(R_j)∈[0,1]`, `G_{j,r}(R_j):=F_{j,r}(R_j)+2mT E_{j,r}(R_j)∈[-mT,3mT]`, and
“There are $(D+1)^{KT}$ denominator-$D$ matrices.” These are internal arithmetic
helpers for the later union bound, not a concentration result.
-/

public section

namespace Bandits.Support.RewardMatrixCount

/-- A denominator-`D` reward table has one of `D + 1` entries at each of `K * T` positions. -/
theorem rewardMatrixCount (D K T : ℕ) :
    Fintype.card (Fin T → Fin K → Fin (D + 1)) = (D + 1) ^ (K * T) := by
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.pow_mul]

/-- The deterministic envelope used for a row cost `F + 2*m*T*E`. -/
theorem combinedCost_mem_Icc {m T F E : ℝ}
    (hm : 0 ≤ m) (hT : 0 ≤ T)
    (hF : -m * T ≤ F ∧ F ≤ m * T)
    (hE : 0 ≤ E ∧ E ≤ 1) :
    F + 2 * m * T * E ∈ Set.Icc (-m * T) (3 * m * T) := by
  have hmt : 0 ≤ m * T := mul_nonneg hm hT
  have htwomt : 0 ≤ 2 * m * T := by nlinarith
  have hterm : 0 ≤ 2 * m * T * E := mul_nonneg htwomt hE.1
  have hterm_le : 2 * m * T * E ≤ 2 * m * T := by
    nlinarith [mul_nonneg htwomt (sub_nonneg.mpr hE.2)]
  constructor
  · calc
      -m * T ≤ F := hF.1
      _ = F + 0 := by ring
      _ ≤ F + 2 * m * T * E := add_le_add_right hterm F
  · calc
      F + 2 * m * T * E ≤ m * T + 2 * m * T := add_le_add hF.2 hterm_le
      _ = 3 * m * T := by ring

end Bandits.Support.RewardMatrixCount
