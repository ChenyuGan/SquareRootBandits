/- Coordinatewise monotonicity of a ratio of source-literal elementary
   symmetric sums. -/
module
public import Bandits.Support.ElementarySymmetricRecurrence

import Bandits.Support.ElementarySymmetricLogConcavity
import Bandits.Support.MarginalRatio
import Mathlib.Tactic.Order

/-!
# Monotonicity of elementary-symmetric coefficient ratios

The main result proves that increasing positive weights cannot increase
`e_(m-1) / e_m`.  Its one-coordinate step uses the source insertion recurrence
and Newton's inequality for the canonical multiset coefficients.  The source
motivation is `sources/zip4/manuscript/04_slow_fast_learner.tex:7-13,84-89`.
This is an internal polynomial ingredient; it does not construct probabilities
or close the source lemma.
-/

public section

namespace Bandits.Support.ElementarySymmetricRatioMonotonicity

open Bandits.Support.ElementarySymmetricRecurrence

variable {α : Type*}

/-- Equality of weights on a finite support gives equality of the source-literal
elementary symmetric sums. -/
theorem elementary_symmetric_congr (J : Finset α) (v w : α → ℝ)
    (hvw : ∀ i ∈ J, v i = w i) (k : ℕ) :
    elementarySymmetric v J k = elementarySymmetric w J k := by
  unfold elementarySymmetric
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.prod_congr rfl
  intro i hi
  exact hvw i ((Finset.mem_powersetCard.mp hs).1 hi)

variable [DecidableEq α]

/-- Replacing one coordinate by a larger positive value cannot increase the
ratio. The other coordinates are identified by erasing the changed index;
Newton's inequality is applied at degree `m - 2` to their canonical
`Multiset.esymm` coefficients. -/
theorem elementary_symmetric_ratio_antitone_single
    (J : Finset α) (v w : α → ℝ) (j : α) (m : ℕ)
    (hj : j ∈ J) (hmlo : 2 ≤ m) (hmhi : m ≤ J.card)
    (hvpos : ∀ i ∈ J, 0 < v i) (hwpos : ∀ i ∈ J, 0 < w i)
    (hcoord : ∀ i ∈ J.erase j, v i = w i) (hvw : v j ≤ w j) :
    elementarySymmetric w J (m - 1) / elementarySymmetric w J m ≤
      elementarySymmetric v J (m - 1) / elementarySymmetric v J m := by
  let I := J.erase j
  let A := elementarySymmetric v I (m - 2)
  let B := elementarySymmetric v I (m - 1)
  let C := elementarySymmetric v I m
  have hjI : j ∉ I := by simp [I]
  have hcoeff (k : ℕ) :
      elementarySymmetric v I k = elementarySymmetric w I k := by
    exact elementary_symmetric_congr I v w (fun i hi => hcoord i (by simpa [I] using hi)) k
  have hnum_v : elementarySymmetric v J (m - 1) =
      elementarySymmetric v I (m - 1) + v j * elementarySymmetric v I (m - 2) := by
    rw [← Finset.insert_erase hj]
    simpa only [show (m - 2) + 1 = m - 1 by omega] using
      elementarySymmetric_insert_succ v I j hjI (m - 2)
  have hden_v : elementarySymmetric v J m =
      elementarySymmetric v I m + v j * elementarySymmetric v I (m - 1) := by
    rw [← Finset.insert_erase hj]
    simpa only [show (m - 1) + 1 = m by omega] using
      elementarySymmetric_insert_succ v I j hjI (m - 1)
  have hnum_w : elementarySymmetric w J (m - 1) =
      elementarySymmetric w I (m - 1) + w j * elementarySymmetric w I (m - 2) := by
    rw [← Finset.insert_erase hj]
    simpa only [show (m - 2) + 1 = m - 1 by omega] using
      elementarySymmetric_insert_succ w I j hjI (m - 2)
  have hden_w : elementarySymmetric w J m =
      elementarySymmetric w I m + w j * elementarySymmetric w I (m - 1) := by
    rw [← Finset.insert_erase hj]
    simpa only [show (m - 1) + 1 = m by omega] using
      elementarySymmetric_insert_succ w I j hjI (m - 1)

  let s := I.val.map v
  have hs_nonneg : ∀ x ∈ s, 0 ≤ x := by
    intro x hx
    rcases Multiset.mem_map.mp hx with ⟨i, hi, rfl⟩
    exact le_of_lt (hvpos i (Finset.mem_of_mem_erase (Finset.mem_val.mp hi)))
  have hnewton :=
    Bandits.Support.ElementarySymmetricLogConcavity.esymm_log_concave s hs_nonneg (m - 2)
  have hAeq : A = s.esymm (m - 2) := by
    simpa only [A, s] using elementarySymmetric_eq_multiset_esymm v I (m - 2)
  have hBeq : B = s.esymm (m - 1) := by
    simpa only [B, s] using elementarySymmetric_eq_multiset_esymm v I (m - 1)
  have hCeq : C = s.esymm m := by
    simpa only [C, s] using elementarySymmetric_eq_multiset_esymm v I m
  have hnewton' : s.esymm (m - 2) * s.esymm m ≤ (s.esymm (m - 1)) ^ 2 := by
    simpa only [show m - 2 + 2 = m by omega,
      show m - 2 + 1 = m - 1 by omega] using hnewton
  have hcurv : A * C ≤ B ^ 2 := by
    calc
      A * C = s.esymm (m - 2) * s.esymm m := by rw [hAeq, hCeq]
      _ ≤ (s.esymm (m - 1)) ^ 2 := hnewton'
      _ = B ^ 2 := by rw [← hBeq]

  have hden_v_pos : 0 < C + v j * B := by
    have hpos := elementarySymmetric_pos v J m hvpos hmhi
    rw [hden_v] at hpos
    simpa only [B, C] using hpos
  have hden_w_pos : 0 < C + w j * B := by
    have hpos := elementarySymmetric_pos w J m hwpos hmhi
    rw [hden_w] at hpos
    rw [← hcoeff m, ← hcoeff (m - 1)] at hpos
    simpa only [B, C] using hpos

  rw [hnum_w, hden_w, hnum_v, hden_v]
  rw [← hcoeff (m - 1), ← hcoeff (m - 2), ← hcoeff m]
  change (B + w j * A) / (C + w j * B) ≤ (B + v j * A) / (C + v j * B)
  exact Bandits.Support.MarginalRatio.ratio_antitone B A C (v j) (w j)
    hvw hcurv hden_v_pos hden_w_pos

/-- For positive weights on `J`, increasing every coordinate weakly decreases
the source-literal ratio `e_(m-1) / e_m`. The finite chain of single-coordinate
updates is constructed in the proof; no chain or curvature property is an
input. -/
theorem elementary_symmetric_ratio_antitone
    (J : Finset α) (v w : α → ℝ) (m : ℕ)
    (hmlo : 2 ≤ m) (hmhi : m ≤ J.card)
    (hvpos : ∀ i ∈ J, 0 < v i) (hwpos : ∀ i ∈ J, 0 < w i)
    (hvw : ∀ i ∈ J, v i ≤ w i) :
    elementarySymmetric w J (m - 1) / elementarySymmetric w J m ≤
      elementarySymmetric v J (m - 1) / elementarySymmetric v J m := by
  let z : Finset α → α → ℝ := fun S i => if i ∈ S then w i else v i
  let R : (α → ℝ) → ℝ := fun f =>
    elementarySymmetric f J (m - 1) / elementarySymmetric f J m
  have zpos (S : Finset α) : ∀ i ∈ J, 0 < z S i := by
    intro i hi
    dsimp [z]
    split_ifs with h
    · exact hwpos i hi
    · exact hvpos i hi
  have step (S : Finset α) (j : α) (hjS : j ∉ S) (hjJ : j ∈ J)
      (hpoint : v j ≤ w j) : R (z (insert j S)) ≤ R (z S) := by
    have hcoord : ∀ i ∈ J.erase j, z S i = z (insert j S) i := by
      intro i hi
      have hij : i ≠ j := (Finset.mem_erase.mp hi).1
      simp [z, hij]
    have hvalue : z S j ≤ z (insert j S) j := by
      simpa [z, hjS] using hpoint
    dsimp [R]
    exact elementary_symmetric_ratio_antitone_single J (z S) (z (insert j S)) j m
      hjJ hmlo hmhi (zpos S) (zpos (insert j S)) hcoord hvalue
  have hchain : ∀ S : Finset α, S ⊆ J → R (z S) ≤ R (z ∅) := by
    intro S hSJ
    induction S using Finset.induction_on with
    | empty => exact le_rfl
    | @insert j S hjS ih =>
        have hjJ : j ∈ J := hSJ (Finset.mem_insert_self j S)
        have hSJ' : S ⊆ J := by
          intro i hi
          exact hSJ (Finset.mem_insert_of_mem hi)
        calc
          R (z (insert j S)) ≤ R (z S) := step S j hjS hjJ (hvw j hjJ)
          _ ≤ R (z ∅) := ih hSJ'
  have hfinal := hchain J (fun _ hi => hi)
  have hzJ (i : α) (hi : i ∈ J) : z J i = w i := by
    simp [z, hi]
  have hz0 (i : α) (hi : i ∈ J) : z ∅ i = v i := by
    simp [z]
  have hcoeffJ (k : ℕ) := elementary_symmetric_congr J (z J) w (fun i hi => hzJ i hi) k
  have hcoeff0 (k : ℕ) := elementary_symmetric_congr J (z ∅) v (fun i hi => hz0 i hi) k
  dsimp [R] at hfinal ⊢
  rw [hcoeffJ (m - 1), hcoeffJ m, hcoeff0 (m - 1), hcoeff0 m] at hfinal
  exact hfinal

end Bandits.Support.ElementarySymmetricRatioMonotonicity
