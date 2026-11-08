/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CanonicalOrientedSetLaw
public import Bandits.Support.CanonicalRecordingRates
public import Bandits.Support.ContinuousCategorical

import Bandits.Support.CanonicalFastMarginalEstimate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Canonical uniformly explored fast-arm law

This module constructs the source mixture on the actual complement of the
existing slow-set carrier, proves its feasibility and auxiliary-arm bound, and
realizes it with one continuous scalar in increasing arm order. The source
formulas are in `sources/zip4/manuscript/04_slow_fast_learner.tex:24-46,96-138`,
`sources/zip4/manuscript/05_binary_transport.tex:128-153`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-44`.

These are internal fixed-weight, fixed-slow-set results. They do not assert an
adaptive conditional-history law, an execution semantics, or manuscript-lemma
closure.
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory

namespace Bandits.Support.CanonicalFastSampling

open Bandits.Support.CanonicalOrientedSetLaw
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.ConstructorDimensions
open Bandits.Support.FiniteOrientationDisintegration
open Bandits.Support.ProductSetLaw

/-- The literal complement of a supported slow set in the full arm carrier.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:20-29`. -/
abbrev fastArmFinset {p : Parameters} (U : SlowSet p.K p.m) : Finset (Fin p.K) :=
  Finset.univ \ U.val

/-- The actual fast-arm carrier, as a subtype of the slow-set complement.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:20-29`. -/
abbrev FastArm {p : Parameters} (U : SlowSet p.K p.m) :=
  {j : Fin p.K // j ∈ (Finset.univ : Finset (Fin p.K)) \ U.val}

/-- The complement has exactly `K - m + 1` arms. -/
theorem fastArmFinset_card {p : Parameters} (U : SlowSet p.K p.m) :
    (fastArmFinset U).card = p.K - p.m + 1 := by
  have hslow : U.val.card + 1 = p.m := slowSet_card p.two_le_m U
  have hmK := p.m_lt_K
  change (Finset.univ \ U.val).card = _
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ U.val),
    Finset.card_univ, Fintype.card_fin]
  omega

/-- The complement has at least two arms, as required by the source algorithm. -/
theorem fastArmFinset_card_ge_two {p : Parameters} (U : SlowSet p.K p.m) :
    2 ≤ (fastArmFinset U).card := by
  rw [fastArmFinset_card]
  have hm := p.two_le_m
  have hmK := p.m_lt_K
  omega

/-- The scalar categorical carrier has positive finite cardinality. -/
theorem fastArmCardinality_ge_two {p : Parameters} (U : SlowSet p.K p.m) :
    2 ≤ p.K - p.m + 1 := by
  rw [← fastArmFinset_card]
  exact fastArmFinset_card_ge_two U

/-- The complement subtype is nonempty, derived from the actual slow-set
cardinality and `m < K`. -/
theorem fastArm_nonempty {p : Parameters} (U : SlowSet p.K p.m) :
    Nonempty (FastArm U) := by
  classical
  have h := slowSet_complement_nonempty p.two_le_m p.m_lt_K U
  rcases h with ⟨j, hj⟩
  exact ⟨⟨j, hj⟩⟩

/-- The ordered complement enumeration is the accepted finite-set order
isomorphism, so its order is increasing arm label. -/
@[expose] noncomputable def fastArmOrderIso {p : Parameters} (U : SlowSet p.K p.m) :
    Fin (p.K - p.m + 1) ≃o FastArm U := by
  classical
  exact (fastArmFinset U).orderIsoOfFin (by rw [fastArmFinset_card])

/-- The source fast-arm probability with the literal uniform-exploration
mixture. The conditional component is the existing `conditionalFastLaw`; its
carrier, anchor semantics, and denominator are not redefined here.

All source assumptions are explicit: positive anchor/current weights, the
pointwise `v ≤ w ≤ 2v` comparison, and the literal learning-rate cap.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:24-29,96-113`. -/
@[expose] noncomputable def qGamma (p : Parameters) (eta : ℝ)
    (_heta : 0 < eta)
    (_heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (_hvw : ∀ j, v j ≤ w j) (_hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (j : FastArm U) : ℝ :=
  (1 - gamma p eta) *
      conditionalFastLaw (Finset.univ : Finset (Fin p.K)) w v U.val
        (Finset.subset_univ _) (slowSet_complement_nonempty p.two_le_m p.m_lt_K U)
        (fun a _ => hw a) (fun a _ => hv a) j +
    gamma p eta / ((p.K - p.m + 1 : ℕ) : ℝ)

private theorem gamma_bounds {p : Parameters} {eta : ℝ} (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ))) :
    0 ≤ gamma p eta ∧ gamma p eta ≤ 1 / 2 :=
  gamma_nonneg_and_le_half p (eta := eta) heta heta_le

private theorem currentConditionalFastLaw_pos (p : Parameters)
    (v w : Fin p.K → ℝ) (hw : ∀ j, 0 < w j) (hv : ∀ j, 0 < v j)
    (U : SlowSet p.K p.m) (j : FastArm U) :
    0 < conditionalFastLaw (Finset.univ : Finset (Fin p.K)) w v U.val
      (Finset.subset_univ _) (slowSet_complement_nonempty p.two_le_m p.m_lt_K U)
      (fun a _ => hw a) (fun a _ => hv a) j := by
  exact conditionalFastLaw_pos (Finset.univ : Finset (Fin p.K)) U.val w v
    (Finset.subset_univ _) (slowSet_complement_nonempty p.two_le_m p.m_lt_K U)
    (fun a _ => hw a) (fun a _ => hv a) j

/-- The mixture assigns strictly positive mass to every complement arm. -/
theorem qGamma_pos (p : Parameters) {eta : ℝ} (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (j : FastArm U) :
    0 < qGamma p eta heta heta_le v w hv hw hvw hwv U j := by
  have hgamma := gamma_bounds (p := p) (eta := eta) heta heta_le
  have hconditional := currentConditionalFastLaw_pos p v w hw hv U j
  have hcoef : 0 < 1 - gamma p eta := by linarith [hgamma.2]
  have hF : (0 : ℝ) < ((p.K - p.m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < p.K - p.m + 1 by omega)
  unfold qGamma
  have huniform : 0 < gamma p eta / ((p.K - p.m + 1 : ℕ) : ℝ) := by
    unfold gamma
    exact div_pos
      (mul_pos (mul_pos (by norm_num) hF) (beta_pos p heta)) hF
  exact add_pos (mul_pos hcoef hconditional) huniform

/-- Nonnegativity of the canonical mixture follows from its two component
probability laws and the source learning-rate cap. -/
theorem qGamma_nonneg (p : Parameters) {eta : ℝ} (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (j : FastArm U) :
    0 ≤ qGamma p eta heta heta_le v w hv hw hvw hwv U j :=
  (qGamma_pos p heta heta_le v w hv hw hvw hwv U j).le

/-- The literal mixture normalizes on the actual complement subtype. -/
theorem qGamma_sum_eq_one (p : Parameters) {eta : ℝ} (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) :
    (∑ j : FastArm U, qGamma p eta heta heta_le v w hv hw hvw hwv U j) = 1 := by
  classical
  let q0 (j : FastArm U) :=
    conditionalFastLaw (Finset.univ : Finset (Fin p.K)) w v U.val
      (Finset.subset_univ _) (slowSet_complement_nonempty p.two_le_m p.m_lt_K U)
      (fun a _ => hw a) (fun a _ => hv a) j
  have hq0 : (∑ j : FastArm U, q0 j) = 1 := by
    change (∑ j ∈ (fastArmFinset U).attach, q0 j) = 1
    simpa only [q0, fastArmFinset] using
      (conditionalFastLaw_sum_eq_one (Finset.univ : Finset (Fin p.K)) U.val w v
        (Finset.subset_univ _) (slowSet_complement_nonempty p.two_le_m p.m_lt_K U)
        (fun a _ => hw a) (fun a _ => hv a))
  have hcard : (Fintype.card (FastArm U) : ℝ) =
      ((p.K - p.m + 1 : ℕ) : ℝ) := by
    rw [Fintype.card_coe, fastArmFinset_card]
  have hdenom : (0 : ℝ) < ((p.K - p.m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt
      (Nat.lt_of_lt_of_le (by decide : 1 < 2) (fastArmCardinality_ge_two U)))
  calc
    (∑ j : FastArm U, qGamma p eta heta heta_le v w hv hw hvw hwv U j) =
        (1 - gamma p eta) * (∑ j : FastArm U, q0 j) +
          (Fintype.card (FastArm U) : ℝ) *
            (gamma p eta / ((p.K - p.m + 1 : ℕ) : ℝ)) := by
      change (∑ j : FastArm U,
          ((1 - gamma p eta) * q0 j + gamma p eta /
            ((p.K - p.m + 1 : ℕ) : ℝ))) = _
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    _ = 1 := by
      rw [hq0, hcard]
      have hcancel :
          ((p.K - p.m + 1 : ℕ) : ℝ) *
            (gamma p eta / ((p.K - p.m + 1 : ℕ) : ℝ)) = gamma p eta := by
        field_simp [ne_of_gt hdenom]
      rw [hcancel]
      ring

/-- The exact normalized probability mass function induced by `qGamma`. -/
@[expose] noncomputable def qGammaPMF (p : Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) : PMF (FastArm U) :=
  PMF.ofFintype
    (fun j => ENNReal.ofReal (qGamma p eta heta heta_le v w hv hw hvw hwv U j))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun j _ => qGamma_nonneg p heta heta_le v w hv hw hvw hwv U j),
        qGamma_sum_eq_one p heta heta_le v w hv hw hvw hwv U,
        ENNReal.ofReal_one])

/-- Exact point masses of the constructed fast-arm PMF. -/
@[simp] theorem qGammaPMF_apply (p : Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (j : FastArm U) :
    qGammaPMF p eta heta heta_le v w hv hw hvw hwv U j =
      ENNReal.ofReal (qGamma p eta heta heta_le v w hv hw hvw hwv U j) := rfl

private theorem conditionalFastLaw_ge_sixteen_m_mul_f_of_mem (p : Parameters)
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (i : Fin p.K)
    (hi : i ∈ fastArmFinset U) :
    conditionalFastLaw (Finset.univ : Finset (Fin p.K)) w v U.val
      (Finset.subset_univ _) (slowSet_complement_nonempty p.two_le_m p.m_lt_K U)
      (fun a _ => hw a) (fun a _ => hv a) ⟨i, hi⟩ ≥
      16 * (p.m : ℝ) * f p v i := by
  have hm := p.two_le_m
  have hmK := p.m_lt_K
  have hcard : U.val.card = p.m - 1 := by
    have h := slowSet_card p.two_le_m U
    omega
  have hnot : i ∉ U.val := (Finset.mem_sdiff.mp hi).2
  have hbase := CanonicalFastMarginalEstimate.canonical_fast_conditional_lower_bound
    v w U.val i p.two_le_m p.m_lt_K hv hw hvw hwv hcard hnot
  let θ := ProductSetLaw.theta p.m v i
  let a := ((p.K - p.m + 1 : ℕ) : ℝ)
  let b := (p.m : ℝ) * (1 - θ)
  have hθpos : 0 < θ := by
    dsimp [θ]
    exact ProductSetLaw.theta_pos v i (Nat.zero_lt_of_lt p.two_le_m) p.m_lt_K hv
  have hθlt : θ < 1 := by
    dsimp [θ]
    exact ProductSetLaw.theta_lt_one v i (Nat.zero_lt_of_lt p.two_le_m) p.m_lt_K hv
  have hapos : 0 < a := by
    dsimp [a]
    exact_mod_cast (show 0 < p.K - p.m + 1 by omega)
  have hbpos : 0 < b := by
    dsimp [b]
    exact mul_pos (Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)) (sub_pos.mpr hθlt)
  have hKpos : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hdenA : 0 < 2 * (a * θ + b) := by positivity
  have hdenK : 0 < 2 * ((p.K : ℝ) * θ + b) := by positivity
  have hAleK : a ≤ (p.K : ℝ) := by
    dsimp [a]
    exact_mod_cast (show p.K - p.m + 1 ≤ p.K by omega)
  have hdenLe : 2 * (a * θ + b) ≤ 2 * ((p.K : ℝ) * θ + b) := by
    have hprod := mul_le_mul_of_nonneg_right hAleK hθpos.le
    nlinarith
  have hfrac : θ / (2 * ((p.K : ℝ) * θ + b)) ≤ θ / (2 * (a * θ + b)) := by
    apply (div_le_div_iff₀ hdenK hdenA).2
    nlinarith
  have hfidentity :
      16 * (p.m : ℝ) * f p v i = θ / (2 * ((p.K : ℝ) * θ + b)) := by
    have hmne : (p.m : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (ConstructorDimensions.m_pos p))
    have hdenne : (p.K : ℝ) * θ + b ≠ 0 := ne_of_gt (by positivity)
    unfold f
    dsimp [θ, b]
    field_simp [hmne, hdenne]; ring
  have hbase' :
      conditionalFastLaw (Finset.univ : Finset (Fin p.K)) w v U.val
        (Finset.subset_univ _) (slowSet_complement_nonempty p.two_le_m p.m_lt_K U)
        (fun a _ => hw a) (fun a _ => hv a) ⟨i, hi⟩ ≥ θ / (2 * (a * θ + b)) := by
    simpa [fastArmFinset, θ, a, b] using hbase
  change _ ≥ 16 * (p.m : ℝ) * f p v i
  rw [hfidentity]
  exact hfrac.trans hbase'

/-- The accepted fixed-anchor conditional bound yields the source `16 m f_i`
lower bound for every genuine complement arm. -/
theorem conditionalFastLaw_ge_sixteen_m_mul_f (p : Parameters)
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (i : FastArm U) :
    conditionalFastLaw (Finset.univ : Finset (Fin p.K)) w v U.val
      (Finset.subset_univ _) (slowSet_complement_nonempty p.two_le_m p.m_lt_K U)
      (fun a _ => hw a) (fun a _ => hv a) i ≥
      16 * (p.m : ℝ) * f p v i :=
  conditionalFastLaw_ge_sixteen_m_mul_f_of_mem p v w hv hw hvw hwv U i.1 i.2

/-- The uniform component contributes exactly `32 β` to each fast-arm mass. -/
theorem qGamma_uniform_contribution_eq (p : Parameters) (eta : ℝ) :
    gamma p eta / ((p.K - p.m + 1 : ℕ) : ℝ) = 32 * beta p eta := by
  have hden : (0 : ℝ) < ((p.K - p.m + 1 : ℕ) : ℝ) := by positivity
  unfold gamma
  field_simp [ne_of_gt hden]

/-- The explored uniform arm mass dominates `32 f_i`, by the literal source
bound on `f_i` and the derived complement cardinality. -/
private theorem uniform_mass_ge_32_f (p : Parameters) (v : Fin p.K → ℝ)
    (hv : ∀ j, 0 < v j) (i : Fin p.K) :
    32 * f p v i ≤ 1 / ((p.K - p.m + 1 : ℕ) : ℝ) := by
  have hm := p.two_le_m
  have hmK := p.m_lt_K
  have hfb := f_le_one_div_32mK p v hv i
  have hmpos : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
  have hKpos : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hFpos : 0 < ((p.K - p.m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < p.K - p.m + 1 by omega)
  have hFleK : ((p.K - p.m + 1 : ℕ) : ℝ) ≤ (p.K : ℝ) := by
    exact_mod_cast (show p.K - p.m + 1 ≤ p.K by omega)
  have hmKle : (p.K : ℝ) ≤ (p.m : ℝ) * (p.K : ℝ) := by
    have hmNatOne : 1 ≤ p.m := by omega
    have hmge1 : (1 : ℝ) ≤ (p.m : ℝ) := by exact_mod_cast hmNatOne
    nlinarith
  have hfirst : 32 * f p v i ≤ 1 / ((p.m : ℝ) * (p.K : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hfb (by norm_num : (0 : ℝ) ≤ 32)
    have hden : (0 : ℝ) < 32 * (p.m : ℝ) * (p.K : ℝ) := by positivity
    rw [div_eq_mul_inv] at hmul ⊢
    field_simp [ne_of_gt hden, ne_of_gt hmpos, ne_of_gt hKpos] at hmul ⊢
    nlinarith
  have hsecond :
      1 / ((p.m : ℝ) * (p.K : ℝ)) ≤
        1 / ((p.K - p.m + 1 : ℕ) : ℝ) := by
    apply (div_le_div_iff₀ (mul_pos hmpos hKpos) hFpos).2
    nlinarith [hFleK, hmKle]
  exact hfirst.trans hsecond

/-- Exact source feasibility: the explored law dominates
`32 * max(β, f_i)`, and hence `16 ξ_i`, for each complement arm. -/
theorem qGamma_ge_32_max (p : Parameters) {eta : ℝ} (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (i : FastArm U) :
    32 * max (beta p eta) (f p v i.1) ≤
      qGamma p eta heta heta_le v w hv hw hvw hwv U i := by
  have hgamma := gamma_bounds (p := p) (eta := eta) heta heta_le
  have hqpos := currentConditionalFastLaw_pos p v w hw hv U i
  have hqf := conditionalFastLaw_ge_sixteen_m_mul_f p v w hv hw hvw hwv U i
  have hqf32 : 32 * f p v i.1 ≤
      conditionalFastLaw (Finset.univ : Finset (Fin p.K)) w v U.val
        (Finset.subset_univ _) (slowSet_complement_nonempty p.two_le_m p.m_lt_K U)
        (fun a _ => hw a) (fun a _ => hv a) i := by
    have hmge2 : (2 : ℝ) ≤ (p.m : ℝ) := by exact_mod_cast p.two_le_m
    nlinarith
  have huniform := uniform_mass_ge_32_f p v hv i.1
  have hcoef : 0 ≤ 1 - gamma p eta := by linarith [hgamma.2]
  have hmix_f : 32 * f p v i.1 ≤
      qGamma p eta heta heta_le v w hv hw hvw hwv U i := by
    unfold qGamma
    have hconvex := add_le_add
      (mul_le_mul_of_nonneg_left hqf32 hcoef)
      (mul_le_mul_of_nonneg_left huniform hgamma.1)
    have hsumWeights : (1 - gamma p eta) + gamma p eta = 1 := by ring
    calc
      32 * f p v i.1 = ((1 - gamma p eta) + gamma p eta) *
          (32 * f p v i.1) := by rw [hsumWeights, one_mul]
      _ = (1 - gamma p eta) * (32 * f p v i.1) +
          gamma p eta * (32 * f p v i.1) := by rw [add_mul]
      _ ≤ (1 - gamma p eta) *
            conditionalFastLaw (Finset.univ : Finset (Fin p.K)) w v U.val
              (Finset.subset_univ _) (slowSet_complement_nonempty p.two_le_m p.m_lt_K U)
              (fun a _ => hw a) (fun a _ => hv a) i +
            gamma p eta * (1 / ((p.K - p.m + 1 : ℕ) : ℝ)) := hconvex
      _ = qGamma p eta heta heta_le v w hv hw hvw hwv U i := by
        simp only [qGamma]
        ring
  have hbeta : 32 * beta p eta ≤
      qGamma p eta heta heta_le v w hv hw hvw hwv U i := by
    unfold qGamma
    have hfirst : 0 ≤ (1 - gamma p eta) *
        conditionalFastLaw (Finset.univ : Finset (Fin p.K)) w v U.val
          (Finset.subset_univ _) (slowSet_complement_nonempty p.two_le_m p.m_lt_K U)
          (fun a _ => hw a) (fun a _ => hv a) i :=
      mul_nonneg hcoef hqpos.le
    rw [qGamma_uniform_contribution_eq p eta]
    linarith
  by_cases hbf : beta p eta ≤ f p v i.1
  · rw [max_eq_right hbf]
    exact hmix_f
  · have hfβ : f p v i.1 ≤ beta p eta := le_of_not_ge hbf
    rw [max_eq_left hfβ]
    exact hbeta

/-- The dyadic envelope turns the previous lower bound into the exact source
feasibility inequality `qΓ_i ≥ 16 ξ_i`. -/
theorem qGamma_ge_16_xi (p : Parameters) {eta : ℝ} (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (i : FastArm U) :
    16 * xi p eta v i.1 ≤ qGamma p eta heta heta_le v w hv hw hvw hwv U i := by
  have hmax := qGamma_ge_32_max p heta heta_le v w hv hw hvw hwv U i
  have hxi := xi_lt_two_max p heta v i.1
  have hscaled : 16 * xi p eta v i.1 < 32 * max (beta p eta) (f p v i.1) := by
    nlinarith
  exact (le_of_lt hscaled).trans hmax

/-- The complement's inverse-CDF sampler, using the accepted continuous
`[0,1)` carrier and increasing-arm order. -/
@[expose] noncomputable def sampleFast (p : Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (x : ContinuousCategorical.Scalar) : FastArm U :=
  fastArmOrderIso U
    (ContinuousCategorical.sample
      (Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le (by decide : 1 < 2)
        (fastArmCardinality_ge_two U)))
      (fun k => qGamma p eta heta heta_le v w hv hw hvw hwv U (fastArmOrderIso U k))
      (by
        calc
          (∑ k, qGamma p eta heta heta_le v w hv hw hvw hwv U
              (fastArmOrderIso U k)) =
              ∑ j : FastArm U, qGamma p eta heta heta_le v w hv hw hvw hwv U j :=
            Equiv.sum_comp (fastArmOrderIso U).toEquiv _
          _ = 1 := qGamma_sum_eq_one p heta heta_le v w hv hw hvw hwv U) x)

/-- The scalar realization is measurable on the genuine continuous input
carrier. -/
theorem measurable_sampleFast (p : Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) :
    Measurable (sampleFast p eta heta heta_le v w hv hw hvw hwv U) := by
  classical
  apply measurable_to_countable'
  intro j
  let masses (k : Fin (p.K - p.m + 1)) :=
    qGamma p eta heta heta_le v w hv hw hvw hwv U (fastArmOrderIso U k)
  have hmasssum : (∑ k, masses k) = 1 := by
    calc
      (∑ k, masses k) =
          ∑ j : FastArm U, qGamma p eta heta heta_le v w hv hw hvw hwv U j := by
        simp only [masses]
        exact Equiv.sum_comp (fastArmOrderIso U).toEquiv _
      _ = 1 := qGamma_sum_eq_one p heta heta_le v w hv hw hvw hwv U
  have hmasses_nonneg : ∀ k, 0 ≤ masses k := by
    intro k
    exact qGamma_nonneg p heta heta_le v w hv hw hvw hwv U (fastArmOrderIso U k)
  have hn : 0 < p.K - p.m + 1 :=
    Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le (by decide : 1 < 2)
      (fastArmCardinality_ge_two U))
  have hfiber :
      sampleFast p eta heta heta_le v w hv hw hvw hwv U ⁻¹' {j} =
        ContinuousCategorical.sample hn masses hmasssum ⁻¹'
          { (fastArmOrderIso U).symm j } := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, sampleFast, masses]
    constructor
    · intro h
      have h' := congrArg (fastArmOrderIso U).symm h
      simpa using h'
    · intro h
      have h' := congrArg (fastArmOrderIso U) h
      simpa using h'
  rw [hfiber]
  exact (measurableSet_singleton ((fastArmOrderIso U).symm j)).preimage
    (ContinuousCategorical.measurable_sample hn hmasses_nonneg hmasssum)

/-- Exact singleton masses of the one-scalar sampler. -/
theorem uniform_sampleFast_singleton (p : Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (j : FastArm U) :
    ContinuousCategorical.uniform
        (sampleFast p eta heta heta_le v w hv hw hvw hwv U ⁻¹' {j}) =
      ENNReal.ofReal (qGamma p eta heta heta_le v w hv hw hvw hwv U j) := by
  have hsum := qGamma_sum_eq_one p heta heta_le v w hv hw hvw hwv U
  have hpnonneg : ∀ k : Fin (p.K - p.m + 1),
      0 ≤ qGamma p eta heta heta_le v w hv hw hvw hwv U (fastArmOrderIso U k) :=
    fun k => qGamma_nonneg p heta heta_le v w hv hw hvw hwv U (fastArmOrderIso U k)
  let mass := fun k : Fin (p.K - p.m + 1) =>
    qGamma p eta heta heta_le v w hv hw hvw hwv U (fastArmOrderIso U k)
  have hmasssum : (∑ k, mass k) = 1 := by
    calc
      (∑ k, mass k) =
          ∑ j : FastArm U, qGamma p eta heta heta_le v w hv hw hvw hwv U j := by
        simp only [mass]
        exact Equiv.sum_comp (fastArmOrderIso U).toEquiv _
      _ = 1 := hsum
  have hfiber :
      sampleFast p eta heta heta_le v w hv hw hvw hwv U ⁻¹' {j} =
        ContinuousCategorical.sample
          (Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le (by decide : 1 < 2)
            (fastArmCardinality_ge_two U)))
          mass hmasssum ⁻¹' { (fastArmOrderIso U).symm j } := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, sampleFast, mass]
    constructor
    · intro h
      have h' := congrArg (fastArmOrderIso U).symm h
      simpa using h'
    · intro h
      have h' := congrArg (fastArmOrderIso U) h
      simpa using h'
  rw [hfiber]
  rw [ContinuousCategorical.uniform_sample_singleton
    (Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le (by decide : 1 < 2)
      (fastArmCardinality_ge_two U)))
    hpnonneg hmasssum]
  congr 1
  change mass ((fastArmOrderIso U).symm j) =
    qGamma p eta heta heta_le v w hv hw hvw hwv U j
  simp [mass]

/-- The one-scalar sampler pushes the existing uniform `[0,1)` law to the
constructed fast PMF. The proof is by the exact interval masses of every atom.
-/
theorem uniform_map_sampleFast (p : Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) :
    ContinuousCategorical.uniform.map
        (sampleFast p eta heta heta_le v w hv hw hvw hwv U) =
      (qGammaPMF p eta heta heta_le v w hv hw hvw hwv U).toMeasure := by
  apply Measure.ext_of_singleton
  intro j
  rw [Measure.map_apply (measurable_sampleFast p eta heta heta_le v w hv hw hvw hwv U)
      (measurableSet_singleton j),
    uniform_sampleFast_singleton p eta heta heta_le v w hv hw hvw hwv U j,
    PMF.toMeasure_apply_singleton _ j (measurableSet_singleton j), qGammaPMF_apply]

private theorem conditionalFastLaw_minimal_arm_upper_bound (p : Parameters)
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (e : FastArm U)
    (hmin : ∀ j : FastArm U, v e.1 ≤ v j.1) :
    conditionalFastLaw (Finset.univ : Finset (Fin p.K)) w v U.val
      (Finset.subset_univ _) (slowSet_complement_nonempty p.two_le_m p.m_lt_K U)
      (fun a _ => hw a) (fun a _ => hv a) e ≤
        2 / ((fastArmFinset U).card + 1 : ℕ) := by
  classical
  let q (j : FastArm U) :=
    conditionalFastLaw (Finset.univ : Finset (Fin p.K)) w v U.val
      (Finset.subset_univ _) (slowSet_complement_nonempty p.two_le_m p.m_lt_K U)
      (fun a _ => hw a) (fun a _ => hv a) j
  let Z := candidateNormalizer (Finset.univ : Finset (Fin p.K)) w v U.val
  have hZpos := candidateNormalizer_pos (Finset.univ : Finset (Fin p.K)) U.val w v
    (Finset.subset_univ _) (slowSet_complement_nonempty p.two_le_m p.m_lt_K U)
    (fun a _ => hw a) (fun a _ => hv a)
  have hsnonneg := inverseAnchorSum_nonneg (Finset.univ : Finset (Fin p.K)) U.val v
    (Finset.subset_univ _) (fun a _ => hv a)
  have hden (j : FastArm U) :
      0 < 1 + inverseAnchorSum v U.val * v j.1 :=
    candidateWeight_denominator_pos (Finset.univ : Finset (Fin p.K)) U.val v
      (Finset.subset_univ _) (fun a _ => hv a) j
  have hcurrentLower (j : FastArm U) :
      candidateWeight v v U.val j.1 ≤ candidateWeight w v U.val j.1 := by
    unfold candidateWeight
    exact div_le_div_of_nonneg_right (hvw j.1) (hden j).le
  have hcurrentUpper (j : FastArm U) :
      candidateWeight w v U.val j.1 ≤ 2 * candidateWeight v v U.val j.1 := by
    unfold candidateWeight
    calc
      w j.1 / (1 + inverseAnchorSum v U.val * v j.1) ≤
          (2 * v j.1) / (1 + inverseAnchorSum v U.val * v j.1) :=
        div_le_div_of_nonneg_right (hwv j.1) (hden j).le
      _ = 2 * (v j.1 / (1 + inverseAnchorSum v U.val * v j.1)) := by ring
  have hanchorMonotone (j : FastArm U) :
      candidateWeight v v U.val e.1 ≤ candidateWeight v v U.val j.1 := by
    unfold candidateWeight
    apply (div_le_div_iff₀ (hden e) (hden j)).2
    nlinarith [hmin j]
  have hpair (j : FastArm U) (hje : j ≠ e) : q e / 2 ≤ q j := by
    have hweight : candidateWeight w v U.val e.1 ≤
        2 * candidateWeight w v U.val j.1 := by
      calc
        candidateWeight w v U.val e.1 ≤ 2 * candidateWeight v v U.val e.1 :=
          hcurrentUpper e
        _ ≤ 2 * candidateWeight v v U.val j.1 :=
          mul_le_mul_of_nonneg_left (hanchorMonotone j) (by norm_num)
        _ ≤ 2 * candidateWeight w v U.val j.1 :=
          mul_le_mul_of_nonneg_left (hcurrentLower j) (by norm_num)
    have hweight' : candidateWeight w v U.val e.1 / 2 ≤
        candidateWeight w v U.val j.1 := by nlinarith
    have hquot := div_le_div_of_nonneg_right hweight' hZpos.le
    change (candidateWeight w v U.val e.1 / Z) / 2 ≤
      candidateWeight w v U.val j.1 / Z
    dsimp [q, Z]
    calc
      (candidateWeight w v U.val e.1 /
          candidateNormalizer (Finset.univ : Finset (Fin p.K)) w v U.val) / 2 =
        (candidateWeight w v U.val e.1 / 2) /
          candidateNormalizer (Finset.univ : Finset (Fin p.K)) w v U.val := by ring
      _ ≤ candidateWeight w v U.val j.1 /
          candidateNormalizer (Finset.univ : Finset (Fin p.K)) w v U.val := hquot
  have hsum : (∑ j : FastArm U, q j) = 1 := by
    change (∑ j ∈ (fastArmFinset U).attach, q j) = 1
    simpa only [q, fastArmFinset] using
      (conditionalFastLaw_sum_eq_one (Finset.univ : Finset (Fin p.K)) U.val w v
        (Finset.subset_univ _) (slowSet_complement_nonempty p.two_le_m p.m_lt_K U)
        (fun a _ => hw a) (fun a _ => hv a))
  have he_mem : e ∈ (Finset.univ : Finset (FastArm U)) := Finset.mem_univ _
  have hsplit : 1 = q e + ∑ j ∈ (Finset.univ : Finset (FastArm U)).erase e, q j := by
    calc
      1 = ∑ j : FastArm U, q j := hsum.symm
      _ = q e + ∑ j ∈ (Finset.univ : Finset (FastArm U)).erase e, q j := by
        rw [← Finset.sum_erase_add _ _ he_mem]
        ring
  have hsumLower :
      (∑ j ∈ (Finset.univ : Finset (FastArm U)).erase e, q e / 2) ≤
        ∑ j ∈ (Finset.univ : Finset (FastArm U)).erase e, q j := by
    apply Finset.sum_le_sum
    intro j hj
    have hje : j ≠ e := (Finset.mem_erase.mp hj).1
    exact hpair j hje
  have hsumLowerEq :
      (∑ j ∈ (Finset.univ : Finset (FastArm U)).erase e, q e / 2) =
        (((Fintype.card (FastArm U) - 1 : ℕ) : ℝ) * (q e / 2)) := by
    rw [Finset.sum_const, Finset.card_erase_of_mem he_mem, Finset.card_univ,
      nsmul_eq_mul]
  have hcard_ge_one : 1 ≤ Fintype.card (FastArm U) := by
    have hF := fastArmFinset_card_ge_two U
    have hcardNat : Fintype.card (FastArm U) = (fastArmFinset U).card := by simp
    rw [hcardNat]
    omega
  have hcastSub :
      ((Fintype.card (FastArm U) - 1 : ℕ) : ℝ) =
        (Fintype.card (FastArm U) : ℝ) - 1 := by
    rw [Nat.cast_sub hcard_ge_one, Nat.cast_one]
  have hnum : (q e) * (((Fintype.card (FastArm U) : ℝ) + 1) / 2) ≤ 1 := by
    rw [hsumLowerEq] at hsumLower
    rw [hcastSub] at hsumLower
    have hlinear : q e +
        ((Fintype.card (FastArm U) : ℝ) - 1) * (q e / 2) =
          q e * (((Fintype.card (FastArm U) : ℝ) + 1) / 2) := by ring
    nlinarith [hsplit, hsumLower, hlinear]
  have hden : 0 < ((Fintype.card (FastArm U) : ℝ) + 1) / 2 := by positivity
  have hq := (le_div_iff₀ hden).2 hnum
  have hcardCast : (Fintype.card (FastArm U) : ℝ) =
      ((fastArmFinset U).card : ℝ) := by simp
  have htargetDen : 0 < ((fastArmFinset U).card + 1 : ℕ) := by omega
  have hrewrite :
      2 / ((fastArmFinset U).card + 1 : ℕ) =
        1 / (((Fintype.card (FastArm U) : ℝ) + 1) / 2) := by
    rw [hcardCast]
    push_cast
    field_simp [ne_of_gt htargetDen]
  change q e ≤ _
  rw [hrewrite]
  exact hq

/-- For an actual complement arm minimizing the anchor weight, the canonical
uniformly explored fast law is at most `2/3`. Minimality is supplied as the
source premise on this queried arm; no arbitrary minimizer is selected. -/
theorem qGamma_auxiliary_arm_le_two_thirds (p : Parameters) {eta : ℝ}
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (e : FastArm U)
    (hmin : ∀ j : FastArm U, v e.1 ≤ v j.1) :
    qGamma p eta heta heta_le v w hv hw hvw hwv U e ≤ 2 / 3 := by
  have hgamma := gamma_bounds (p := p) (eta := eta) heta heta_le
  have hq := conditionalFastLaw_minimal_arm_upper_bound p v w hv hw hvw hwv U e hmin
  have hcard := fastArmFinset_card_ge_two U
  have hFpos : 0 < ((fastArmFinset U).card : ℝ) := by
    have hFcard := fastArmFinset_card_ge_two U
    exact_mod_cast (show 0 < (fastArmFinset U).card by omega)
  have huniform : 1 / ((fastArmFinset U).card : ℝ) ≤ 2 / 3 := by
    have hFreal : (2 : ℝ) ≤ ((fastArmFinset U).card : ℝ) := by exact_mod_cast hcard
    apply (div_le_div_iff₀ hFpos (by norm_num : (0 : ℝ) < 3)).2
    norm_num
    nlinarith
  have hconditional :
      (2 : ℝ) / ((fastArmFinset U).card + 1 : ℕ) ≤ (2 : ℝ) / 3 := by
    have hdenPos :
        (0 : ℝ) < ((fastArmFinset U).card + 1 : ℕ) := by positivity
    have hdenGe :
        (3 : ℝ) ≤ ((fastArmFinset U).card + 1 : ℕ) := by
      exact_mod_cast (show 3 ≤ (fastArmFinset U).card + 1 by omega)
    apply (div_le_div_iff₀ hdenPos (by norm_num : (0 : ℝ) < 3)).2
    nlinarith
  have hcoeff : 0 ≤ 1 - gamma p eta := by linarith [hgamma.2]
  unfold qGamma
  calc
    (1 - gamma p eta) *
        conditionalFastLaw (Finset.univ : Finset (Fin p.K)) w v U.val
          (Finset.subset_univ _) (slowSet_complement_nonempty p.two_le_m p.m_lt_K U)
          (fun a _ => hw a) (fun a _ => hv a) e +
      gamma p eta / ((p.K - p.m + 1 : ℕ) : ℝ) ≤
        (1 - gamma p eta) *
          ((2 : ℝ) / ((fastArmFinset U).card + 1 : ℕ)) +
          gamma p eta * (2 / 3) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hq hcoeff
            · have hmass := huniform
              rw [fastArmFinset_card] at hmass
              have hmass' :
                  1 / ((p.K - p.m + 1 : ℕ) : ℝ) ≤ 2 / 3 := by
                exact hmass
              calc
                gamma p eta / ((p.K - p.m + 1 : ℕ) : ℝ) =
                    gamma p eta * (1 / ((p.K - p.m + 1 : ℕ) : ℝ)) := by ring
                _ ≤ gamma p eta * (2 / 3) :=
                  mul_le_mul_of_nonneg_left hmass' hgamma.1
    _ ≤ (1 - gamma p eta) * (2 / 3) + gamma p eta * (2 / 3) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hconditional hcoeff
      · rfl
    _ = 2 / 3 := by ring

end Bandits.Support.CanonicalFastSampling

end
