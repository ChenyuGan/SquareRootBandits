/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.ProductSetLaw
public import Bandits.Support.ProductSetDistribution
public import Bandits.Support.CanonicalOrientedSetLaw
public import Bandits.Support.CanonicalRecordingRates
public import Bandits.Support.CanonicalFastSampling

import Bandits.Support.FiniteOrientationDisintegration
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fixed-snapshot mixed auxiliary reward

This module proves the finite one-round reward comparison for the existing
slow-set and fast-complement laws. Its finite expectation uses the actual
`slowSetPMF`, `fastArmConditionalMass`, and `qGamma` carriers. It does not
assert an adaptive history law or an accumulated regret comparison.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:7-37,96-113,379-390`.
-/

public section

open scoped BigOperators

namespace Bandits.Support.MixedAuxiliaryReward

open Bandits.Support.CanonicalFastSampling
open Bandits.Support.CanonicalOrientedSetLaw
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ProductSetLaw

/-- Pull a constant through a Fintype sum, stated in the form used by the
dependent finite expectation below. -/
private theorem fintype_mul_sum {α : Type*} [Fintype α] (a : ℝ) (f : α → ℝ) :
    a * (∑ x, f x) = ∑ x, a * f x := by
  classical
  exact Finset.mul_sum _ _ _

/-- Subtraction distributes over a finite Fintype sum. -/
private theorem fintype_sum_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    (∑ x, (f x - g x)) = (∑ x, f x) - ∑ x, g x := by
  classical
  exact Finset.sum_sub_distrib (s := (Finset.univ : Finset α)) f g

/-- Pull a constant right factor out of a finite Fintype sum. -/
private theorem fintype_sum_mul {α : Type*} [Fintype α] (f : α → ℝ) (a : ℝ) :
    (∑ x, f x) * a = ∑ x, f x * a := by
  classical
  exact Finset.sum_mul _ _ _

/-- The literal reward of the supported slow set and its complementary fast
arm.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:20-29,379-382`. -/
@[expose] def oneRoundAuxiliaryReward {p : Parameters}
    (r : Fin p.K → ℝ) (U : SlowSet p.K p.m) (j : FastArm U) : ℝ :=
  (∑ i ∈ U.1, r i) + r j.1

/-- The reward sum on a supported product set. -/
private def productSetReward {K m : ℕ} (r : Fin K → ℝ)
    (S : ProductSet K m) : ℝ :=
  ∑ i ∈ S.1, r i

/-- Expand the supported set reward onto the whole arm carrier with a zero
outside the set. -/
private theorem productSetReward_eq_univ_sum {K m : ℕ}
    (r : Fin K → ℝ) (S : ProductSet K m) :
    productSetReward r S =
      ∑ i : Fin K, if i ∈ S.1 then r i else 0 := by
  classical
  unfold productSetReward
  have hfilter : (Finset.univ : Finset (Fin K)).filter (fun i => i ∈ S.1) = S.1 := by
    ext i
    simp
  calc
    (∑ i ∈ S.1, r i) =
        ∑ i ∈ (Finset.univ : Finset (Fin K)).filter (fun i => i ∈ S.1), r i := by
      rw [hfilter]
    _ = ∑ i : Fin K, if i ∈ S.1 then r i else 0 := by
      rw [← Finset.sum_filter]

/-- The reward of the slow arms and inserted arm is the reward of their
inserted set.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:20-23,30-37`. -/
private theorem oneRoundAuxiliaryReward_eq_insert {p : Parameters}
    (r : Fin p.K → ℝ) (U : SlowSet p.K p.m) (j : FastArm U) :
    oneRoundAuxiliaryReward r U j =
      ∑ i ∈ insert j.1 U.1, r i := by
  unfold oneRoundAuxiliaryReward
  rw [Finset.sum_insert (Finset.mem_sdiff.mp j.2).2]
  ring

/-- The auxiliary reward is between zero and `m`, derived from the actual
`(m - 1)`-set and its complement arm.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:20-29`. -/
theorem oneRoundAuxiliaryReward_bounds {p : Parameters}
    (r : Fin p.K → ℝ) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (U : SlowSet p.K p.m) (j : FastArm U) :
    0 ≤ oneRoundAuxiliaryReward r U j ∧
      oneRoundAuxiliaryReward r U j ≤ (p.m : ℝ) := by
  have hslow_nonneg : 0 ≤ ∑ i ∈ U.1, r i :=
    Finset.sum_nonneg fun i _ => (hr i).1
  have hslow_le : (∑ i ∈ U.1, r i) ≤ (U.1.card : ℝ) := by
    calc
      (∑ i ∈ U.1, r i) ≤ ∑ i ∈ U.1, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => (hr i).2
      _ = (U.1.card : ℝ) := by simp
  have hcard : (U.1.card : ℝ) + 1 = (p.m : ℝ) := by
    exact_mod_cast slowSet_card p.two_le_m U
  constructor
  · unfold oneRoundAuxiliaryReward
    exact add_nonneg hslow_nonneg (hr j.1).1
  · unfold oneRoundAuxiliaryReward
    calc
      (∑ i ∈ U.1, r i) + r j.1 ≤ (U.1.card : ℝ) + 1 :=
        add_le_add hslow_le (hr j.1).2
      _ = (p.m : ℝ) := hcard

/-- The unmixed finite expectation, with the existing slow-set PMF and
conditional fast-arm mass on their supported carriers.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:7-37`. -/
@[expose] noncomputable def unmixedAuxiliaryRewardExpectation
    (p : Parameters) (v w : Fin p.K → ℝ)
    (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (r : Fin p.K → ℝ) : ℝ :=
  ∑ U : SlowSet p.K p.m,
    (slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal *
      ∑ j : FastArm U,
        fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U j *
          oneRoundAuxiliaryReward r U j

/-- The actual mixed finite expectation, with `U ~ slowSetPMF w v` and the
existing `qGamma` law on the complement of `U`.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:24-29,96-113`. -/
@[expose] noncomputable def mixedAuxiliaryRewardExpectation
    (p : Parameters) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (hwv : ∀ i, w i ≤ 2 * v i)
    (r : Fin p.K → ℝ) : ℝ :=
  ∑ U : SlowSet p.K p.m,
    (slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal *
      ∑ j : FastArm U,
        qGamma p eta heta heta_le v w hv hw hvw hwv U j *
          oneRoundAuxiliaryReward r U j

/-- Insert a complementary fast arm into its supported slow set. -/
private def insertSlowFastPair (p : Parameters) :
    (Σ U : SlowSet p.K p.m, FastArm U) ≃
      (Σ S : ProductSet p.K p.m, {j : Fin p.K // j ∈ S.1}) where
  toFun z :=
    let U := z.1
    let j := z.2
    let S : ProductSet p.K p.m :=
      ⟨insert j.1 U.1, Finset.mem_powersetCard.mpr
        ⟨Finset.insert_subset (Finset.mem_univ _) (Finset.subset_univ _), by
          rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp j.2).2]
          exact slowSet_card p.two_le_m U⟩⟩
    ⟨S, ⟨j.1, Finset.mem_insert_self _ _⟩⟩
  invFun z :=
    ⟨eraseSlowSet p.two_le_m z.1 z.2,
      erasedFastCandidate p.two_le_m z.1 z.2⟩
  left_inv := by
    rintro ⟨U, j⟩
    apply Sigma.subtype_ext
    · apply Subtype.ext
      change (insert j.1 U.1).erase j.1 = U.1
      exact Finset.erase_insert (Finset.mem_sdiff.mp j.2).2
    · rfl
  right_inv := by
    rintro ⟨S, j⟩
    apply Sigma.subtype_ext
    · apply Subtype.ext
      change insert j.1 (S.1.erase j.1) = S.1
      exact Finset.insert_erase j.2
    · rfl

/-- The real weight times one-round reward on a dependent slow/fast pair. -/
private noncomputable def unmixedPairTerm (p : Parameters) (v w : Fin p.K → ℝ)
    (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i) (r : Fin p.K → ℝ)
    (z : Σ U : SlowSet p.K p.m, FastArm U) : ℝ :=
  slowMarginal w v p.two_le_m p.m_lt_K hw hv z.1 *
    (fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv z.1 z.2 *
      oneRoundAuxiliaryReward r z.1 z.2)

/-- The reward of the erased slow set and its inserted fast arm is the reward
of the original supported product set. -/
private theorem oneRoundAuxiliaryReward_erased_eq_productSetReward
    (p : Parameters) (r : Fin p.K → ℝ)
    (S : ProductSet p.K p.m) (j : {j : Fin p.K // j ∈ S.1}) :
    oneRoundAuxiliaryReward r (eraseSlowSet p.two_le_m S j)
        (erasedFastCandidate p.two_le_m S j) = productSetReward r S := by
  rw [oneRoundAuxiliaryReward_eq_insert, insert_erasedSlowSet]
  rfl

/-- The conditional fast-arm law is normalized on the actual complement
subtype. -/
private theorem fastArmConditionalMass_sum_eq_one (p : Parameters)
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (U : SlowSet p.K p.m) :
    (∑ j : FastArm U,
      CanonicalOrientedSetLaw.fastArmConditionalMass w v p.two_le_m p.m_lt_K
        hw hv U j) = 1 := by
  classical
  change (∑ j ∈ (fastArmFinset U).attach,
      FiniteOrientationDisintegration.conditionalFastLaw
        (Finset.univ : Finset (Fin p.K)) w v U.1 (Finset.subset_univ _)
        (slowSet_complement_nonempty p.two_le_m p.m_lt_K U)
        (fun i _ => hw i) (fun i _ => hv i) j) = 1
  exact FiniteOrientationDisintegration.conditionalFastLaw_sum_eq_one
    (Finset.univ : Finset (Fin p.K)) U.1 w v (Finset.subset_univ _)
    (slowSet_complement_nonempty p.two_le_m p.m_lt_K U)
    (fun i _ => hw i) (fun i _ => hv i)

/-- The unmixed finite expectation is exactly the product-law marginal reward.
The proof reindexes the dependent insertion pairs, applies the accepted
two-stage insertion identity, and then expands `theta` by its accepted finite
sum formula.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:7-37`. -/
theorem unmixedAuxiliaryRewardExpectation_eq_theta
    (p : Parameters) (v w : Fin p.K → ℝ)
    (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (r : Fin p.K → ℝ) :
    unmixedAuxiliaryRewardExpectation p v w hv hw r =
      ∑ i : Fin p.K, ProductSetLaw.theta p.m w i * r i := by
  classical
  rw [unmixedAuxiliaryRewardExpectation]
  simp_rw [slowSetPMF_toReal_apply]
  have hfactor (U : SlowSet p.K p.m) :
      slowMarginal w v p.two_le_m p.m_lt_K hw hv U *
          (∑ j : FastArm U,
            fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U j *
              oneRoundAuxiliaryReward r U j) =
        ∑ j : FastArm U,
          slowMarginal w v p.two_le_m p.m_lt_K hw hv U *
            (fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U j *
              oneRoundAuxiliaryReward r U j) :=
    fintype_mul_sum _ _
  simp_rw [hfactor, ← Fintype.sum_sigma']
  let e := insertSlowFastPair p
  let term := unmixedPairTerm p v w hv hw r
  calc
    (∑ z : Σ U : SlowSet p.K p.m, FastArm U, term z)
      = ∑ z : Σ S : ProductSet p.K p.m, {j : Fin p.K // j ∈ S.1},
          term (e.symm z) := by
        exact Fintype.sum_equiv e term (fun z => term (e.symm z)) (by
          intro z
          simp [e])
    _ = ∑ S : ProductSet p.K p.m,
          ∑ j : {j : Fin p.K // j ∈ S.1},
            slowMarginal w v p.two_le_m p.m_lt_K hw hv
                (eraseSlowSet p.two_le_m S j) *
              (fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv
                (eraseSlowSet p.two_le_m S j)
                (erasedFastCandidate p.two_le_m S j) *
              oneRoundAuxiliaryReward r
                (eraseSlowSet p.two_le_m S j)
                (erasedFastCandidate p.two_le_m S j)) := by
        calc
          (∑ z : Σ S : ProductSet p.K p.m, {j : Fin p.K // j ∈ S.1},
              term (e.symm z)) =
              ∑ S : ProductSet p.K p.m,
                ∑ j : {j : Fin p.K // j ∈ S.1},
                  term (e.symm ⟨S, j⟩) :=
            Fintype.sum_sigma' (fun S j => term (e.symm ⟨S, j⟩))
          _ = ∑ S : ProductSet p.K p.m,
                ∑ j : {j : Fin p.K // j ∈ S.1},
                  slowMarginal w v p.two_le_m p.m_lt_K hw hv
                      (eraseSlowSet p.two_le_m S j) *
                    (fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv
                      (eraseSlowSet p.two_le_m S j)
                      (erasedFastCandidate p.two_le_m S j) *
                    oneRoundAuxiliaryReward r
                      (eraseSlowSet p.two_le_m S j)
                      (erasedFastCandidate p.two_le_m S j)) := by
            simp [term, unmixedPairTerm, e, insertSlowFastPair]
    _ = ∑ S : ProductSet p.K p.m,
          ∑ j : {j : Fin p.K // j ∈ S.1},
            (slowMarginal w v p.two_le_m p.m_lt_K hw hv
                (eraseSlowSet p.two_le_m S j) *
              fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv
                (eraseSlowSet p.two_le_m S j)
                (erasedFastCandidate p.two_le_m S j)) *
              productSetReward r S := by
        apply Finset.sum_congr rfl
        intro S hS
        apply Finset.sum_congr rfl
        intro j hj
        rw [oneRoundAuxiliaryReward_erased_eq_productSetReward]
        ring
    _ = ∑ S : ProductSet p.K p.m,
          (∑ j : {j : Fin p.K // j ∈ S.1},
            slowMarginal w v p.two_le_m p.m_lt_K hw hv
                (eraseSlowSet p.two_le_m S j) *
              fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv
                (eraseSlowSet p.two_le_m S j)
                (erasedFastCandidate p.two_le_m S j)) *
              productSetReward r S := by
        apply Finset.sum_congr rfl
        intro S hS
        exact (fintype_sum_mul _ _).symm
    _ = ∑ S : ProductSet p.K p.m,
          ProductSetLaw.Q p.m w S * productSetReward r S := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [CanonicalOrientedSetLaw.twoStageInsertion_sum_eq_Q
          w v p.two_le_m p.m_lt_K hw hv S]
    _ = ∑ i : Fin p.K, ProductSetLaw.theta p.m w i * r i := by
        calc
          (∑ S : ProductSet p.K p.m,
              ProductSetLaw.Q p.m w S * productSetReward r S)
              = ∑ S : ProductSet p.K p.m,
                  ∑ i : Fin p.K,
                    if i ∈ S.1 then ProductSetLaw.Q p.m w S * r i else 0 := by
                  apply Finset.sum_congr rfl
                  intro S hS
                  rw [productSetReward_eq_univ_sum, fintype_mul_sum]
                  apply Finset.sum_congr rfl
                  intro i hi
                  by_cases himem : i ∈ S.1 <;> simp [himem]
          _ = ∑ i : Fin p.K,
                ∑ S : ProductSet p.K p.m,
                  if i ∈ S.1 then ProductSetLaw.Q p.m w S * r i else 0 := by
                rw [← Fintype.sum_prod_type']
                exact Fintype.sum_prod_type_right'
                  (fun S i => if i ∈ S.1 then
                    ProductSetLaw.Q p.m w S * r i else 0)
          _ = ∑ i : Fin p.K,
                r i * (∑ S : ProductSet p.K p.m,
                  if i ∈ S.1 then ProductSetLaw.Q p.m w S else 0) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [fintype_mul_sum]
                apply Finset.sum_congr rfl
                intro S hS
                by_cases himem : i ∈ S.1 <;> simp [himem, mul_comm]
          _ = ∑ i : Fin p.K, ProductSetLaw.theta p.m w i * r i := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [ProductSetDistribution.theta_eq_sum_productSet_Q w i]
                ring

/-- The actual mixed finite joint mass is normalized. This combines the
existing `qGamma` normalization on every complement with the global
`slowSetPMF` normalization.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:20-29,96-113`. -/
theorem mixedJointWeights_sum_eq_one
    (p : Parameters) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (hwv : ∀ i, w i ≤ 2 * v i) :
    (∑ U : SlowSet p.K p.m,
      (slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal *
        ∑ j : FastArm U,
          qGamma p eta heta heta_le v w hv hw hvw hwv U j) = 1 := by
  classical
  calc
    _ = ∑ U : SlowSet p.K p.m,
          (slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal := by
        apply Finset.sum_congr rfl
        intro U hU
        rw [qGamma_sum_eq_one p (eta := eta) heta heta_le v w hv hw hvw hwv U]
        ring
    _ = 1 := by
        simp_rw [slowSetPMF_toReal_apply]
        exact slowMarginal_sum_eq_one w v p.two_le_m p.m_lt_K hw hv

/-- A normalized fast-arm law preserves the slow reward in expectation, so
only its fast-arm term remains to compare. -/
private theorem auxiliaryReward_expectation_split {p : Parameters}
    (r : Fin p.K → ℝ) (U : SlowSet p.K p.m) (q : FastArm U → ℝ)
    (hq : (∑ j : FastArm U, q j) = 1) :
    (∑ j : FastArm U, q j * oneRoundAuxiliaryReward r U j) =
      (∑ i ∈ U.1, r i) + ∑ j : FastArm U, q j * r j.1 := by
  classical
  calc
    (∑ j : FastArm U, q j * oneRoundAuxiliaryReward r U j) =
        ∑ j : FastArm U,
          (q j * (∑ i ∈ U.1, r i) + q j * r j.1) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [oneRoundAuxiliaryReward]
      ring
    _ = (∑ j : FastArm U, q j * (∑ i ∈ U.1, r i)) +
          ∑ j : FastArm U, q j * r j.1 := by
      rw [Finset.sum_add_distrib]
    _ = (∑ j : FastArm U, q j) * (∑ i ∈ U.1, r i) +
          ∑ j : FastArm U, q j * r j.1 := by
      rw [Finset.sum_mul]
    _ = (∑ i ∈ U.1, r i) + ∑ j : FastArm U, q j * r j.1 := by
      rw [hq]
      ring

/-- With fixed positive weights in the source range, gamma mixing loses at
most `gamma` in the one-round expected reward. Only the fast-arm reward is
changed by the mixture.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:96-113,379-382`. -/
private theorem mixedInnerExpectation_ge_unmixed_sub_gamma
    (p : Parameters) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (hwv : ∀ i, w i ≤ 2 * v i)
    (r : Fin p.K → ℝ) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (U : SlowSet p.K p.m) :
    (∑ j : FastArm U,
      qGamma p eta heta heta_le v w hv hw hvw hwv U j *
        oneRoundAuxiliaryReward r U j) ≥
      (∑ j : FastArm U,
        fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U j *
          oneRoundAuxiliaryReward r U j) - gamma p eta := by
  classical
  have hgamma := gamma_nonneg_and_le_half p heta heta_le
  have hq0sum := fastArmConditionalMass_sum_eq_one p v w hv hw U
  have hqmixsum := qGamma_sum_eq_one p (eta := eta) heta heta_le v w hv hw hvw hwv U
  have hsplitMix := auxiliaryReward_expectation_split (p := p) r U
    (q := qGamma p eta heta heta_le v w hv hw hvw hwv U) hqmixsum
  have hsplitBase := auxiliaryReward_expectation_split (p := p) r U
    (q := fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U) hq0sum
  rw [hsplitMix, hsplitBase]
  have hbase_nonneg (j : FastArm U) :
      0 ≤ fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U j := by
    exact (FiniteOrientationDisintegration.conditionalFastLaw_pos
      (Finset.univ : Finset (Fin p.K)) U.1 w v (Finset.subset_univ _)
      (slowSet_complement_nonempty p.two_le_m p.m_lt_K U)
      (fun i _ => hw i) (fun i _ => hv i) j).le
  have hbase_reward_nonneg :
      0 ≤ ∑ j : FastArm U,
        fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U j * r j.1 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hbase_nonneg j) (hr j.1).1
  have hbase_reward_le_one :
      (∑ j : FastArm U,
        fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U j * r j.1) ≤ 1 := by
    calc
      _ ≤ ∑ j : FastArm U,
          fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U j * 1 :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hr j.1).2 (hbase_nonneg j)
      _ = 1 := by simpa using hq0sum
  have hfastMix (j : FastArm U) :
      qGamma p eta heta heta_le v w hv hw hvw hwv U j =
        (1 - gamma p eta) *
          fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U j +
          gamma p eta / ((p.K - p.m + 1 : ℕ) : ℝ) := by
    rfl
  have hmixedFast_eq :
      (∑ j : FastArm U,
        qGamma p eta heta heta_le v w hv hw hvw hwv U j * r j.1) =
        (1 - gamma p eta) *
            (∑ j : FastArm U,
              fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U j * r j.1) +
          (gamma p eta / ((p.K - p.m + 1 : ℕ) : ℝ)) *
            (∑ j : FastArm U, r j.1) := by
    calc
      _ = ∑ j : FastArm U,
          ((1 - gamma p eta) *
              (fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U j * r j.1) +
            (gamma p eta / ((p.K - p.m + 1 : ℕ) : ℝ)) * r j.1) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hfastMix j]
          ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hfast_uniform_nonneg :
      0 ≤ (gamma p eta / ((p.K - p.m + 1 : ℕ) : ℝ)) *
        (∑ j : FastArm U, r j.1) := by
    have hFpos : (0 : ℝ) < ((p.K - p.m + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < p.K - p.m + 1 by omega)
    exact mul_nonneg
      (div_nonneg hgamma.1 (le_of_lt hFpos))
      (Finset.sum_nonneg fun j _ => (hr j.1).1)
  have hbase_gamma :
      (1 - gamma p eta) *
          (∑ j : FastArm U,
            fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U j * r j.1) ≥
        (∑ j : FastArm U,
          fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U j * r j.1) -
          gamma p eta := by
    have hprod := mul_nonneg hgamma.1 (sub_nonneg.mpr hbase_reward_le_one)
    nlinarith only [hprod]
  have hfast_le :
      (∑ j : FastArm U,
        qGamma p eta heta heta_le v w hv hw hvw hwv U j * r j.1) ≥
        (∑ j : FastArm U,
          fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U j * r j.1) -
          gamma p eta := by
    rw [hmixedFast_eq]
    linarith
  linarith

/-- The mixed one-round expectation is at least the canonical marginal reward
minus the literal source exploration rate. The inputs include positive anchor
and current weights, the source learning-rate cap, `v ≤ w ≤ 2v`, and
coordinate rewards in `[0,1]`.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:7-37,96-113,379-382`.
This is a fixed-snapshot finite-law result; it does not close an adaptive
conditional-history or accumulated-comparison statement. -/
theorem mixedAuxiliaryRewardExpectation_ge_theta_sub_gamma
    (p : Parameters) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (hwv : ∀ i, w i ≤ 2 * v i)
    (r : Fin p.K → ℝ) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1) :
    mixedAuxiliaryRewardExpectation p eta heta heta_le v w hv hw hvw hwv r ≥
      (∑ i : Fin p.K, ProductSetLaw.theta p.m w i * r i) - gamma p eta := by
  classical
  have hslow_sum :
      (∑ U : SlowSet p.K p.m,
        (slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal) = 1 := by
    simp_rw [slowSetPMF_toReal_apply]
    exact slowMarginal_sum_eq_one w v p.two_le_m p.m_lt_K hw hv
  have hslow_mass_nonneg (U : SlowSet p.K p.m) :
      0 ≤ (slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal := by
    rw [slowSetPMF_toReal_apply]
    exact (slowMarginal_pos w v p.two_le_m p.m_lt_K hw hv U).le
  have hconditional (U : SlowSet p.K p.m) :
      (∑ j : FastArm U,
        qGamma p eta heta heta_le v w hv hw hvw hwv U j *
          oneRoundAuxiliaryReward r U j) ≥
        (∑ j : FastArm U,
          fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U j *
            oneRoundAuxiliaryReward r U j) - gamma p eta :=
    mixedInnerExpectation_ge_unmixed_sub_gamma p eta heta heta_le v w hv hw hvw hwv
      r hr U
  have houter :
      mixedAuxiliaryRewardExpectation p eta heta heta_le v w hv hw hvw hwv r ≥
        unmixedAuxiliaryRewardExpectation p v w hv hw r - gamma p eta := by
    unfold mixedAuxiliaryRewardExpectation unmixedAuxiliaryRewardExpectation
    have hterms :
        (∑ U : SlowSet p.K p.m,
          (slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal *
            ((∑ j : FastArm U,
              fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U j *
                oneRoundAuxiliaryReward r U j) - gamma p eta)) ≤
          ∑ U : SlowSet p.K p.m,
            (slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal *
              ∑ j : FastArm U,
                qGamma p eta heta heta_le v w hv hw hvw hwv U j *
                  oneRoundAuxiliaryReward r U j :=
      Finset.sum_le_sum (s := Finset.univ) fun U hU =>
        mul_le_mul_of_nonneg_left (hconditional U) (hslow_mass_nonneg U)
    have herror :
        (∑ U : SlowSet p.K p.m,
          (slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal *
            ((∑ j : FastArm U,
              fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U j *
                oneRoundAuxiliaryReward r U j) - gamma p eta)) =
          (∑ U : SlowSet p.K p.m,
            (slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal *
              ∑ j : FastArm U,
                fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U j *
                  oneRoundAuxiliaryReward r U j) - gamma p eta := by
      calc
        _ = ∑ U : SlowSet p.K p.m,
              (((slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal *
                  (∑ j : FastArm U,
                    fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U j *
                      oneRoundAuxiliaryReward r U j)) -
                ((slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal * gamma p eta)) := by
            apply Finset.sum_congr rfl
            intro U hU
            ring
        _ = (∑ U : SlowSet p.K p.m,
              (slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal *
                ∑ j : FastArm U,
                  fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U j *
                    oneRoundAuxiliaryReward r U j) -
              ∑ U : SlowSet p.K p.m,
                (slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal * gamma p eta := by
            exact fintype_sum_sub (α := SlowSet p.K p.m)
              (fun U =>
                (slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal *
                  ∑ j : FastArm U,
                    fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U j *
                      oneRoundAuxiliaryReward r U j)
              (fun U =>
                (slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal * gamma p eta)
        _ = (∑ U : SlowSet p.K p.m,
              (slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal *
                ∑ j : FastArm U,
                  fastArmConditionalMass w v p.two_le_m p.m_lt_K hw hv U j *
                    oneRoundAuxiliaryReward r U j) -
              gamma p eta *
                (∑ U : SlowSet p.K p.m,
                  (slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal) := by
            congr 1
            calc
              (∑ U : SlowSet p.K p.m,
                (slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal * gamma p eta) =
                  ∑ U : SlowSet p.K p.m,
                    gamma p eta *
                      (slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal := by
                    apply Finset.sum_congr rfl
                    intro U hU
                    ring
              _ = gamma p eta *
                    ∑ U : SlowSet p.K p.m,
                      (slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal :=
                  (fintype_mul_sum (gamma p eta) fun U =>
                    (slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal).symm
        _ = _ := by rw [hslow_sum]; ring
    linarith
  rw [unmixedAuxiliaryRewardExpectation_eq_theta p v w hv hw r] at houter
  exact houter

end Bandits.Support.MixedAuxiliaryReward

end
