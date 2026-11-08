/- Finite inverse-anchor orientation on its positive, valid-set domain. -/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Field

import Bandits.Support.ElementarySymmetricRecurrence
import Bandits.Support.OrientationAlgebra
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp

/-!
# Finite inverse-anchor orientation

Internal finite-set identities for
`sources/zip4/manuscript/04_slow_fast_learner.tex:7-37`.
Every probability formula takes its positive weights and actual support data in
its definition domain. The unrestricted sums and candidate weights are arithmetic
helpers, not probability objects.

The product-set mass is private: this module does not supply the canonical
`Fin K` law or its inclusion marginals. After `ProductSetLaw` lands, an application
must specialize the finite carrier and prove equality of its canonical `Q` with
the product/partition-function factor used here, including the inserted-set
carrier identification. No such equality or sampler coupling is assumed here.
These are fully proved internal identities, not frozen anchors or manuscript
theorem closure.
-/

public section

namespace Bandits.Support.FiniteOrientationDisintegration

variable {ι : Type*} [DecidableEq ι]

/-- Arithmetic elementary symmetric sum; it is not an additional probability law.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:7-13`. -/
@[expose] def partitionFunction (I : Finset ι) (m : ℕ) (w : ι → ℝ) : ℝ :=
  ∑ S ∈ I.powersetCard m, ∏ i ∈ S, w i

/-- Private product-set factor on actual supported sets and positive weights.
Nonempty support is source data, not an assumed positive normalizer.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:7-13`. -/
private noncomputable def productSetMass
    (I : Finset ι) (m : ℕ) (w : ι → ℝ)
    (_hw : ∀ i ∈ I, 0 < w i) (_hsupport : (I.powersetCard m).Nonempty)
    (S : {S // S ∈ I.powersetCard m}) : ℝ :=
  (∏ i ∈ S.1, w i) / partitionFunction I m w

/-- Arithmetic inverse-anchor sum.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:24-28`. -/
@[expose] noncomputable def inverseAnchorSum (anchor : ι → ℝ) (U : Finset ι) : ℝ :=
  ∑ i ∈ U, 1 / anchor i

/-- Orientation probability on a nonempty set with positive anchor weights,
evaluated only at one of its members.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:16-19`. -/
@[expose] noncomputable def orientationProbability (anchor : ι → ℝ) (S : Finset ι)
    (_hS : S.Nonempty) (_hanchor : ∀ i ∈ S, 0 < anchor i)
    (j : {j // j ∈ S}) : ℝ :=
  (1 / anchor j.1) / ∑ i ∈ S, 1 / anchor i

/-- Arithmetic, unnormalized candidate weight; positivity is proved separately.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:24-29`. -/
@[expose] noncomputable def candidateWeight (w anchor : ι → ℝ) (U : Finset ι)
    (j : ι) : ℝ :=
  w j / (1 + inverseAnchorSum anchor U * anchor j)

private theorem insert_mem_powersetCard (I U : Finset ι) (m : ℕ)
    (hU : U ⊆ I) (hsize : U.card + 1 = m) (j : {j // j ∈ I \ U}) :
    insert j.1 U ∈ I.powersetCard m := by
  rcases Finset.mem_sdiff.mp j.2 with ⟨hjI, hjU⟩
  exact Finset.mem_powersetCard.mpr
    ⟨Finset.insert_subset hjI hU, (Finset.card_insert_of_notMem hjU).trans hsize⟩

/-- Joint mass of a valid slow set and a genuine complement candidate. The
inserted set is an actual member of the product-set support; its anchor is
positive by restriction of the positive anchor on `I`.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:20-23,30-36`. -/
@[expose] noncomputable def orientedJointMass
    (I : Finset ι) (m : ℕ) (w anchor : ι → ℝ) (U : Finset ι)
    (hU : U ⊆ I) (hsize : U.card + 1 = m)
    (_hw : ∀ i ∈ I, 0 < w i) (hanchor : ∀ i ∈ I, 0 < anchor i)
    (j : {j // j ∈ I \ U}) : ℝ :=
  let S : {S // S ∈ I.powersetCard m} :=
    ⟨insert j.1 U, Finset.mem_powersetCard.mpr
      ⟨Finset.insert_subset (Finset.mem_sdiff.mp j.2).1 hU,
        (Finset.card_insert_of_notMem (Finset.mem_sdiff.mp j.2).2).trans hsize⟩⟩
  ((∏ i ∈ S.1, w i) / partitionFunction I m w) *
    orientationProbability anchor S.1 (Finset.insert_nonempty _ _)
      (fun i hi => hanchor i ((Finset.mem_powersetCard.mp S.2).1 hi))
      ⟨j.1, Finset.mem_insert_self _ _⟩

/-- Arithmetic candidate sum, with each complement element counted once.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:24-29`. -/
@[expose] noncomputable def candidateNormalizer (I : Finset ι) (w anchor : ι → ℝ)
    (U : Finset ι) : ℝ :=
  ∑ j ∈ (I \ U).attach, candidateWeight w anchor U j.1

/-- Conditional fast-arm probability on a nonempty valid complement and
positive current and anchor weights. This formula normalizes for every `U ⊆ I`
with a nonempty complement; its definition does not need a cardinality parameter.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:24-29`. -/
@[expose] noncomputable def conditionalFastLaw (I : Finset ι) (w anchor : ι → ℝ)
    (U : Finset ι) (_hU : U ⊆ I) (_hcandidates : (I \ U).Nonempty)
    (_hw : ∀ i ∈ I, 0 < w i) (_hanchor : ∀ i ∈ I, 0 < anchor i)
    (j : {j // j ∈ I \ U}) : ℝ :=
  candidateWeight w anchor U j.1 / candidateNormalizer I w anchor U

/-- Slow-set marginal on valid slow sets with a nonempty complement. All masses
summed here use actual complement candidates and positive source weights.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:20-23`. -/
@[expose] noncomputable def slowMarginal
    (I : Finset ι) (m : ℕ) (w anchor : ι → ℝ) (U : Finset ι)
    (hU : U ⊆ I) (hsize : U.card + 1 = m) (_hcandidates : (I \ U).Nonempty)
    (hw : ∀ i ∈ I, 0 < w i) (hanchor : ∀ i ∈ I, 0 < anchor i) : ℝ :=
  ∑ j ∈ (I \ U).attach, orientedJointMass I m w anchor U hU hsize hw hanchor j

omit [DecidableEq ι] in
/-- Positive anchor weights make the inverse-anchor sum nonnegative. -/
theorem inverseAnchorSum_nonneg (I U : Finset ι) (anchor : ι → ℝ)
    (hU : U ⊆ I) (hanchor : ∀ i ∈ I, 0 < anchor i) :
    0 ≤ inverseAnchorSum anchor U := by
  unfold inverseAnchorSum
  exact Finset.sum_nonneg fun i hi => (one_div_pos.mpr (hanchor i (hU hi))).le

omit [DecidableEq ι] in
/-- A nonempty set of positive anchors gives a positive orientation denominator. -/
theorem inverseAnchorSum_pos (S : Finset ι) (anchor : ι → ℝ)
    (hS : S.Nonempty) (hanchor : ∀ i ∈ S, 0 < anchor i) :
    0 < inverseAnchorSum anchor S := by
  exact Finset.sum_pos (fun i hi => one_div_pos.mpr (hanchor i hi)) hS

omit [DecidableEq ι] in
/-- Positivity of the product-set normalizer follows from positive weights and
nonempty support, using the integrated elementary-symmetric-sum API.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:7-13`. -/
theorem partitionFunction_pos (I : Finset ι) (m : ℕ) (w : ι → ℝ)
    (hw : ∀ i ∈ I, 0 < w i) (hsupport : (I.powersetCard m).Nonempty) :
    0 < partitionFunction I m w := by
  exact ElementarySymmetricRecurrence.elementarySymmetric_pos w I m hw
    (Finset.powersetCard_nonempty.mp hsupport)

omit [DecidableEq ι] in
private theorem productSetMass_pos (I : Finset ι) (m : ℕ) (w : ι → ℝ)
    (hw : ∀ i ∈ I, 0 < w i) (hsupport : (I.powersetCard m).Nonempty)
    (S : {S // S ∈ I.powersetCard m}) :
    0 < productSetMass I m w hw hsupport S := by
  exact div_pos
    (Finset.prod_pos fun i hi => hw i ((Finset.mem_powersetCard.mp S.2).1 hi))
    (partitionFunction_pos I m w hw hsupport)

omit [DecidableEq ι] in
/-- Every orientation probability on its definition domain is positive. -/
theorem orientationProbability_pos (anchor : ι → ℝ) (S : Finset ι)
    (hS : S.Nonempty) (hanchor : ∀ i ∈ S, 0 < anchor i) (j : {j // j ∈ S}) :
    0 < orientationProbability anchor S hS hanchor j := by
  exact div_pos (one_div_pos.mpr (hanchor j.1 j.2))
    (inverseAnchorSum_pos S anchor hS hanchor)

omit [DecidableEq ι] in
/-- Orientation probabilities sum to one over the actual nonempty set.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:16-19,37`. -/
theorem orientationProbability_sum_eq_one (anchor : ι → ℝ) (S : Finset ι)
    (hS : S.Nonempty) (hanchor : ∀ i ∈ S, 0 < anchor i) :
    (∑ j ∈ S.attach, orientationProbability anchor S hS hanchor j) = 1 := by
  unfold orientationProbability
  rw [← Finset.sum_div, S.sum_attach (f := fun i => 1 / anchor i)]
  exact div_self (ne_of_gt (inverseAnchorSum_pos S anchor hS hanchor))

/-- The denominator of each valid candidate weight is strictly positive. -/
theorem candidateWeight_denominator_pos (I U : Finset ι) (anchor : ι → ℝ)
    (hU : U ⊆ I) (hanchor : ∀ i ∈ I, 0 < anchor i)
    (j : {j // j ∈ I \ U}) :
    0 < 1 + inverseAnchorSum anchor U * anchor j.1 := by
  exact add_pos_of_pos_of_nonneg zero_lt_one
    (mul_nonneg (inverseAnchorSum_nonneg I U anchor hU hanchor)
      (hanchor j.1 (Finset.mem_sdiff.mp j.2).1).le)

/-- Every valid complement candidate has positive reweighted mass. -/
theorem candidateWeight_pos (I : Finset ι) (w anchor : ι → ℝ) (U : Finset ι)
    (hU : U ⊆ I) (hw : ∀ i ∈ I, 0 < w i) (hanchor : ∀ i ∈ I, 0 < anchor i)
    (j : {j // j ∈ I \ U}) :
    0 < candidateWeight w anchor U j.1 := by
  exact div_pos (hw j.1 (Finset.mem_sdiff.mp j.2).1)
    (candidateWeight_denominator_pos I U anchor hU hanchor j)

/-- A nonempty valid complement makes the candidate normalizer positive. -/
theorem candidateNormalizer_pos (I U : Finset ι) (w anchor : ι → ℝ)
    (hU : U ⊆ I) (hcandidates : (I \ U).Nonempty)
    (hw : ∀ i ∈ I, 0 < w i) (hanchor : ∀ i ∈ I, 0 < anchor i) :
    0 < candidateNormalizer I w anchor U := by
  unfold candidateNormalizer
  apply Finset.sum_pos
  · intro j _
    exact candidateWeight_pos I w anchor U hU hw hanchor j
  · obtain ⟨j, hj⟩ := hcandidates
    exact ⟨⟨j, hj⟩, Finset.mem_attach _ _⟩

/-- Every conditional fast-arm probability on its definition domain is positive. -/
theorem conditionalFastLaw_pos (I U : Finset ι) (w anchor : ι → ℝ)
    (hU : U ⊆ I) (hcandidates : (I \ U).Nonempty)
    (hw : ∀ i ∈ I, 0 < w i) (hanchor : ∀ i ∈ I, 0 < anchor i)
    (j : {j // j ∈ I \ U}) :
    0 < conditionalFastLaw I w anchor U hU hcandidates hw hanchor j := by
  exact div_pos (candidateWeight_pos I w anchor U hU hw hanchor j)
    (candidateNormalizer_pos I U w anchor hU hcandidates hw hanchor)

/-- The reciprocal-anchor cancellation on an inserted valid set.

The factor on the right is internal finite-`I` arithmetic. Identifying the
product-set factor with canonical `Q` is a separate application obligation.
Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:30-35`. -/
theorem orientedJointMass_eq_product_factor (I U : Finset ι) (m : ℕ)
    (w anchor : ι → ℝ) (hU : U ⊆ I) (hsize : U.card + 1 = m)
    (hw : ∀ i ∈ I, 0 < w i) (hanchor : ∀ i ∈ I, 0 < anchor i)
    (j : {j // j ∈ I \ U}) :
    orientedJointMass I m w anchor U hU hsize hw hanchor j =
      ((∏ i ∈ U, w i) / partitionFunction I m w) *
        (w j.1 / (1 + inverseAnchorSum anchor U * anchor j.1)) := by
  have hjI : j.1 ∈ I := (Finset.mem_sdiff.mp j.2).1
  have hjU : j.1 ∉ U := (Finset.mem_sdiff.mp j.2).2
  have hsupport : (I.powersetCard m).Nonempty :=
    ⟨insert j.1 U, insert_mem_powersetCard I U m hU hsize j⟩
  have hZ := partitionFunction_pos I m w hw hsupport
  have hs := inverseAnchorSum_nonneg I U anchor hU hanchor
  have hAlpha :
      (1 / anchor j.1) / (∑ i ∈ insert j.1 U, 1 / anchor i) =
        (1 / anchor j.1) / (inverseAnchorSum anchor U + 1 / anchor j.1) := by
    rw [Finset.sum_insert hjU, add_comm]
    rfl
  have hcancel :=
    OrientationAlgebra.product_mass_union_orientation_cancel
      U j.1 w anchor (inverseAnchorSum anchor U) hjU (hanchor j.1 hjI) hs
  have hUnion : U ∪ {j.1} = insert j.1 U := by
    ext i
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert, or_comm]
  change ((∏ i ∈ insert j.1 U, w i) / partitionFunction I m w) *
    ((1 / anchor j.1) / (∑ i ∈ insert j.1 U, 1 / anchor i)) = _
  rw [hAlpha]
  calc
    ((∏ i ∈ insert j.1 U, w i) / partitionFunction I m w) *
        ((1 / anchor j.1) / (inverseAnchorSum anchor U + 1 / anchor j.1)) =
      ((∏ i ∈ U ∪ {j.1}, w i) *
        ((1 / anchor j.1) / (inverseAnchorSum anchor U + 1 / anchor j.1))) /
          partitionFunction I m w := by
            rw [← hUnion]
            field_simp [ne_of_gt hZ]
    _ = ((∏ i ∈ U, w i) * (w j.1 / (1 + inverseAnchorSum anchor U * anchor j.1))) /
          partitionFunction I m w := by rw [hcancel]
    _ = ((∏ i ∈ U, w i) / partitionFunction I m w) *
          (w j.1 / (1 + inverseAnchorSum anchor U * anchor j.1)) := by
            field_simp [ne_of_gt hZ]

/-- Every oriented joint mass on its definition domain is positive. -/
theorem orientedJointMass_pos (I U : Finset ι) (m : ℕ) (w anchor : ι → ℝ)
    (hU : U ⊆ I) (hsize : U.card + 1 = m)
    (hw : ∀ i ∈ I, 0 < w i) (hanchor : ∀ i ∈ I, 0 < anchor i)
    (j : {j // j ∈ I \ U}) :
    0 < orientedJointMass I m w anchor U hU hsize hw hanchor j := by
  unfold orientedJointMass
  apply mul_pos
  · exact productSetMass_pos I m w hw
      ⟨insert j.1 U, insert_mem_powersetCard I U m hU hsize j⟩
      ⟨insert j.1 U, insert_mem_powersetCard I U m hU hsize j⟩
  · exact orientationProbability_pos anchor (insert j.1 U) (Finset.insert_nonempty _ _)
      (fun i hi => hanchor i ((Finset.mem_powersetCard.mp
        (insert_mem_powersetCard I U m hU hsize j)).1 hi))
      ⟨j.1, Finset.mem_insert_self _ _⟩

/-- Summing the joint factorization extracts the same candidate-independent
factor for every candidate, with all valid-domain inputs supplied.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:20-35`. -/
theorem slowMarginal_eq_product_factor_mul_candidateNormalizer
    (I U : Finset ι) (m : ℕ) (w anchor : ι → ℝ)
    (hU : U ⊆ I) (hsize : U.card + 1 = m) (hcandidates : (I \ U).Nonempty)
    (hw : ∀ i ∈ I, 0 < w i) (hanchor : ∀ i ∈ I, 0 < anchor i) :
    slowMarginal I m w anchor U hU hsize hcandidates hw hanchor =
      ((∏ i ∈ U, w i) / partitionFunction I m w) *
        candidateNormalizer I w anchor U := by
  unfold slowMarginal candidateNormalizer
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact orientedJointMass_eq_product_factor I U m w anchor hU hsize hw hanchor j

/-- Every slow marginal on its definition domain is positive. -/
theorem slowMarginal_pos (I U : Finset ι) (m : ℕ) (w anchor : ι → ℝ)
    (hU : U ⊆ I) (hsize : U.card + 1 = m) (hcandidates : (I \ U).Nonempty)
    (hw : ∀ i ∈ I, 0 < w i) (hanchor : ∀ i ∈ I, 0 < anchor i) :
    0 < slowMarginal I m w anchor U hU hsize hcandidates hw hanchor := by
  unfold slowMarginal
  apply Finset.sum_pos
  · intro j _
    exact orientedJointMass_pos I U m w anchor hU hsize hw hanchor j
  · obtain ⟨j, hj⟩ := hcandidates
    exact ⟨⟨j, hj⟩, Finset.mem_attach _ _⟩

/-- Conditional fast-arm probabilities normalize over their actual complement.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:24-29`. -/
theorem conditionalFastLaw_sum_eq_one (I U : Finset ι) (w anchor : ι → ℝ)
    (hU : U ⊆ I) (hcandidates : (I \ U).Nonempty)
    (hw : ∀ i ∈ I, 0 < w i) (hanchor : ∀ i ∈ I, 0 < anchor i) :
    (∑ j ∈ (I \ U).attach,
      conditionalFastLaw I w anchor U hU hcandidates hw hanchor j) = 1 := by
  have hnormalizer := candidateNormalizer_pos I U w anchor hU hcandidates hw hanchor
  unfold conditionalFastLaw
  rw [← Finset.sum_div]
  change candidateNormalizer I w anchor U / candidateNormalizer I w anchor U = 1
  exact div_self (ne_of_gt hnormalizer)

/-- Joint equals slow marginal times conditional, on the complete valid domain.
No normalization, factorization or positive-normalizer result is an input.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:30-37`. -/
theorem orientedJointMass_eq_slowMarginal_mul_conditionalFastLaw
    (I U : Finset ι) (m : ℕ) (w anchor : ι → ℝ)
    (hU : U ⊆ I) (hsize : U.card + 1 = m) (hcandidates : (I \ U).Nonempty)
    (hw : ∀ i ∈ I, 0 < w i) (hanchor : ∀ i ∈ I, 0 < anchor i)
    (j : {j // j ∈ I \ U}) :
    orientedJointMass I m w anchor U hU hsize hw hanchor j =
      slowMarginal I m w anchor U hU hsize hcandidates hw hanchor *
        conditionalFastLaw I w anchor U hU hcandidates hw hanchor j := by
  have hnormalizer := candidateNormalizer_pos I U w anchor hU hcandidates hw hanchor
  have hfactor := slowMarginal_eq_product_factor_mul_candidateNormalizer
    I U m w anchor hU hsize hcandidates hw hanchor
  rw [orientedJointMass_eq_product_factor I U m w anchor hU hsize hw hanchor j]
  unfold conditionalFastLaw candidateWeight
  rw [hfactor]
  field_simp [ne_of_gt hnormalizer]

end Bandits.Support.FiniteOrientationDisintegration

end
