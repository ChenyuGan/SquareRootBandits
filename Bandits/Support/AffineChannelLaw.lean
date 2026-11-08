/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.UniformOn
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# The one-round affine binary channel

This module formalizes the literal one-round affine hash from
`sources/zip4/manuscript/05_binary_transport.tex:11-21`, sampled as in
`sources/zip4/manuscript/appendix_b_communication.tex:46-55`. The sender and receiver
interpretation is recorded in `sources/zip4/manuscript/appendix_a_local_protocol.tex:110-165`.

The joint law is uniform over the complete coefficient vector and offset. The results here
cover one fixed round only; adaptive batches and protocol-level collision or decoding claims
are not part of this module.
-/

public section

open scoped BigOperators ENNReal NNReal Classical

namespace Bandits.Support.AffineChannelLaw

/-- The binary field used by the affine hash. -/
abbrev Bit := ZMod 2

/-- A length-`B` binary word or coefficient vector. Width zero has exactly one word. -/
abbrev Word (B : ℕ) := Fin B → Bit

/-- The full affine-hash sample, retaining both the coefficient vector and offset. -/
abbrev Sample (B : ℕ) := Word B × Bit

/-- Every subset of the finite sample carrier is measurable, including when `B = 0`. -/
instance sampleMeasurableSpace (B : ℕ) : MeasurableSpace (Sample B) := ⊤

/-- The binary dot product of a coefficient vector with a word. -/
@[expose] def dotProduct {B : ℕ} (c u : Word B) : Bit :=
  ∑ i : Fin B, c i * u i

/-- The source-literal affine binary map `u ↦ ∑ᵣ cᵣ uᵣ + b`. -/
@[expose] def affineHash {B : ℕ} (sample : Sample B) (u : Word B) : Bit :=
  dotProduct sample.1 u + sample.2

/-- At width zero the affine map still uses its uniformly sampled offset. -/
theorem affineHash_zero_width (s : Sample 0) (u : Word 0) :
    affineHash s u = s.2 := by
  simp only [affineHash, dotProduct, Finset.univ_eq_empty, Finset.sum_empty, zero_add]

/-- There are no distinct words at width zero, so the two-word law is vacuous there. -/
theorem word_zero_eq (u v : Word 0) : u = v := by
  funext i
  exact Fin.elim0 i

/-- The complete joint sampling law of all coefficients and the offset. Each pair
`(c,b) : (Fin B → 𝔽₂) × 𝔽₂` has the same mass. This is Mathlib's uniform counting
measure on the entire finite carrier, converted to its corresponding `PMF`. -/
@[expose] noncomputable def jointLaw (B : ℕ) : PMF (Sample B) :=
  (ProbabilityTheory.uniformOn (Set.univ : Set (Sample B))).toPMF

/-- The joint law is exactly Mathlib's uniform measure, with no restriction on the sample. -/
theorem jointLaw_toMeasure (B : ℕ) :
    (jointLaw B).toMeasure = ProbabilityTheory.uniformOn (Set.univ : Set (Sample B)) := by
  exact MeasureTheory.Measure.toPMF_toMeasure _

/-- Every full coefficient/offset sample has equal mass. -/
theorem jointLaw_apply (B : ℕ) (s : Sample B) :
    jointLaw B s = (Fintype.card (Sample B) : ℝ≥0∞)⁻¹ := by
  rw [jointLaw, MeasureTheory.Measure.toPMF_apply, ProbabilityTheory.uniformOn_univ,
    MeasureTheory.Measure.count_singleton, one_div]

private theorem sample_card {B : ℕ} :
    Fintype.card (Sample B) = 2 * Fintype.card (Word B) := by
  simp [Sample, Fintype.card_prod, ZMod.card, Nat.mul_comm]

/-- There are exactly `2^(B+1)` complete samples, all with equal mass. -/
theorem jointLaw_apply_eq_inv_pow (B : ℕ) (s : Sample B) :
    jointLaw B s = (2 ^ (B + 1) : ℝ≥0∞)⁻¹ := by
  rw [jointLaw_apply, sample_card]
  simp only [Word, Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_pow, pow_succ, mul_comm]

/-- Probability assigned by the joint law to an event on the full sample. -/
@[expose] noncomputable def eventProbability {B : ℕ} (event : Sample B → Prop) : ℝ≥0∞ :=
  (jointLaw B).toOuterMeasure {s | event s}

/-- Event probabilities can be consumed as ordinary Mathlib measure evaluations. -/
theorem eventProbability_eq_measure {B : ℕ} (event : Sample B → Prop) :
    eventProbability event = (jointLaw B).toMeasure {s | event s} := by
  exact (PMF.toMeasure_apply_eq_toOuterMeasure_apply _ MeasurableSet.of_discrete).symm

private theorem eventProbability_eq_card_ratio {B : ℕ} (event : Sample B → Prop)
    [Fintype {s : Sample B // event s}] :
    eventProbability event =
      (Fintype.card {s : Sample B // event s} : ℝ≥0∞) /
        (Fintype.card (Sample B) : ℝ≥0∞) := by
  classical
  rw [eventProbability, PMF.toOuterMeasure_apply_fintype]
  simp only [Set.indicator, Set.mem_ofPred_eq, jointLaw_apply]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul, Fintype.card_subtype]
  rw [div_eq_mul_inv]

private abbrev singleFiber {B : ℕ} (u : Word B) (a : Bit) :=
  {s : Sample B // affineHash s u = a}

private def singleFiberEquivWord {B : ℕ} (u : Word B) (a : Bit) :
    singleFiber u a ≃ Word B where
  toFun s := s.1.1
  invFun c := ⟨(c, a - dotProduct c u), by simp [affineHash]⟩
  left_inv s := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    ·
      have hs := s.2
      change dotProduct s.1.1 u + s.1.2 = a at hs
      calc
        a - dotProduct s.1.1 u =
            (dotProduct s.1.1 u + s.1.2) - dotProduct s.1.1 u :=
              congrArg (fun x : Bit => x - dotProduct s.1.1 u) hs.symm
        _ = s.1.2 := by abel
  right_inv _ := rfl

private theorem singleFiber_card {B : ℕ} (u : Word B) (a : Bit)
    [Fintype (singleFiber u a)] :
    Fintype.card (singleFiber u a) = Fintype.card (Word B) :=
  Fintype.card_congr (singleFiberEquivWord u a)

/-- Every fixed word maps to either fixed bit with probability exactly one half. -/
theorem affineHash_probability {B : ℕ} (u : Word B) (a : Bit) :
    eventProbability (fun s => affineHash s u = a) = (1 : ℝ≥0∞) / 2 := by
  classical
  rw [eventProbability_eq_card_ratio, singleFiber_card]
  rw [sample_card, Nat.cast_mul]
  have hn : (Fintype.card (Word B) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := Word B))
  calc
    (Fintype.card (Word B) : ℝ≥0∞) /
        ((2 : ℝ≥0∞) * Fintype.card (Word B)) =
      (Fintype.card (Word B) : ℝ≥0∞) /
        ((Fintype.card (Word B) : ℝ≥0∞) * 2) := by rw [mul_comm]
    _ = (1 : ℝ≥0∞) / 2 := by
      simpa only [one_mul, mul_comm (2 : ℝ≥0∞)] using
        (ENNReal.mul_div_mul_right 1 2 hn (ENNReal.natCast_ne_top _))

private theorem dotProduct_add {B : ℕ} (c d u : Word B) :
    dotProduct (c + d) u = dotProduct c u + dotProduct d u := by
  unfold dotProduct
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem dotProduct_single {B : ℕ} (i : Fin B) (u : Word B) :
    dotProduct (Pi.single i (1 : Bit)) u = u i := by
  classical
  unfold dotProduct
  rw [Fintype.sum_eq_single i]
  · simp only [Pi.single_eq_same, one_mul]
  · intro j hji
    rw [Pi.single_eq_of_ne hji, zero_mul]

private theorem one_add_one_eq_zero : (1 : Bit) + 1 = 0 := by
  calc
    (1 : Bit) + 1 = 2 := by norm_num
    _ = 0 := ZMod.natCast_self 2

private theorem coordinate_toggle_involutive {B : ℕ} (i : Fin B) (c : Word B) :
    (c + Pi.single i (1 : Bit)) + Pi.single i 1 = c := by
  ext j
  by_cases hji : j = i
  · subst j
    simp only [Pi.add_apply, Pi.single_eq_same]
    calc
      c i + 1 + 1 = c i + ((1 : Bit) + 1) := by abel
      _ = c i := by rw [one_add_one_eq_zero]; simp
  · simp [hji]

private abbrev differenceDot {B : ℕ} (u v c : Word B) : Bit :=
  dotProduct c u - dotProduct c v

private theorem differenceDot_coordinate_toggle {B : ℕ} (u v c : Word B) (i : Fin B)
    (hbit : u i - v i = 1) :
    differenceDot u v (c + Pi.single i (1 : Bit)) = differenceDot u v c + 1 := by
  simp only [differenceDot, dotProduct_add, dotProduct_single]
  calc
    (dotProduct c u + u i) - (dotProduct c v + v i) =
        (dotProduct c u - dotProduct c v) + (u i - v i) := by abel
    _ = dotProduct c u - dotProduct c v + 1 := by rw [hbit]

private abbrev coefficientFiber {B : ℕ} (u v : Word B) (z : Bit) :=
  {c : Word B // differenceDot u v c = z}

private def coefficientToggleEquiv {B : ℕ} (u v : Word B) (i : Fin B)
    (hbit : u i - v i = 1) (z : Bit) :
    coefficientFiber u v z ≃ coefficientFiber u v (z + 1) where
  toFun c := ⟨c.1 + Pi.single i (1 : Bit), by
    rw [differenceDot_coordinate_toggle u v c.1 i hbit, c.2]⟩
  invFun c := ⟨c.1 + Pi.single i (1 : Bit), by
    rw [differenceDot_coordinate_toggle u v c.1 i hbit, c.2]
    calc
      z + 1 + 1 = z + ((1 : Bit) + 1) := by abel
      _ = z := by rw [one_add_one_eq_zero]; simp⟩
  left_inv c := by
    apply Subtype.ext
    exact coordinate_toggle_involutive i c.1
  right_inv c := by
    apply Subtype.ext
    exact coordinate_toggle_involutive i c.1

private theorem bit_eq_zero_or_one (a : Bit) : a = 0 ∨ a = 1 := by
  have ha : a.val < 2 := ZMod.val_lt a
  interval_cases hval : a.val
  · left
    calc
      a = (a.val : Bit) := (ZMod.natCast_zmod_val a).symm
      _ = 0 := by rw [hval]; rfl
  · right
    calc
      a = (a.val : Bit) := (ZMod.natCast_zmod_val a).symm
      _ = 1 := by rw [hval]; rfl

private theorem coefficientFiber_card_eq {B : ℕ} (u v : Word B) (i : Fin B)
    (hbit : u i - v i = 1) (z : Bit)
    [Fintype (coefficientFiber u v z)] [Fintype (coefficientFiber u v 0)] :
    Fintype.card (coefficientFiber u v z) = Fintype.card (coefficientFiber u v 0) := by
  classical
  rcases bit_eq_zero_or_one z with hz | hz
  · simp [hz]
  · subst z
    simpa using (Fintype.card_congr (coefficientToggleEquiv u v i hbit 0)).symm

private abbrev coefficientFiberUnion {B : ℕ} (u v : Word B) :=
  {c : Word B // differenceDot u v c = 0 ∨ differenceDot u v c = 1}

private def coefficientFiberUnionEquiv {B : ℕ} (u v : Word B) :
    coefficientFiberUnion u v ≃ Word B where
  toFun c := c.1
  invFun c := ⟨c, bit_eq_zero_or_one (differenceDot u v c)⟩
  left_inv c := by apply Subtype.ext; rfl
  right_inv _ := rfl

private theorem coefficientFiber_zero_card {B : ℕ} (u v : Word B) (i : Fin B)
    (hbit : u i - v i = 1)
    [Fintype (coefficientFiber u v 0)] [Fintype (coefficientFiber u v 1)] :
    Fintype.card (Word B) = 2 * Fintype.card (coefficientFiber u v 0) := by
  classical
  have hdisj : Disjoint (fun c : Word B => differenceDot u v c = 0)
      (fun c => differenceDot u v c = 1) := by
    refine Pi.disjoint_iff.mpr fun c => ?_
    rw [Prop.disjoint_iff]
    rintro ⟨hc0, hc1⟩
    have h01 : (0 : Bit) ≠ 1 := by
      intro h
      have hv := (ZMod.natCast_eq_natCast_iff' (0 : ℕ) (1 : ℕ) 2).mp h
      norm_num at hv
    exact h01 (hc0.symm.trans hc1)
  have hcard : Fintype.card (coefficientFiber u v 1) =
      Fintype.card (coefficientFiber u v 0) := by
    simpa using (Fintype.card_congr (coefficientToggleEquiv u v i hbit 0)).symm
  calc
    Fintype.card (Word B) = Fintype.card (coefficientFiberUnion u v) :=
      (Fintype.card_congr (coefficientFiberUnionEquiv u v)).symm
    _ = Fintype.card (coefficientFiber u v 0) +
        Fintype.card (coefficientFiber u v 1) :=
      Fintype.card_subtype_or_disjoint _ _ hdisj
    _ = 2 * Fintype.card (coefficientFiber u v 0) := by
      rw [hcard]
      simp [two_mul]

private abbrev pairFiber {B : ℕ} (u v : Word B) (a d : Bit) :=
  {s : Sample B // affineHash s u = a ∧ affineHash s v = d}

private def pairFiberEquivCoefficientFiber {B : ℕ} (u v : Word B) (a d : Bit) :
    pairFiber u v a d ≃ coefficientFiber u v (a - d) where
  toFun s := ⟨s.1.1, by
    rcases s.2 with ⟨hsu, hsv⟩
    change dotProduct s.1.1 u + s.1.2 = a at hsu
    change dotProduct s.1.1 v + s.1.2 = d at hsv
    calc
      dotProduct s.1.1 u - dotProduct s.1.1 v =
          (dotProduct s.1.1 u + s.1.2) - (dotProduct s.1.1 v + s.1.2) := by abel
      _ = a - d := by rw [hsu, hsv]
    ⟩
  invFun c := ⟨(c.1, a - dotProduct c.1 u), by
    constructor
    · simp [affineHash]
    · change dotProduct c.1 v + (a - dotProduct c.1 u) = d
      have hc := c.2
      change dotProduct c.1 u - dotProduct c.1 v = a - d at hc
      calc
        dotProduct c.1 v + (a - dotProduct c.1 u) =
            a - (dotProduct c.1 u - dotProduct c.1 v) := by abel
        _ = d := by rw [hc]; abel
    ⟩
  left_inv s := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    ·
      have hs := s.2.1
      change dotProduct s.1.1 u + s.1.2 = a at hs
      calc
        a - dotProduct s.1.1 u =
            (dotProduct s.1.1 u + s.1.2) - dotProduct s.1.1 u :=
              congrArg (fun x : Bit => x - dotProduct s.1.1 u) hs.symm
        _ = s.1.2 := by abel
  right_inv _ := rfl

private theorem exists_coordinate_of_ne {B : ℕ} {u v : Word B} (h : u ≠ v) :
    ∃ i : Fin B, u i ≠ v i := by
  by_contra hnot
  apply h
  funext i
  exact not_ne_iff.mp (not_exists.mp hnot i)

private theorem distinct_coordinate_difference_is_one {B : ℕ} {u v : Word B}
    {i : Fin B} (h : u i ≠ v i) : u i - v i = 1 := by
  rcases bit_eq_zero_or_one (u i) with hu | hu <;>
    rcases bit_eq_zero_or_one (v i) with hv | hv
  · rw [hu, hv] at h
    exact (h rfl).elim
  · rw [hu, hv, zero_sub]
    exact ZMod.neg_one_eq_one_iff.mpr (Or.inr rfl)
  · rw [hu, hv]
    simp
  · rw [hu, hv] at h
    exact (h rfl).elim

private theorem pairFiber_card {B : ℕ} {u v : Word B} (huv : u ≠ v)
    (a d : Bit) [Fintype (pairFiber u v a d)]
    [Fintype (coefficientFiber u v 0)] : Fintype.card (pairFiber u v a d) =
      Fintype.card (coefficientFiber u v 0) := by
  classical
  obtain ⟨i, hi⟩ := exists_coordinate_of_ne huv
  rw [Fintype.card_congr (pairFiberEquivCoefficientFiber u v a d)]
  exact coefficientFiber_card_eq u v i (distinct_coordinate_difference_is_one hi) (a - d)

/-- For distinct words, the two affine hash outputs have each prescribed pair of bits
with probability exactly one quarter. The distinctness premise is impossible for `B = 0`. -/
theorem affineHash_pair_probability {B : ℕ} {u v : Word B} (huv : u ≠ v)
    (a d : Bit) :
    eventProbability (fun s => affineHash s u = a ∧ affineHash s v = d) =
      (1 : ℝ≥0∞) / 4 := by
  classical
  rw [eventProbability_eq_card_ratio, pairFiber_card huv]
  obtain ⟨i, hi⟩ := exists_coordinate_of_ne huv
  rw [sample_card, coefficientFiber_zero_card u v i
    (distinct_coordinate_difference_is_one hi)]
  rw [Nat.cast_mul, Nat.cast_mul]
  have hpos : 0 < Fintype.card (coefficientFiber u v 0) := by
    apply Fintype.card_pos_iff.mpr
    refine ⟨⟨0, ?_⟩⟩
    simp [differenceDot, dotProduct]
  have hq : (Fintype.card (coefficientFiber u v 0) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hpos.ne'
  have hden : (↑(2 : ℕ) : ℝ≥0∞) * ((↑(2 : ℕ) : ℝ≥0∞) *
      (Fintype.card (coefficientFiber u v 0) : ℝ≥0∞)) =
      (Fintype.card (coefficientFiber u v 0) : ℝ≥0∞) * ↑(4 : ℕ) := by
    calc
      (↑(2 : ℕ) : ℝ≥0∞) * ((↑(2 : ℕ) : ℝ≥0∞) *
          (Fintype.card (coefficientFiber u v 0) : ℝ≥0∞)) =
          ((↑(2 : ℕ) : ℝ≥0∞) * ↑(2 : ℕ)) *
            (Fintype.card (coefficientFiber u v 0) : ℝ≥0∞) := by ac_rfl
      _ = (Fintype.card (coefficientFiber u v 0) : ℝ≥0∞) * ↑(4 : ℕ) := by
        norm_num
        ac_rfl
  rw [hden]
  have hcast4 : (↑(4 : ℕ) : ℝ≥0∞) = 4 := by norm_num
  rw [hcast4]
  simpa only [one_mul, mul_comm] using
    (ENNReal.mul_div_mul_right 1 4 hq (ENNReal.natCast_ne_top _))

/-- Given either prescribed output at one word, either output at a distinct word has
probability one half. This is the exact event-probability ratio. -/
theorem affineHash_conditional_probability {B : ℕ} {u v : Word B} (huv : u ≠ v)
    (a d : Bit) :
    eventProbability (fun s => affineHash s u = a ∧ affineHash s v = d) /
      eventProbability (fun s => affineHash s u = a) = (1 : ℝ≥0∞) / 2 := by
  rw [affineHash_pair_probability huv a d, affineHash_probability u a]
  have hratio : (2 : ℝ≥0∞) / 4 = (1 : ℝ≥0∞) / 2 := by
    have h4 : (2 : ℝ≥0∞) * 2 = 4 := by norm_num
    rw [← h4]
    have hcast2 : (↑(2 : ℕ) : ℝ≥0∞) = 2 := by norm_num
    simpa only [one_mul, hcast2] using
      (ENNReal.mul_div_mul_right 1 2 (by norm_num)
        (ENNReal.natCast_ne_top 2))
  have hinv : ((1 : ℝ≥0∞) / 2)⁻¹ = (2 : ℝ≥0∞) := by
    rw [ENNReal.inv_div (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ∞))
      (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))]
    simp
  rw [ENNReal.div_eq_inv_mul, hinv]
  simpa only [div_eq_mul_inv, one_mul] using hratio

/-- Conditional on `H(u)=1`, a distinct fixed word has hash bit one with probability one half,
expressed as the exact conditional event-probability ratio. -/
theorem affineHash_conditional_one {B : ℕ} {u v : Word B} (huv : u ≠ v) :
    eventProbability (fun s => affineHash s u = 1 ∧ affineHash s v = 1) /
      eventProbability (fun s => affineHash s u = 1) = (1 : ℝ≥0∞) / 2 :=
  affineHash_conditional_probability huv 1 1

/-- The conditioning event has positive probability, for every width including zero. -/
theorem affineHash_one_probability_pos {B : ℕ} (u : Word B) :
    0 < eventProbability (fun s => affineHash s u = 1) := by
  rw [affineHash_probability]
  exact ENNReal.div_pos one_ne_zero (by norm_num)

/-- The same half-probability in Mathlib's conditional-measure API, conditioned on `H(u)=1`.
Only the distinctness of the two fixed words is required. -/
theorem affineHash_conditional_measure {B : ℕ} {u v : Word B} (huv : u ≠ v)
    (d : Bit) :
    ProbabilityTheory.cond (jointLaw B).toMeasure {s | affineHash s u = 1}
      {s | affineHash s v = d} = (1 : ℝ≥0∞) / 2 := by
  rw [ProbabilityTheory.cond_apply MeasurableSet.of_discrete]
  change ((jointLaw B).toMeasure {s | affineHash s u = 1})⁻¹ *
    (jointLaw B).toMeasure {s | affineHash s u = 1 ∧ affineHash s v = d} = _
  rw [← eventProbability_eq_measure, ← eventProbability_eq_measure,
    ← ENNReal.div_eq_inv_mul]
  exact affineHash_conditional_probability huv 1 d

end Bandits.Support.AffineChannelLaw

end
