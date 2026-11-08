/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CanonicalFastSampling

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Complement-local fast-arm sampling

The literal candidate score uses current weights only on the actual fast-arm
complement. The frozen anchor remains available on every arm, including the
slow set, through its reciprocal-anchor sum. The local law and sampler are
proved equal to the existing canonical law and inverse-CDF sampler whenever a
positive global current-weight vector is restricted to the complement.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:16-37,96-113` and
`sources/zip4/manuscript/05_binary_transport.tex:65-85`. These are internal
fixed-local-data results, not a coordinator recovery invariant or a closed
manuscript lemma.
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory

namespace Bandits.Support.FastComplementLocality

open Bandits.Support.CanonicalFastSampling
open Bandits.Support.CanonicalOrientedSetLaw
open Bandits.Support.ConstructorDimensions
open Bandits.Support.FiniteOrientationDisintegration
open Bandits.Support.CanonicalRecordingRates

/-- The source's unnormalized fast-arm score, with current weight supplied only
on the actual complement subtype. The anchor sum includes every frozen anchor
value on `U`.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:24-29`. -/
@[expose] noncomputable def localFastCandidateMass {p : Parameters}
    (v : Fin p.K → ℝ) (U : SlowSet p.K p.m)
    (w : FastArm U → ℝ) (j : FastArm U) : ℝ :=
  w j / (1 + inverseAnchorSum v U.val * v j.1)

/-- The source normalizer, summed over the genuine complement only.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:24-29`. -/
@[expose] noncomputable def localFastNormalizer {p : Parameters}
    (v : Fin p.K → ℝ) (U : SlowSet p.K p.m) (w : FastArm U → ℝ) : ℝ :=
  ∑ j : FastArm U, localFastCandidateMass v U w j

/-- The normalized source conditional fast-arm mass on the complement.
Positivity and normalization are established below from the literal inputs.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:24-29`. -/
@[expose] noncomputable def localConditionalFastMass {p : Parameters}
    (v : Fin p.K → ℝ) (U : SlowSet p.K p.m) (w : FastArm U → ℝ)
    (_hv : ∀ i, 0 < v i) (_hw : ∀ j, 0 < w j)
    (j : FastArm U) : ℝ :=
  localFastCandidateMass v U w j / localFastNormalizer v U w

/-- The locally specified, uniformly explored fast-arm law. Every current
weight argument is indexed by `FastArm U`; the anchor remains a positive
function on all of `Fin p.K`. The learning-rate cap and envelope are the
source inputs used by the canonical mixture.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:24-29,96-113`. -/
@[expose] noncomputable def localFastLaw (p : Parameters) (eta : ℝ)
    (_heta : 0 < eta)
    (_heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v : Fin p.K → ℝ) (U : SlowSet p.K p.m)
    (w : FastArm U → ℝ) (_hv : ∀ i, 0 < v i)
    (_hw : ∀ j, 0 < w j) (_hvw : ∀ j, v j.1 ≤ w j)
    (_hwv : ∀ j, w j ≤ 2 * v j.1) (j : FastArm U) : ℝ :=
  (1 - gamma p eta) * localConditionalFastMass v U w _hv _hw j +
    gamma p eta / ((p.K - p.m + 1 : ℕ) : ℝ)

/-- The local score has a positive denominator on each actual complement arm. -/
theorem localFastCandidateMass_denominator_pos {p : Parameters}
    (v : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (U : SlowSet p.K p.m)
    (j : FastArm U) :
    0 < 1 + inverseAnchorSum v U.val * v j.1 := by
  exact candidateWeight_denominator_pos (Finset.univ : Finset (Fin p.K))
    U.val v (Finset.subset_univ _) (fun i _ => hv i) j

/-- Every local unnormalized candidate score is positive. -/
theorem localFastCandidateMass_pos {p : Parameters}
    (v : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (U : SlowSet p.K p.m)
    (w : FastArm U → ℝ) (hw : ∀ j, 0 < w j) (j : FastArm U) :
    0 < localFastCandidateMass v U w j := by
  exact div_pos (hw j) (localFastCandidateMass_denominator_pos v hv U j)

/-- The complement-local normalizer is positive; no global current weights are
used to establish its denominator. -/
theorem localFastNormalizer_pos {p : Parameters}
    (v : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (U : SlowSet p.K p.m)
    (w : FastArm U → ℝ) (hw : ∀ j, 0 < w j) :
    0 < localFastNormalizer v U w := by
  unfold localFastNormalizer
  apply Finset.sum_pos
  · intro j _
    exact localFastCandidateMass_pos v hv U w hw j
  · obtain ⟨j⟩ := fastArm_nonempty U
    exact ⟨j, Finset.mem_univ j⟩

/-- The normalized local candidate masses form a positive conditional law. -/
theorem localConditionalFastMass_pos {p : Parameters}
    (v : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (U : SlowSet p.K p.m)
    (w : FastArm U → ℝ) (hw : ∀ j, 0 < w j) (j : FastArm U) :
    0 < localConditionalFastMass v U w hv hw j := by
  exact div_pos (localFastCandidateMass_pos v hv U w hw j)
    (localFastNormalizer_pos v hv U w hw)

/-- The conditional local masses normalize on the actual complement subtype. -/
theorem localConditionalFastMass_sum_eq_one {p : Parameters}
    (v : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (U : SlowSet p.K p.m)
    (w : FastArm U → ℝ) (hw : ∀ j, 0 < w j) :
    (∑ j : FastArm U, localConditionalFastMass v U w hv hw j) = 1 := by
  have hnormalizer := localFastNormalizer_pos v hv U w hw
  unfold localConditionalFastMass
  rw [← Finset.sum_div]
  change localFastNormalizer v U w / localFastNormalizer v U w = 1
  exact div_self (ne_of_gt hnormalizer)

private theorem localGamma_bounds {p : Parameters} {eta : ℝ}
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ))) :
    0 ≤ gamma p eta ∧ gamma p eta ≤ 1 / 2 :=
  gamma_nonneg_and_le_half p heta heta_le

private theorem localGamma_pos {p : Parameters} {eta : ℝ} (heta : 0 < eta) :
    0 < gamma p eta := by
  unfold gamma
  have hcard : 0 < ((p.K - p.m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < p.K - p.m + 1 by omega)
  exact mul_pos (mul_pos (by norm_num) hcard) (beta_pos p heta)

/-- The full locally defined mixture has positive mass on every complement
arm. -/
theorem localFastLaw_pos (p : Parameters) {eta : ℝ} (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (U : SlowSet p.K p.m)
    (w : FastArm U → ℝ) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j.1 ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j.1)
    (j : FastArm U) :
    0 < localFastLaw p eta heta heta_le v U w hv hw hvw hwv j := by
  have hgamma := localGamma_bounds heta heta_le
  have hcoef : 0 < 1 - gamma p eta := by linarith
  have hconditional := localConditionalFastMass_pos v hv U w hw j
  have hcard : (0 : ℝ) < ((p.K - p.m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < p.K - p.m + 1 by omega)
  unfold localFastLaw
  have huniform : 0 < gamma p eta / ((p.K - p.m + 1 : ℕ) : ℝ) :=
    div_pos (localGamma_pos heta) hcard
  exact add_pos (mul_pos hcoef hconditional) huniform

/-- The local mixture's masses sum to one, proved from the local denominator,
the conditional normalization, and the source exploration bound. -/
theorem localFastLaw_sum_eq_one (p : Parameters) {eta : ℝ}
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (U : SlowSet p.K p.m)
    (w : FastArm U → ℝ) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j.1 ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j.1) :
    (∑ j : FastArm U, localFastLaw p eta heta heta_le v U w hv hw hvw hwv j) = 1 := by
  have hconditional := localConditionalFastMass_sum_eq_one v hv U w hw
  have hcard : (Fintype.card (FastArm U) : ℝ) =
      ((p.K - p.m + 1 : ℕ) : ℝ) := by
    rw [Fintype.card_coe, fastArmFinset_card]
  have hdenom : (0 : ℝ) < ((p.K - p.m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt
      (Nat.lt_of_lt_of_le (by decide : 1 < 2) (fastArmCardinality_ge_two U)))
  calc
    (∑ j : FastArm U, localFastLaw p eta heta heta_le v U w hv hw hvw hwv j) =
        (1 - gamma p eta) *
            (∑ j : FastArm U, localConditionalFastMass v U w hv hw j) +
          (Fintype.card (FastArm U) : ℝ) *
            (gamma p eta / ((p.K - p.m + 1 : ℕ) : ℝ)) := by
      simp only [localFastLaw]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    _ = 1 := by
      rw [hconditional, hcard]
      have hcancel :
          ((p.K - p.m + 1 : ℕ) : ℝ) *
            (gamma p eta / ((p.K - p.m + 1 : ℕ) : ℝ)) = gamma p eta := by
        field_simp [ne_of_gt hdenom]
      rw [hcancel]
      ring

/-- The finite PMF induced by the local mixed masses. -/
@[expose] noncomputable def localFastPMF (p : Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (U : SlowSet p.K p.m)
    (w : FastArm U → ℝ) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j.1 ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j.1) : PMF (FastArm U) :=
  PMF.ofFintype
    (fun j => ENNReal.ofReal (localFastLaw p eta heta heta_le v U w hv hw hvw hwv j))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun j _ => (localFastLaw_pos p heta heta_le v hv U w hw hvw hwv j).le),
        localFastLaw_sum_eq_one p heta heta_le v hv U w hw hvw hwv,
        ENNReal.ofReal_one])

/-- Exact point masses of the local fast-arm PMF. -/
@[simp] theorem localFastPMF_apply (p : Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (U : SlowSet p.K p.m)
    (w : FastArm U → ℝ) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j.1 ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j.1)
    (j : FastArm U) :
    localFastPMF p eta heta heta_le v hv U w hw hvw hwv j =
      ENNReal.ofReal (localFastLaw p eta heta heta_le v U w hv hw hvw hwv j) := rfl

/-- The local one-scalar inverse-CDF sampler. It uses the very same increasing
complement order and `ContinuousCategorical.sample` as the canonical sampler.
-/
@[expose] noncomputable def sampleLocalFast (p : Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (U : SlowSet p.K p.m)
    (w : FastArm U → ℝ) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j.1 ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j.1)
    (x : ContinuousCategorical.Scalar) : FastArm U :=
  fastArmOrderIso U
    (ContinuousCategorical.sample
      (Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le (by decide : 1 < 2)
        (fastArmCardinality_ge_two U)))
      (fun k => localFastLaw p eta heta heta_le v U w hv hw hvw hwv
        (fastArmOrderIso U k))
      (by
        calc
          (∑ k, localFastLaw p eta heta heta_le v U w hv hw hvw hwv
              (fastArmOrderIso U k)) =
              ∑ j : FastArm U, localFastLaw p eta heta heta_le v U w hv hw hvw hwv j :=
            Equiv.sum_comp (fastArmOrderIso U).toEquiv _
          _ = 1 := localFastLaw_sum_eq_one p heta heta_le v hv U w hw hvw hwv) x)

private theorem scalarSample_eq_of_masses_eq {n : ℕ} (hn : 0 < n)
    (p q : Fin n → ℝ) (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1)
    (x : ContinuousCategorical.Scalar) (hmass : ∀ i, p i = q i) :
    ContinuousCategorical.sample hn p hp x =
      ContinuousCategorical.sample hn q hq x := by
  have hupper (i : Fin n) :
      ContinuousCategorical.upper p i = ContinuousCategorical.upper q i := by
    unfold ContinuousCategorical.upper
    apply Finset.sum_congr rfl
    intro j hj
    exact hmass j
  have hpLeast :
      x.val < ContinuousCategorical.upper q (ContinuousCategorical.sample hn p hp x) ∧
        ∀ j < ContinuousCategorical.sample hn p hp x,
          ContinuousCategorical.upper q j ≤ x.val := by
    have h :=
      (ContinuousCategorical.sample_eq_iff_least hn p hp x
        (ContinuousCategorical.sample hn p hp x)).mp rfl
    refine ⟨?_, ?_⟩
    · rw [← hupper]
      exact h.1
    · intro j hj
      rw [← hupper j]
      exact h.2 j hj
  have hqLeast :=
    (ContinuousCategorical.sample_eq_iff_least hn q hq x
      (ContinuousCategorical.sample hn q hq x)).mp rfl
  exact (ContinuousCategorical.exists_unique_least hn q hq x).unique hpLeast hqLeast

/-- Restricting a global current-weight vector to `FastArm U` leaves the
literal local candidate score unchanged. -/
theorem localFastCandidateMass_eq_candidateWeight {p : Parameters}
    (v w : Fin p.K → ℝ) (U : SlowSet p.K p.m) (j : FastArm U) :
    localFastCandidateMass v U (fun k => w k.1) j =
      candidateWeight w v U.val j.1 := rfl

/-- The local normalization denominator is exactly the accepted conditional
normalizer after restricting global weights to the complement. -/
theorem localFastNormalizer_eq_candidateNormalizer {p : Parameters}
    (v w : Fin p.K → ℝ) (U : SlowSet p.K p.m) :
    localFastNormalizer v U (fun k => w k.1) =
      candidateNormalizer (Finset.univ : Finset (Fin p.K)) w v U.val := by
  classical
  unfold localFastNormalizer candidateNormalizer
  change (∑ j ∈ (fastArmFinset U).attach,
      localFastCandidateMass v U (fun k => w k.1) j) =
    ∑ j ∈ (fastArmFinset U).attach, candidateWeight w v U.val j.1
  apply Finset.sum_congr rfl
  intro j hj
  rfl

/-- The normalized local conditional mass agrees pointwise with the accepted
`conditionalFastLaw` for every global current-weight vector. -/
theorem localConditionalFastMass_eq_conditionalFastLaw {p : Parameters}
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i)
    (hw : ∀ i, 0 < w i) (U : SlowSet p.K p.m) (j : FastArm U) :
    localConditionalFastMass v U (fun k => w k.1) hv (fun k => hw k.1) j =
      conditionalFastLaw (Finset.univ : Finset (Fin p.K)) w v U.val
        (Finset.subset_univ _) (slowSet_complement_nonempty p.two_le_m p.m_lt_K U)
        (fun i _ => hw i) (fun i _ => hv i) j := by
  unfold localConditionalFastMass conditionalFastLaw
  rw [localFastCandidateMass_eq_candidateWeight,
    localFastNormalizer_eq_candidateNormalizer]

/-- Complete pointwise characterization of the local mixed mass by the
existing canonical `qGamma`. -/
theorem localFastLaw_eq_qGamma (p : Parameters) {eta : ℝ} (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (hwv : ∀ i, w i ≤ 2 * v i)
    (U : SlowSet p.K p.m) (j : FastArm U) :
    localFastLaw p eta heta heta_le v U (fun k => w k.1) hv
        (fun k => hw k.1) (fun k => hvw k.1) (fun k => hwv k.1) j =
      CanonicalFastSampling.qGamma p eta heta heta_le v w hv hw hvw hwv U j := by
  unfold localFastLaw CanonicalFastSampling.qGamma
  rw [localConditionalFastMass_eq_conditionalFastLaw v w hv hw U j]

/-- The local sampler is pointwise the existing canonical sampler for every
scalar input, not merely equal in distribution. -/
theorem sampleLocalFast_eq_sampleFast (p : Parameters) {eta : ℝ} (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (hwv : ∀ i, w i ≤ 2 * v i)
    (U : SlowSet p.K p.m) (x : ContinuousCategorical.Scalar) :
    sampleLocalFast p eta heta heta_le v hv U (fun k => w k.1)
        (fun k => hw k.1) (fun k => hvw k.1) (fun k => hwv k.1) x =
      CanonicalFastSampling.sampleFast p eta heta heta_le v w hv hw hvw hwv U x := by
  unfold sampleLocalFast CanonicalFastSampling.sampleFast
  apply congrArg (fastArmOrderIso U)
  apply scalarSample_eq_of_masses_eq _ _ _ _ _ x
  intro k
  exact localFastLaw_eq_qGamma p heta heta_le v w hv hw hvw hwv U
    (fastArmOrderIso U k)

/-- Local samplers are unchanged when their complement current-weight
functions agree pointwise. -/
theorem sampleLocalFast_eq_of_weights_eq (p : Parameters) {eta : ℝ}
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (U : SlowSet p.K p.m)
    (w w' : FastArm U → ℝ) (hw : ∀ j, 0 < w j) (hw' : ∀ j, 0 < w' j)
    (hvw : ∀ j, v j.1 ≤ w j) (hvw' : ∀ j, v j.1 ≤ w' j)
    (hwv : ∀ j, w j ≤ 2 * v j.1) (hwv' : ∀ j, w' j ≤ 2 * v j.1)
    (hweight : w = w') (x : ContinuousCategorical.Scalar) :
    sampleLocalFast p eta heta heta_le v hv U w hw hvw hwv x =
      sampleLocalFast p eta heta heta_le v hv U w' hw' hvw' hwv' x := by
  subst w'
  rfl

/-- The local sampler is measurable on its actual continuous scalar carrier. -/
theorem measurable_sampleLocalFast (p : Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (U : SlowSet p.K p.m)
    (w : FastArm U → ℝ) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j.1 ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j.1) :
    Measurable (sampleLocalFast p eta heta heta_le v hv U w hw hvw hwv) := by
  classical
  apply measurable_to_countable'
  intro j
  let masses (k : Fin (p.K - p.m + 1)) :=
    localFastLaw p eta heta heta_le v U w hv hw hvw hwv (fastArmOrderIso U k)
  have hmasssum : (∑ k, masses k) = 1 := by
    calc
      (∑ k, masses k) =
          ∑ j : FastArm U, localFastLaw p eta heta heta_le v U w hv hw hvw hwv j := by
        simp only [masses]
        exact Equiv.sum_comp (fastArmOrderIso U).toEquiv _
      _ = 1 := localFastLaw_sum_eq_one p heta heta_le v hv U w hw hvw hwv
  have hmasses_nonneg : ∀ k, 0 ≤ masses k := by
    intro k
    exact (localFastLaw_pos p heta heta_le v hv U w hw hvw hwv
      (fastArmOrderIso U k)).le
  have hn : 0 < p.K - p.m + 1 :=
    Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le (by decide : 1 < 2)
      (fastArmCardinality_ge_two U))
  have hfiber :
      sampleLocalFast p eta heta heta_le v hv U w hw hvw hwv ⁻¹' {j} =
        ContinuousCategorical.sample hn masses hmasssum ⁻¹'
          { (fastArmOrderIso U).symm j } := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, sampleLocalFast, masses]
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

/-- The local sampler has the exact source mass at each complement arm under
the existing uniform scalar measure. -/
theorem uniform_sampleLocalFast_singleton (p : Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (U : SlowSet p.K p.m)
    (w : FastArm U → ℝ) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j.1 ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j.1)
    (j : FastArm U) :
    ContinuousCategorical.uniform
        (sampleLocalFast p eta heta heta_le v hv U w hw hvw hwv ⁻¹' {j}) =
      ENNReal.ofReal (localFastLaw p eta heta heta_le v U w hv hw hvw hwv j) := by
  have hsum := localFastLaw_sum_eq_one p heta heta_le v hv U w hw hvw hwv
  have hpnonneg : ∀ k : Fin (p.K - p.m + 1),
      0 ≤ localFastLaw p eta heta heta_le v U w hv hw hvw hwv
        (fastArmOrderIso U k) :=
    fun k => (localFastLaw_pos p heta heta_le v hv U w hw hvw hwv
      (fastArmOrderIso U k)).le
  let mass := fun k : Fin (p.K - p.m + 1) =>
    localFastLaw p eta heta heta_le v U w hv hw hvw hwv (fastArmOrderIso U k)
  have hmasssum : (∑ k, mass k) = 1 := by
    calc
      (∑ k, mass k) =
          ∑ j : FastArm U, localFastLaw p eta heta heta_le v U w hv hw hvw hwv j := by
        simp only [mass]
        exact Equiv.sum_comp (fastArmOrderIso U).toEquiv _
      _ = 1 := hsum
  have hfiber :
      sampleLocalFast p eta heta heta_le v hv U w hw hvw hwv ⁻¹' {j} =
        ContinuousCategorical.sample
          (Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le (by decide : 1 < 2)
            (fastArmCardinality_ge_two U)))
          mass hmasssum ⁻¹' { (fastArmOrderIso U).symm j } := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, sampleLocalFast, mass]
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
      (fastArmCardinality_ge_two U))) hpnonneg hmasssum]
  congr 1
  change mass ((fastArmOrderIso U).symm j) =
    localFastLaw p eta heta heta_le v U w hv hw hvw hwv j
  simp [mass]

/-- The actual uniform scalar pushforward of the local sampler is its finite
local fast-arm PMF. -/
theorem uniform_map_sampleLocalFast (p : Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (U : SlowSet p.K p.m)
    (w : FastArm U → ℝ) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j.1 ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j.1) :
    ContinuousCategorical.uniform.map
        (sampleLocalFast p eta heta heta_le v hv U w hw hvw hwv) =
      (localFastPMF p eta heta heta_le v hv U w hw hvw hwv).toMeasure := by
  apply Measure.ext_of_singleton
  intro j
  rw [Measure.map_apply
      (measurable_sampleLocalFast p eta heta heta_le v hv U w hw hvw hwv)
      (measurableSet_singleton j),
    uniform_sampleLocalFast_singleton p eta heta heta_le v hv U w hw hvw hwv j,
    PMF.toMeasure_apply_singleton _ j (measurableSet_singleton j),
    localFastPMF_apply]

/-- For global weights satisfying the existing source inputs, `qGamma` is
unchanged by any modification confined to the slow set. -/
theorem qGamma_eq_of_eq_on_complement (p : Parameters) {eta : ℝ}
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w w' : Fin p.K → ℝ) (hv : ∀ i, 0 < v i)
    (hw : ∀ i, 0 < w i) (hw' : ∀ i, 0 < w' i)
    (hvw : ∀ i, v i ≤ w i) (hvw' : ∀ i, v i ≤ w' i)
    (hwv : ∀ i, w i ≤ 2 * v i) (hwv' : ∀ i, w' i ≤ 2 * v i)
    (U : SlowSet p.K p.m)
    (heq : ∀ i, i ∉ U.val → w i = w' i) (j : FastArm U) :
    CanonicalFastSampling.qGamma p eta heta heta_le v w hv hw hvw hwv U j =
      CanonicalFastSampling.qGamma p eta heta heta_le v w' hv hw' hvw' hwv' U j := by
  have hlocal : (fun k : FastArm U => w k.1) = fun k => w' k.1 := by
    funext k
    exact heq k.1 (Finset.mem_sdiff.mp k.2).2
  calc
    CanonicalFastSampling.qGamma p eta heta heta_le v w hv hw hvw hwv U j =
        localFastLaw p eta heta heta_le v U (fun k => w k.1) hv
          (fun k => hw k.1) (fun k => hvw k.1) (fun k => hwv k.1) j :=
      (localFastLaw_eq_qGamma p heta heta_le v w hv hw hvw hwv U j).symm
    _ = localFastLaw p eta heta heta_le v U (fun k => w' k.1) hv
          (fun k => hw' k.1) (fun k => hvw' k.1) (fun k => hwv' k.1) j := by
      unfold localFastLaw localConditionalFastMass localFastCandidateMass localFastNormalizer
      rw [hlocal]
    _ = CanonicalFastSampling.qGamma p eta heta heta_le v w' hv hw' hvw' hwv' U j :=
      localFastLaw_eq_qGamma p heta heta_le v w' hv hw' hvw' hwv' U j

/-- The canonical fast sampler is pathwise invariant under changes to current
weights on `U`, for every fixed scalar input. -/
theorem sampleFast_eq_of_eq_on_complement (p : Parameters) {eta : ℝ}
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w w' : Fin p.K → ℝ) (hv : ∀ i, 0 < v i)
    (hw : ∀ i, 0 < w i) (hw' : ∀ i, 0 < w' i)
    (hvw : ∀ i, v i ≤ w i) (hvw' : ∀ i, v i ≤ w' i)
    (hwv : ∀ i, w i ≤ 2 * v i) (hwv' : ∀ i, w' i ≤ 2 * v i)
    (U : SlowSet p.K p.m)
    (heq : ∀ i, i ∉ U.val → w i = w' i)
    (x : ContinuousCategorical.Scalar) :
    CanonicalFastSampling.sampleFast p eta heta heta_le v w hv hw hvw hwv U x =
      CanonicalFastSampling.sampleFast p eta heta heta_le v w' hv hw' hvw' hwv' U x := by
  have hlocal : (fun k : FastArm U => w k.1) = fun k => w' k.1 := by
    funext k
    exact heq k.1 (Finset.mem_sdiff.mp k.2).2
  calc
    CanonicalFastSampling.sampleFast p eta heta heta_le v w hv hw hvw hwv U x =
        sampleLocalFast p eta heta heta_le v hv U (fun k => w k.1)
          (fun k => hw k.1) (fun k => hvw k.1) (fun k => hwv k.1) x :=
      (sampleLocalFast_eq_sampleFast p heta heta_le v w hv hw hvw hwv U x).symm
    _ = sampleLocalFast p eta heta heta_le v hv U (fun k => w' k.1)
          (fun k => hw' k.1) (fun k => hvw' k.1) (fun k => hwv' k.1) x := by
      exact sampleLocalFast_eq_of_weights_eq p heta heta_le v hv U
        (fun k => w k.1) (fun k => w' k.1)
        (fun k => hw k.1) (fun k => hw' k.1)
        (fun k => hvw k.1) (fun k => hvw' k.1)
        (fun k => hwv k.1) (fun k => hwv' k.1) hlocal x
    _ = CanonicalFastSampling.sampleFast p eta heta heta_le v w' hv hw' hvw' hwv' U x :=
      sampleLocalFast_eq_sampleFast p heta heta_le v w' hv hw' hvw' hwv' U x

end Bandits.Support.FastComplementLocality

end
