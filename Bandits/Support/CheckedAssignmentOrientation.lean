/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.ContinuousCategorical
public import Bandits.Support.ContinuousControlSlice
public import Bandits.Support.FiniteOrientationDisintegration
public import Bandits.Support.OrientedAssignmentLaw
public import Bandits.Support.CanonicalAssignmentVector

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.FunProp

/-!
# Checked orientation after a supported set draw

This module checks the raw anchor only on the already selected supported set,
then checks its actual inverse-anchor normalizer and the resulting categorical
parameters before drawing the oriented arm.  It does not inspect or resample
the prefix coordinates, construct a set sampler, or turn local failure into a
protocol error state.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:16-37`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14,66-77`, and
`sources/zip4/manuscript/appendix_b_communication.tex:34-44`.
-/

public section

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Bandits.Support.CheckedAssignmentOrientation

open Bandits.Support.ContinuousCategorical
open Bandits.Support.FiniteOrientationDisintegration

/-- The explicit finite output of the raw checked orientation operation.
Failure carries no arm, so no default or repaired arm can be mistaken for a
sample. -/
inductive Output (K : ℕ) where
  | failure
  | sampled (arm : Fin K)
  deriving DecidableEq, Fintype

instance outputMeasurableSpace (K : ℕ) : MeasurableSpace (Output K) := ⊤

instance outputDiscreteMeasurableSpace (K : ℕ) : DiscreteMeasurableSpace (Output K) :=
  ⟨fun _ => trivial⟩

/-- The source's input product: a raw real anchor vector and one genuine
half-open scalar. -/
abbrev RawInput (p : ConstructorDimensions.Parameters) :=
  (Fin p.K → ℝ) × ContinuousControlSlice.Scalar

/-- The inverse-anchor probability at ordered rank `r`, written on the raw
anchor domain.  This helper is used to describe measurable level sets; the
checked operation evaluates it only after all used anchor coordinates and its
normalizer have passed their checks. -/
private def rawOrderedMasses {p : ConstructorDimensions.Parameters}
    (S : PrefixSetSampler.SetCarrier p.K p.m) (anchor : Fin p.K → ℝ) :
    Fin S.1.card → ℝ := fun r =>
  (1 / anchor (S.1.orderEmbOfFin rfl r)) /
    FiniteOrientationDisintegration.inverseAnchorSum anchor S.1

/-- The source inverse-anchor masses on the increasing enumeration of the
already selected set.  Positivity is required only for coordinates in `S`.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:16-19`. -/
@[expose] def usedOrientationMasses {p : ConstructorDimensions.Parameters}
    (S : PrefixSetSampler.SetCarrier p.K p.m) (anchor : Fin p.K → ℝ)
    (hanchor : ∀ i ∈ S.1, 0 < anchor i) : Fin S.1.card → ℝ := fun r =>
  FiniteOrientationDisintegration.orientationProbability anchor S.1
    (OrientedAssignmentLaw.sampled_set_nonempty p.two_le_m S) hanchor
    ⟨S.1.orderEmbOfFin rfl r, S.1.orderEmbOfFin_mem rfl r⟩

theorem usedOrientationMasses_pos {p : ConstructorDimensions.Parameters}
    (S : PrefixSetSampler.SetCarrier p.K p.m) (anchor : Fin p.K → ℝ)
    (hanchor : ∀ i ∈ S.1, 0 < anchor i) (r : Fin S.1.card) :
    0 < usedOrientationMasses S anchor hanchor r := by
  exact FiniteOrientationDisintegration.orientationProbability_pos anchor S.1
    (OrientedAssignmentLaw.sampled_set_nonempty p.two_le_m S) hanchor
    ⟨S.1.orderEmbOfFin rfl r, S.1.orderEmbOfFin_mem rfl r⟩

/-- The accepted local finite-orientation formula normalizes on the members of
the selected set. -/
theorem usedOrientationMasses_sum_eq_one {p : ConstructorDimensions.Parameters}
    (S : PrefixSetSampler.SetCarrier p.K p.m) (anchor : Fin p.K → ℝ)
    (hanchor : ∀ i ∈ S.1, 0 < anchor i) :
    (∑ r, usedOrientationMasses S anchor hanchor r) = 1 := by
  classical
  let e : Fin S.1.card ≃ {i // i ∈ S.1} :=
    (S.1.orderIsoOfFin rfl).toEquiv
  calc
    (∑ r, usedOrientationMasses S anchor hanchor r) =
        ∑ i : {i // i ∈ S.1},
          FiniteOrientationDisintegration.orientationProbability anchor S.1
            (OrientedAssignmentLaw.sampled_set_nonempty p.two_le_m S) hanchor i := by
      apply Fintype.sum_equiv e
      intro r
      rfl
    _ = 1 := by
      change (∑ i ∈ S.1.attach,
        FiniteOrientationDisintegration.orientationProbability anchor S.1
          (OrientedAssignmentLaw.sampled_set_nonempty p.two_le_m S) hanchor i) = 1
      exact FiniteOrientationDisintegration.orientationProbability_sum_eq_one anchor S.1
        (OrientedAssignmentLaw.sampled_set_nonempty p.two_le_m S) hanchor

theorem usedOrientationMasses_le_one {p : ConstructorDimensions.Parameters}
    (S : PrefixSetSampler.SetCarrier p.K p.m) (anchor : Fin p.K → ℝ)
    (hanchor : ∀ i ∈ S.1, 0 < anchor i) (r : Fin S.1.card) :
    usedOrientationMasses S anchor hanchor r ≤ 1 := by
  rw [← usedOrientationMasses_sum_eq_one S anchor hanchor]
  exact Finset.single_le_sum
    (fun q hq => (usedOrientationMasses_pos S anchor hanchor q).le)
    (Finset.mem_univ r)

theorem usedOrientationMasses_mem_Icc {p : ConstructorDimensions.Parameters}
    (S : PrefixSetSampler.SetCarrier p.K p.m) (anchor : Fin p.K → ℝ)
    (hanchor : ∀ i ∈ S.1, 0 < anchor i) (r : Fin S.1.card) :
    usedOrientationMasses S anchor hanchor r ∈ Set.Icc 0 1 :=
  ⟨(usedOrientationMasses_pos S anchor hanchor r).le,
    usedOrientationMasses_le_one S anchor hanchor r⟩

private theorem usedOrientationMasses_eq_rawOrderedMasses
    {p : ConstructorDimensions.Parameters}
    (S : PrefixSetSampler.SetCarrier p.K p.m) (anchor : Fin p.K → ℝ)
    (hanchor : ∀ i ∈ S.1, 0 < anchor i) :
    usedOrientationMasses S anchor hanchor = rawOrderedMasses S anchor := by
  funext r
  rfl

/-- The checked operation's ordered inverse-anchor draw.  Its branch order is
part of the definition: all used scalar denominators are checked before the
inverse-anchor sum, that sum is checked before division, and every categorical
parameter is checked before `ContinuousCategorical.sample` is called.

An invalid input returns `.failure` without an arm.  The first-block set is
already an input and is neither rechecked nor sampled here.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:16-19`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`, and
`sources/zip4/manuscript/appendix_b_communication.tex:34-44`. -/
@[expose] noncomputable def checkedOrientation
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (anchor : Fin p.K → ℝ) (v : ContinuousControlSlice.Scalar) : Output p.K :=
  if hanchor : ∀ i ∈ S.1, 0 < anchor i then
    if _hdenom : 0 < FiniteOrientationDisintegration.inverseAnchorSum anchor S.1 then
      let masses := usedOrientationMasses S anchor hanchor
      let invalidParameters := Finset.univ.filter
        (fun r : Fin S.1.card => ¬ (0 ≤ masses r ∧ masses r ≤ 1))
      if invalidParameters.Nonempty then
        Output.failure
      else
        Output.sampled (S.1.orderEmbOfFin rfl
          (ContinuousCategorical.sample
            (Finset.card_pos.mpr
              (OrientedAssignmentLaw.sampled_set_nonempty p.two_le_m S))
            masses (usedOrientationMasses_sum_eq_one S anchor hanchor) v))
    else Output.failure
  else Output.failure

theorem inverseAnchorSum_pos_of_used_anchor_pos
    {p : ConstructorDimensions.Parameters}
    (S : PrefixSetSampler.SetCarrier p.K p.m) (anchor : Fin p.K → ℝ)
    (hanchor : ∀ i ∈ S.1, 0 < anchor i) :
    0 < FiniteOrientationDisintegration.inverseAnchorSum anchor S.1 :=
  FiniteOrientationDisintegration.inverseAnchorSum_pos S.1 anchor
    (OrientedAssignmentLaw.sampled_set_nonempty p.two_le_m S) hanchor

/-- Once the local source denominators are positive, the checked normalizer
and every parameter check pass, and the operation is exactly the increasing
inverse-CDF draw with the original scalar. -/
theorem checkedOrientation_eq_sample_of_used_anchor_pos
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (anchor : Fin p.K → ℝ) (v : ContinuousControlSlice.Scalar)
    (hanchor : ∀ i ∈ S.1, 0 < anchor i) :
    checkedOrientation p S anchor v =
      Output.sampled (S.1.orderEmbOfFin rfl
        (ContinuousCategorical.sample
          (Finset.card_pos.mpr
            (OrientedAssignmentLaw.sampled_set_nonempty p.two_le_m S))
          (usedOrientationMasses S anchor hanchor)
          (usedOrientationMasses_sum_eq_one S anchor hanchor) v)) := by
  have hdenom := inverseAnchorSum_pos_of_used_anchor_pos S anchor hanchor
  have hparameters : ¬ (Finset.univ.filter
      (fun r : Fin S.1.card => ¬
        (0 ≤ usedOrientationMasses S anchor hanchor r ∧
          usedOrientationMasses S anchor hanchor r ≤ 1))).Nonempty := by
    rintro ⟨r, hr⟩
    exact (Finset.mem_filter.mp hr).2
      ⟨(usedOrientationMasses_pos S anchor hanchor r).le,
        usedOrientationMasses_le_one S anchor hanchor r⟩
  unfold checkedOrientation
  rw [dite_eq_left hanchor, dite_eq_left hdenom, ite_eq_right hparameters]

/-- The failure branch is taken exactly when some required anchor coordinate
on `S` is nonpositive.  The inverse-sum and parameter failure branches are
unreachable after the preceding checks pass. -/
theorem checkedOrientation_eq_failure_iff
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (anchor : Fin p.K → ℝ) (v : ContinuousControlSlice.Scalar) :
    checkedOrientation p S anchor v = Output.failure ↔
      ¬ ∀ i ∈ S.1, 0 < anchor i := by
  constructor
  · intro hresult hanchor
    rw [checkedOrientation_eq_sample_of_used_anchor_pos p S anchor v hanchor] at hresult
    cases hresult
  · intro hanchor
    unfold checkedOrientation
    exact dite_eq_right hanchor

/-- Success is equivalent to positivity of every used anchor denominator and
the actual inverse-anchor sum denominator.  The latter is then positive by the
accepted local finite-orientation formula. -/
theorem checkedOrientation_success_iff_denominators
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (anchor : Fin p.K → ℝ) (v : ContinuousControlSlice.Scalar) :
    (∃ j, checkedOrientation p S anchor v = Output.sampled j) ↔
      (∀ i ∈ S.1, 0 < anchor i) ∧
        0 < FiniteOrientationDisintegration.inverseAnchorSum anchor S.1 := by
  constructor
  · rintro ⟨j, hresult⟩
    have hanchor : ∀ i ∈ S.1, 0 < anchor i := by
      by_contra hnot
      have hfailure := (checkedOrientation_eq_failure_iff p S anchor v).2 hnot
      rw [hfailure] at hresult
      cases hresult
    exact ⟨hanchor, inverseAnchorSum_pos_of_used_anchor_pos S anchor hanchor⟩
  · rintro ⟨hanchor, _hdenom⟩
    refine ⟨S.1.orderEmbOfFin rfl
      (ContinuousCategorical.sample
        (Finset.card_pos.mpr (OrientedAssignmentLaw.sampled_set_nonempty p.two_le_m S))
        (usedOrientationMasses S anchor hanchor)
        (usedOrientationMasses_sum_eq_one S anchor hanchor) v), ?_⟩
    exact checkedOrientation_eq_sample_of_used_anchor_pos p S anchor v hanchor

theorem checkedOrientation_success_iff_used_anchors_positive
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (anchor : Fin p.K → ℝ) (v : ContinuousControlSlice.Scalar) :
    (∃ j, checkedOrientation p S anchor v = Output.sampled j) ↔
      ∀ i ∈ S.1, 0 < anchor i := by
  constructor
  · rintro ⟨j, hresult⟩
    exact (checkedOrientation_success_iff_denominators p S anchor v).mp
      ⟨j, hresult⟩ |>.1
  · intro hanchor
    exact (checkedOrientation_success_iff_denominators p S anchor v).mpr
      ⟨hanchor, inverseAnchorSum_pos_of_used_anchor_pos S anchor hanchor⟩

/-- Every successful output arm belongs to the supplied selected set. -/
theorem checkedOrientation_sampled_mem
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (anchor : Fin p.K → ℝ) (v : ContinuousControlSlice.Scalar)
    (j : Fin p.K)
    (hresult : checkedOrientation p S anchor v = Output.sampled j) :
    j ∈ S.1 := by
  have hanchor : ∀ i ∈ S.1, 0 < anchor i := by
    by_contra hnot
    have hfailure := (checkedOrientation_eq_failure_iff p S anchor v).2 hnot
    rw [hfailure] at hresult
    cases hresult
  rw [checkedOrientation_eq_sample_of_used_anchor_pos p S anchor v hanchor] at hresult
  have hj := Output.sampled.inj hresult
  have hmem :
      S.1.orderEmbOfFin rfl
        (ContinuousCategorical.sample
          (Finset.card_pos.mpr
            (OrientedAssignmentLaw.sampled_set_nonempty p.two_le_m S))
          (usedOrientationMasses S anchor hanchor)
          (usedOrientationMasses_sum_eq_one S anchor hanchor) v) ∈ S.1 :=
    S.1.orderEmbOfFin_mem rfl _
  rw [hj] at hmem
  exact hmem

private theorem checkedOrientation_sampled_iff_of_used_anchor_pos
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (anchor : Fin p.K → ℝ) (v : ContinuousControlSlice.Scalar)
    (hanchor : ∀ i ∈ S.1, 0 < anchor i)
    (j : Fin p.K) (hj : j ∈ S.1) :
    checkedOrientation p S anchor v = Output.sampled j ↔
      ContinuousCategorical.lower (rawOrderedMasses S anchor)
          (OrientedAssignmentLaw.orientationRank S ⟨j, hj⟩) ≤ v.1 ∧
        v.1 < ContinuousCategorical.upper (rawOrderedMasses S anchor)
          (OrientedAssignmentLaw.orientationRank S ⟨j, hj⟩) := by
  let rank := OrientedAssignmentLaw.orientationRank S ⟨j, hj⟩
  let masses := usedOrientationMasses S anchor hanchor
  let sample := ContinuousCategorical.sample
    (Finset.card_pos.mpr (OrientedAssignmentLaw.sampled_set_nonempty p.two_le_m S))
    masses (usedOrientationMasses_sum_eq_one S anchor hanchor) v
  have hformula :=
    checkedOrientation_eq_sample_of_used_anchor_pos p S anchor v hanchor
  have hmass : masses = rawOrderedMasses S anchor := by
    exact usedOrientationMasses_eq_rawOrderedMasses S anchor hanchor
  have hlower :
      ContinuousCategorical.lower masses rank =
        ContinuousCategorical.lower (rawOrderedMasses S anchor) rank := by
    rw [hmass]
  have hupper :
      ContinuousCategorical.upper masses rank =
        ContinuousCategorical.upper (rawOrderedMasses S anchor) rank := by
    rw [hmass]
  have hcat : sample = rank ↔
      ContinuousCategorical.lower (rawOrderedMasses S anchor) rank ≤ v.1 ∧
        v.1 < ContinuousCategorical.upper (rawOrderedMasses S anchor) rank := by
    have h := ContinuousCategorical.sample_eq_iff
      (Finset.card_pos.mpr (OrientedAssignmentLaw.sampled_set_nonempty p.two_le_m S))
      (fun r => (usedOrientationMasses_pos S anchor hanchor r).le)
      (usedOrientationMasses_sum_eq_one S anchor hanchor) v rank
    change sample = rank ↔
      ContinuousCategorical.lower masses rank ≤ v.1 ∧
        v.1 < ContinuousCategorical.upper masses rank at h
    constructor
    · intro hsample
      rcases h.mp hsample with ⟨hlo, hhi⟩
      constructor
      · rw [hlower] at hlo
        exact hlo
      · rw [hupper] at hhi
        exact hhi
    · rintro ⟨hlo, hhi⟩
      apply h.mpr
      constructor
      · rw [hlower]
        exact hlo
      · rw [hupper]
        exact hhi
  have harm : S.1.orderEmbOfFin rfl sample = j ↔ sample = rank := by
    let e : Fin S.1.card ≃o {i // i ∈ S.1} := S.1.orderIsoOfFin rfl
    constructor
    · intro hjarm
      have heq : e sample = ⟨j, hj⟩ := by
        apply Subtype.ext
        exact hjarm
      have hidx : sample = e.symm ⟨j, hj⟩ := by
        apply e.injective
        simpa using heq
      simpa [rank, OrientedAssignmentLaw.orientationRank] using hidx
    · intro hsample
      have heq : e sample = ⟨j, hj⟩ := by
        rw [hsample]
        change e (e.symm ⟨j, hj⟩) = _
        exact e.apply_symm_apply ⟨j, hj⟩
      change (e sample).1 = j
      exact congrArg Subtype.val heq
  rw [hformula]
  simp only [Output.sampled.injEq]
  change S.1.orderEmbOfFin rfl sample = j ↔ _
  exact harm.trans hcat

/-- The actual slow set after a successful fast-arm draw, transported to the
existing supported canonical `(m-1)`-set carrier. -/
@[expose] def slowSetAfter
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (j : Fin p.K) (hj : j ∈ S.1) :
    CanonicalOrientedSetLaw.SlowSet p.K p.m :=
  CanonicalAssignmentVector.slowCarrierEquiv p.two_le_m
    ⟨S.1.erase j, by
      have hcard : S.1.card = p.m := (Finset.mem_powersetCard.mp S.2).2
      rw [Finset.card_erase_add_one hj, hcard]⟩

@[simp] theorem slowSetAfter_val
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (j : Fin p.K) (hj : j ∈ S.1) :
    (slowSetAfter p S j hj).1 = S.1.erase j := rfl

theorem slowSetAfter_card
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (j : Fin p.K) (hj : j ∈ S.1) :
    (slowSetAfter p S j hj).1.card = p.m - 1 :=
  CanonicalAssignmentVector.slowSet_card_eq_sub_one p.two_le_m
    (slowSetAfter p S j hj)

/-- The accepted increasing follower enumeration of the actual erasure has
image exactly `S.erase j`. -/
theorem slowSetAfter_followerArm_image
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (j : Fin p.K) (hj : j ∈ S.1) :
    Finset.univ.image
        (CanonicalAssignmentVector.followerArm p.two_le_m (slowSetAfter p S j hj)) =
      S.1.erase j := by
  rw [CanonicalAssignmentVector.followerArm_image]
  rfl

theorem slowSetAfter_followerArm_strictMono
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (j : Fin p.K) (hj : j ∈ S.1) :
    StrictMono
      (CanonicalAssignmentVector.followerArm p.two_le_m (slowSetAfter p S j hj)) :=
  CanonicalAssignmentVector.followerArm_strictMono p.two_le_m
    (slowSetAfter p S j hj)

/-- Deleting the selected arm agrees with the existing oriented assignment's
slow-outcome carrier, then with the canonical sorted slow-set carrier. -/
theorem slowSetAfter_eq_existingSlowOutcome
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (j : Fin p.K) (hj : j ∈ S.1) :
    slowSetAfter p S j hj =
      CanonicalAssignmentVector.slowCarrierEquiv p.two_le_m
        (OrientedAssignmentLaw.slowOutcome ⟨(S, j), hj⟩) := by
  apply Subtype.ext
  rfl

/-- The checked raw operation agrees pointwise, for every scalar, with the
accepted global-positive-anchor orientation operation.  Global positivity is
used only in this comparison theorem. -/
theorem checkedOrientation_eq_orientationArm
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (anchor : Fin p.K → ℝ) (v : ContinuousControlSlice.Scalar)
    (hanchor : ∀ i, 0 < anchor i) :
    checkedOrientation p S anchor v =
      Output.sampled
        (OrientedAssignmentLaw.orientationArm p.two_le_m anchor hanchor S v) := by
  have hused : ∀ i ∈ S.1, 0 < anchor i := fun i _ => hanchor i
  rw [checkedOrientation_eq_sample_of_used_anchor_pos p S anchor v hused]
  congr 1

/-- In the same globally-positive comparison, the source slow set obtained by
sorting the checked output is exactly the existing oriented slow outcome. -/
theorem checkedOrientation_slowSet_eq_existing
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (anchor : Fin p.K → ℝ) (v : ContinuousControlSlice.Scalar)
    (hanchor : ∀ i, 0 < anchor i) :
    slowSetAfter p S
        (OrientedAssignmentLaw.orientationArm p.two_le_m anchor hanchor S v)
        (S.1.orderEmbOfFin_mem rfl _) =
      CanonicalAssignmentVector.slowCarrierEquiv p.two_le_m
        (OrientedAssignmentLaw.slowOutcome
          ⟨(S, OrientedAssignmentLaw.orientationArm p.two_le_m anchor hanchor S v),
            S.1.orderEmbOfFin_mem rfl _⟩) := by
  exact slowSetAfter_eq_existingSlowOutcome p S _ _

/-- The full assignment-vector adapter reads exactly coordinate `K+1`, the
original final scalar, for the already selected set `S`. -/
@[expose] def checkedOrientationFromAssignmentVector
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (anchor : Fin p.K → ℝ)
    (v : Fin (p.K + 1) → ContinuousControlSlice.Scalar) : Output p.K :=
  checkedOrientation p S anchor (v (Fin.last p.K))

@[simp] theorem checkedOrientationFromAssignmentVector_apply
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (anchor : Fin p.K → ℝ)
    (v : Fin (p.K + 1) → ContinuousControlSlice.Scalar) :
    checkedOrientationFromAssignmentVector p S anchor v =
      checkedOrientation p S anchor (v (Fin.last p.K)) := rfl

theorem checkedOrientationFromAssignmentVector_eq_of_last_eq
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (anchor : Fin p.K → ℝ)
    (v w : Fin (p.K + 1) → ContinuousControlSlice.Scalar)
    (hlast : v (Fin.last p.K) = w (Fin.last p.K)) :
    checkedOrientationFromAssignmentVector p S anchor v =
      checkedOrientationFromAssignmentVector p S anchor w := by
  simp [checkedOrientationFromAssignmentVector, hlast]

private def validAnchorDomain {p : ConstructorDimensions.Parameters}
    (S : PrefixSetSampler.SetCarrier p.K p.m) : Set (RawInput p) :=
  {z | ∀ i ∈ S.1, 0 < z.1 i}

private def rawInverseCDFLevel {p : ConstructorDimensions.Parameters}
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (j : Fin p.K) (hj : j ∈ S.1) : Set (RawInput p) :=
  {z | ContinuousCategorical.lower (rawOrderedMasses S z.1)
        (OrientedAssignmentLaw.orientationRank S ⟨j, hj⟩) ≤ z.2.1 ∧
      z.2.1 < ContinuousCategorical.upper (rawOrderedMasses S z.1)
        (OrientedAssignmentLaw.orientationRank S ⟨j, hj⟩)}

private theorem measurable_rawOrderedMasses
    {p : ConstructorDimensions.Parameters}
    (S : PrefixSetSampler.SetCarrier p.K p.m) (r : Fin S.1.card) :
    Measurable (fun z : RawInput p => rawOrderedMasses S z.1 r) := by
  have hcoord (i : Fin p.K) : Measurable (fun z : RawInput p => z.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have hdenom : Measurable
      (fun z : RawInput p =>
        FiniteOrientationDisintegration.inverseAnchorSum z.1 S.1) := by
    unfold FiniteOrientationDisintegration.inverseAnchorSum
    exact Finset.measurable_sum S.1 (fun i hi => measurable_const.div (hcoord i))
  unfold rawOrderedMasses
  exact (measurable_const.div (hcoord (S.1.orderEmbOfFin rfl r))).div hdenom

private theorem measurable_rawLower
    {p : ConstructorDimensions.Parameters}
    (S : PrefixSetSampler.SetCarrier p.K p.m) (r : Fin S.1.card) :
    Measurable (fun z : RawInput p =>
      ContinuousCategorical.lower (rawOrderedMasses S z.1) r) := by
  change Measurable (fun z : RawInput p =>
    ∑ q ∈ Finset.Iio r, rawOrderedMasses S z.1 q)
  exact Finset.measurable_sum (Finset.Iio r) (fun q hq =>
    measurable_rawOrderedMasses S q)

private theorem measurable_rawUpper
    {p : ConstructorDimensions.Parameters}
    (S : PrefixSetSampler.SetCarrier p.K p.m) (r : Fin S.1.card) :
    Measurable (fun z : RawInput p =>
      ContinuousCategorical.upper (rawOrderedMasses S z.1) r) := by
  change Measurable (fun z : RawInput p =>
    ∑ q ∈ Finset.Iic r, rawOrderedMasses S z.1 q)
  exact Finset.measurable_sum (Finset.Iic r) (fun q hq =>
    measurable_rawOrderedMasses S q)

private theorem measurable_validAnchorDomain
    {p : ConstructorDimensions.Parameters}
    (S : PrefixSetSampler.SetCarrier p.K p.m) :
    MeasurableSet (validAnchorDomain S) := by
  rw [show validAnchorDomain S =
      ⋂ i : Fin p.K, {z : RawInput p | i ∈ S.1 → 0 < z.1 i} by
        ext z
        simp [validAnchorDomain]]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i ∈ S.1
  · simp only [hi, true_implies]
    exact measurableSet_lt measurable_const
      ((measurable_pi_apply i).comp measurable_fst)
  · simp [hi]

private theorem measurable_rawInverseCDFLevel
    {p : ConstructorDimensions.Parameters}
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (j : Fin p.K) (hj : j ∈ S.1) : MeasurableSet (rawInverseCDFLevel S j hj) := by
  let r := OrientedAssignmentLaw.orientationRank S ⟨j, hj⟩
  have hscalar : Measurable (fun z : RawInput p => z.2.1) :=
    measurable_subtype_coe.comp measurable_snd
  change MeasurableSet
    {z : RawInput p |
      ContinuousCategorical.lower (rawOrderedMasses S z.1) r ≤ z.2.1 ∧
        z.2.1 < ContinuousCategorical.upper (rawOrderedMasses S z.1) r}
  exact (measurableSet_le (measurable_rawLower S r) hscalar).inter
    (measurableSet_lt hscalar (measurable_rawUpper S r))

/-- Joint Borel measurability of the raw checked result in the real anchor
vector and the original `[0,1)` scalar.  The proof uses the finite inverse-CDF
level sets, so no measurability assumption is made on a normalized anchor
vector and the real input vector retains its Borel product sigma algebra. -/
theorem measurable_checkedOrientation
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m) :
    Measurable (fun z : RawInput p => checkedOrientation p S z.1 z.2) := by
  classical
  apply measurable_to_countable'
  intro y
  cases y with
  | failure =>
      have hpre :
          (fun z : RawInput p => checkedOrientation p S z.1 z.2) ⁻¹'
              {Output.failure} = (validAnchorDomain S)ᶜ := by
        ext z
        change checkedOrientation p S z.1 z.2 = Output.failure ↔
          ¬ ∀ i ∈ S.1, 0 < z.1 i
        exact checkedOrientation_eq_failure_iff p S z.1 z.2
      rw [hpre]
      exact (measurable_validAnchorDomain S).compl
  | sampled j =>
      by_cases hj : j ∈ S.1
      · let r := OrientedAssignmentLaw.orientationRank S ⟨j, hj⟩
        have hpre :
            (fun z : RawInput p => checkedOrientation p S z.1 z.2) ⁻¹'
                {Output.sampled j} =
              {z | z ∈ validAnchorDomain S ∧ z ∈ rawInverseCDFLevel S j hj} := by
          ext z
          simp only [Set.mem_preimage, Set.mem_singleton_iff,
            Set.mem_ofPred_eq]
          constructor
          · intro hresult
            have hanchor : ∀ i ∈ S.1, 0 < z.1 i := by
              by_contra hnot
              have hfailure :=
                (checkedOrientation_eq_failure_iff p S z.1 z.2).2 hnot
              rw [hfailure] at hresult
              cases hresult
            have hlevels :=
              (checkedOrientation_sampled_iff_of_used_anchor_pos
                p S z.1 z.2 hanchor j hj).mp hresult
            exact ⟨hanchor, hlevels⟩
          · rintro ⟨hanchor, hlevels⟩
            exact (checkedOrientation_sampled_iff_of_used_anchor_pos
              p S z.1 z.2 hanchor j hj).mpr hlevels
        rw [hpre]
        exact (measurable_validAnchorDomain S).inter
          (measurable_rawInverseCDFLevel S j hj)
      · have hpre :
            (fun z : RawInput p => checkedOrientation p S z.1 z.2) ⁻¹'
              {Output.sampled j} = ∅ := by
          ext z
          simp only [Set.mem_preimage, Set.mem_singleton_iff,
            Set.mem_empty_iff_false, iff_false]
          intro hresult
          exact hj (checkedOrientation_sampled_mem p S z.1 z.2 j hresult)
        rw [hpre]
        exact MeasurableSet.empty

/-- The full-vector adapter remains jointly measurable and reads only the
last coordinate of the existing assignment vector. -/
theorem measurable_checkedOrientationFromAssignmentVector
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m) (anchor : Fin p.K → ℝ) :
    Measurable (fun v : Fin (p.K + 1) → ContinuousControlSlice.Scalar =>
      checkedOrientationFromAssignmentVector p S anchor v) := by
  unfold checkedOrientationFromAssignmentVector
  exact (measurable_checkedOrientation p S).comp
    (measurable_const.prodMk (measurable_pi_apply (Fin.last p.K)))

/-- The original final coordinate keeps its product-uniform scalar law under
the existing entire assignment-vector law. -/
theorem measurePreserving_assignmentLastCoordinate (K : ℕ) :
    MeasurePreserving
      (fun v : Fin (K + 1) → ContinuousControlSlice.Scalar => v (Fin.last K))
      (ContinuousControlSlice.assignmentLaw K) ContinuousControlSlice.scalarLaw := by
  change MeasurePreserving
    (fun v : Fin (K + 1) → ContinuousControlSlice.Scalar => v (Fin.last K))
    (Measure.pi (fun _ : Fin (K + 1) => ContinuousControlSlice.scalarLaw))
    ContinuousControlSlice.scalarLaw
  exact measurePreserving_eval
    (fun _ : Fin (K + 1) => ContinuousControlSlice.scalarLaw) (Fin.last K)

theorem map_assignmentLastCoordinate (K : ℕ) :
    (ContinuousControlSlice.assignmentLaw K).map
      (fun v : Fin (K + 1) → ContinuousControlSlice.Scalar => v (Fin.last K)) =
        ContinuousControlSlice.scalarLaw :=
  (measurePreserving_assignmentLastCoordinate K).map_eq

/-- Pointwise comparison with the accepted orientation arm, including the
accepted half-open scalar atom law. -/
theorem scalarLaw_checkedOrientation_atom
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (j : Fin p.K) (hj : j ∈ S.1) :
    ContinuousControlSlice.scalarLaw
      (checkedOrientation p S anchor ⁻¹' {Output.sampled j}) =
        ENNReal.ofReal
          (OrientedAssignmentLaw.orientationMasses p.two_le_m anchor hanchor S
            (OrientedAssignmentLaw.orientationRank S ⟨j, hj⟩)) := by
  have hpre :
      checkedOrientation p S anchor ⁻¹' {Output.sampled j} =
        OrientedAssignmentLaw.orientationArm p.two_le_m anchor hanchor S ⁻¹' {j} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [checkedOrientation_eq_orientationArm p S anchor v hanchor]
    simp only [Output.sampled.injEq]
  have hpre' :
      OrientedAssignmentLaw.orientationArm p.two_le_m anchor hanchor S ⁻¹' {j} =
        OrientedAssignmentLaw.orientationScalarFibre p.two_le_m anchor hanchor S
          (OrientedAssignmentLaw.orientationRank S ⟨j, hj⟩) := by
    ext v
    exact (OrientedAssignmentLaw.orientationArm_eq_iff p.two_le_m anchor hanchor S
      v ⟨j, hj⟩)
  rw [hpre, hpre']
  exact OrientedAssignmentLaw.scalarLaw_orientationScalarFibre p.two_le_m
    anchor hanchor S (OrientedAssignmentLaw.orientationRank S ⟨j, hj⟩)

/-- Under the actual whole-vector product law, a successful orientation atom
has the same mass as the existing scalar orientation draw.  This transports
only the local final-coordinate operation; it makes no claim about a full
assignment-vector conditional law. -/
theorem assignmentLaw_checkedOrientation_atom
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (j : Fin p.K) (hj : j ∈ S.1) :
    ContinuousControlSlice.assignmentLaw p.K
      (checkedOrientationFromAssignmentVector p S anchor ⁻¹'
        {Output.sampled j}) =
      ENNReal.ofReal
        (OrientedAssignmentLaw.orientationMasses p.two_le_m anchor hanchor S
          (OrientedAssignmentLaw.orientationRank S ⟨j, hj⟩)) := by
  have hfixed : Measurable (fun v : ContinuousControlSlice.Scalar =>
      checkedOrientation p S anchor v) := by
    exact (measurable_checkedOrientation p S).comp
      (measurable_const.prodMk measurable_id)
  have hset : MeasurableSet
      (checkedOrientation p S anchor ⁻¹' {Output.sampled j}) :=
    hfixed (measurableSet_singleton (Output.sampled j))
  have hpre :
      checkedOrientationFromAssignmentVector p S anchor ⁻¹'
          {Output.sampled j} =
        (fun v : Fin (p.K + 1) → ContinuousControlSlice.Scalar =>
          v (Fin.last p.K)) ⁻¹'
            (checkedOrientation p S anchor ⁻¹' {Output.sampled j}) := by
    ext v
    rfl
  rw [hpre,
    (measurePreserving_assignmentLastCoordinate p.K).measure_preimage
      hset.nullMeasurableSet]
  exact scalarLaw_checkedOrientation_atom p S anchor hanchor j hj

end Bandits.Support.CheckedAssignmentOrientation

end
