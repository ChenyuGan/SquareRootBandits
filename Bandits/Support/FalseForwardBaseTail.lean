/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CompletePublicTable
public import Bandits.Support.FalseRowSliceFactorization
public import Bandits.Support.ForwardPrefixRareTail
public import Bandits.Support.ForwardPrefixSlice
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Base-measurable false-forward rare tail on the published output

For one fixed family of eligible lists, this module allows each list to depend
measurably on the shared ID array, every continuous learning/control row, the
true forward row, and private randomness. The family receives no false-forward
bits. Its section at a fixed base is the accepted fixed-context eligible
family. The false-row law is transported from the accepted full-family
rare-tail estimate, then integrated over the literal factorization of the same
`PublishedOutput`.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:298-344,352-375`
and `sources/zip4/manuscript/07_public_setup.tex:11-25`.
This is probability assembly only. It supplies no physical eligibility
producer, private-history result, finite-context union, or source closure.
-/

public section

open MeasureTheory ProbabilityTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ForwardPrefixSlice
open Bandits.Support.FalseRowSliceFactorization
open scoped BigOperators

namespace Bandits.Support.FalseForwardBaseTail

/-- A labelwise eligible-list family which sees the entire actual base tuple
and private randomness, but no false-forward coordinate. -/
abbrev BaseMeasurableEligibleFamily (p : ConstructorDimensions.Parameters)
    (s : Fin (BootstrapDimensions.n_boot p)) (Ω : Type*) [MeasurableSpace Ω] :=
  SliceLabel p → EligibleListFunction p s (FalseFactorBase p × Ω)

/-- Restrict one jointly measurable eligible-list function to a fixed actual
base tuple. Its block-subset property and private measurability are inherited
from the supplied `EligibleListFunction`. -/
@[expose] noncomputable def baseSectionEligibleList
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω]
    (E : BaseMeasurableEligibleFamily p s Ω) (b : FalseFactorBase p)
    (label : SliceLabel p) : EligibleListFunction p s Ω where
  choose := fun ω => (E label).choose (b, ω)
  choose_subset := fun ω => (E label).choose_subset (b, ω)
  measurable_choose := (E label).measurable_choose.comp
    (measurable_const.prodMk measurable_id)

/-- The actual full-time false-forward slice from the factorized published
output, retaining its original row and ID labels. -/
@[expose] def factorFalseForwardSlice
    (p : ConstructorDimensions.Parameters) (J : Fin (M p))
    (label : SliceLabel p) (hfalse : label.1 ≠ J)
    (z : FalseFactorOutput p J) : ForwardSlice p :=
  fun t => z.2 ⟨label.1, hfalse⟩ label.2 t

/-- The joint event on a factor tuple and private outcome for one false
forward slice. -/
@[expose] def factorFalseForwardPassSet
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p))
    (label : SliceLabel p) (hfalse : label.1 ≠ J) :
    Set (FalseFactorOutput p J × Ω) :=
  {y | privatePrefixPasses
    (baseSectionEligibleList E y.1.1 label) y.2
    (factorFalseForwardSlice p J label hfalse y.1)}

/-- Joint measurability of the private passing event in all base coordinates,
the selected false-forward slice, and private randomness. -/
theorem measurableSet_factorFalseForwardPassSet
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p))
    (label : SliceLabel p) (hfalse : label.1 ≠ J) :
    MeasurableSet (factorFalseForwardPassSet E J label hfalse) := by
  classical
  let choosePair : FalseFactorOutput p J × Ω → FalseFactorBase p × Ω :=
    fun y => (y.1.1, y.2)
  let slice : FalseFactorOutput p J × Ω → ForwardSlice p :=
    fun y => factorFalseForwardSlice p J label hfalse y.1
  let test : Finset (Fin p.T) × ForwardSlice p → Bool := fun c =>
    decide (prefixPasses c.1.sort c.2 (q_dec p))
  have hchoosePair : Measurable choosePair :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hchoose : Measurable (fun y => (E label).choose (choosePair y)) :=
    (E label).measurable_choose.comp hchoosePair
  have hslice : Measurable slice := by
    apply measurable_pi_iff.mpr
    intro t
    exact (measurable_pi_apply t).comp
      ((measurable_pi_apply label.2).comp
        ((measurable_pi_apply (⟨label.1, hfalse⟩ : FalseRow p J)).comp
          (measurable_snd.comp measurable_fst)))
  have hpair : Measurable (fun y => ((E label).choose (choosePair y), slice y)) :=
    hchoose.prodMk hslice
  have htest : Measurable test := measurable_of_finite test
  have hset : factorFalseForwardPassSet E J label hfalse =
      (test ∘ fun y => ((E label).choose (choosePair y), slice y)) ⁻¹' {true} := by
    ext y
    simp [factorFalseForwardPassSet, test, choosePair, slice,
      baseSectionEligibleList, privatePrefixPasses,
      chronologicalEligibleTimes, Function.comp_def]
  rw [hset]
  exact (htest.comp hpair) (measurableSet_singleton true)

/-- The private passing integral for one factor-space false slice. This is the
literal indicator integral in the source's private probability space. -/
@[expose] noncomputable def factorFalseForwardPassingProbability
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p))
    (label : SliceLabel p) (hfalse : label.1 ≠ J)
    (z : FalseFactorOutput p J) : ℝ :=
  ∫ ω, (factorFalseForwardPassSet E J label hfalse).indicator
    (fun _ => (1 : ℝ)) (z, ω) ∂P

/-- At every fixed factor point, the joint event section is exactly the
accepted private passing probability for the corresponding eligible-list
section and actual false-forward slice. -/
theorem factorFalseForwardPassingProbability_eq_integratedPrivatePassing
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p))
    (label : SliceLabel p) (hfalse : label.1 ≠ J)
    (z : FalseFactorOutput p J) :
    factorFalseForwardPassingProbability P E J label hfalse z =
      integratedPrivatePassing P (baseSectionEligibleList E z.1 label)
        (factorFalseForwardSlice p J label hfalse z) := by
  classical
  rw [factorFalseForwardPassingProbability, integratedPrivatePassing]
  change (∫ ω, (if privatePrefixPasses
        (baseSectionEligibleList E z.1 label) ω
        (factorFalseForwardSlice p J label hfalse z) then (1 : ℝ) else 0) ∂P) = _
  rfl

/-- Every factor-space passing probability is a genuine probability. -/
theorem factorFalseForwardPassingProbability_mem_unitInterval
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p))
    (label : SliceLabel p) (hfalse : label.1 ≠ J)
    (z : FalseFactorOutput p J) :
    factorFalseForwardPassingProbability P E J label hfalse z ∈ Set.Icc (0 : ℝ) 1 := by
  rw [factorFalseForwardPassingProbability_eq_integratedPrivatePassing]
  exact ⟨integratedPrivatePassing_nonneg P _ _, integratedPrivatePassing_le_one P _ _⟩

/-- The literal inverse-alphabet sum of private false-prefix passing
probabilities on the actual false-row factor. The true row contributes zero. -/
@[expose] noncomputable def factorFalseForwardStatistic
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p))
    (z : FalseFactorOutput p J) : ℝ :=
  (1 / (A_id p : ℝ)) *
    ∑ v : Fin (M p), ∑ u : Fin (A_id p),
      if hfalse : v ≠ J then
        factorFalseForwardPassingProbability P E J (v, u) hfalse z
      else 0

/-- The fixed-base version of the same statistic, expressed using the
false-forward rows alone. -/
@[expose] noncomputable def fixedBaseFalseForwardStatistic
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p))
    (b : FalseFactorBase p) (rows : FalseForwardRows p J) : ℝ :=
  (1 / (A_id p : ℝ)) *
    ∑ v : Fin (M p), ∑ u : Fin (A_id p),
      if hfalse : v ≠ J then
        integratedPrivatePassing P (baseSectionEligibleList E b (v, u))
          (fun t => rows ⟨v, hfalse⟩ u t)
      else 0

/-- Exact section equality: fixing the complete base tuple recovers the
fixed-base false-row statistic with no change of coordinates or law. -/
theorem factorFalseForwardStatistic_section_eq_fixedBase
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p))
    (b : FalseFactorBase p) (rows : FalseForwardRows p J) :
    factorFalseForwardStatistic P E J (b, rows) =
      fixedBaseFalseForwardStatistic P E J b rows := by
  unfold factorFalseForwardStatistic fixedBaseFalseForwardStatistic
  congr 1

/-- Measurability of one integrated private passing probability as a function
of the complete base and false-row tuple. -/
theorem measurable_factorFalseForwardPassingProbability
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p))
    (label : SliceLabel p) (hfalse : label.1 ≠ J) :
    Measurable (factorFalseForwardPassingProbability P E J label hfalse) := by
  have hindicator : Measurable
      ((factorFalseForwardPassSet E J label hfalse).indicator
        (fun _ => (1 : ℝ))) :=
    measurable_const.indicator (measurableSet_factorFalseForwardPassSet E J label hfalse)
  exact hindicator.stronglyMeasurable.integral_prod_right'.measurable

/-- Joint measurability of the assembled fixed-family statistic on the
factorized published output. -/
theorem measurable_factorFalseForwardStatistic
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p)) :
    Measurable (factorFalseForwardStatistic P E J) := by
  have hterm (v : Fin (M p)) (u : Fin (A_id p)) :
      Measurable (fun z : FalseFactorOutput p J =>
        if hfalse : v ≠ J then
          factorFalseForwardPassingProbability P E J (v, u) hfalse z
        else 0) := by
    by_cases hfalse : v ≠ J
    · simpa [hfalse] using
        measurable_factorFalseForwardPassingProbability P E J (v, u) hfalse
    · simp [hfalse]
  have hsum (v : Fin (M p)) :
      Measurable (fun z : FalseFactorOutput p J =>
        ∑ u : Fin (A_id p),
          if hfalse : v ≠ J then
            factorFalseForwardPassingProbability P E J (v, u) hfalse z
          else 0) := by
    apply Finset.measurable_sum Finset.univ
    intro u hu
    exact hterm v u
  have htotal : Measurable (fun z : FalseFactorOutput p J =>
      ∑ v : Fin (M p), ∑ u : Fin (A_id p),
        if hfalse : v ≠ J then
          factorFalseForwardPassingProbability P E J (v, u) hfalse z
        else 0) := by
    apply Finset.measurable_sum Finset.univ
    intro v hv
    exact hsum v
  unfold factorFalseForwardStatistic
  exact measurable_const.mul htotal

/-- Each summand is in `[0,1]`, so the inverse-alphabet statistic is bounded
by the number of complete row labels. This finite bound also covers the
empty false-row family when `M = 1`. -/
theorem factorFalseForwardStatistic_mem_unitInterval_M
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p))
    (z : FalseFactorOutput p J) :
    factorFalseForwardStatistic P E J z ∈ Set.Icc (0 : ℝ) (M p : ℝ) := by
  have hterm (v : Fin (M p)) (u : Fin (A_id p)) :
      0 ≤ (if hfalse : v ≠ J then
        factorFalseForwardPassingProbability P E J (v, u) hfalse z else 0) ∧
      (if hfalse : v ≠ J then
        factorFalseForwardPassingProbability P E J (v, u) hfalse z else 0) ≤ 1 := by
    by_cases hfalse : v ≠ J
    · simpa [hfalse] using
        factorFalseForwardPassingProbability_mem_unitInterval P E J (v, u) hfalse z
    · simp [hfalse]
  have hsum_nonneg : 0 ≤ ∑ v : Fin (M p), ∑ u : Fin (A_id p),
      if hfalse : v ≠ J then
        factorFalseForwardPassingProbability P E J (v, u) hfalse z else 0 :=
    Finset.sum_nonneg fun v hv => Finset.sum_nonneg fun u hu => (hterm v u).1
  have hsum_le : (∑ v : Fin (M p), ∑ u : Fin (A_id p),
      if hfalse : v ≠ J then
        factorFalseForwardPassingProbability P E J (v, u) hfalse z else 0) ≤
      (M p : ℝ) * (A_id p : ℝ) := by
    calc
      _ ≤ ∑ v : Fin (M p), ∑ u : Fin (A_id p), (1 : ℝ) :=
        Finset.sum_le_sum fun v hv => Finset.sum_le_sum fun u hu => (hterm v u).2
      _ = (M p : ℝ) * (A_id p : ℝ) := by simp
  have hApos : 0 < (A_id p : ℝ) := Nat.cast_pos.mpr (A_id_pos p)
  constructor
  · unfold factorFalseForwardStatistic
    exact mul_nonneg (by positivity) hsum_nonneg
  · unfold factorFalseForwardStatistic
    calc
      (1 / (A_id p : ℝ)) *
          (∑ v : Fin (M p), ∑ u : Fin (A_id p),
            if hfalse : v ≠ J then
              factorFalseForwardPassingProbability P E J (v, u) hfalse z else 0) ≤
          (1 / (A_id p : ℝ)) * ((M p : ℝ) * (A_id p : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = (M p : ℝ) := by
        field_simp [ne_of_gt hApos]

/-- The factor-space bad event is exactly the statistic exceeding the source
local threshold. -/
@[expose] noncomputable def factorFalseForwardBadSet
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p)) :
    Set (FalseFactorOutput p J) :=
  {z | factorFalseForwardStatistic P E J z >
    1 / ((B_boot p : ℝ) * (n_boot p : ℝ))}

/-- Measurability of the factor-space bad event. -/
theorem measurableSet_factorFalseForwardBadSet
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p)) :
    MeasurableSet (factorFalseForwardBadSet P E J) := by
  change MeasurableSet ((factorFalseForwardStatistic P E J) ⁻¹'
    Set.Ioi (1 / ((B_boot p : ℝ) * (n_boot p : ℝ))))
  exact measurable_factorFalseForwardStatistic P E J measurableSet_Ioi

/-- The bad section at one complete base tuple. -/
@[expose] noncomputable def fixedBaseFalseForwardBadSet
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p))
    (b : FalseFactorBase p) : Set (FalseForwardRows p J) :=
  {rows | fixedBaseFalseForwardStatistic P E J b rows >
    1 / ((B_boot p : ℝ) * (n_boot p : ℝ))}

/-- The section equality identifies every fixed-base bad section with the
literal false-row statistic under the original false-row coordinate. -/
theorem factorFalseForwardBadSet_section_iff
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p))
    (b : FalseFactorBase p) (rows : FalseForwardRows p J) :
    (b, rows) ∈ factorFalseForwardBadSet P E J ↔
      rows ∈ fixedBaseFalseForwardBadSet P E J b := by
  change factorFalseForwardStatistic P E J (b, rows) >
      1 / ((B_boot p : ℝ) * (n_boot p : ℝ)) ↔
    fixedBaseFalseForwardStatistic P E J b rows >
      1 / ((B_boot p : ℝ) * (n_boot p : ℝ))
  rw [factorFalseForwardStatistic_section_eq_fixedBase]

/-- Every fixed-base bad section is measurable, as a section of the joint
factor-space event. -/
theorem measurableSet_fixedBaseFalseForwardBadSet
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p))
    (b : FalseFactorBase p) :
    MeasurableSet (fixedBaseFalseForwardBadSet P E J b) := by
  change MeasurableSet ((fun rows : FalseForwardRows p J => (b, rows)) ⁻¹'
    factorFalseForwardBadSet P E J)
  exact (measurable_const.prodMk measurable_id)
    (measurableSet_factorFalseForwardBadSet P E J)

/-- The exact full-family law splits into the true row and all false rows. -/
theorem measurePreserving_splitRowsAtJEquiv
    (p : ConstructorDimensions.Parameters) (J : Fin (M p)) :
    MeasurePreserving (splitRowsAtJEquiv p J) (forwardFamilyMeasure p)
      ((forwardRowMeasure p).prod (falseForwardRowsMeasure p J)) := by
  classical
  let _ : Fintype (TrueRow p J) := Subtype.fintype (fun v : Fin (M p) => v = J)
  let _ : Fintype (FalseRow p J) := Subtype.fintype (fun v : Fin (M p) => v ≠ J)
  let splitPi := measurePreserving_piEquivPiSubtypeProd
    (α := fun _ : Fin (M p) => ForwardRow p)
    (μ := fun _ : Fin (M p) => forwardRowMeasure p) (fun v => v = J)
  have hTrue : MeasurePreserving (trueRowEquiv p J)
      (Measure.pi (fun _ : TrueRow p J => forwardRowMeasure p))
      (forwardRowMeasure p) := by
    change MeasurePreserving (fun f : TrueRow p J → ForwardRow p =>
      f (⟨J, rfl⟩ : TrueRow p J)) _ _
    exact measurePreserving_eval (fun _ : TrueRow p J => forwardRowMeasure p)
      (⟨J, rfl⟩ : TrueRow p J)
  have h := (hTrue.prod (MeasurePreserving.id
      (Measure.pi (fun _ : FalseRow p J => forwardRowMeasure p)))).comp splitPi
  change MeasurePreserving
    ((MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : Fin (M p) => ForwardRow p) (fun v => v = J)).trans
      ((trueRowEquiv p J).prodCongr (MeasurableEquiv.refl _)))
    (forwardFamilyMeasure p)
    ((forwardRowMeasure p).prod (falseForwardRowsMeasure p J))
  exact h

/-- The false-row projection of a complete forward family, using the same
row labels and excluding only its actual true index. -/
@[expose] def falseRowsOfForwardFamily
    (p : ConstructorDimensions.Parameters) (J : Fin (M p))
    (x : ForwardFamily p) : FalseForwardRows p J :=
  fun v => x v.1

/-- The fixed-base rare-tail estimate under the actual false-row law.
Transport to the accepted complete-family law adds its true row; that
coordinate contributes zero to the statistic. The hypothesis is precisely
the accepted full-family result for this section, not a false-row section
bound. -/
private theorem fixedBaseFalseForwardBadSet_probability_le
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p))
    (b : FalseFactorBase p)
    (Ebase : SliceLabel p → EligibleListFunction p s Ω)
    (hEbase : Ebase = fun label => baseSectionEligibleList E b label)
    (hrare :
      MeasurableSet (ForwardPrefixRareTail.falseForwardRareTailBadSet P Ebase J) ∧
      (∀ x : ForwardFamily p,
        x ∈ ForwardPrefixRareTail.falseForwardRareTailBadSet P Ebase J ↔
          (1 / (A_id p : ℝ)) *
            (∑ v : Fin (M p), ∑ u : Fin (A_id p),
              if v ≠ J then integratedPrivatePassing P (Ebase (v, u))
                (forwardSliceAt p (v, u) x) else 0) >
            1 / ((B_boot p : ℝ) * (n_boot p : ℝ))) ∧
      (forwardFamilyMeasure p).real
        (ForwardPrefixRareTail.falseForwardRareTailBadSet P Ebase J) ≤
        Real.exp (-(5 / 2 : ℝ) *
          ((B_boot p : ℝ) + (b_N p : ℝ)))) :
    (falseForwardRowsMeasure p J).real (fixedBaseFalseForwardBadSet P E J b) ≤
      Real.exp (-(5 / 2 : ℝ) *
        ((B_boot p : ℝ) + (b_N p : ℝ))) := by
  let bad := ForwardPrefixRareTail.falseForwardRareTailBadSet P Ebase J
  have hsplit := measurePreserving_splitRowsAtJEquiv p J
  have hpre : (splitRowsAtJEquiv p J).symm ⁻¹' bad =
      Prod.snd ⁻¹' fixedBaseFalseForwardBadSet P E J b := by
    ext z
    rcases z with ⟨trueRow, rows⟩
    have hmem := hrare.2.1 ((splitRowsAtJEquiv p J).symm (trueRow, rows))
    have hfalseRows :
        (fun v : FalseRow p J => (splitRowsAtJEquiv p J).symm (trueRow, rows) v.1) = rows := by
      funext v
      change ((MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : Fin (M p) => ForwardRow p) (fun q => q = J)).symm
          ((trueRowEquiv p J).symm trueRow, rows)) v.1 = rows v
      simp [v.property, MeasurableEquiv.piEquivPiSubtypeProd]
    have hstat :
        (1 / (A_id p : ℝ)) *
          (∑ v : Fin (M p), ∑ u : Fin (A_id p),
            if hfalse : v ≠ J then
              integratedPrivatePassing P (Ebase (v, u))
                (forwardSliceAt p (v, u)
                  ((splitRowsAtJEquiv p J).symm (trueRow, rows))) else 0) =
        fixedBaseFalseForwardStatistic P E J b rows := by
      unfold fixedBaseFalseForwardStatistic
      congr 1
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro u hu
      by_cases hfalse : v ≠ J
      · simp only [dite_eq_left hfalse]
        have hElabel := congrFun hEbase (v, u)
        rw [hElabel]
        have hrow := congrFun hfalseRows ⟨v, hfalse⟩
        have hslice :
            forwardSliceAt p (v, u) ((splitRowsAtJEquiv p J).symm (trueRow, rows)) =
              (fun t => rows ⟨v, hfalse⟩ u t) := by
          funext t
          exact congrFun (congrArg (fun r : ForwardRow p => r u) hrow) t
        exact congrArg
          (integratedPrivatePassing P (baseSectionEligibleList E b (v, u))) hslice
      · simp [hfalse]
    change ((splitRowsAtJEquiv p J).symm (trueRow, rows) ∈ bad) ↔
      rows ∈ fixedBaseFalseForwardBadSet P E J b
    change _ ↔ fixedBaseFalseForwardStatistic P E J b rows >
      1 / ((B_boot p : ℝ) * (n_boot p : ℝ))
    rw [← hstat]
    exact hmem
  have hSymm := MeasurePreserving.symm (splitRowsAtJEquiv p J) hsplit
  have hmap := Measure.map_apply hSymm.measurable hrare.1
    (μ := (forwardRowMeasure p).prod (falseForwardRowsMeasure p J))
  rw [hSymm.map_eq] at hmap
  have hμsplit : (forwardFamilyMeasure p).real bad =
      ((forwardRowMeasure p).prod (falseForwardRowsMeasure p J)).real
        (Prod.snd ⁻¹' fixedBaseFalseForwardBadSet P E J b) := by
    calc
      (forwardFamilyMeasure p).real bad =
          ((forwardRowMeasure p).prod (falseForwardRowsMeasure p J)).real
            ((splitRowsAtJEquiv p J).symm ⁻¹' bad) :=
        congrArg ENNReal.toReal hmap
      _ = ((forwardRowMeasure p).prod (falseForwardRowsMeasure p J)).real
          (Prod.snd ⁻¹' fixedBaseFalseForwardBadSet P E J b) := by rw [hpre]
  have hprodmap :
      ((forwardRowMeasure p).prod (falseForwardRowsMeasure p J)).map Prod.snd =
        falseForwardRowsMeasure p J := measurePreserving_snd.map_eq
  have hsection_meas := measurableSet_fixedBaseFalseForwardBadSet P E J b
  have hrow_measure :
      ((forwardRowMeasure p).prod (falseForwardRowsMeasure p J)).real
        (Prod.snd ⁻¹' fixedBaseFalseForwardBadSet P E J b) =
      (falseForwardRowsMeasure p J).real
        (fixedBaseFalseForwardBadSet P E J b) := by
    have h := Measure.map_apply measurable_snd hsection_meas
      (μ := (forwardRowMeasure p).prod (falseForwardRowsMeasure p J))
    rw [hprodmap] at h
    exact congrArg ENNReal.toReal h.symm
  calc
    (falseForwardRowsMeasure p J).real (fixedBaseFalseForwardBadSet P E J b) =
        (forwardFamilyMeasure p).real bad := hrow_measure.symm.trans hμsplit.symm
    _ ≤ Real.exp (-(5 / 2 : ℝ) *
        ((B_boot p : ℝ) + (b_N p : ℝ))) := hrare.2.2

/-- The requested statistic on the same complete `PublishedOutput`: one
inverse-`A_id` sum of private passing probabilities, with each eligible list
evaluated at the complete true/base coordinates and each tested slice taken
from that output's actual false forward row. -/
@[expose] noncomputable def publishedFalseForwardStatistic
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p))
    (x : PublishedOutput p) : ℝ :=
  (1 / (A_id p : ℝ)) *
    ∑ v : Fin (M p), ∑ u : Fin (A_id p),
      if v ≠ J then
        integratedPrivatePassing P
          (baseSectionEligibleList E (falseRowFactorEquiv p J x).1 (v, u))
          (forwardSliceAt p (v, u) (completeRowsForward p x.2))
      else 0

/-- The literal same-output statistic agrees with its expression on the
accepted false-row factor coordinates. -/
theorem publishedFalseForwardStatistic_eq_factor
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p))
    (x : PublishedOutput p) :
    publishedFalseForwardStatistic P E J x =
      factorFalseForwardStatistic P E J (falseRowFactorEquiv p J x) := by
  unfold publishedFalseForwardStatistic factorFalseForwardStatistic
  congr 1

/-- The public bad event on one complete, unchanged published-output sample.
Only the fixed family `E` is quantified; there is no uniform event over all
eligible families. -/
@[expose] noncomputable def publishedFalseForwardBadSet
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p)) :
    Set (PublishedOutput p) :=
  {x | publishedFalseForwardStatistic P E J x >
    1 / ((B_boot p : ℝ) * (n_boot p : ℝ))}

/-- The public event is the exact preimage of the corresponding factor-space
event under the accepted measurable equivalence. -/
theorem publishedFalseForwardBadSet_eq_preimage
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p)) :
    publishedFalseForwardBadSet P E J =
      (falseRowFactorEquiv p J) ⁻¹' factorFalseForwardBadSet P E J := by
  ext x
  change publishedFalseForwardStatistic P E J x >
      1 / ((B_boot p : ℝ) * (n_boot p : ℝ)) ↔
    factorFalseForwardStatistic P E J (falseRowFactorEquiv p J x) >
      1 / ((B_boot p : ℝ) * (n_boot p : ℝ))
  rw [publishedFalseForwardStatistic_eq_factor]

/-- The public bad event is jointly measurable on the complete output. -/
theorem measurableSet_publishedFalseForwardBadSet
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p)) :
    MeasurableSet (publishedFalseForwardBadSet P E J) := by
  rw [publishedFalseForwardBadSet_eq_preimage]
  exact (falseRowFactorEquiv p J).measurable
    (measurableSet_factorFalseForwardBadSet P E J)

/-- The public false-forward event has the accepted exponential tail. The
outer integral is over the actual false-factor base law, and the inner event
uses the original false rows from `PublishedOutput`. The only conditional
input is the accepted full-family rare-tail package for each fixed base; the
false-row section estimate is derived inside this proof. -/
private theorem publishedFalseForwardBadSet_probability_le
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : BaseMeasurableEligibleFamily p s Ω) (J : Fin (M p))
    (hrareForBase : ∀ b : FalseFactorBase p,
      let Ebase : SliceLabel p → EligibleListFunction p s Ω :=
        fun label => baseSectionEligibleList E b label
      MeasurableSet (ForwardPrefixRareTail.falseForwardRareTailBadSet P Ebase J) ∧
      (∀ x : ForwardFamily p,
        x ∈ ForwardPrefixRareTail.falseForwardRareTailBadSet P Ebase J ↔
          (1 / (A_id p : ℝ)) *
            (∑ v : Fin (M p), ∑ u : Fin (A_id p),
              if v ≠ J then integratedPrivatePassing P (Ebase (v, u))
                (forwardSliceAt p (v, u) x) else 0) >
            1 / ((B_boot p : ℝ) * (n_boot p : ℝ))) ∧
      (forwardFamilyMeasure p).real
        (ForwardPrefixRareTail.falseForwardRareTailBadSet P Ebase J) ≤
        Real.exp (-(5 / 2 : ℝ) *
          ((B_boot p : ℝ) + (b_N p : ℝ)))) :
    (publishedOutputMeasure p).real (publishedFalseForwardBadSet P E J) ≤
      Real.exp (-(5 / 2 : ℝ) *
        ((B_boot p : ℝ) + (b_N p : ℝ))) := by
  let factorBad := factorFalseForwardBadSet P E J
  let indicator : FalseFactorOutput p J → ℝ :=
    factorBad.indicator (fun _ => (1 : ℝ))
  have hindicator : Measurable indicator :=
    measurable_const.indicator (measurableSet_factorFalseForwardBadSet P E J)
  have hbound : ∀ z, ‖indicator z‖ ≤ 1 := by
    intro z
    by_cases hz : z ∈ factorBad <;> simp [indicator, hz]
  have hFubini := integral_falseRowFactor_fubini p J indicator hindicator 1 hbound
  have hleft :
      (∫ x, indicator (falseRowFactorEquiv p J x) ∂publishedOutputMeasure p) =
        (publishedOutputMeasure p).real (publishedFalseForwardBadSet P E J) := by
    classical
    rw [← integral_indicator_one (measurableSet_publishedFalseForwardBadSet P E J)]
    apply integral_congr_ae
    filter_upwards [] with x
    change (if falseRowFactorEquiv p J x ∈ factorBad then (1 : ℝ) else 0) =
      (if x ∈ publishedFalseForwardBadSet P E J then (1 : ℝ) else 0)
    rw [publishedFalseForwardBadSet_eq_preimage]
    rfl
  rw [← hleft, hFubini]
  let inner : FalseFactorBase p → ℝ := fun b =>
    ∫ rows, indicator (b, rows) ∂falseForwardRowsMeasure p J
  have hinner_meas : Measurable inner := by
    exact hindicator.stronglyMeasurable.integral_prod_right'.measurable
  have hinner_eq (b : FalseFactorBase p) :
      inner b = (falseForwardRowsMeasure p J).real
        (fixedBaseFalseForwardBadSet P E J b) := by
    change (∫ rows, indicator (b, rows) ∂falseForwardRowsMeasure p J) = _
    calc
      (∫ rows, indicator (b, rows) ∂falseForwardRowsMeasure p J) =
          ∫ rows,
            (fixedBaseFalseForwardBadSet P E J b).indicator
              (fun _ => (1 : ℝ)) rows ∂falseForwardRowsMeasure p J := by
        apply integral_congr_ae
        filter_upwards [] with rows
        classical
        by_cases hr : rows ∈ fixedBaseFalseForwardBadSet P E J b
        · have hmem :=
            (factorFalseForwardBadSet_section_iff P E J b rows).2 hr
          simp [indicator, factorBad, hmem, hr]
        · have hmem : (b, rows) ∉ factorBad := by
            intro h
            exact hr ((factorFalseForwardBadSet_section_iff P E J b rows).1 h)
          simp [indicator, factorBad, hmem, hr]
      _ = (falseForwardRowsMeasure p J).real
          (fixedBaseFalseForwardBadSet P E J b) :=
        integral_indicator_one (measurableSet_fixedBaseFalseForwardBadSet P E J b)
  have hinner_bound (b : FalseFactorBase p) : 0 ≤ inner b ∧ inner b ≤ 1 := by
    rw [hinner_eq]
    exact ⟨by positivity, measureReal_le_one⟩
  have hinner_integrable : Integrable inner (falseFactorBaseMeasure p) :=
    Integrable.of_bound hinner_meas.aestronglyMeasurable 1
      (ae_of_all _ fun b => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hinner_bound b).1]
        exact (hinner_bound b).2)
  have htail (b : FalseFactorBase p) :
      inner b ≤ Real.exp (-(5 / 2 : ℝ) *
        ((B_boot p : ℝ) + (b_N p : ℝ))) := by
    rw [hinner_eq]
    let Ebase : SliceLabel p → EligibleListFunction p s Ω :=
      fun label => baseSectionEligibleList E b label
    exact fixedBaseFalseForwardBadSet_probability_le P E J b Ebase rfl
      (hrareForBase b)
  calc
    (∫ b, inner b ∂falseFactorBaseMeasure p) ≤
        ∫ _b, Real.exp (-(5 / 2 : ℝ) *
          ((B_boot p : ℝ) + (b_N p : ℝ))) ∂falseFactorBaseMeasure p :=
      integral_mono hinner_integrable (integrable_const _) htail
    _ = Real.exp (-(5 / 2 : ℝ) *
          ((B_boot p : ℝ) + (b_N p : ℝ))) := by simp

/-- The accepted universal cutoff also suffices after the fixed-family
base-measurable assembly. -/
theorem exists_universal_N0_publishedFalseForwardBadSet_probability_le
    :
    ∃ N₀ : ℕ, ∀ p : ConstructorDimensions.Parameters,
      N₀ ≤ N p → ∀ s : Fin (BootstrapDimensions.n_boot p),
      ∀ J : Fin (M p), ∀ {Ω : Type*} [MeasurableSpace Ω],
      ∀ (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ E : BaseMeasurableEligibleFamily p s Ω,
        MeasurableSet (publishedFalseForwardBadSet P E J) ∧
        (publishedOutputMeasure p).real (publishedFalseForwardBadSet P E J) ≤
          Real.exp (-(5 / 2 : ℝ) *
            ((B_boot p : ℝ) + (b_N p : ℝ))) := by
  obtain ⟨N₀, hN₀⟩ :=
    ForwardPrefixRareTail.exists_universal_N0_fixedContext_falseForwardRareTail
  refine ⟨N₀, ?_⟩
  intro p hN s J Ω hΩ P hP E
  have hrareForBase : ∀ b : FalseFactorBase p,
      let Ebase : SliceLabel p → EligibleListFunction p s Ω :=
        fun label => baseSectionEligibleList E b label
      MeasurableSet (ForwardPrefixRareTail.falseForwardRareTailBadSet P Ebase J) ∧
      (∀ x : ForwardFamily p,
        x ∈ ForwardPrefixRareTail.falseForwardRareTailBadSet P Ebase J ↔
          (1 / (A_id p : ℝ)) *
            (∑ v : Fin (M p), ∑ u : Fin (A_id p),
              if v ≠ J then integratedPrivatePassing P (Ebase (v, u))
                (forwardSliceAt p (v, u) x) else 0) >
            1 / ((B_boot p : ℝ) * (n_boot p : ℝ))) ∧
      (forwardFamilyMeasure p).real
        (ForwardPrefixRareTail.falseForwardRareTailBadSet P Ebase J) ≤
        Real.exp (-(5 / 2 : ℝ) *
          ((B_boot p : ℝ) + (b_N p : ℝ))) := by
    intro b
    exact hN₀ p hN s J P
      (fun label => baseSectionEligibleList E b label)
  exact ⟨measurableSet_publishedFalseForwardBadSet P E J,
    publishedFalseForwardBadSet_probability_le P E J hrareForBase⟩

end Bandits.Support.FalseForwardBaseTail
