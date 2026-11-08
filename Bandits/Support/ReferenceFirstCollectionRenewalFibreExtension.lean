/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# A source-indexed analytical renewal fibre extension

Sources: `sources/zip4/manuscript/06_interruptions.tex:399-422`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:176-215`.

At the actual first-collection renewal call, extend the unnormalized law of
the whole physical source and an analytical auxiliary array by the existing
assignment fibre kernel. The resulting full `K + 1` vector realizes the
auxiliary slow set at the same reconstructed parameter. Jointly with the
whole original source and every old auxiliary block coordinate, its law is
the full assignment cube law. The original source and whole auxiliary array
also retain their joint marginal on this extension.
The vector product law retains the old auxiliary block. The extra renewal
coordinate participates in the analytical sample and fibre selection.

The proof uses the source-indexed joint sample-fibre identity, including its
null and empty source cases. It integrates the actual varying-parameter
kernel on each finite sample fibre before summing the fibre measures.

The intended consumer is a subsequent chronological assignment coupling with
actual physical past and current-row reconstruction. No vector is swapped
into the original physical source here. Such a swap still needs parameter
and past locality and rollout provenance. Stored weights are the existing
reconstructed weights; no identification with manuscript `w_t`, logical
reset, residual process, history field, or overflow coupling is asserted.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Bandits.Support.ReferenceFirstCollectionRenewalFibreExtension

open ReferenceFirstCollectionRenewalAuxiliaryLaw

variable {p : ConstructorDimensions.Parameters}

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩
local instance outcomeMeasurableSpace : MeasurableSpace (Option (SlowSet p)) := ⊤
local instance outcomeDiscrete : DiscreteMeasurableSpace (Option (SlowSet p)) :=
  ⟨fun _ => trivial⟩

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

/-- The whole original renewal source and the whole auxiliary seed array. -/
abbrev RenewalBase :=
  RenewalCallSource rate rewards C_star C_h u t × AuxiliaryArray p

/-- The whole original renewal source and all old auxiliary block coordinates. -/
abbrev RenewalBlockBase :=
  RenewalCallSource rate rewards C_star C_h u t × (AuxiliaryCellIndex u t → Scalar)

/-- Literal unnormalized product law before adding a full assignment vector. -/
def renewalBaseLaw : Measure (RenewalBase rate rewards C_star C_h u t) :=
  (renewalSourceLaw rate rewards C_star C_h u t).prod
    (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)

/-- Literal product law of the retained source and old seed block. -/
def renewalBlockLaw : Measure (RenewalBlockBase rate rewards C_star C_h u t) :=
  (renewalSourceLaw rate rewards C_star C_h u t).prod
    (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellLaw u t)

instance renewalBaseLaw_finite :
    IsFiniteMeasure (renewalBaseLaw rate rewards C_star C_h u t) := by
  unfold renewalBaseLaw
  infer_instance

instance renewalBlockLaw_finite :
    IsFiniteMeasure (renewalBlockLaw rate rewards C_star C_h u t) := by
  unfold renewalBlockLaw
  infer_instance

/-- Markovness is inherited from the actual full-vector assignment kernel
and its measurable comap. It is not an additional conditional-law input. -/
instance renewalAssignmentFibreKernel_markov :
    ProbabilityTheory.IsMarkovKernel
      (renewalAssignmentFibreKernel rate rewards C_star C_h u t) := by
  unfold renewalAssignmentFibreKernel
  infer_instance

/-- The analytical extension is literally the measure-kernel composition
product. Neither factor is normalized by the renewal event mass. -/
def renewalLiftLaw : Measure
    (RenewalBase rate rewards C_star C_h u t × CheckedAssignmentSample.AssignmentVector p) :=
  Measure.compProd (renewalBaseLaw rate rewards C_star C_h u t)
    (renewalAssignmentFibreKernel rate rewards C_star C_h u t)

instance renewalLiftLaw_finite :
    IsFiniteMeasure (renewalLiftLaw rate rewards C_star C_h u t) := by
  unfold renewalLiftLaw
  infer_instance

/-- Retain the source and restrict the array to the original old block. -/
def renewalBlockProjection (w : RenewalBase rate rewards C_star C_h u t) :
    RenewalBlockBase rate rewards C_star C_h u t :=
  (w.1, ReferenceFirstCollectionAuxiliarySeeds.auxiliaryBlock u t w.2)

theorem measurable_renewalBlockProjection :
    Measurable (renewalBlockProjection rate rewards C_star C_h u t) :=
  measurable_fst.prodMk
    ((ReferenceFirstCollectionAuxiliarySeeds.measurable_auxiliaryBlock u t).comp
      measurable_snd)

/-- The block projection of the extension retains the new full vector too. -/
def renewalLiftBlockProjection
    (wv : RenewalBase rate rewards C_star C_h u t ×
      CheckedAssignmentSample.AssignmentVector p) :
    RenewalBlockBase rate rewards C_star C_h u t ×
      CheckedAssignmentSample.AssignmentVector p :=
  (renewalBlockProjection rate rewards C_star C_h u t wv.1, wv.2)

theorem measurable_renewalLiftBlockProjection :
    Measurable (renewalLiftBlockProjection rate rewards C_star C_h u t) :=
  ((measurable_renewalBlockProjection rate rewards C_star C_h u t).comp
    measurable_fst).prodMk measurable_snd

/-- Whole-source AND whole-array preservation on the analytical extension. -/
theorem renewalLiftLaw_map_fst :
    (renewalLiftLaw rate rewards C_star C_h u t).map Prod.fst =
      renewalBaseLaw rate rewards C_star C_h u t := by
  exact Measure.fst_compProd _ _

/-- The total mass is the original renewal event mass, including zero. -/
theorem renewalLiftLaw_univ :
    renewalLiftLaw rate rewards C_star C_h u t Set.univ =
      BootstrapPrivateRoundStreams.sourceInputLaw p
        (renewalCallEvent rate rewards C_star C_h u t) := by
  rw [renewalLiftLaw, Measure.compProd_apply_univ, renewalBaseLaw,
    ← Set.univ_prod_univ, Measure.prod_prod,
    measure_univ (μ := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p), mul_one,
    renewalSourceLaw_univ rate rewards C_star C_h u t]

/-- The sampler outcome of a candidate full vector at the original source's
actual reconstructed renewal parameter. -/
def renewalLiftOutcome
    (wv : RenewalBase rate rewards C_star C_h u t ×
      CheckedAssignmentSample.AssignmentVector p) : Option (SlowSet p) :=
  AssignmentParameterFibreKernel.successfulSlowSet p
    (renewalCallParameter rate rewards C_star C_h u t wv.1.1) wv.2

theorem measurable_renewalLiftOutcome :
    Measurable (renewalLiftOutcome rate rewards C_star C_h u t) :=
  (AssignmentParameterFibreKernel.measurable_successfulSlowSet_joint p).comp
    (((measurable_renewalCallParameter rate rewards C_star C_h u t).comp
      (measurable_fst.comp measurable_fst)).prodMk measurable_snd)

/-- Every kernel row uses a positive sample fibre. This row statement is
then integrated against the entire unnormalized original base measure. -/
theorem ae_renewalAssignmentFibreKernel_outcome
    (w : RenewalBase rate rewards C_star C_h u t) :
    ∀ᵐ v ∂renewalAssignmentFibreKernel rate rewards C_star C_h u t w,
      AssignmentParameterFibreKernel.successfulSlowSet p
        (renewalCallParameter rate rewards C_star C_h u t w.1) v =
          some (renewalAuxiliarySample rate rewards C_star C_h u t w.1 w.2) := by
  exact AssignmentParameterFibreKernel.ae_successfulSlowSet_eq_of_fibreMass_pos p
    (renewalCallParameter rate rewards C_star C_h u t w.1)
    (some (renewalAuxiliarySample rate rewards C_star C_h u t w.1 w.2))
    (renewal_sample_fibreMass_pos rate rewards C_star C_h u t w.1 w.2)

/-- The new vector realizes the actual auxiliary renewal set almost surely,
using precisely the same parameter, source, and old auxiliary array. -/
theorem ae_renewalLiftLaw_outcome :
    ∀ᵐ wv ∂renewalLiftLaw rate rewards C_star C_h u t,
      AssignmentParameterFibreKernel.successfulSlowSet p
        (renewalCallParameter rate rewards C_star C_h u t wv.1.1) wv.2 =
          some (renewalAuxiliarySample rate rewards C_star C_h u t wv.1.1 wv.1.2) := by
  have hsome : Measurable (fun wv : RenewalBase rate rewards C_star C_h u t ×
      CheckedAssignmentSample.AssignmentVector p =>
      some (renewalAuxiliarySample rate rewards C_star C_h u t wv.1.1 wv.1.2)) :=
    (measurable_of_countable (some : SlowSet p → Option (SlowSet p))).comp
      ((measurable_renewalAuxiliarySample rate rewards C_star C_h u t).comp
        measurable_fst)
  apply Measure.ae_compProd_of_ae_ae
    (measurableSet_eq_fun
      (measurable_renewalLiftOutcome rate rewards C_star C_h u t) hsome)
  exact Filter.Eventually.of_forall
    (ae_renewalAssignmentFibreKernel_outcome rate rewards C_star C_h u t)

/-- One finite outcome fibre of the actual auxiliary sample. -/
def renewalSampleFibre (U : SlowSet p) : Set (RenewalBase rate rewards C_star C_h u t) :=
  {w | renewalAuxiliarySample rate rewards C_star C_h u t w.1 w.2 = U}

theorem measurableSet_renewalSampleFibre (U : SlowSet p) :
    MeasurableSet (renewalSampleFibre rate rewards C_star C_h u t U) :=
  (measurable_renewalAuxiliarySample rate rewards C_star C_h u t)
    (measurableSet_singleton U)

/-- On each sample fibre, retaining the whole source and old block gives
the source-indexed PMF density. This is the admitted joint fibre identity,
extended from measurable cells to an equality of measures. -/
theorem renewalSampleFibre_map_block (U : SlowSet p) :
    ((renewalBaseLaw rate rewards C_star C_h u t).restrict
      (renewalSampleFibre rate rewards C_star C_h u t U)).map
        (renewalBlockProjection rate rewards C_star C_h u t) =
      (renewalBlockLaw rate rewards C_star C_h u t).withDensity
        (fun x => renewalSlowSetPMF rate rewards C_star C_h u t x.1 U) := by
  ext A hA
  rw [Measure.map_apply
    (measurable_renewalBlockProjection rate rewards C_star C_h u t) hA,
    Measure.restrict_apply
      ((measurable_renewalBlockProjection rate rewards C_star C_h u t) hA),
    withDensity_apply _ hA]
  exact renewalAuxiliarySample_joint_fibre rate rewards C_star C_h u t A hA U

/-- Arbitrary nonnegative Borel tests may depend jointly on the whole source
and all old seeds. No independence of those tests from the parameter is used. -/
theorem lintegral_renewalSampleFibre (U : SlowSet p)
    (f : RenewalBlockBase rate rewards C_star C_h u t → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ w in renewalSampleFibre rate rewards C_star C_h u t U,
        f (renewalBlockProjection rate rewards C_star C_h u t w)
        ∂renewalBaseLaw rate rewards C_star C_h u t =
      ∫⁻ x, renewalSlowSetPMF rate rewards C_star C_h u t x.1 U * f x
        ∂renewalBlockLaw rate rewards C_star C_h u t := by
  rw [← lintegral_map hf
    (measurable_renewalBlockProjection rate rewards C_star C_h u t),
    renewalSampleFibre_map_block rate rewards C_star C_h u t U]
  exact lintegral_withDensity_eq_lintegral_mul _
    ((measurable_renewalSlowSetPMF rate rewards C_star C_h u t U).comp measurable_fst) hf

/-- Fixed supported-outcome slice of the public joint fibre kernel.
Evaluation is Borel for every full-vector Borel set. -/
theorem measurable_fibreMeasure_some (U : SlowSet p)
    (C : Set (CheckedAssignmentSample.AssignmentVector p)) (hC : MeasurableSet C) :
    Measurable (fun theta : Theta p =>
      AssignmentParameterFibreKernel.fibreMeasure p theta (some U) C) := by
  change Measurable (fun theta : AssignmentParameterFibreKernel.Theta p =>
    AssignmentParameterFibreKernel.assignmentParameterFibreKernel p (theta, some U) C)
  exact (ProbabilityTheory.Kernel.measurable_coe
    (AssignmentParameterFibreKernel.assignmentParameterFibreKernel p) hC).comp
      measurable_prodMk_right

/-- Pull the fixed-outcome Borel evaluation back along the actual source
parameter. The source carrier and all continuous Borel structures persist. -/
theorem measurable_renewalFibreMeasure_apply (U : SlowSet p)
    (C : Set (CheckedAssignmentSample.AssignmentVector p)) (hC : MeasurableSet C) :
    Measurable (fun x : RenewalBlockBase rate rewards C_star C_h u t =>
      AssignmentParameterFibreKernel.fibreMeasure p
        (renewalCallParameter rate rewards C_star C_h u t x.1) (some U) C) := by
  have htheta : Measurable (fun x : RenewalBlockBase rate rewards C_star C_h u t =>
      renewalCallParameter rate rewards C_star C_h u t x.1) :=
    (measurable_renewalCallParameter rate rewards C_star C_h u t).comp
      (measurable_fst : Measurable (Prod.fst :
        RenewalBlockBase rate rewards C_star C_h u t →
          RenewalCallSource rate rewards C_star C_h u t))
  exact (measurable_fibreMeasure_some U C hC).comp htheta

/-- Summation over supported slow sets recovers the full continuous cube.
The omitted checked-failure outcome is proved to have mass zero at renewal. -/
theorem renewal_sum_pmf_mul_fibreMeasure
    (z : RenewalCallSource rate rewards C_star C_h u t)
    (C : Set (CheckedAssignmentSample.AssignmentVector p)) :
    (∑ U : SlowSet p, renewalSlowSetPMF rate rewards C_star C_h u t z U *
      AssignmentParameterFibreKernel.fibreMeasure p
        (renewalCallParameter rate rewards C_star C_h u t z) (some U) C) =
      ContinuousControlSlice.assignmentLaw p.K C := by
  classical
  have hnone := (renewal_parameter_fibreMass rate rewards C_star C_h u t z
    (slowSetEnumeration p ⟨0, slowSet_card_pos p⟩)).2
  have hsum := congrArg (fun μ : Measure (CheckedAssignmentSample.AssignmentVector p) => μ C)
    (AssignmentParameterFibreKernel.sum_fibreMass_smul_fibreMeasure p
      (renewalCallParameter rate rewards C_star C_h u t z))
  rw [Measure.finsetSum_apply] at hsum
  simp only [Measure.smul_apply, smul_eq_mul,
    Fintype.sum_option, hnone, zero_mul, zero_add] at hsum
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro U hU
  rw [(renewal_parameter_fibreMass rate rewards C_star C_h u t z U).1]

/-- Integrate an arbitrary Borel function of both the finite sample and the
retained source/block. Each varying source weight stays inside the integral.
This is the nonnegative extension of the admitted cellwise fibre identity. -/
theorem lintegral_renewalSample
    (f : SlowSet p → RenewalBlockBase rate rewards C_star C_h u t → ℝ≥0∞)
    (hf : ∀ U, Measurable (f U)) :
    ∫⁻ w, f (renewalAuxiliarySample rate rewards C_star C_h u t w.1 w.2)
        (renewalBlockProjection rate rewards C_star C_h u t w)
        ∂renewalBaseLaw rate rewards C_star C_h u t =
      ∫⁻ x, ∑ U : SlowSet p,
        renewalSlowSetPMF rate rewards C_star C_h u t x.1 U * f U x
        ∂renewalBlockLaw rate rewards C_star C_h u t := by
  classical
  have hpart (U : SlowSet p) : Measurable
      ((renewalSampleFibre rate rewards C_star C_h u t U).indicator
        (fun w => f U (renewalBlockProjection rate rewards C_star C_h u t w))) :=
    ((hf U).comp (measurable_renewalBlockProjection rate rewards C_star C_h u t)).indicator
      (measurableSet_renewalSampleFibre rate rewards C_star C_h u t U)
  have hmass (U : SlowSet p) : Measurable
      (fun x : RenewalBlockBase rate rewards C_star C_h u t =>
        renewalSlowSetPMF rate rewards C_star C_h u t x.1 U * f U x) :=
    ((measurable_renewalSlowSetPMF rate rewards C_star C_h u t U).comp
      measurable_fst).mul (hf U)
  calc
    _ = ∫⁻ w, ∑ U : SlowSet p,
        (renewalSampleFibre rate rewards C_star C_h u t U).indicator
          (fun w => f U (renewalBlockProjection rate rewards C_star C_h u t w)) w
        ∂renewalBaseLaw rate rewards C_star C_h u t := by
      apply lintegral_congr
      intro w
      rw [Finset.sum_eq_single
        (renewalAuxiliarySample rate rewards C_star C_h u t w.1 w.2)]
      · exact (Set.indicator_of_mem (show w ∈ renewalSampleFibre rate rewards
          C_star C_h u t (renewalAuxiliarySample rate rewards C_star C_h u t w.1 w.2)
          from rfl) (fun w' =>
            f (renewalAuxiliarySample rate rewards C_star C_h u t w.1 w.2)
              (renewalBlockProjection rate rewards C_star C_h u t w'))).symm
      · intro U hU hne
        exact Set.indicator_of_notMem (show w ∉
          renewalSampleFibre rate rewards C_star C_h u t U from
            fun h => hne h.symm)
          (fun w => f U (renewalBlockProjection rate rewards C_star C_h u t w))
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    _ = ∑ U : SlowSet p, ∫⁻ w,
        (renewalSampleFibre rate rewards C_star C_h u t U).indicator
          (fun w => f U (renewalBlockProjection rate rewards C_star C_h u t w)) w
        ∂renewalBaseLaw rate rewards C_star C_h u t :=
      lintegral_finsetSum _ (fun U _ => hpart U)
    _ = ∑ U : SlowSet p, ∫⁻ w in renewalSampleFibre rate rewards C_star C_h u t U,
        f U (renewalBlockProjection rate rewards C_star C_h u t w)
        ∂renewalBaseLaw rate rewards C_star C_h u t := by
      apply Finset.sum_congr rfl
      intro U hU
      exact lintegral_indicator
        (measurableSet_renewalSampleFibre rate rewards C_star C_h u t U) _
    _ = ∑ U : SlowSet p, ∫⁻ x,
        renewalSlowSetPMF rate rewards C_star C_h u t x.1 U * f U x
        ∂renewalBlockLaw rate rewards C_star C_h u t := by
      apply Finset.sum_congr rfl
      intro U hU
      exact lintegral_renewalSampleFibre rate rewards C_star C_h u t U (f U) (hf U)
    _ = _ := (lintegral_finsetSum _ (fun U _ => hmass U)).symm

/-- Integrating the actual varying-parameter fibre kernel over any retained
source/block cell yields the full assignment cube law times that cell's mass.
The source and old seeds are tested jointly, rather than through their
separate marginals or through a parameter-only pushforward. -/
theorem lintegral_renewalKernel_block
    (A : Set (RenewalBlockBase rate rewards C_star C_h u t)) (hA : MeasurableSet A)
    (C : Set (CheckedAssignmentSample.AssignmentVector p)) (hC : MeasurableSet C) :
    ∫⁻ w, (renewalBlockProjection rate rewards C_star C_h u t ⁻¹' A).indicator
        (fun w => renewalAssignmentFibreKernel rate rewards C_star C_h u t w C) w
        ∂renewalBaseLaw rate rewards C_star C_h u t =
      renewalBlockLaw rate rewards C_star C_h u t A *
        ContinuousControlSlice.assignmentLaw p.K C := by
  classical
  let f : SlowSet p → RenewalBlockBase rate rewards C_star C_h u t → ℝ≥0∞ :=
    fun U => A.indicator (fun x => AssignmentParameterFibreKernel.fibreMeasure p
      (renewalCallParameter rate rewards C_star C_h u t x.1) (some U) C)
  have hf (U : SlowSet p) : Measurable (f U) :=
    (measurable_renewalFibreMeasure_apply rate rewards C_star C_h u t U C hC).indicator hA
  calc
    _ = ∫⁻ w, f (renewalAuxiliarySample rate rewards C_star C_h u t w.1 w.2)
        (renewalBlockProjection rate rewards C_star C_h u t w)
        ∂renewalBaseLaw rate rewards C_star C_h u t := by
      apply lintegral_congr
      intro w
      by_cases hw : renewalBlockProjection rate rewards C_star C_h u t w ∈ A
      · rw [Set.indicator_of_mem (show w ∈
          renewalBlockProjection rate rewards C_star C_h u t ⁻¹' A from hw)]
        change _ = A.indicator _ (renewalBlockProjection rate rewards C_star C_h u t w)
        rw [Set.indicator_of_mem hw]
        rfl
      · rw [Set.indicator_of_notMem (show w ∉
          renewalBlockProjection rate rewards C_star C_h u t ⁻¹' A from hw)]
        change 0 = A.indicator _ (renewalBlockProjection rate rewards C_star C_h u t w)
        rw [Set.indicator_of_notMem hw]
    _ = ∫⁻ x, ∑ U : SlowSet p,
        renewalSlowSetPMF rate rewards C_star C_h u t x.1 U * f U x
        ∂renewalBlockLaw rate rewards C_star C_h u t :=
      lintegral_renewalSample rate rewards C_star C_h u t f hf
    _ = ∫⁻ x, A.indicator (fun _ => ContinuousControlSlice.assignmentLaw p.K C) x
        ∂renewalBlockLaw rate rewards C_star C_h u t := by
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ A
      · simp only [f, Set.indicator_of_mem hx]
        exact renewal_sum_pmf_mul_fibreMeasure rate rewards C_star C_h u t x.1 C
      · simp only [f, Set.indicator_of_notMem hx, mul_zero, Finset.sum_const_zero]
    _ = _ := by rw [lintegral_indicator_const hA, mul_comm]

/-- The arbitrary measurable source/block and full-vector rectangle identity
on the extension, with its unnormalized source mass. -/
theorem renewalLiftLaw_block_rectangle
    (A : Set (RenewalBlockBase rate rewards C_star C_h u t)) (hA : MeasurableSet A)
    (C : Set (CheckedAssignmentSample.AssignmentVector p)) (hC : MeasurableSet C) :
    renewalLiftLaw rate rewards C_star C_h u t
        {wv | renewalBlockProjection rate rewards C_star C_h u t wv.1 ∈ A ∧ wv.2 ∈ C} =
      renewalBlockLaw rate rewards C_star C_h u t A *
        ContinuousControlSlice.assignmentLaw p.K C := by
  have hset : MeasurableSet
      {wv : RenewalBase rate rewards C_star C_h u t ×
        CheckedAssignmentSample.AssignmentVector p |
        renewalBlockProjection rate rewards C_star C_h u t wv.1 ∈ A ∧ wv.2 ∈ C} :=
    (((measurable_renewalBlockProjection rate rewards C_star C_h u t).comp
      measurable_fst) hA).inter (measurable_snd hC)
  rw [renewalLiftLaw, Measure.compProd_apply hset]
  calc
    _ = ∫⁻ w, (renewalBlockProjection rate rewards C_star C_h u t ⁻¹' A).indicator
        (fun w => renewalAssignmentFibreKernel rate rewards C_star C_h u t w C) w
        ∂renewalBaseLaw rate rewards C_star C_h u t := by
      apply lintegral_congr
      intro w
      by_cases hw : renewalBlockProjection rate rewards C_star C_h u t w ∈ A
      · have hsection : (Prod.mk w ⁻¹'
            {wv | renewalBlockProjection rate rewards C_star C_h u t wv.1 ∈ A ∧
              wv.2 ∈ C}) = C := by
          ext v
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, hw, true_and]
        rw [hsection, Set.indicator_of_mem (show w ∈
          renewalBlockProjection rate rewards C_star C_h u t ⁻¹' A from hw)]
      · have hsection : (Prod.mk w ⁻¹'
            {wv | renewalBlockProjection rate rewards C_star C_h u t wv.1 ∈ A ∧
              wv.2 ∈ C}) = ∅ := by
          ext v
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, hw, false_and, Set.mem_empty_iff_false]
        rw [hsection, measure_empty, Set.indicator_of_notMem (show w ∉
          renewalBlockProjection rate rewards C_star C_h u t ⁻¹' A from hw)]
    _ = _ := lintegral_renewalKernel_block rate rewards C_star C_h u t A hA C hC

/-- The full joint law retains the WHOLE original source and ALL old block
coordinates, and makes the new vector uniform on the original full cube.
This equality applies to every Borel test on the complete product space.

Source motivation: `06_interruptions.tex:410-422`. It is an analytical
extension at the actual renewal parameter, without a physical vector swap. -/
theorem renewalLiftLaw_map_block_vector :
    (renewalLiftLaw rate rewards C_star C_h u t).map
        (renewalLiftBlockProjection rate rewards C_star C_h u t) =
      (renewalBlockLaw rate rewards C_star C_h u t).prod
        (ContinuousControlSlice.assignmentLaw p.K) := by
  apply Measure.ext_prod
  intro A C hA hC
  rw [Measure.map_apply
    (measurable_renewalLiftBlockProjection rate rewards C_star C_h u t) (hA.prod hC),
    Measure.prod_prod]
  exact renewalLiftLaw_block_rectangle rate rewards C_star C_h u t A hA C hC

/-- A measure-preserving projection to the retained source/block and fresh
vector. Both measures have their original unnormalized renewal mass. -/
theorem renewalLiftBlockProjection_measurePreserving :
    MeasurePreserving (renewalLiftBlockProjection rate rewards C_star C_h u t)
      (renewalLiftLaw rate rewards C_star C_h u t)
      ((renewalBlockLaw rate rewards C_star C_h u t).prod
        (ContinuousControlSlice.assignmentLaw p.K)) :=
  ⟨measurable_renewalLiftBlockProjection rate rewards C_star C_h u t,
    renewalLiftLaw_map_block_vector rate rewards C_star C_h u t⟩

/-- Arbitrary Borel events on the complete retained product, rather than
only rectangles, have precisely the stated joint product measure. -/
theorem renewalLiftLaw_block_vector_preimage
    (E : Set (RenewalBlockBase rate rewards C_star C_h u t ×
      CheckedAssignmentSample.AssignmentVector p)) (hE : MeasurableSet E) :
    renewalLiftLaw rate rewards C_star C_h u t
        (renewalLiftBlockProjection rate rewards C_star C_h u t ⁻¹' E) =
      ((renewalBlockLaw rate rewards C_star C_h u t).prod
        (ContinuousControlSlice.assignmentLaw p.K)) E := by
  rw [← Measure.map_apply
    (measurable_renewalLiftBlockProjection rate rewards C_star C_h u t) hE,
    renewalLiftLaw_map_block_vector rate rewards C_star C_h u t]

/-- The joint law acts on every nonnegative Borel test of the entire source,
old block and new vector. Tonelli needs no finite real-integral premise. -/
theorem lintegral_renewalLift_block_vector
    (f : RenewalBlockBase rate rewards C_star C_h u t ×
      CheckedAssignmentSample.AssignmentVector p → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ wv, f (renewalLiftBlockProjection rate rewards C_star C_h u t wv)
        ∂renewalLiftLaw rate rewards C_star C_h u t =
      ∫⁻ x, ∫⁻ v, f (x, v) ∂ContinuousControlSlice.assignmentLaw p.K
        ∂renewalBlockLaw rate rewards C_star C_h u t := by
  rw [← lintegral_map hf
    (measurable_renewalLiftBlockProjection rate rewards C_star C_h u t),
    renewalLiftLaw_map_block_vector rate rewards C_star C_h u t]
  exact lintegral_prod f hf.aemeasurable

/-- Keep the old block and the auxiliary sample in addition to the new
vector. The sample is recorded as the actual successful `Option` outcome. -/
def renewalLiftSampleGraph
    (wv : RenewalBase rate rewards C_star C_h u t ×
      CheckedAssignmentSample.AssignmentVector p) :
    (RenewalBlockBase rate rewards C_star C_h u t × Option (SlowSet p)) ×
      CheckedAssignmentSample.AssignmentVector p :=
  ((renewalBlockProjection rate rewards C_star C_h u t wv.1,
    some (renewalAuxiliarySample rate rewards C_star C_h u t wv.1.1 wv.1.2)), wv.2)

theorem measurable_renewalLiftSampleGraph :
    Measurable (renewalLiftSampleGraph rate rewards C_star C_h u t) := by
  have hsample : Measurable (fun wv : RenewalBase rate rewards C_star C_h u t ×
      CheckedAssignmentSample.AssignmentVector p =>
      some (renewalAuxiliarySample rate rewards C_star C_h u t wv.1.1 wv.1.2)) :=
    (measurable_of_countable (some : SlowSet p → Option (SlowSet p))).comp
      ((measurable_renewalAuxiliarySample rate rewards C_star C_h u t).comp
        measurable_fst)
  exact (((measurable_renewalBlockProjection rate rewards C_star C_h u t).comp
    measurable_fst).prodMk hsample).prodMk measurable_snd

/-- On the product-law side, recover the slow set from the same source's
actual reconstructed parameter and the entire new assignment vector. -/
def renewalBlockVectorGraph
    (xv : RenewalBlockBase rate rewards C_star C_h u t ×
      CheckedAssignmentSample.AssignmentVector p) :
    (RenewalBlockBase rate rewards C_star C_h u t × Option (SlowSet p)) ×
      CheckedAssignmentSample.AssignmentVector p :=
  ((xv.1, AssignmentParameterFibreKernel.successfulSlowSet p
    (renewalCallParameter rate rewards C_star C_h u t xv.1.1) xv.2), xv.2)

theorem measurable_renewalBlockVectorGraph :
    Measurable (renewalBlockVectorGraph rate rewards C_star C_h u t) := by
  have houtcome : Measurable (fun xv : RenewalBlockBase rate rewards C_star C_h u t ×
      CheckedAssignmentSample.AssignmentVector p =>
      AssignmentParameterFibreKernel.successfulSlowSet p
        (renewalCallParameter rate rewards C_star C_h u t xv.1.1) xv.2) :=
    (AssignmentParameterFibreKernel.measurable_successfulSlowSet_joint p).comp
      (((measurable_renewalCallParameter rate rewards C_star C_h u t).comp
        (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
  exact (measurable_fst.prodMk houtcome).prodMk measurable_snd

/-- On the analytical extension the two complete graph readouts agree almost
surely. This retains the original source and old block, not only `theta`. -/
theorem ae_renewalLiftSampleGraph_eq :
    renewalLiftSampleGraph rate rewards C_star C_h u t =ᵐ[
      renewalLiftLaw rate rewards C_star C_h u t]
      (renewalBlockVectorGraph rate rewards C_star C_h u t ∘
        renewalLiftBlockProjection rate rewards C_star C_h u t) := by
  filter_upwards [ae_renewalLiftLaw_outcome rate rewards C_star C_h u t] with wv hwv
  change ((renewalBlockProjection rate rewards C_star C_h u t wv.1,
      some (renewalAuxiliarySample rate rewards C_star C_h u t wv.1.1 wv.1.2)), wv.2) =
    ((renewalBlockProjection rate rewards C_star C_h u t wv.1,
      AssignmentParameterFibreKernel.successfulSlowSet p
        (renewalCallParameter rate rewards C_star C_h u t wv.1.1) wv.2), wv.2)
  rw [hwv]

/-- Strong joint graph identity for the whole original source, whole old
block, analytical sample and full new vector. It follows from the full joint
product law and the almost-sure same-parameter fibre relation.

This is stronger than the parameter-only joint measure identity: the source
and every old seed coordinate remain in both sides of this equality. -/
theorem renewalLiftLaw_map_sample_graph :
    (renewalLiftLaw rate rewards C_star C_h u t).map
        (renewalLiftSampleGraph rate rewards C_star C_h u t) =
      ((renewalBlockLaw rate rewards C_star C_h u t).prod
        (ContinuousControlSlice.assignmentLaw p.K)).map
          (renewalBlockVectorGraph rate rewards C_star C_h u t) := by
  calc
    _ = (renewalLiftLaw rate rewards C_star C_h u t).map
        (renewalBlockVectorGraph rate rewards C_star C_h u t ∘
          renewalLiftBlockProjection rate rewards C_star C_h u t) :=
      Measure.map_congr (ae_renewalLiftSampleGraph_eq rate rewards C_star C_h u t)
    _ = ((renewalLiftLaw rate rewards C_star C_h u t).map
        (renewalLiftBlockProjection rate rewards C_star C_h u t)).map
          (renewalBlockVectorGraph rate rewards C_star C_h u t) :=
      (Measure.map_map (measurable_renewalBlockVectorGraph rate rewards C_star C_h u t)
        (measurable_renewalLiftBlockProjection rate rewards C_star C_h u t)).symm
    _ = _ := by rw [renewalLiftLaw_map_block_vector rate rewards C_star C_h u t]

/-- Arbitrary Borel graph events retain the whole original source and old
block. Equality on this graph space does not identify the new vector with a
physical current vector already present in that source. -/
theorem renewalLiftLaw_graph_preimage
    (E : Set ((RenewalBlockBase rate rewards C_star C_h u t × Option (SlowSet p)) ×
      CheckedAssignmentSample.AssignmentVector p)) (hE : MeasurableSet E) :
    renewalLiftLaw rate rewards C_star C_h u t
        (renewalLiftSampleGraph rate rewards C_star C_h u t ⁻¹' E) =
      ((renewalBlockLaw rate rewards C_star C_h u t).prod
        (ContinuousControlSlice.assignmentLaw p.K))
          (renewalBlockVectorGraph rate rewards C_star C_h u t ⁻¹' E) := by
  rw [← Measure.map_apply
    (measurable_renewalLiftSampleGraph rate rewards C_star C_h u t) hE,
    renewalLiftLaw_map_sample_graph rate rewards C_star C_h u t,
    Measure.map_apply (measurable_renewalBlockVectorGraph rate rewards C_star C_h u t) hE]

/-- Every nonnegative Borel graph test can be evaluated under the original
source/block product and the full assignment cube, with no integrability
assumption and no loss of original source coordinates. -/
theorem lintegral_renewalLift_sample_graph
    (f : (RenewalBlockBase rate rewards C_star C_h u t × Option (SlowSet p)) ×
      CheckedAssignmentSample.AssignmentVector p → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ wv, f (renewalLiftSampleGraph rate rewards C_star C_h u t wv)
        ∂renewalLiftLaw rate rewards C_star C_h u t =
      ∫⁻ x, ∫⁻ v, f (renewalBlockVectorGraph rate rewards C_star C_h u t (x, v))
        ∂ContinuousControlSlice.assignmentLaw p.K
        ∂renewalBlockLaw rate rewards C_star C_h u t := by
  rw [← lintegral_map hf
    (measurable_renewalLiftSampleGraph rate rewards C_star C_h u t),
    renewalLiftLaw_map_sample_graph rate rewards C_star C_h u t,
    lintegral_map hf (measurable_renewalBlockVectorGraph rate rewards C_star C_h u t)]
  exact lintegral_prod _
    (hf.comp (measurable_renewalBlockVectorGraph rate rewards C_star C_h u t)).aemeasurable

/-- A selected slow-set and vector rectangle, jointly with an arbitrary
retained source/block cell. The right side uses the actual sampler fibre in
the full cube at each original source's reconstructed parameter. -/
theorem renewalLiftLaw_sample_vector_rectangle
    (A : Set (RenewalBlockBase rate rewards C_star C_h u t)) (hA : MeasurableSet A)
    (U : SlowSet p)
    (C : Set (CheckedAssignmentSample.AssignmentVector p)) (hC : MeasurableSet C) :
    renewalLiftLaw rate rewards C_star C_h u t
        {wv | renewalBlockProjection rate rewards C_star C_h u t wv.1 ∈ A ∧
          renewalAuxiliarySample rate rewards C_star C_h u t wv.1.1 wv.1.2 = U ∧
          wv.2 ∈ C} =
      ∫⁻ x in A, ContinuousControlSlice.assignmentLaw p.K
        (C ∩ {v | AssignmentParameterFibreKernel.successfulSlowSet p
          (renewalCallParameter rate rewards C_star C_h u t x.1) v = some U})
        ∂renewalBlockLaw rate rewards C_star C_h u t := by
  let E : Set ((RenewalBlockBase rate rewards C_star C_h u t × Option (SlowSet p)) ×
      CheckedAssignmentSample.AssignmentVector p) := (A ×ˢ {some U}) ×ˢ C
  have hE : MeasurableSet E := (hA.prod (measurableSet_singleton _)).prod hC
  have hleft : renewalLiftSampleGraph rate rewards C_star C_h u t ⁻¹' E =
      {wv | renewalBlockProjection rate rewards C_star C_h u t wv.1 ∈ A ∧
        renewalAuxiliarySample rate rewards C_star C_h u t wv.1.1 wv.1.2 = U ∧
        wv.2 ∈ C} := by
    ext wv
    simp only [Set.mem_preimage, E, renewalLiftSampleGraph, Set.mem_prod,
      Set.mem_singleton_iff, Option.some.injEq, Set.mem_ofPred_eq, and_assoc]
  rw [← hleft, renewalLiftLaw_graph_preimage rate rewards C_star C_h u t E hE]
  rw [Measure.prod_apply
    ((measurable_renewalBlockVectorGraph rate rewards C_star C_h u t) hE)]
  calc
    _ = ∫⁻ x, A.indicator (fun x => ContinuousControlSlice.assignmentLaw p.K
        (C ∩ {v | AssignmentParameterFibreKernel.successfulSlowSet p
          (renewalCallParameter rate rewards C_star C_h u t x.1) v = some U})) x
        ∂renewalBlockLaw rate rewards C_star C_h u t := by
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ A
      · have hsection : Prod.mk x ⁻¹'
            (renewalBlockVectorGraph rate rewards C_star C_h u t ⁻¹' E) =
            C ∩ {v | AssignmentParameterFibreKernel.successfulSlowSet p
              (renewalCallParameter rate rewards C_star C_h u t x.1) v = some U} := by
          ext v
          simp only [Set.mem_preimage, E, renewalBlockVectorGraph, Set.mem_prod,
            Set.mem_singleton_iff, hx, true_and, Set.mem_inter_iff, Set.mem_ofPred_eq,
            and_comm]
        rw [hsection, Set.indicator_of_mem hx]
      · have hsection : Prod.mk x ⁻¹'
            (renewalBlockVectorGraph rate rewards C_star C_h u t ⁻¹' E) = ∅ := by
          ext v
          simp only [Set.mem_preimage, E, renewalBlockVectorGraph, Set.mem_prod,
            hx, false_and, Set.mem_empty_iff_false]
        rw [hsection, measure_empty, Set.indicator_of_notMem hx]
    _ = _ := lintegral_indicator hA _

/-- Forgetting the new vector is a measure-preserving map to the entire
original source/auxiliary pair. This statement keeps the whole array, not
just the old block retained by the independent-vector product law. -/
theorem renewalLift_fst_measurePreserving :
    MeasurePreserving Prod.fst
      (renewalLiftLaw rate rewards C_star C_h u t)
      (renewalBaseLaw rate rewards C_star C_h u t) :=
  ⟨measurable_fst, renewalLiftLaw_map_fst rate rewards C_star C_h u t⟩

/-- Arbitrary nonnegative tests of all original coordinates have the same
integral before and after adjoining the analytical full vector. -/
theorem lintegral_renewalLift_base
    (f : RenewalBase rate rewards C_star C_h u t → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ wv, f wv.1 ∂renewalLiftLaw rate rewards C_star C_h u t =
      ∫⁻ w, f w ∂renewalBaseLaw rate rewards C_star C_h u t := by
  rw [← lintegral_map hf measurable_fst, renewalLiftLaw_map_fst rate rewards C_star C_h u t]

/-- The original source-subtype marginal is preserved with its full mass. -/
theorem renewalLiftLaw_map_source :
    (renewalLiftLaw rate rewards C_star C_h u t).map (fun wv => wv.1.1) =
      renewalSourceLaw rate rewards C_star C_h u t := by
  calc
    _ = ((renewalLiftLaw rate rewards C_star C_h u t).map Prod.fst).map Prod.fst :=
      (Measure.map_map measurable_fst measurable_fst).symm
    _ = _ := by
      rw [renewalLiftLaw_map_fst rate rewards C_star C_h u t, renewalBaseLaw,
        Measure.map_fst_prod,
        measure_univ (μ := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p),
        one_smul]

/-- Returning to the WHOLE physical source gives its original law restricted
to the literal renewal event. No row, private array, or original `J` is lost. -/
theorem renewalLiftLaw_map_original_source :
    (renewalLiftLaw rate rewards C_star C_h u t).map (fun wv => wv.1.1.val) =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (renewalCallEvent rate rewards C_star C_h u t) := by
  calc
    _ = ((renewalLiftLaw rate rewards C_star C_h u t).map
        (fun wv => wv.1.1)).map Subtype.val :=
      (Measure.map_map measurable_subtype_coe (measurable_fst.comp measurable_fst)).symm
    _ = _ := by
      rw [renewalLiftLaw_map_source rate rewards C_star C_h u t,
        renewalSourceLaw_map_val rate rewards C_star C_h u t]

/-- The retained block product has exactly the original source mass. -/
theorem renewalBlockLaw_univ :
    renewalBlockLaw rate rewards C_star C_h u t Set.univ =
      renewalSourceLaw rate rewards C_star C_h u t Set.univ := by
  rw [renewalBlockLaw, ← Set.univ_prod_univ, Measure.prod_prod,
    measure_univ (μ := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellLaw u t), mul_one]

/-- The vector marginal is the full cube law multiplied by the renewal cell
mass. On an unnormalized extension it is not in general a probability law. -/
theorem renewalLiftLaw_map_vector :
    (renewalLiftLaw rate rewards C_star C_h u t).map Prod.snd =
      renewalSourceLaw rate rewards C_star C_h u t Set.univ •
        ContinuousControlSlice.assignmentLaw p.K := by
  calc
    _ = ((renewalLiftLaw rate rewards C_star C_h u t).map
        (renewalLiftBlockProjection rate rewards C_star C_h u t)).map Prod.snd := by
      rw [Measure.map_map measurable_snd
        (measurable_renewalLiftBlockProjection rate rewards C_star C_h u t)]
      rfl
    _ = _ := by
      rw [renewalLiftLaw_map_block_vector rate rewards C_star C_h u t,
        Measure.map_snd_prod, renewalBlockLaw_univ rate rewards C_star C_h u t]

/-- Null renewal cells produce the zero extension. There is no need to
choose a conditional distribution on such cells or assume positive mass. -/
theorem renewalLiftLaw_eq_zero_iff :
    renewalLiftLaw rate rewards C_star C_h u t = 0 ↔
      renewalSourceLaw rate rewards C_star C_h u t = 0 := by
  rw [← Measure.measure_univ_eq_zero, renewalLiftLaw_univ rate rewards C_star C_h u t,
    ← renewalSourceLaw_univ rate rewards C_star C_h u t, Measure.measure_univ_eq_zero]

/-- In particular, an empty actual source cell has zero extension measure.
This is a consequence of the literal construction, with no inhabitance
assumption used by any of the main product or graph identities. -/
theorem renewalLiftLaw_eq_zero_of_isEmpty
    [IsEmpty (RenewalCallSource rate rewards C_star C_h u t)] :
    renewalLiftLaw rate rewards C_star C_h u t = 0 := by
  exact (renewalLiftLaw_eq_zero_iff rate rewards C_star C_h u t).mpr
    (Subsingleton.elim _ _)

/-- Integrability of real tests transfers exactly along the established
joint projection. Measurability is the only test input in this equivalence. -/
theorem integrable_renewalLift_block_vector_iff
    (f : RenewalBlockBase rate rewards C_star C_h u t ×
      CheckedAssignmentSample.AssignmentVector p → ℝ) (hf : Measurable f) :
    Integrable (fun wv => f (renewalLiftBlockProjection rate rewards C_star C_h u t wv))
        (renewalLiftLaw rate rewards C_star C_h u t) ↔
      Integrable f ((renewalBlockLaw rate rewards C_star C_h u t).prod
        (ContinuousControlSlice.assignmentLaw p.K)) :=
  (renewalLiftBlockProjection_measurePreserving rate rewards C_star C_h u t).integrable_comp
    hf.aestronglyMeasurable

/-- Bounded real Borel tests are integrable on the unnormalized extension.
The bound is an explicit test-function condition, not a physical-history,
conditional-law, parameter-locality, or execution hypothesis. -/
theorem integrable_renewalLift_block_vector_of_bound
    (f : RenewalBlockBase rate rewards C_star C_h u t ×
      CheckedAssignmentSample.AssignmentVector p → ℝ) (hf : Measurable f)
    (bound : ℝ) (hbound : ∀ xv, ‖f xv‖ ≤ bound) :
    Integrable (fun wv => f (renewalLiftBlockProjection rate rewards C_star C_h u t wv))
      (renewalLiftLaw rate rewards C_star C_h u t) := by
  apply (integrable_renewalLift_block_vector_iff rate rewards C_star C_h u t f hf).mpr
  exact (integrable_const bound).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

/-- Real Borel test integrals agree under the full joint law. The preceding
bound theorem provides finiteness for every bounded such test. -/
theorem integral_renewalLift_block_vector
    (f : RenewalBlockBase rate rewards C_star C_h u t ×
      CheckedAssignmentSample.AssignmentVector p → ℝ) (hf : Measurable f) :
    ∫ wv, f (renewalLiftBlockProjection rate rewards C_star C_h u t wv)
        ∂renewalLiftLaw rate rewards C_star C_h u t =
      ∫ xv, f xv ∂(renewalBlockLaw rate rewards C_star C_h u t).prod
        (ContinuousControlSlice.assignmentLaw p.K) := by
  rw [← integral_map
    (measurable_renewalLiftBlockProjection rate rewards C_star C_h u t).aemeasurable
    hf.aestronglyMeasurable,
    renewalLiftLaw_map_block_vector rate rewards C_star C_h u t]

/-- The complete original auxiliary array keeps its original unnormalized
marginal. Its joint marginal with the physical source is the stronger
`renewalLiftLaw_map_fst` statement. -/
theorem renewalLiftLaw_map_auxiliary_array :
    (renewalLiftLaw rate rewards C_star C_h u t).map (fun wv => wv.1.2) =
      renewalSourceLaw rate rewards C_star C_h u t Set.univ •
        ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p := by
  calc
    _ = ((renewalLiftLaw rate rewards C_star C_h u t).map Prod.fst).map Prod.snd :=
      (Measure.map_map measurable_snd measurable_fst).symm
    _ = _ := by
      rw [renewalLiftLaw_map_fst rate rewards C_star C_h u t, renewalBaseLaw,
        Measure.map_snd_prod]

/-- The retained whole-source/old-block marginal, obtained from the full
joint vector law rather than by separately checking two factor marginals. -/
theorem renewalLiftLaw_map_block :
    (renewalLiftLaw rate rewards C_star C_h u t).map
        (fun wv => renewalBlockProjection rate rewards C_star C_h u t wv.1) =
      renewalBlockLaw rate rewards C_star C_h u t := by
  calc
    _ = ((renewalLiftLaw rate rewards C_star C_h u t).map
        (renewalLiftBlockProjection rate rewards C_star C_h u t)).map Prod.fst := by
      rw [Measure.map_map measurable_fst
        (measurable_renewalLiftBlockProjection rate rewards C_star C_h u t)]
      rfl
    _ = _ := by
      rw [renewalLiftLaw_map_block_vector rate rewards C_star C_h u t,
        Measure.map_fst_prod,
        measure_univ (μ := ContinuousControlSlice.assignmentLaw p.K), one_smul]

/-- Every original physical-source event has its original mass intersected
with the literal renewal event. This includes events involving unread rows,
all original private arrays, and the original private index `J`. -/
theorem renewalLiftLaw_original_source_event
    (A : Set (BootstrapPrivateRoundStreams.SourceInput p)) (hA : MeasurableSet A) :
    renewalLiftLaw rate rewards C_star C_h u t {wv | wv.1.1.val ∈ A} =
      BootstrapPrivateRoundStreams.sourceInputLaw p
        (A ∩ renewalCallEvent rate rewards C_star C_h u t) := by
  have hprojection : Measurable (fun wv : RenewalBase rate rewards C_star C_h u t ×
      CheckedAssignmentSample.AssignmentVector p => wv.1.1.val) :=
    measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)
  change renewalLiftLaw rate rewards C_star C_h u t
    ((fun wv => wv.1.1.val) ⁻¹' A) = _
  rw [← Measure.map_apply
    hprojection hA,
    renewalLiftLaw_map_original_source rate rewards C_star C_h u t,
    Measure.restrict_apply hA]

/-- An arbitrary event of the WHOLE original physical source is jointly
independent of the new analytical vector under the unnormalized renewal
restriction. This does not compare that vector to the original current row
or claim that swapping it into that row preserves execution. -/
theorem renewalLiftLaw_original_source_vector_rectangle
    (A : Set (BootstrapPrivateRoundStreams.SourceInput p)) (hA : MeasurableSet A)
    (C : Set (CheckedAssignmentSample.AssignmentVector p)) (hC : MeasurableSet C) :
    renewalLiftLaw rate rewards C_star C_h u t
        {wv | wv.1.1.val ∈ A ∧ wv.2 ∈ C} =
      BootstrapPrivateRoundStreams.sourceInputLaw p
        (A ∩ renewalCallEvent rate rewards C_star C_h u t) *
          ContinuousControlSlice.assignmentLaw p.K C := by
  let B : Set (RenewalBlockBase rate rewards C_star C_h u t) := {x | x.1.val ∈ A}
  have hB : MeasurableSet B := (measurable_subtype_coe.comp measurable_fst) hA
  have hmass : renewalBlockLaw rate rewards C_star C_h u t B =
      renewalSourceLaw rate rewards C_star C_h u t (Subtype.val ⁻¹' A) := by
    change renewalBlockLaw rate rewards C_star C_h u t
      (Prod.fst ⁻¹' (Subtype.val ⁻¹' A)) = _
    rw [← Measure.map_apply measurable_fst (measurable_subtype_coe hA),
      renewalBlockLaw, Measure.map_fst_prod,
      measure_univ (μ := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellLaw u t),
      one_smul]
  have hsource : renewalSourceLaw rate rewards C_star C_h u t (Subtype.val ⁻¹' A) =
      BootstrapPrivateRoundStreams.sourceInputLaw p
        (A ∩ renewalCallEvent rate rewards C_star C_h u t) := by
    rw [← Measure.map_apply measurable_subtype_coe hA,
      renewalSourceLaw_map_val rate rewards C_star C_h u t, Measure.restrict_apply hA]
  change renewalLiftLaw rate rewards C_star C_h u t
    {wv | renewalBlockProjection rate rewards C_star C_h u t wv.1 ∈ B ∧ wv.2 ∈ C} = _
  rw [renewalLiftLaw_block_rectangle rate rewards C_star C_h u t B hB C hC,
    hmass, hsource]

/-- Bounded real graph tests are integrable on the extension. All bounds
belong to the explicitly chosen test function; none constrains the actual
physical source, reconstruction, execution, or original current vector. -/
theorem integrable_renewalLift_sample_graph_of_bound
    (f : (RenewalBlockBase rate rewards C_star C_h u t × Option (SlowSet p)) ×
      CheckedAssignmentSample.AssignmentVector p → ℝ) (hf : Measurable f)
    (bound : ℝ) (hbound : ∀ g, ‖f g‖ ≤ bound) :
    Integrable (fun wv => f (renewalLiftSampleGraph rate rewards C_star C_h u t wv))
      (renewalLiftLaw rate rewards C_star C_h u t) := by
  apply (integrable_const bound).mono'
    (hf.comp (measurable_renewalLiftSampleGraph rate rewards C_star C_h u t)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun wv =>
    hbound (renewalLiftSampleGraph rate rewards C_star C_h u t wv))

/-- Real graph-test integrals agree with the full source/block/vector
product graph. Bounded tests have finite integrals by the preceding lemma. -/
theorem integral_renewalLift_sample_graph
    (f : (RenewalBlockBase rate rewards C_star C_h u t × Option (SlowSet p)) ×
      CheckedAssignmentSample.AssignmentVector p → ℝ) (hf : Measurable f) :
    ∫ wv, f (renewalLiftSampleGraph rate rewards C_star C_h u t wv)
        ∂renewalLiftLaw rate rewards C_star C_h u t =
      ∫ xv, f (renewalBlockVectorGraph rate rewards C_star C_h u t xv)
        ∂(renewalBlockLaw rate rewards C_star C_h u t).prod
          (ContinuousControlSlice.assignmentLaw p.K) := by
  rw [← integral_map
    (measurable_renewalLiftSampleGraph rate rewards C_star C_h u t).aemeasurable
    hf.aestronglyMeasurable,
    renewalLiftLaw_map_sample_graph rate rewards C_star C_h u t,
    integral_map
      (measurable_renewalBlockVectorGraph rate rewards C_star C_h u t).aemeasurable
      hf.aestronglyMeasurable]

end Bandits.Support.ReferenceFirstCollectionRenewalFibreExtension

end
