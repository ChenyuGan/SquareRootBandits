/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteRewardMeasurability
public import Bandits.Support.ReferenceInitializationIndexMixture

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Original-index private expectations of the complete selected-row reward

Sources: `sources/zip4/manuscript/07_public_setup.tex:123-164` and
`sources/zip4/manuscript/08_main_theorem.tex:29-48,67-75`.

We restrict the original private law to its actual coordinator-index cell and
normalize it. Public fibres replace one whole continuous row in the original
public product. The complete physical reward's admitted source-data equality
proves locality under this construction, with every private coordinate retained.
The resulting expectations and regret functions are defined at every row and
the uniform decomposition holds at every fixed public output. These are internal
identities, not a manuscript regret bound or a source-closure assertion.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.PrivateSourceStreams
open scoped ENNReal

namespace Bandits.Support.ReferenceCompleteSelectedRowExpectation

variable {p : Parameters}

/-- The actual original-private event `J=j`; no index coordinate is resampled. -/
def indexCell (p : Parameters) (j : Fin (ConstructorDimensions.M p)) :
    Set (ExtendedPrivateCoordinates p) :=
  {e | coordinatorIndex p e.1.2 = j}

theorem measurableSet_indexCell (p : Parameters) (j : Fin (ConstructorDimensions.M p)) :
    MeasurableSet (indexCell p j) :=
  ((measurable_coordinatorIndex p).comp
    (measurable_snd.comp measurable_fst)) (measurableSet_singleton j)

/-- Mass of the original index cell, from the original scalar/residual product. -/
theorem measure_indexCell (p : Parameters) (j : Fin (ConstructorDimensions.M p)) :
    extendedPrivateLaw p (indexCell p j) =
      ENNReal.ofReal (1 / (ConstructorDimensions.M p : ℝ)) := by
  let atom : Set ContinuousCategorical.Scalar := coordinatorIndex p ⁻¹' {j}
  have hatom : MeasurableSet atom :=
    measurable_coordinatorIndex p (measurableSet_singleton j)
  have h := (ReferenceInitializationIndexMixture.measurePreserving_scalarAndResidual p).measure_preimage
    (hatom.prod MeasurableSet.univ).nullMeasurableSet
  have hpre : ReferenceInitializationIndexMixture.scalarAndResidual ⁻¹' (atom ×ˢ Set.univ) =
      indexCell p j := by
    ext e
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true,
      atom, ReferenceInitializationIndexMixture.scalarAndResidual, indexCell,
      Set.mem_ofPred_eq, Set.mem_singleton_iff]
  rw [hpre] at h
  rw [h, Measure.prod_prod, measure_univ, mul_one]
  exact coordinatorIndex_uniform_atom p j

/-- Normalized restriction of the entire original private tuple to `J=j`. -/
def selectedIndexPrivateLaw (p : Parameters) (j : Fin (ConstructorDimensions.M p)) :
    Measure (ExtendedPrivateCoordinates p) :=
  ENNReal.ofReal (ConstructorDimensions.M p : ℝ) •
    (extendedPrivateLaw p).restrict (indexCell p j)

instance selectedIndexPrivateLaw_probability (p : Parameters)
    (j : Fin (ConstructorDimensions.M p)) :
    IsProbabilityMeasure (selectedIndexPrivateLaw p j) := by
  constructor
  rw [selectedIndexPrivateLaw, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply_univ, measure_indexCell]
  have hm : (0 : ℝ) < ConstructorDimensions.M p := Nat.cast_pos.mpr (M_pos p)
  rw [← ENNReal.ofReal_mul hm.le, mul_one_div_cancel hm.ne', ENNReal.ofReal_one]

theorem ae_selectedIndexPrivateLaw_mem (p : Parameters)
    (j : Fin (ConstructorDimensions.M p)) :
    ∀ᵐ e ∂selectedIndexPrivateLaw p j, e ∈ indexCell p j :=
  Measure.ae_smul_measure (ae_restrict_mem (measurableSet_indexCell p j)) _

/-- The original scalar-first reordering retains the original restricted scalar
and all block, player-round and target factors. The restriction/product identity
is the one characterized by measurable rectangles in the original product. -/
theorem selectedIndexPrivateLaw_map_scalarAndResidual (p : Parameters)
    (j : Fin (ConstructorDimensions.M p)) :
    (selectedIndexPrivateLaw p j).map ReferenceInitializationIndexMixture.scalarAndResidual =
      (ENNReal.ofReal (ConstructorDimensions.M p : ℝ) •
        ContinuousCategorical.uniform.restrict (coordinatorIndex p ⁻¹' {j})).prod
          (ReferenceInitializationIndexMixture.privateResidualLaw p) := by
  let atom : Set ContinuousCategorical.Scalar := coordinatorIndex p ⁻¹' {j}
  have hatom : MeasurableSet atom :=
    measurable_coordinatorIndex p (measurableSet_singleton j)
  have hpre : ReferenceInitializationIndexMixture.scalarAndResidual ⁻¹' (atom ×ˢ Set.univ) = indexCell p j := by
    ext e
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true,
      atom, ReferenceInitializationIndexMixture.scalarAndResidual, indexCell, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  rw [selectedIndexPrivateLaw,
    Measure.map_smul _ (ReferenceInitializationIndexMixture.measurePreserving_scalarAndResidual p).measurable.aemeasurable,
    ← hpre, ← Measure.restrict_map (ReferenceInitializationIndexMixture.measurePreserving_scalarAndResidual p).measurable
      (hatom.prod MeasurableSet.univ),
    (ReferenceInitializationIndexMixture.measurePreserving_scalarAndResidual p).map_eq,
    ← Measure.restrict_prod_eq_prod_univ, Measure.prod_smul_left]

/-- Whole-row public fibre, including exact rows of zero public probability.
Every nuisance coordinate is integrated using the original public product. -/
def selectedRowPublicFiberLaw (p : Parameters) (j : Fin (ConstructorDimensions.M p))
    (rho : CompleteRow p) : Measure (CompleteRows p) :=
  (completeRowsMeasure p).map (fun rows => Function.update rows j rho)

instance selectedRowPublicFiberLaw_probability (p : Parameters)
    (j : Fin (ConstructorDimensions.M p)) (rho : CompleteRow p) :
    IsProbabilityMeasure (selectedRowPublicFiberLaw p j rho) := by
  constructor
  rw [selectedRowPublicFiberLaw, Measure.map_apply measurable_update_left MeasurableSet.univ,
    Set.preimage_univ, measure_univ]

/-- Explicit product characterization of the public fibre. -/
theorem selectedRowPublicFiberLaw_eq_pi (p : Parameters)
    (j : Fin (ConstructorDimensions.M p)) (rho : CompleteRow p) :
    selectedRowPublicFiberLaw p j rho =
      Measure.pi (fun k => if k = j then Measure.dirac rho else completeRowMeasure p) := by
  classical
  let f : Fin (ConstructorDimensions.M p) → CompleteRow p → CompleteRow p :=
    fun k x => if k = j then rho else x
  have hf (k : Fin (ConstructorDimensions.M p)) : Measurable (f k) := by
    by_cases hk : k = j
    · simp only [f, hk, ite_true]
      exact measurable_const
    · simp only [f, hk, ite_false]
      exact measurable_id
  have hmap (k : Fin (ConstructorDimensions.M p)) :
      (completeRowMeasure p).map (f k) =
        if k = j then Measure.dirac rho else completeRowMeasure p := by
    by_cases hk : k = j
    · simp only [f, hk, ite_true, Measure.map_const, measure_univ, one_smul]
    · simp only [f, hk, ite_false]
      exact Measure.map_id
  have hfinite (k : Fin (ConstructorDimensions.M p)) :
      IsProbabilityMeasure ((completeRowMeasure p).map (f k)) :=
    by infer_instance
  have heq : (fun rows : CompleteRows p => Function.update rows j rho) =
      fun rows k => f k (rows k) := by
    funext rows k
    by_cases hk : k = j
    · subst k
      simp only [Function.update_self, f, ite_true]
    · simp only [Function.update_of_ne hk, f, hk, ite_false]
  rw [selectedRowPublicFiberLaw, completeRowsMeasure, heq, Measure.pi_map_pi
    (fun k => (hf k).aemeasurable)]
  congr 1
  funext k
  exact hmap k

/-- The pinned whole row is exactly `rho` almost surely in its public fibre. -/
theorem ae_selectedRowPublicFiberLaw_apply_eq (p : Parameters)
    (j : Fin (ConstructorDimensions.M p)) (rho : CompleteRow p) :
    ∀ᵐ rows ∂selectedRowPublicFiberLaw p j rho, rows j = rho := by
  rw [selectedRowPublicFiberLaw]
  apply (ae_map_iff (f := fun rows : CompleteRows p => Function.update rows j rho)
    measurable_update_left.aemeasurable
    ((measurable_pi_apply j) (measurableSet_singleton rho))).2
  apply ae_of_all
  intro rows
  change Function.update rows j rho j = rho
  exact Function.update_self j rho rows


private theorem measurePreserving_replace_from_two_rows (p : Parameters)
    (j : Fin (ConstructorDimensions.M p)) :
    MeasurePreserving (fun z : CompleteRows p × CompleteRows p =>
      Function.update z.2 j (z.1 j))
      ((completeRowsMeasure p).prod (completeRowsMeasure p)) (completeRowsMeasure p) := by
  classical
  let f : Fin (ConstructorDimensions.M p) → CompleteRow p × CompleteRow p → CompleteRow p :=
    fun k z => if k = j then z.1 else z.2
  have hf (k : Fin (ConstructorDimensions.M p)) :
      MeasurePreserving (f k) ((completeRowMeasure p).prod (completeRowMeasure p))
        (completeRowMeasure p) := by
    by_cases hk : k = j
    · simpa only [f, hk, ite_true] using
        (measurePreserving_fst (μ := completeRowMeasure p) (ν := completeRowMeasure p))
    · simpa only [f, hk, ite_false] using
        (measurePreserving_snd (μ := completeRowMeasure p) (ν := completeRowMeasure p))
  have hpi := measurePreserving_pi
    (fun _ : Fin (ConstructorDimensions.M p) =>
      (completeRowMeasure p).prod (completeRowMeasure p))
    (fun _ : Fin (ConstructorDimensions.M p) => completeRowMeasure p) hf
  have hsplit := (measurePreserving_arrowProdEquivProdArrow
    (CompleteRow p) (CompleteRow p) (Fin (ConstructorDimensions.M p))
    (fun _ => completeRowMeasure p) (fun _ => completeRowMeasure p)).symm
  convert hpi.comp hsplit using 1
  · funext z k
    change Function.update z.2 j (z.1 j) k = if k = j then z.1 k else z.2 k
    by_cases hk : k = j
    · subst k
      simp only [Function.update_self, ite_true]
    · simp only [Function.update_of_ne hk, hk, ite_false]
  · rfl
  · rfl

/-- Replacing one coordinate by an independently drawn row recovers the original
public product. Both factors here are the original row/family laws. -/
theorem measurePreserving_update_selectedRow (p : Parameters)
    (j : Fin (ConstructorDimensions.M p)) :
    MeasurePreserving (fun z : CompleteRow p × CompleteRows p =>
      Function.update z.2 j z.1)
      ((completeRowMeasure p).prod (completeRowsMeasure p)) (completeRowsMeasure p) := by
  have heval := measurePreserving_eval
    (fun _ : Fin (ConstructorDimensions.M p) => completeRowMeasure p) j
  have hev : MeasurePreserving
      (fun z : CompleteRows p × CompleteRows p => (z.1 j, z.2))
      ((completeRowsMeasure p).prod (completeRowsMeasure p))
      ((completeRowMeasure p).prod (completeRowsMeasure p)) :=
    heval.prod (MeasurePreserving.id (completeRowsMeasure p))
  have hu : Measurable (fun z : CompleteRow p × CompleteRows p =>
      Function.update z.2 j z.1) := measurable_update'.comp measurable_swap
  refine ⟨hu, ?_⟩
  rw [← hev.map_eq, Measure.map_map hu hev.measurable]
  exact (measurePreserving_replace_from_two_rows p j).map_eq

/-- Integrating the exact-row fibre against the original row law reconstructs
the original public integral. The test is any measurable integrable real function. -/
theorem selectedRowPublicFiberLaw_reconstruction (p : Parameters)
    (j : Fin (ConstructorDimensions.M p))
    (g : CompleteRows p → ℝ) (hg : Measurable g)
    (hgi : Integrable g (completeRowsMeasure p)) :
    (∫ rho : CompleteRow p, ∫ rows : CompleteRows p, g rows
      ∂selectedRowPublicFiberLaw p j rho ∂completeRowMeasure p) =
        ∫ rows : CompleteRows p, g rows ∂completeRowsMeasure p := by
  have hmp := measurePreserving_update_selectedRow p j
  have hcomp := hmp.integrable_comp_of_integrable hgi
  have heq (rho : CompleteRow p) :
      (∫ rows, g rows ∂selectedRowPublicFiberLaw p j rho) =
        ∫ rows : CompleteRows p, g (Function.update rows j rho) ∂completeRowsMeasure p :=
    integral_map_of_stronglyMeasurable measurable_update_left hg.stronglyMeasurable
  simp_rw [heq]
  rw [← integral_prod (fun z : CompleteRow p × CompleteRows p =>
    g (Function.update z.2 j z.1)) hcomp]
  calc
    _ = ∫ rows, g rows ∂((completeRowMeasure p).prod (completeRowsMeasure p)).map
        (fun z : CompleteRow p × CompleteRows p => Function.update z.2 j z.1) :=
      (integral_map_of_stronglyMeasurable hmp.measurable hg.stronglyMeasurable).symm
    _ = _ := by rw [hmp.map_eq]


/-- The literal private expected complete reward, after fixing the selected
whole row and integrating the original public nuisance coordinates. -/
def fixedRowPrivateExpectedCompleteReward
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (ids : IDArray p) (j : Fin (ConstructorDimensions.M p)) (rho : CompleteRow p) : ℝ :=
  ∫ rows : CompleteRows p, ∫ e : ExtendedPrivateCoordinates p,
    ReferenceCompletePhysicalRewards.completeReward rate
      ((ids, Function.update rows j rho), e) rewards C_star C_h
      ∂selectedIndexPrivateLaw p j ∂completeRowsMeasure p

/-- Joint Borel measurability of the actual updated-source integrand. -/
theorem measurable_updatedCompleteReward
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (j : Fin (ConstructorDimensions.M p)) :
    Measurable (fun z : ((IDArray p × CompleteRow p) × CompleteRows p) ×
        ExtendedPrivateCoordinates p =>
      ReferenceCompletePhysicalRewards.completeReward rate
        ((z.1.1.1, Function.update z.1.2 j z.1.1.2), z.2) rewards C_star C_h) := by
  have hupdate : Measurable (fun z : ((IDArray p × CompleteRow p) × CompleteRows p) ×
      ExtendedPrivateCoordinates p => Function.update z.1.2 j z.1.1.2) :=
    measurable_update'.comp ((measurable_snd.comp measurable_fst).prodMk
      (measurable_snd.comp (measurable_fst.comp measurable_fst)))
  exact (ReferenceCompleteRewardMeasurability.measurable_completeReward_source
    rate rewards C_star C_h).comp
      (((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk hupdate).prodMk
        measurable_snd)

/-- Two parameter integrals give Borel measurability jointly in IDs and row. -/
theorem measurable_fixedRowPrivateExpectedCompleteReward
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (j : Fin (ConstructorDimensions.M p)) :
    Measurable (fun z : IDArray p × CompleteRow p =>
      fixedRowPrivateExpectedCompleteReward rate rewards C_star C_h z.1 j z.2) := by
  have hf := (measurable_updatedCompleteReward rate rewards C_star C_h j).stronglyMeasurable
  have hg := hf.integral_prod_right' (ν := selectedIndexPrivateLaw p j)
  exact (hg.integral_prod_right' (ν := completeRowsMeasure p)).measurable

/-- Every fixed public output has an integrable complete-reward section under
its normalized original-index restriction. -/
theorem integrable_completeReward_selectedIndex
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (published : PublishedOutput p) (j : Fin (ConstructorDimensions.M p)) :
    Integrable (fun e : ExtendedPrivateCoordinates p =>
      ReferenceCompletePhysicalRewards.completeReward rate (published, e) rewards C_star C_h)
        (selectedIndexPrivateLaw p j) := by
  apply Integrable.of_mem_Icc 0 ((p.m : ℝ) * (p.T : ℝ))
    (ReferenceCompleteRewardMeasurability.measurable_completeReward_privateSection
      rate rewards C_star C_h published).aemeasurable
  exact ae_of_all _ fun e =>
    ReferenceCompletePhysicalRewards.completeReward_bounds rate (published, e) rewards C_star C_h

private theorem selectedIndexIntegral_bounds
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (published : PublishedOutput p) (j : Fin (ConstructorDimensions.M p)) :
    (∫ e : ExtendedPrivateCoordinates p,
      ReferenceCompletePhysicalRewards.completeReward rate (published, e) rewards C_star C_h
        ∂selectedIndexPrivateLaw p j) ∈ Set.Icc (0 : ℝ) ((p.m : ℝ) * (p.T : ℝ)) := by
  have hf := integrable_completeReward_selectedIndex rate rewards C_star C_h published j
  constructor
  · exact integral_nonneg (fun e =>
      (ReferenceCompletePhysicalRewards.completeReward_bounds rate
        (published, e) rewards C_star C_h).1)
  · have h := integral_mono hf (integrable_const ((p.m : ℝ) * (p.T : ℝ)))
      (fun e => (ReferenceCompletePhysicalRewards.completeReward_bounds rate
        (published, e) rewards C_star C_h).2)
    simpa only [integral_const, probReal_univ, one_smul] using h

/-- Integrability of the public nuisance-coordinate section, for every pinned row. -/
theorem integrable_selectedIndexIntegral_updatedRows
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (ids : IDArray p) (j : Fin (ConstructorDimensions.M p)) (rho : CompleteRow p) :
    Integrable (fun rows : CompleteRows p => ∫ e : ExtendedPrivateCoordinates p,
      ReferenceCompletePhysicalRewards.completeReward rate
        ((ids, Function.update rows j rho), e) rewards C_star C_h
        ∂selectedIndexPrivateLaw p j) (completeRowsMeasure p) := by
  have hupdate : Measurable (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      Function.update z.1 j rho) := measurable_update_left.comp measurable_fst
  have hf : Measurable (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      ReferenceCompletePhysicalRewards.completeReward rate
        ((ids, Function.update z.1 j rho), z.2) rewards C_star C_h) :=
    (ReferenceCompleteRewardMeasurability.measurable_completeReward_source
      rate rewards C_star C_h).comp
        ((measurable_const.prodMk hupdate).prodMk measurable_snd)
  have hg := hf.stronglyMeasurable.integral_prod_right' (ν := selectedIndexPrivateLaw p j)
  apply Integrable.of_mem_Icc 0 ((p.m : ℝ) * (p.T : ℝ)) hg.measurable.aemeasurable
  exact ae_of_all _ fun rows => selectedIndexIntegral_bounds rate rewards C_star C_h
    (ids, Function.update rows j rho) j

/-- Pointwise physical bounds descend to the everywhere-defined row expectation. -/
theorem fixedRowPrivateExpectedCompleteReward_bounds
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (ids : IDArray p) (j : Fin (ConstructorDimensions.M p)) (rho : CompleteRow p) :
    fixedRowPrivateExpectedCompleteReward rate rewards C_star C_h ids j rho ∈
      Set.Icc (0 : ℝ) ((p.m : ℝ) * (p.T : ℝ)) := by
  have hf := integrable_selectedIndexIntegral_updatedRows rate rewards C_star C_h ids j rho
  constructor
  · exact integral_nonneg (fun rows => (selectedIndexIntegral_bounds rate rewards C_star C_h
      (ids, Function.update rows j rho) j).1)
  · have h := integral_mono hf (integrable_const ((p.m : ℝ) * (p.T : ℝ)))
      (fun rows => (selectedIndexIntegral_bounds rate rewards C_star C_h
        (ids, Function.update rows j rho) j).2)
    simpa only [fixedRowPrivateExpectedCompleteReward, integral_const,
      probReal_univ, one_smul] using h

/-- Integrability on the original whole continuous row law, for every fixed ID array. -/
theorem integrable_fixedRowPrivateExpectedCompleteReward
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (ids : IDArray p) (j : Fin (ConstructorDimensions.M p)) :
    Integrable (fixedRowPrivateExpectedCompleteReward rate rewards C_star C_h ids j)
      (completeRowMeasure p) := by
  apply Integrable.of_mem_Icc 0 ((p.m : ℝ) * (p.T : ℝ))
    ((measurable_fixedRowPrivateExpectedCompleteReward rate rewards C_star C_h j).comp
      (measurable_const.prodMk measurable_id)).aemeasurable
  exact ae_of_all _ fun rho =>
    fixedRowPrivateExpectedCompleteReward_bounds rate rewards C_star C_h ids j rho

/-- The complete reward is integrable on the actual public-fibre/private product. -/
theorem integrable_completeReward_fiberProduct
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (ids : IDArray p) (j : Fin (ConstructorDimensions.M p)) (rho : CompleteRow p) :
    Integrable (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      ReferenceCompletePhysicalRewards.completeReward rate ((ids, z.1), z.2) rewards C_star C_h)
      ((selectedRowPublicFiberLaw p j rho).prod (selectedIndexPrivateLaw p j)) := by
  have hf : Measurable (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      ReferenceCompletePhysicalRewards.completeReward rate ((ids, z.1), z.2)
        rewards C_star C_h) :=
    (ReferenceCompleteRewardMeasurability.measurable_completeReward_source
      rate rewards C_star C_h).comp
        ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  apply Integrable.of_mem_Icc 0 ((p.m : ℝ) * (p.T : ℝ)) hf.aemeasurable
  exact ae_of_all _ fun z => ReferenceCompletePhysicalRewards.completeReward_bounds rate
    ((ids, z.1), z.2) rewards C_star C_h

/-- The nuisance-coordinate definition equals the integral on the genuine public
fibre times the normalized original-private index law. -/
theorem fixedRowPrivateExpectedCompleteReward_eq_fiberProductIntegral
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (ids : IDArray p) (j : Fin (ConstructorDimensions.M p)) (rho : CompleteRow p) :
    fixedRowPrivateExpectedCompleteReward rate rewards C_star C_h ids j rho =
      ∫ z : CompleteRows p × ExtendedPrivateCoordinates p,
        ReferenceCompletePhysicalRewards.completeReward rate ((ids, z.1), z.2) rewards C_star C_h
          ∂(selectedRowPublicFiberLaw p j rho).prod (selectedIndexPrivateLaw p j) := by
  have hf : Measurable (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      ReferenceCompletePhysicalRewards.completeReward rate ((ids, z.1), z.2)
        rewards C_star C_h) :=
    (ReferenceCompleteRewardMeasurability.measurable_completeReward_source
      rate rewards C_star C_h).comp
        ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  rw [integral_prod _ (integrable_completeReward_fiberProduct rate rewards C_star C_h ids j rho)]
  exact (integral_map_of_stronglyMeasurable measurable_update_left
    (hf.stronglyMeasurable.integral_prod_right'
      (ν := selectedIndexPrivateLaw p j))).symm

/-- Locality is produced from the complete physical source-data theorem:
IDs and the entire private tuple are unchanged, and the actual selected row agrees. -/
theorem completeReward_update_eq_on_indexCell
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (ids : IDArray p) (j : Fin (ConstructorDimensions.M p))
    (rows publishedRows : CompleteRows p) (e : ExtendedPrivateCoordinates p)
    (he : e ∈ indexCell p j) :
    ReferenceCompletePhysicalRewards.completeReward rate
      ((ids, Function.update rows j (publishedRows j)), e) rewards C_star C_h =
    ReferenceCompletePhysicalRewards.completeReward rate
      ((ids, publishedRows), e) rewards C_star C_h := by
  exact ReferenceCompletePhysicalRewards.completeReward_eq_of_source_data rate
    ((ids, Function.update rows j (publishedRows j)), e) ((ids, publishedRows), e)
    rewards C_star C_h j rfl rfl he (Function.update_self j (publishedRows j) rows)

/-- Every fixed public family has exactly the constructed selected-row private
expectation, with no almost-everywhere public exception. -/
theorem fixedRowPrivateExpectedCompleteReward_eq_fixedPublicIntegral
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (ids : IDArray p) (j : Fin (ConstructorDimensions.M p)) (rows : CompleteRows p) :
    fixedRowPrivateExpectedCompleteReward rate rewards C_star C_h ids j (rows j) =
      ∫ e : ExtendedPrivateCoordinates p,
        ReferenceCompletePhysicalRewards.completeReward rate ((ids, rows), e) rewards C_star C_h
          ∂selectedIndexPrivateLaw p j := by
  unfold fixedRowPrivateExpectedCompleteReward
  have heq (nuisance : CompleteRows p) :
      (∫ e : ExtendedPrivateCoordinates p,
        ReferenceCompletePhysicalRewards.completeReward rate
          ((ids, Function.update nuisance j (rows j)), e) rewards C_star C_h
          ∂selectedIndexPrivateLaw p j) =
      ∫ e : ExtendedPrivateCoordinates p,
        ReferenceCompletePhysicalRewards.completeReward rate ((ids, rows), e) rewards C_star C_h
          ∂selectedIndexPrivateLaw p j := by
    apply integral_congr_ae
    filter_upwards [ae_selectedIndexPrivateLaw_mem p j] with e he
    exact completeReward_update_eq_on_indexCell rate rewards C_star C_h ids j nuisance rows e he
  simp_rw [heq]
  simp only [integral_const, probReal_univ, one_smul]

/-- The normalized restriction is also the literal scaled original set integral. -/
theorem fixedRowPrivateExpectedCompleteReward_eq_mul_setIntegral
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (ids : IDArray p) (j : Fin (ConstructorDimensions.M p)) (rows : CompleteRows p) :
    fixedRowPrivateExpectedCompleteReward rate rewards C_star C_h ids j (rows j) =
      (ConstructorDimensions.M p : ℝ) *
        ∫ e in indexCell p j,
          ReferenceCompletePhysicalRewards.completeReward rate ((ids, rows), e)
            rewards C_star C_h ∂extendedPrivateLaw p := by
  rw [fixedRowPrivateExpectedCompleteReward_eq_fixedPublicIntegral,
    selectedIndexPrivateLaw, integral_smul_measure, smul_eq_mul,
    ENNReal.toReal_ofReal (Nat.cast_nonneg _)]

/-- The disjoint exhaustive original J cells give the uniform row decomposition
at every public output, with the same rate, table and two constants throughout. -/
theorem completePrivateExpectedReward_eq_uniform_fixedRows
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (published : PublishedOutput p) :
    ReferenceCompleteRewardMeasurability.completePrivateExpectedReward
      rate rewards C_star C_h published =
      (1 / (ConstructorDimensions.M p : ℝ)) *
        ∑ j : Fin (ConstructorDimensions.M p),
          fixedRowPrivateExpectedCompleteReward rate rewards C_star C_h published.1 j
            (published.2 j) := by
  have hdisjoint : Pairwise (fun i j => Disjoint (indexCell p i) (indexCell p j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro e hi hj
    exact hij (hi.symm.trans hj)
  have hcover : (⋃ j, indexCell p j) = Set.univ := by
    ext e
    simp only [Set.mem_iUnion, indexCell, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨coordinatorIndex p e.1.2, rfl⟩
  have hpartition := integral_iUnion_fintype (μ := extendedPrivateLaw p)
    (f := fun e : ExtendedPrivateCoordinates p =>
      ReferenceCompletePhysicalRewards.completeReward rate (published, e) rewards C_star C_h)
    (measurableSet_indexCell p) hdisjoint
    (fun j => (ReferenceCompleteRewardMeasurability.integrable_completeReward_privateSection
      rate rewards C_star C_h published).integrableOn)
  rw [hcover, setIntegral_univ] at hpartition
  rw [ReferenceCompleteRewardMeasurability.completePrivateExpectedReward, hpartition]
  simp_rw [fixedRowPrivateExpectedCompleteReward_eq_mul_setIntegral]
  rw [← Finset.mul_sum, ← mul_assoc, one_div_mul_cancel
    (Nat.cast_ne_zero.mpr (M_pos p).ne' : (ConstructorDimensions.M p : ℝ) ≠ 0), one_mul]

/-- The real reward matrix is precisely the supplied denominator-D grid table. -/
def gridRewardMatrix (p : Parameters)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    FiniteBanditModel.RewardMatrix p.T p.K where
  reward t a := RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t a)
  reward_mem_Icc t a :=
    RealRewardGridCount.realRewardGridValue_mem_Icc (D p) (D_pos p) (rewards t a)

/-- The same best fixed m-set comparator of the actual supplied grid table. -/
def gridComparator (p : Parameters)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) : ℝ :=
  FiniteBanditModel.bestFixedMSetComparator
    (by have := p.two_le_m; omega) p.m_lt_K.le (gridRewardMatrix p rewards)

theorem gridComparator_bounds (p : Parameters)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    gridComparator p rewards ∈ Set.Icc (0 : ℝ) ((p.m : ℝ) * (p.T : ℝ)) :=
  FiniteBanditModel.bestFixedMSetComparator_mem_Icc _ _ _

/-- Private expected complete reference regret on a fixed selected whole row. -/
def fixedRowPrivateExpectedRegret
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (ids : IDArray p) (j : Fin (ConstructorDimensions.M p)) (rho : CompleteRow p) : ℝ :=
  gridComparator p rewards -
    fixedRowPrivateExpectedCompleteReward rate rewards C_star C_h ids j rho

theorem measurable_fixedRowPrivateExpectedRegret
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (j : Fin (ConstructorDimensions.M p)) :
    Measurable (fun z : IDArray p × CompleteRow p =>
      fixedRowPrivateExpectedRegret rate rewards C_star C_h z.1 j z.2) :=
  measurable_const.sub
    (measurable_fixedRowPrivateExpectedCompleteReward rate rewards C_star C_h j)

theorem integrable_fixedRowPrivateExpectedRegret
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (ids : IDArray p) (j : Fin (ConstructorDimensions.M p)) :
    Integrable (fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j)
      (completeRowMeasure p) :=
  (integrable_const _).sub
    (integrable_fixedRowPrivateExpectedCompleteReward rate rewards C_star C_h ids j)

theorem fixedRowPrivateExpectedRegret_bounds
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (ids : IDArray p) (j : Fin (ConstructorDimensions.M p)) (rho : CompleteRow p) :
    fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j rho ∈
      Set.Icc (-((p.m : ℝ) * (p.T : ℝ))) ((p.m : ℝ) * (p.T : ℝ)) := by
  have hH := gridComparator_bounds p rewards
  have hB := fixedRowPrivateExpectedCompleteReward_bounds rate rewards C_star C_h ids j rho
  change -((p.m : ℝ) * (p.T : ℝ)) ≤ gridComparator p rewards - _ ∧
    gridComparator p rewards - _ ≤ (p.m : ℝ) * (p.T : ℝ)
  constructor <;> linarith only [hH.1, hH.2, hB.1, hB.2]

/-- Named fixed-public regret consumer, subtracting from the same comparator. -/
theorem referenceRegret_eq_uniform_fixedRows
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (published : PublishedOutput p) :
    gridComparator p rewards - ReferenceCompleteRewardMeasurability.completePrivateExpectedReward
      rate rewards C_star C_h published =
      (1 / (ConstructorDimensions.M p : ℝ)) *
        ∑ j : Fin (ConstructorDimensions.M p),
          fixedRowPrivateExpectedRegret rate rewards C_star C_h published.1 j (published.2 j) := by
  rw [completePrivateExpectedReward_eq_uniform_fixedRows]
  simp only [fixedRowPrivateExpectedRegret, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_sub, ← mul_assoc, one_div_mul_cancel
    (Nat.cast_ne_zero.mpr (M_pos p).ne' : (ConstructorDimensions.M p : ℝ) ≠ 0), one_mul]

end Bandits.Support.ReferenceCompleteSelectedRowExpectation

end
