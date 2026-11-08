/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionPrecallOverflowSelectedRowLocality
public import Bandits.Support.ReferenceCompleteSelectedRowExpectation

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Original-index pre-call overflow row expectation

The observable is the indicator of the unchanged pre-call overflow event. The
selected-index restriction is the original private tuple restricted to its
actual coordinator-index cell, and a row fibre retains all other whole rows
with their original product law. These identities stop at the selected-row
expectation and its original ID-averaged mean.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceInitializationIndexMixture
open Bandits.Support.ReferenceCompleteSelectedRowExpectation
open scoped BigOperators

namespace Bandits.Support.ReferenceFirstCollectionPrecallOverflowSelectedRowExpectation

variable {p : ConstructorDimensions.Parameters}

/-- The literal indicator of the already defined pre-call overflow event. -/
def precallOverflowIndicator
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) : ℝ := by
  classical
  exact if source ∈ ReferenceFirstCollectionPrecallOverflowBound.precallOverflow
    rate rewards C_star C_h then (1 : ℝ) else 0

theorem measurable_preCallOverflowIndicator
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (precallOverflowIndicator rate rewards C_star C_h) := by
  classical
  change Measurable ((ReferenceFirstCollectionPrecallOverflowBound.precallOverflow
    rate rewards C_star C_h).indicator (fun _ : BootstrapPrivateRoundStreams.SourceInput p =>
      (1 : ℝ)))
  exact measurable_const.indicator
    (ReferenceFirstCollectionPrecallOverflowBound.measurableSet_precallOverflow
      rate rewards C_star C_h control0)

theorem precallOverflowIndicator_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    precallOverflowIndicator rate rewards C_star C_h source ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  simp only [precallOverflowIndicator]
  split <;> norm_num

/-- The nuisance-row integral of the original-index private indicator after
pinning the complete selected row. -/
def selectedRowPrecallOverflowExpectation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (ConstructorDimensions.M p))
    (rho : CompleteRow p) : ℝ :=
  ∫ rows : CompleteRows p, ∫ e : ExtendedPrivateCoordinates p,
    precallOverflowIndicator rate rewards C_star C_h
      ((ids, Function.update rows j rho), e)
      ∂ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j
      ∂completeRowsMeasure p

private theorem measurable_updatedSource
    (j : Fin (ConstructorDimensions.M p)) :
    Measurable (fun z : ((IDArray p × CompleteRow p) × CompleteRows p) ×
        ExtendedPrivateCoordinates p =>
      ((z.1.1.1, Function.update z.1.2 j z.1.1.2), z.2) :
        ((IDArray p × CompleteRow p) × CompleteRows p) × ExtendedPrivateCoordinates p →
          BootstrapPrivateRoundStreams.SourceInput p) := by
  have hupdate : Measurable (fun z : ((IDArray p × CompleteRow p) × CompleteRows p) ×
      ExtendedPrivateCoordinates p => Function.update z.1.2 j z.1.1.2) :=
    measurable_update'.comp ((measurable_snd.comp measurable_fst).prodMk
      (measurable_snd.comp (measurable_fst.comp measurable_fst)))
  exact ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk hupdate).prodMk
    measurable_snd

/-- Joint Borel measurability in the ID array and pinned complete row. -/
theorem measurable_selectedRowPrecallOverflowExpectation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (ConstructorDimensions.M p))
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (fun z : IDArray p × CompleteRow p =>
      selectedRowPrecallOverflowExpectation rate rewards C_star C_h z.1 j z.2) := by
  have hf : Measurable (fun z : ((IDArray p × CompleteRow p) × CompleteRows p) ×
      ExtendedPrivateCoordinates p =>
      precallOverflowIndicator rate rewards C_star C_h
        ((z.1.1.1, Function.update z.1.2 j z.1.1.2), z.2)) :=
    (measurable_preCallOverflowIndicator rate rewards C_star C_h control0).comp
      (measurable_updatedSource j)
  have hg := hf.stronglyMeasurable.integral_prod_right'
    (ν := ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j)
  exact (hg.integral_prod_right' (ν := completeRowsMeasure p)).measurable

private theorem measurable_updatedIndicator
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (ConstructorDimensions.M p))
    (rho : CompleteRow p) (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      precallOverflowIndicator rate rewards C_star C_h
        ((ids, Function.update z.1 j rho), z.2)) := by
  exact (measurable_preCallOverflowIndicator rate rewards C_star C_h control0).comp
    ((measurable_const.prodMk (measurable_update_left.comp measurable_fst)).prodMk
      measurable_snd)

private theorem integrable_selectedIndexIndicatorSection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (ConstructorDimensions.M p))
    (rho : CompleteRow p) (rows : CompleteRows p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (fun e : ExtendedPrivateCoordinates p =>
      precallOverflowIndicator rate rewards C_star C_h
        ((ids, Function.update rows j rho), e))
      (ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j) := by
  apply Integrable.of_mem_Icc 0 1
    ((measurable_updatedIndicator rate rewards C_star C_h ids j rho control0).comp
      (measurable_const.prodMk measurable_id)).aemeasurable
  exact ae_of_all _ fun e => precallOverflowIndicator_bounds rate rewards C_star C_h
    ((ids, Function.update rows j rho), e)

private theorem integrable_updatedRowSection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (ConstructorDimensions.M p))
    (rho : CompleteRow p) (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (fun rows : CompleteRows p =>
      ∫ e : ExtendedPrivateCoordinates p,
        precallOverflowIndicator rate rewards C_star C_h
          ((ids, Function.update rows j rho), e)
          ∂ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j)
      (completeRowsMeasure p) := by
  have hstrong :=
    (measurable_updatedIndicator rate rewards C_star C_h ids j rho control0).stronglyMeasurable
  have hm := hstrong.integral_prod_right'
    (ν := ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j)
  apply Integrable.of_mem_Icc 0 1 hm.measurable.aemeasurable
  exact ae_of_all _ fun rows => by
    have hI := integrable_selectedIndexIndicatorSection
      rate rewards C_star C_h ids j rho rows control0
    constructor
    · exact integral_nonneg fun e =>
        (precallOverflowIndicator_bounds rate rewards C_star C_h
          ((ids, Function.update rows j rho), e)).1
    · have h := integral_mono hI (integrable_const (1 : ℝ)) fun e =>
        (precallOverflowIndicator_bounds rate rewards C_star C_h
          ((ids, Function.update rows j rho), e)).2
      simpa only [integral_const, probReal_univ, one_smul] using h

theorem selectedRowPrecallOverflowExpectation_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (ConstructorDimensions.M p))
    (rho : CompleteRow p) (control0 : ContinuousLearningRows.TimeControl p) :
    selectedRowPrecallOverflowExpectation rate rewards C_star C_h ids j rho ∈
      Set.Icc (0 : ℝ) 1 := by
  have hI := integrable_updatedRowSection rate rewards C_star C_h ids j rho control0
  constructor
  · exact integral_nonneg fun rows => by
      exact integral_nonneg fun e =>
        (precallOverflowIndicator_bounds rate rewards C_star C_h
          ((ids, Function.update rows j rho), e)).1
  · have h := integral_mono hI (integrable_const (1 : ℝ)) fun rows => by
      have hi := integrable_selectedIndexIndicatorSection
        rate rewards C_star C_h ids j rho rows control0
      have hm := integral_mono hi (integrable_const (1 : ℝ)) fun e =>
        (precallOverflowIndicator_bounds rate rewards C_star C_h
          ((ids, Function.update rows j rho), e)).2
      simpa only [integral_const, probReal_univ, one_smul] using hm
    simpa only [selectedRowPrecallOverflowExpectation, integral_const,
      probReal_univ, one_smul] using h

theorem integrable_selectedRowPrecallOverflowExpectation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (ConstructorDimensions.M p))
    (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (selectedRowPrecallOverflowExpectation rate rewards C_star C_h ids j)
      (completeRowMeasure p) := by
  apply Integrable.of_mem_Icc 0 1
    ((measurable_selectedRowPrecallOverflowExpectation
      rate rewards C_star C_h j control0).comp
        (measurable_const.prodMk measurable_id)).aemeasurable
  exact ae_of_all _ fun rho =>
    selectedRowPrecallOverflowExpectation_bounds rate rewards C_star C_h ids j rho control0

private theorem measurable_fixedPublicPrecallOverflowSection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (rows : CompleteRows p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (fun e : ExtendedPrivateCoordinates p =>
      precallOverflowIndicator rate rewards C_star C_h ((ids, rows), e)) := by
  exact (measurable_preCallOverflowIndicator rate rewards C_star C_h control0).comp
    (measurable_const.prodMk measurable_id)

private theorem integrable_fixedPublicPrecallOverflowSection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (rows : CompleteRows p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (fun e : ExtendedPrivateCoordinates p =>
      precallOverflowIndicator rate rewards C_star C_h ((ids, rows), e))
      (extendedPrivateLaw p) := by
  apply Integrable.of_mem_Icc 0 1
    ((measurable_fixedPublicPrecallOverflowSection rate rewards C_star C_h ids rows
      control0).aemeasurable)
  exact ae_of_all _ fun e => precallOverflowIndicator_bounds rate rewards C_star C_h
    ((ids, rows), e)

private theorem integrable_updatedFiberProduct
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (ConstructorDimensions.M p))
    (rho : CompleteRow p) (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      precallOverflowIndicator rate rewards C_star C_h ((ids, z.1), z.2))
      ((ReferenceCompleteSelectedRowExpectation.selectedRowPublicFiberLaw p j rho).prod
        (ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j)) := by
  have hf : Measurable (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      precallOverflowIndicator rate rewards C_star C_h ((ids, z.1), z.2)) :=
    (measurable_preCallOverflowIndicator rate rewards C_star C_h control0).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  apply Integrable.of_mem_Icc 0 1 hf.aemeasurable
  exact ae_of_all _ fun z => precallOverflowIndicator_bounds rate rewards C_star C_h
    ((ids, z.1), z.2)

/-- The selected-row integral is exactly the integral on the genuine product
of the public row fibre and the normalized original-index private law. -/
theorem selectedRowPrecallOverflowExpectation_eq_fiberProductIntegral
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (ConstructorDimensions.M p))
    (rho : CompleteRow p) (control0 : ContinuousLearningRows.TimeControl p) :
    selectedRowPrecallOverflowExpectation rate rewards C_star C_h ids j rho =
      ∫ z : CompleteRows p × ExtendedPrivateCoordinates p,
        precallOverflowIndicator rate rewards C_star C_h ((ids, z.1), z.2)
          ∂(ReferenceCompleteSelectedRowExpectation.selectedRowPublicFiberLaw p j rho).prod
            (ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j) := by
  have hf : Measurable (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      precallOverflowIndicator rate rewards C_star C_h ((ids, z.1), z.2)) :=
    (measurable_preCallOverflowIndicator rate rewards C_star C_h control0).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  rw [selectedRowPrecallOverflowExpectation, integral_prod _
    (integrable_updatedFiberProduct rate rewards C_star C_h ids j rho control0)]
  exact (integral_map_of_stronglyMeasurable measurable_update_left
    (hf.stronglyMeasurable.integral_prod_right'
      (ν := ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j))).symm

private theorem indicator_update_eq_on_indexCell
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (ConstructorDimensions.M p))
    (rows nuisance : CompleteRows p) (e : ExtendedPrivateCoordinates p)
    (he : e ∈ ReferenceCompleteSelectedRowExpectation.indexCell p j) :
    precallOverflowIndicator rate rewards C_star C_h
        ((ids, Function.update nuisance j (rows j)), e) =
      precallOverflowIndicator rate rewards C_star C_h ((ids, rows), e) := by
  have hindex : PrivateSourceStreams.coordinatorIndex p
      (ReferenceInitializationIndexMixture.scalarAndResidual e).1 = j := by
    simpa [ReferenceCompleteSelectedRowExpectation.indexCell,
      ReferenceInitializationIndexMixture.scalarAndResidual] using he
  have hrow : Function.update nuisance j (rows j) j = rows j :=
    Function.update_self j (rows j) nuisance
  have hmem :=
    ReferenceFirstCollectionPrecallOverflowSelectedRowLocality.mem_precallOverflow_iff
      p rate rewards C_star C_h ids (Function.update nuisance j (rows j)) rows
      (ReferenceInitializationIndexMixture.scalarAndResidual e).2
      (ReferenceInitializationIndexMixture.scalarAndResidual e).1
      (ReferenceInitializationIndexMixture.scalarAndResidual e).1 j hindex hindex hrow
  have hsource :
      ((ids, Function.update nuisance j (rows j)), e) ∈
          ReferenceFirstCollectionPrecallOverflowBound.precallOverflow rate rewards C_star C_h ↔
        ((ids, rows), e) ∈
          ReferenceFirstCollectionPrecallOverflowBound.precallOverflow rate rewards C_star C_h := by
    simpa [ReferenceFirstCollectionPrecallOverflowSelectedRowLocality.sourceLeft,
      ReferenceFirstCollectionPrecallOverflowSelectedRowLocality.sourceRight,
      ReferenceInitializationIndexMixture.insertScalarResidual,
      ReferenceInitializationIndexMixture.scalarAndResidual] using hmem
  classical
  simp only [precallOverflowIndicator]
  exact congrArg (fun P : Prop => if P then (1 : ℝ) else 0) (propext hsource)

/-- At every fixed public output, pinning its true row gives the exact
selected-index private expectation. -/
theorem selectedRowPrecallOverflowExpectation_eq_selectedIndexIntegral
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (ConstructorDimensions.M p))
    (rows : CompleteRows p) :
    selectedRowPrecallOverflowExpectation rate rewards C_star C_h ids j (rows j) =
      ∫ e : ExtendedPrivateCoordinates p,
        precallOverflowIndicator rate rewards C_star C_h ((ids, rows), e)
          ∂ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j := by
  unfold selectedRowPrecallOverflowExpectation
  have heq (nuisance : CompleteRows p) :
      (∫ e : ExtendedPrivateCoordinates p,
        precallOverflowIndicator rate rewards C_star C_h
          ((ids, Function.update nuisance j (rows j)), e)
          ∂ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j) =
      ∫ e : ExtendedPrivateCoordinates p,
        precallOverflowIndicator rate rewards C_star C_h ((ids, rows), e)
          ∂ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j := by
    apply integral_congr_ae
    filter_upwards
      [ReferenceCompleteSelectedRowExpectation.ae_selectedIndexPrivateLaw_mem p j]
      with e he
    exact indicator_update_eq_on_indexCell rate rewards C_star C_h ids j rows nuisance e he
  simp_rw [heq]
  simp only [integral_const, probReal_univ, one_smul]

/-- The normalized selected-index integral is the original J-cell set integral
multiplied by the original uniform-index factor. -/
theorem selectedRowPrecallOverflowExpectation_eq_mul_setIntegral
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (ConstructorDimensions.M p))
    (rows : CompleteRows p) :
    selectedRowPrecallOverflowExpectation rate rewards C_star C_h ids j (rows j) =
      (ConstructorDimensions.M p : ℝ) *
        ∫ e in ReferenceCompleteSelectedRowExpectation.indexCell p j,
          precallOverflowIndicator rate rewards C_star C_h ((ids, rows), e)
            ∂extendedPrivateLaw p := by
  rw [selectedRowPrecallOverflowExpectation_eq_selectedIndexIntegral
      rate rewards C_star C_h ids j rows,
    ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw,
    integral_smul_measure, smul_eq_mul,
    ENNReal.toReal_ofReal (Nat.cast_nonneg _)]

/-- The original private expectation at every fixed public output is the
uniform partition over the original coordinator index. -/
theorem precallOverflow_privateExpectation_eq_uniform_selectedRows
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (rows : CompleteRows p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    (∫ e : ExtendedPrivateCoordinates p,
      precallOverflowIndicator rate rewards C_star C_h ((ids, rows), e)
        ∂extendedPrivateLaw p) =
      (1 / (ConstructorDimensions.M p : ℝ)) *
        ∑ j : Fin (ConstructorDimensions.M p),
          selectedRowPrecallOverflowExpectation rate rewards C_star C_h ids j (rows j) := by
  have hdisjoint : Pairwise (fun i j =>
      Disjoint (ReferenceCompleteSelectedRowExpectation.indexCell p i)
        (ReferenceCompleteSelectedRowExpectation.indexCell p j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro e hi hj
    exact hij (hi.symm.trans hj)
  have hcover : (⋃ j : Fin (ConstructorDimensions.M p),
      ReferenceCompleteSelectedRowExpectation.indexCell p j) = Set.univ := by
    ext e
    simp only [Set.mem_iUnion, ReferenceCompleteSelectedRowExpectation.indexCell,
      Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨PrivateSourceStreams.coordinatorIndex p e.1.2, rfl⟩
  have hf := integrable_fixedPublicPrecallOverflowSection
    rate rewards C_star C_h ids rows control0
  have hpartition := integral_iUnion_fintype (μ := extendedPrivateLaw p)
    (f := fun e : ExtendedPrivateCoordinates p =>
      precallOverflowIndicator rate rewards C_star C_h ((ids, rows), e))
    (ReferenceCompleteSelectedRowExpectation.measurableSet_indexCell p) hdisjoint
    (fun j => hf.integrableOn)
  rw [hcover, setIntegral_univ] at hpartition
  rw [hpartition]
  simp_rw [selectedRowPrecallOverflowExpectation_eq_mul_setIntegral
    rate rewards C_star C_h ids _ rows]
  rw [← Finset.mul_sum, ← mul_assoc, one_div_mul_cancel
    (Nat.cast_ne_zero.mpr (ConstructorDimensions.M_pos p).ne' :
      (ConstructorDimensions.M p : ℝ) ≠ 0), one_mul]

/-- The original ID-array law averages the fixed-ID uniform row mean. -/
def originalIDPrecallOverflowRowMean
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) : ℝ :=
  (1 / (ConstructorDimensions.M p : ℝ)) *
    ∑ j : Fin (ConstructorDimensions.M p),
      ∫ rho : CompleteRow p,
        selectedRowPrecallOverflowExpectation rate rewards C_star C_h ids j rho
          ∂completeRowMeasure p

theorem measurable_originalIDPrecallOverflowRowMean
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (originalIDPrecallOverflowRowMean rate rewards C_star C_h) := by
  have hterm (j : Fin (ConstructorDimensions.M p)) :
      Measurable (fun ids : IDArray p =>
        ∫ rho : CompleteRow p,
          selectedRowPrecallOverflowExpectation rate rewards C_star C_h ids j rho
            ∂completeRowMeasure p) :=
    ((measurable_selectedRowPrecallOverflowExpectation
      rate rewards C_star C_h j control0).stronglyMeasurable.integral_prod_right'
        (ν := completeRowMeasure p)).measurable
  have hsum : Measurable (fun ids : IDArray p =>
      ∑ j : Fin (ConstructorDimensions.M p),
        ∫ rho : CompleteRow p,
          selectedRowPrecallOverflowExpectation rate rewards C_star C_h ids j rho
            ∂completeRowMeasure p) := by
    apply Finset.measurable_sum Finset.univ
    intro j hj
    exact hterm j
  change Measurable (fun ids : IDArray p =>
    (1 / (ConstructorDimensions.M p : ℝ)) *
      ∑ j : Fin (ConstructorDimensions.M p),
        ∫ rho : CompleteRow p,
          selectedRowPrecallOverflowExpectation rate rewards C_star C_h ids j rho
            ∂completeRowMeasure p)
  exact measurable_const.mul hsum

theorem originalIDPrecallOverflowRowMean_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    originalIDPrecallOverflowRowMean rate rewards C_star C_h ids ∈ Set.Icc (0 : ℝ) 1 := by
  have hF j rho := selectedRowPrecallOverflowExpectation_bounds
    rate rewards C_star C_h ids j rho control0
  have hmean j :
      (∫ rho : CompleteRow p,
        selectedRowPrecallOverflowExpectation rate rewards C_star C_h ids j rho
          ∂completeRowMeasure p) ∈ Set.Icc (0 : ℝ) 1 := by
    have hI := integrable_selectedRowPrecallOverflowExpectation
      rate rewards C_star C_h ids j control0
    constructor
    · exact integral_nonneg fun rho => (hF j rho).1
    · have h := integral_mono hI (integrable_const (1 : ℝ)) (fun rho => (hF j rho).2)
      simpa only [integral_const, probReal_univ, one_smul] using h
  rw [originalIDPrecallOverflowRowMean]
  constructor
  · apply mul_nonneg
    · positivity
    · exact Finset.sum_nonneg fun j hj => (hmean j).1
  · have hsum :
        (∑ j : Fin (ConstructorDimensions.M p),
          ∫ rho : CompleteRow p,
            selectedRowPrecallOverflowExpectation rate rewards C_star C_h ids j rho
              ∂completeRowMeasure p) ≤ (ConstructorDimensions.M p : ℝ) := by
      have hconst :
          (∑ j : Fin (ConstructorDimensions.M p), (1 : ℝ)) =
            (ConstructorDimensions.M p : ℝ) := by
        classical
        have hconstNat :
            (∑ j : Fin (ConstructorDimensions.M p), (1 : ℕ)) = ConstructorDimensions.M p := by
          simp [Finset.sum_const, Fintype.card_fin]
        exact_mod_cast hconstNat
      have hsum' :
          (∑ j : Fin (ConstructorDimensions.M p),
            ∫ rho : CompleteRow p,
              selectedRowPrecallOverflowExpectation rate rewards C_star C_h ids j rho
                ∂completeRowMeasure p) ≤
            ∑ j : Fin (ConstructorDimensions.M p), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact (hmean j).2
      rw [hconst] at hsum'
      exact hsum'
    have hM : 0 < (ConstructorDimensions.M p : ℝ) :=
      Nat.cast_pos.mpr (ConstructorDimensions.M_pos p)
    have hrecip : 1 / (ConstructorDimensions.M p : ℝ) > 0 := one_div_pos.mpr hM
    calc
      _ = (1 / (ConstructorDimensions.M p : ℝ)) *
          ∑ j : Fin (ConstructorDimensions.M p),
            ∫ rho : CompleteRow p,
              selectedRowPrecallOverflowExpectation rate rewards C_star C_h ids j rho
                ∂completeRowMeasure p := rfl
      _ ≤ (1 / (ConstructorDimensions.M p : ℝ)) * (ConstructorDimensions.M p : ℝ) :=
        mul_le_mul_of_nonneg_left hsum hrecip.le
      _ = 1 := by field_simp

private theorem integrable_privateExpectation_fixedPublic
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (fun z : PublishedOutput p =>
      ∫ e : ExtendedPrivateCoordinates p,
        precallOverflowIndicator rate rewards C_star C_h (z, e)
          ∂extendedPrivateLaw p) (publishedOutputMeasure p) := by
  have hmeas : Measurable (fun z : PublishedOutput p =>
      ∫ e : ExtendedPrivateCoordinates p,
        precallOverflowIndicator rate rewards C_star C_h (z, e)
          ∂extendedPrivateLaw p) := by
    have hf := (measurable_preCallOverflowIndicator rate rewards C_star C_h control0).stronglyMeasurable
    exact (hf.integral_prod_right' (ν := extendedPrivateLaw p)).measurable
  apply Integrable.of_mem_Icc 0 1 hmeas.aemeasurable
  exact ae_of_all _ fun z => by
    have hI := integrable_fixedPublicPrecallOverflowSection rate rewards C_star C_h z.1 z.2
      control0
    constructor
    · exact integral_nonneg fun e => (precallOverflowIndicator_bounds
        rate rewards C_star C_h (z, e)).1
    · have h := integral_mono hI (integrable_const (1 : ℝ)) fun e =>
        (precallOverflowIndicator_bounds rate rewards C_star C_h (z, e)).2
      simpa only [integral_const, probReal_univ, one_smul] using h

private theorem integrable_fixedIDRowAverage
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (fun z : PublishedOutput p =>
      (1 / (ConstructorDimensions.M p : ℝ)) *
        ∑ j : Fin (ConstructorDimensions.M p),
          selectedRowPrecallOverflowExpectation rate rewards C_star C_h z.1 j (z.2 j))
      (publishedOutputMeasure p) := by
  have hmeas : Measurable (fun z : PublishedOutput p =>
      (1 / (ConstructorDimensions.M p : ℝ)) *
        ∑ j : Fin (ConstructorDimensions.M p),
          selectedRowPrecallOverflowExpectation rate rewards C_star C_h z.1 j (z.2 j)) := by
    have hsection : Measurable (fun z : PublishedOutput p =>
        ∫ e : ExtendedPrivateCoordinates p,
          precallOverflowIndicator rate rewards C_star C_h (z, e)
            ∂extendedPrivateLaw p) := by
      have hi := measurable_preCallOverflowIndicator rate rewards C_star C_h control0
      exact (hi.stronglyMeasurable.integral_prod_right'
        (ν := extendedPrivateLaw p)).measurable
    have hEq :
        (fun z : PublishedOutput p =>
          (1 / (ConstructorDimensions.M p : ℝ)) *
            ∑ j : Fin (ConstructorDimensions.M p),
              selectedRowPrecallOverflowExpectation rate rewards C_star C_h z.1 j (z.2 j)) =
        fun z => ∫ e : ExtendedPrivateCoordinates p,
          precallOverflowIndicator rate rewards C_star C_h (z, e)
            ∂extendedPrivateLaw p := by
      funext z
      exact (precallOverflow_privateExpectation_eq_uniform_selectedRows
        rate rewards C_star C_h z.1 z.2 control0).symm
    rw [hEq]
    exact hsection
  apply Integrable.of_mem_Icc 0 1 hmeas.aemeasurable
  exact ae_of_all _ fun z => by
    have hF (j : Fin (ConstructorDimensions.M p)) :
        selectedRowPrecallOverflowExpectation rate rewards C_star C_h z.1 j (z.2 j) ∈
          Set.Icc (0 : ℝ) 1 :=
      selectedRowPrecallOverflowExpectation_bounds rate rewards C_star C_h z.1 j (z.2 j)
        control0
    have hsum0 : 0 ≤ ∑ j : Fin (ConstructorDimensions.M p),
        selectedRowPrecallOverflowExpectation rate rewards C_star C_h z.1 j (z.2 j) :=
      Finset.sum_nonneg fun j hj => (hF j).1
    have hsum1 : ∑ j : Fin (ConstructorDimensions.M p),
        selectedRowPrecallOverflowExpectation rate rewards C_star C_h z.1 j (z.2 j) ≤
          (ConstructorDimensions.M p : ℝ) := by
      have hsum' :
          (∑ j : Fin (ConstructorDimensions.M p),
            selectedRowPrecallOverflowExpectation rate rewards C_star C_h z.1 j (z.2 j)) ≤
            ∑ j : Fin (ConstructorDimensions.M p), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact (hF j).2
      calc
        _ ≤ ∑ j : Fin (ConstructorDimensions.M p), (1 : ℝ) := hsum'
      _ = (ConstructorDimensions.M p : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
    have hM : 0 < (ConstructorDimensions.M p : ℝ) :=
      Nat.cast_pos.mpr (ConstructorDimensions.M_pos p)
    constructor
    · exact mul_nonneg (by positivity) hsum0
    · calc
        _ = (1 / (ConstructorDimensions.M p : ℝ)) *
            ∑ j : Fin (ConstructorDimensions.M p),
              selectedRowPrecallOverflowExpectation rate rewards C_star C_h z.1 j (z.2 j) := rfl
        _ ≤ (1 / (ConstructorDimensions.M p : ℝ)) * (ConstructorDimensions.M p : ℝ) :=
          mul_le_mul_of_nonneg_left hsum1 (one_div_pos.mpr hM).le
        _ = 1 := by field_simp

/-- Exact reconstruction of the original source-input event probability by
the original ID-array law and the uniform selected-row mean. -/
theorem originalSourcePrecallOverflow_measureReal_eq_IDArrayRowMean
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (ReferenceFirstCollectionPrecallOverflowBound.precallOverflow rate rewards C_star C_h) =
      ∫ ids : IDArray p,
        originalIDPrecallOverflowRowMean rate rewards C_star C_h ids
          ∂idArrayMeasure p := by
  let I : BootstrapPrivateRoundStreams.SourceInput p → ℝ :=
    precallOverflowIndicator rate rewards C_star C_h
  have hI : Measurable I := measurable_preCallOverflowIndicator
    rate rewards C_star C_h control0
  have hIint : Integrable I (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
    apply Integrable.of_mem_Icc 0 1 hI.aemeasurable
    exact ae_of_all _ fun source => precallOverflowIndicator_bounds
      rate rewards C_star C_h source
  have hmeasEvent := ReferenceFirstCollectionPrecallOverflowBound.measurableSet_precallOverflow
    rate rewards C_star C_h control0
  rw [← integral_indicator_one hmeasEvent]
  change ∫ source : BootstrapPrivateRoundStreams.SourceInput p,
      I source ∂BootstrapPrivateRoundStreams.sourceInputLaw p = _
  rw [BootstrapPrivateRoundStreams.sourceInputLaw]
  rw [integral_prod _ hIint]
  have hrowavg := integrable_fixedIDRowAverage rate rewards C_star C_h control0
  have hEqPublic (z : PublishedOutput p) :
      (∫ e : ExtendedPrivateCoordinates p, I (z, e) ∂extendedPrivateLaw p) =
        (1 / (ConstructorDimensions.M p : ℝ)) *
          ∑ j : Fin (ConstructorDimensions.M p),
            selectedRowPrecallOverflowExpectation rate rewards C_star C_h z.1 j (z.2 j) := by
    exact precallOverflow_privateExpectation_eq_uniform_selectedRows
      rate rewards C_star C_h z.1 z.2 control0
  simp_rw [hEqPublic]
  rw [publishedOutputMeasure]
  rw [integral_prod _ hrowavg]
  congr 1
  funext ids
  rw [integral_const_mul]
  rw [integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    change (∫ a : CompleteRows p,
        selectedRowPrecallOverflowExpectation rate rewards C_star C_h ids j (a j)
          ∂completeRowsMeasure p) =
      ∫ rho : CompleteRow p,
        selectedRowPrecallOverflowExpectation rate rewards C_star C_h ids j rho
          ∂completeRowMeasure p
    have hFint := integrable_selectedRowPrecallOverflowExpectation
      rate rewards C_star C_h ids j control0
    have hFae : AEStronglyMeasurable
        (fun rho : CompleteRow p =>
          selectedRowPrecallOverflowExpectation rate rewards C_star C_h ids j rho)
        ((completeRowsMeasure p).map (fun a : CompleteRows p => a j)) := by
      simpa only [map_completeRowProjection] using hFint.aestronglyMeasurable
    rw [← integral_map (measurable_completeRowProjection p j).aemeasurable hFae,
      map_completeRowProjection]
  · intro j hj
    exact (measurePreserving_completeRowProjection p j).integrable_comp_of_integrable
      (integrable_selectedRowPrecallOverflowExpectation
        rate rewards C_star C_h ids j control0)

/-- The reconstructed original event inherits only the original ID-averaged
inverse-square bound. -/
theorem originalSourcePrecallOverflow_measureReal_le_inv_N_sq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (ReferenceFirstCollectionPrecallOverflowBound.precallOverflow rate rewards C_star C_h) ≤
      1 / (ConstructorDimensions.N p : ℝ) ^ 2 := by
  calc
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (ReferenceFirstCollectionPrecallOverflowBound.precallOverflow rate rewards C_star C_h) =
        ∫ ids : IDArray p,
          originalIDPrecallOverflowRowMean rate rewards C_star C_h ids
            ∂idArrayMeasure p :=
      originalSourcePrecallOverflow_measureReal_eq_IDArrayRowMean
        rate rewards C_star C_h control0
    _ ≤ 1 / (ConstructorDimensions.N p : ℝ) ^ 2 :=
      by
        have hb := ReferenceFirstCollectionPrecallOverflowBound.precallOverflow_measureReal_le_inv_N_sq
          rate rewards C_star C_h control0
        rw [originalSourcePrecallOverflow_measureReal_eq_IDArrayRowMean
          rate rewards C_star C_h control0] at hb
        exact hb

end Bandits.Support.ReferenceFirstCollectionPrecallOverflowSelectedRowExpectation

end
