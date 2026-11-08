/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionPrecallOverflowSelectedRowExpectation
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Literal fixed-ID section of the original source law

The section law pins only the original shared identification array.  It keeps
the full independent complete-row product and every coordinate of the original
private product.  It is a genuine section of `sourceInputLaw`, with no
conditioning or redraw of continuous coordinates.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceCompleteSelectedRowExpectation
open Bandits.Support.ReferenceFirstCollectionPrecallOverflowBound
open Bandits.Support.ReferenceFirstCollectionPrecallOverflowSelectedRowExpectation
open scoped BigOperators
open scoped ENNReal

namespace Bandits.Support.ReferenceFixedIDSourceSection

variable {p : ConstructorDimensions.Parameters}

/-- The literal section of the original source carrier with shared ID `ids`. -/
def fixedIDSourceSection (ids : IDArray p) :
    Set (BootstrapPrivateRoundStreams.SourceInput p) :=
  {z | z.1.1 = ids}

/-- Insert a fixed shared ID into the original whole-row/private product. -/
def fixedIDSourceInsertion (ids : IDArray p) :
    CompleteRows p × ExtendedPrivateCoordinates p → SourceInput p :=
  fun w => ((ids, w.1), w.2)

theorem measurable_fixedIDSourceSection (ids : IDArray p) :
    MeasurableSet (fixedIDSourceSection (p := p) ids) := by
  exact (measurable_fst.comp measurable_fst) (measurableSet_singleton ids)

theorem measurable_fixedIDSourceInsertion (ids : IDArray p) :
    Measurable (fixedIDSourceInsertion (p := p) ids) := by
  exact ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)

/-- The section law is the image of the original complete-row and private
product under literal insertion of the fixed shared ID array. -/
noncomputable def fixedIDSourceLaw (ids : IDArray p) :
    Measure (SourceInput p) :=
  (completeRowsMeasure p).prod (extendedPrivateLaw p) |>.map
    (fixedIDSourceInsertion (p := p) ids)

/-- The map definition is exactly the product of the existing fixed-ID
published-output law and the unchanged original private law. -/
theorem fixedIDSourceLaw_eq_fixedIDPublishedOutputProduct (ids : IDArray p) :
    fixedIDSourceLaw (p := p) ids =
      (CompletePublicTable.fixedIDPublishedOutputMeasure p ids).prod
        (extendedPrivateLaw p) := by
  change ((completeRowsMeasure p).prod (extendedPrivateLaw p)).map
      (Prod.map (fun rows : CompleteRows p => (ids, rows)) id) = _
  calc
    _ = ((completeRowsMeasure p).map (fun rows : CompleteRows p => (ids, rows))).prod
        ((extendedPrivateLaw p).map id) :=
      (Measure.map_prod_map _ _ (measurable_const.prodMk measurable_id) measurable_id).symm
    _ = (CompletePublicTable.fixedIDPublishedOutputMeasure p ids).prod
        (extendedPrivateLaw p) := by
      rw [← Measure.dirac_prod ids]
      simp [CompletePublicTable.fixedIDPublishedOutputMeasure,
        CompletePublicTable.fixedIDCompleteRowsMeasure, Measure.map_id]

instance fixedIDSourceLaw_probability (ids : IDArray p) :
    IsProbabilityMeasure (fixedIDSourceLaw (p := p) ids) := by
  rw [fixedIDSourceLaw_eq_fixedIDPublishedOutputProduct]
  infer_instance

/-- Every fixed ID has positive mass under the literal nested fair-bit product. -/
theorem idArrayAtom_positive (ids : IDArray p) :
    0 < (idArrayMeasure p).real {ids} := by
  classical
  have hmass : idArrayMeasure p {ids} ≠ 0 := by
    rw [idArrayMeasure, Measure.pi_singleton]
    apply Finset.prod_ne_zero_iff.mpr
    intro u hu
    rw [Measure.pi_singleton]
    apply Finset.prod_ne_zero_iff.mpr
    intro t ht
    have hbit : CompletePublicTable.fairBitLaw {ids u t} ≠ 0 := by
      have hreal : CompletePublicTable.fairBitLaw.real {ids u t} ≠ 0 := by
        cases ids u t <;> simp
      exact (measureReal_ne_zero_iff (ne_of_lt (measure_lt_top _ _))).mp hreal
    exact hbit
  have hfinite : idArrayMeasure p {ids} < ∞ := measure_lt_top _ _
  have hpos : 0 < idArrayMeasure p {ids} := bot_lt_iff_ne_bot.mpr hmass
  exact ENNReal.toReal_pos_iff.mpr ⟨hpos, hfinite⟩

/-- The ENNReal atom used to scale the literal section. -/
theorem idArrayAtom_lt_top (ids : IDArray p) :
    idArrayMeasure p {ids} < ∞ :=
  measure_lt_top _ _

private theorem idArrayAtom_restrict_singleton (ids : IDArray p) :
    (idArrayMeasure p).restrict {ids} =
      idArrayMeasure p {ids} • Measure.dirac ids := by
  classical
  ext s hs
  rw [Measure.restrict_apply hs,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
  by_cases hids : ids ∈ s <;> simp [hids]

/-- Restricting the original source law to the fixed-ID section gives the
positive original ID atom times the literal section law. -/
theorem sourceInputLaw_restrict_fixedIDSourceSection (ids : IDArray p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (fixedIDSourceSection (p := p) ids) =
      idArrayMeasure p {ids} • fixedIDSourceLaw (p := p) ids := by
  have hrect : fixedIDSourceSection (p := p) ids =
      (({ids} : Set (IDArray p)) ×ˢ (Set.univ : Set (CompleteRows p))) ×ˢ
        (Set.univ : Set (ExtendedPrivateCoordinates p)) := by
    ext z
    simp [fixedIDSourceSection]
  have hrestrict :
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          (fixedIDSourceSection (p := p) ids) =
        (((idArrayMeasure p).restrict {ids}).prod (completeRowsMeasure p)).prod
          (extendedPrivateLaw p) := by
    rw [hrect, BootstrapPrivateRoundStreams.sourceInputLaw,
      CompletePublicTable.publishedOutputMeasure,
      ← Measure.prod_restrict, ← Measure.restrict_prod_eq_prod_univ]
    simp only [Measure.restrict_univ]
  calc
    _ = (((idArrayMeasure p).restrict {ids}).prod (completeRowsMeasure p)).prod
        (extendedPrivateLaw p) := hrestrict
    _ = ((idArrayMeasure p {ids} • Measure.dirac ids).prod
        (completeRowsMeasure p)).prod (extendedPrivateLaw p) := by
          rw [idArrayAtom_restrict_singleton]
    _ = idArrayMeasure p {ids} •
        ((Measure.dirac ids).prod (completeRowsMeasure p)).prod
          (extendedPrivateLaw p) := by
          rw [Measure.prod_smul_left, Measure.prod_smul_left]
    _ = idArrayMeasure p {ids} • fixedIDSourceLaw (p := p) ids := by
          rw [fixedIDSourceLaw_eq_fixedIDPublishedOutputProduct]
          rfl

/-- The fixed-ID section has exactly the mass of its ID atom. -/
theorem sourceInputLaw_real_fixedIDSourceSection (ids : IDArray p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (fixedIDSourceSection (p := p) ids) = (idArrayMeasure p).real {ids} := by
  rw [← measureReal_restrict_apply_univ,
    sourceInputLaw_restrict_fixedIDSourceSection,
    measureReal_ennreal_smul_apply]
  simp [Measure.real]

/-- A generic set-probability transport identity on the original source
carrier, suitable for dividing a localized bound by the positive ID atom. -/
theorem sourceInputLaw_real_inter_fixedIDSourceSection (ids : IDArray p)
    (E : Set (SourceInput p)) (hE : MeasurableSet E) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (fixedIDSourceSection (p := p) ids ∩ E) =
      (idArrayMeasure p).real {ids} * (fixedIDSourceLaw (p := p) ids).real E := by
  calc
    _ = ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (fixedIDSourceSection (p := p) ids)).real E := by
          rw [measureReal_restrict_apply hE, Set.inter_comm]
    _ = (idArrayMeasure p {ids} • fixedIDSourceLaw (p := p) ids).real E := by
          rw [sourceInputLaw_restrict_fixedIDSourceSection]
    _ = (idArrayMeasure p).real {ids} *
        (fixedIDSourceLaw (p := p) ids).real E := by
          rw [measureReal_ennreal_smul_apply]
          rfl

/-- Dividing the localized event mass by the strictly positive original ID
atom recovers its probability under the literal fixed-ID section law. -/
theorem fixedIDSourceLaw_real_eq_section_probability (ids : IDArray p)
    (E : Set (SourceInput p)) (hE : MeasurableSet E) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (fixedIDSourceSection (p := p) ids ∩ E) /
          (BootstrapPrivateRoundStreams.sourceInputLaw p).real
            (fixedIDSourceSection (p := p) ids) =
      (fixedIDSourceLaw (p := p) ids).real E := by
  rw [sourceInputLaw_real_inter_fixedIDSourceSection ids E hE,
    sourceInputLaw_real_fixedIDSourceSection]
  have hpos := idArrayAtom_positive (p := p) ids
  field_simp [ne_of_gt hpos]

/-- Integrating over the original fixed-ID section multiplies the section-law
integral by the original ID atom mass. -/
theorem sourceInputLaw_setIntegral_fixedIDSourceSection (ids : IDArray p)
    (f : SourceInput p → ℝ) :
    (∫ z in fixedIDSourceSection (p := p) ids, f z
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p) =
      (idArrayMeasure p).real {ids} *
        ∫ z, f z ∂fixedIDSourceLaw (p := p) ids := by
  rw [sourceInputLaw_restrict_fixedIDSourceSection, integral_smul_measure]
  rfl

/-- Change of variables for the literal fixed-ID insertion map. -/
theorem fixedIDSourceLaw_integral_eq_insertion (ids : IDArray p)
    (f : SourceInput p → ℝ)
    (hf : Integrable f (fixedIDSourceLaw (p := p) ids)) :
    (∫ z, f z ∂fixedIDSourceLaw (p := p) ids) =
      ∫ w, f (fixedIDSourceInsertion (p := p) ids w)
        ∂(completeRowsMeasure p).prod (extendedPrivateLaw p) := by
  rw [fixedIDSourceLaw]
  exact integral_map (measurable_fixedIDSourceInsertion (p := p) ids).aemeasurable
    hf.aestronglyMeasurable

/-- The selected-row kernel averaged over the original private product is
exactly its source-defined uniform average over the whole complete rows. -/
theorem fixedIDSourceLaw_precallOverflow_eq_originalIDRowMean
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (ids : IDArray p) :
    (fixedIDSourceLaw (p := p) ids).real
        (ReferenceFirstCollectionPrecallOverflowBound.precallOverflow
          rate rewards C_star C_h) =
      originalIDPrecallOverflowRowMean rate rewards C_star C_h ids := by
  have hevent := measurableSet_precallOverflow rate rewards C_star C_h control0
  have hI : Measurable
      (precallOverflowIndicator rate rewards C_star C_h) :=
    measurable_preCallOverflowIndicator rate rewards C_star C_h control0
  have hIint : Integrable
      (precallOverflowIndicator rate rewards C_star C_h)
      (fixedIDSourceLaw (p := p) ids) := by
    apply Integrable.of_mem_Icc 0 1 hI.aemeasurable
    exact ae_of_all _ fun z => precallOverflowIndicator_bounds rate rewards C_star C_h z
  rw [← integral_indicator_one hevent]
  change (∫ z, precallOverflowIndicator rate rewards C_star C_h z
      ∂fixedIDSourceLaw (p := p) ids) = _
  rw [fixedIDSourceLaw_integral_eq_insertion (p := p) ids _ hIint]
  have hcompMeas : Measurable (fun w : CompleteRows p × ExtendedPrivateCoordinates p =>
      precallOverflowIndicator rate rewards C_star C_h
          (fixedIDSourceInsertion (p := p) ids w)) :=
    hI.comp (measurable_fixedIDSourceInsertion (p := p) ids)
  have hcompInt : Integrable (fun w : CompleteRows p × ExtendedPrivateCoordinates p =>
      precallOverflowIndicator rate rewards C_star C_h
          (fixedIDSourceInsertion (p := p) ids w))
      ((completeRowsMeasure p).prod (extendedPrivateLaw p)) := by
    apply Integrable.of_mem_Icc 0 1 hcompMeas.aemeasurable
    exact ae_of_all _ fun w => precallOverflowIndicator_bounds rate rewards C_star C_h
      (fixedIDSourceInsertion (p := p) ids w)
  rw [integral_prod _ hcompInt]
  simp_rw [fixedIDSourceInsertion,
    precallOverflow_privateExpectation_eq_uniform_selectedRows
      rate rewards C_star C_h ids _ control0]
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    change (∫ rows : CompleteRows p,
        selectedRowPrecallOverflowExpectation rate rewards C_star C_h ids j (rows j)
          ∂completeRowsMeasure p) =
      ∫ rho : CompleteRow p,
        selectedRowPrecallOverflowExpectation rate rewards C_star C_h ids j rho
          ∂completeRowMeasure p
    have hFint := integrable_selectedRowPrecallOverflowExpectation
      rate rewards C_star C_h ids j control0
    have hFae : AEStronglyMeasurable
        (fun rho : CompleteRow p =>
          selectedRowPrecallOverflowExpectation rate rewards C_star C_h ids j rho)
        ((completeRowsMeasure p).map fun rows : CompleteRows p => rows j) := by
      simpa only [map_completeRowProjection] using hFint.aestronglyMeasurable
    rw [← integral_map (measurable_completeRowProjection p j).aemeasurable hFae,
      map_completeRowProjection]
  · intro j hj
    exact (measurePreserving_completeRowProjection p j).integrable_comp_of_integrable
      (integrable_selectedRowPrecallOverflowExpectation
        rate rewards C_star C_h ids j control0)

end Bandits.Support.ReferenceFixedIDSourceSection

end
