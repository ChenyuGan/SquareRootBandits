/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteSelectedRowLocality
public import Bandits.Support.ReferenceCompleteSelectedRowExpectation
public import Bandits.Support.ReferenceGeneratedSavedWrongEvent

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Selected-whole-row probability of saved wrong diagnostics

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`,
`05_binary_transport.tex:20-55`, `07_public_setup.tex:123-164`,
`08_main_theorem.tex:29-50,67-75`, and `06_interruptions.tex:355-362`,
all under `sources/zip4/manuscript/`.

The event here is exactly the existing saved-wrong diagnostic event on the
complete physical suffix, with an arbitrary chronological prefix count. It is
not identified with the manuscript's overflow-stopped decoder event. The
probability is a literal nuisance-row average under the normalized restriction
of the original extended private law to its actual J cell. Locality removes
that nuisance average at every fixed public output, including null rows.

This internal component supplies a measurable row probability for the original
ID-integrated decoder-tail and subsequent whole-row concentration consumers.
It asserts no quantitative decoder bound or manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.PrivateSourceStreams (coordinatorIndex)
open Bandits.Support.ReferenceCompleteSelectedRowExpectation
open scoped ENNReal

namespace Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p

variable {p : Parameters}

/-- Exact wrong-diagnostic projection of the already computed round evidence:
UP uses the saved coordinator flag and DOWN uses the saved follower cuts. -/
def savedWrongEvidenceFlag {rate : RateInput p}
    (evidence : ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate)) : Bool := by
  classical
  exact decide
    ((∃ diagnostic, evidence.coordinator.up = some diagnostic ∧
        diagnostic.wrongUniqueAccepted = true) ∨
      (∃ i cut, (evidence.followers i).down = some cut ∧
        ReferenceDownReception.wrongUniqueAccepted cut))

/-- Projecting actual evidence reproduces the existing record flag exactly. -/
theorem savedWrongEvidenceFlag_record {rate : RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    savedWrongEvidenceFlag record.evidence =
      ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag record := by
  classical
  unfold savedWrongEvidenceFlag ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag
  apply decide_eq_decide.mpr
  rfl

/-- Prefix-any on evidence is the existing Boolean on actual records. -/
theorem savedWrongSuffixPrefixCode_eq_evidenceAny
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (source : SourceInput p) :
    ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixCode
        rate rewards C_star C_h k source =
      ((ReferenceCompletePhysicalHistory.completeSuffixEvidence
        rate source rewards C_star C_h).take k).any savedWrongEvidenceFlag := by
  simp only [ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixCode,
    ReferenceCompletePhysicalHistory.completeSuffixEvidence, ← List.map_take,
    List.any_map, Function.comp_def, savedWrongEvidenceFlag_record]

/-- Pointwise whole-row and same-J-cell locality; the original scalar may
change inside its cell while all residual private coordinates stay literal. -/
theorem savedWrongSuffixPrefixCode_eq_of_selectedRow
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (ids : IDArray p) (R S : CompleteRows p)
    (q : ReferenceInitializationIndexMixture.PrivateResidual p)
    (s t : ContinuousCategorical.Scalar) (j : Fin (M p))
    (hs : coordinatorIndex p s = j) (ht : coordinatorIndex p t = j)
    (hrow : R j = S j) :
    ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixCode rate rewards C_star C_h k
        ((ids, R), ReferenceInitializationIndexMixture.insertScalarResidual (s, q)) =
      ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixCode rate rewards C_star C_h k
        ((ids, S), ReferenceInitializationIndexMixture.insertScalarResidual (t, q)) := by
  rw [savedWrongSuffixPrefixCode_eq_evidenceAny,
    savedWrongSuffixPrefixCode_eq_evidenceAny,
    ReferenceCompleteSelectedRowLocality.completeSuffixEvidence_eq
      p rate rewards C_star C_h ids R S q s t j hs ht hrow]

/-- The existing event itself has the same pointwise selected-row locality. -/
theorem savedWrongSuffixPrefixEvent_iff_of_selectedRow
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (ids : IDArray p) (R S : CompleteRows p)
    (q : ReferenceInitializationIndexMixture.PrivateResidual p)
    (s t : ContinuousCategorical.Scalar) (j : Fin (M p))
    (hs : coordinatorIndex p s = j) (ht : coordinatorIndex p t = j)
    (hrow : R j = S j) :
    ((ids, R), ReferenceInitializationIndexMixture.insertScalarResidual (s, q)) ∈
        ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
          rate rewards C_star C_h k ↔
      ((ids, S), ReferenceInitializationIndexMixture.insertScalarResidual (t, q)) ∈
        ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
          rate rewards C_star C_h k := by
  change _ = true ↔ _ = true
  rw [savedWrongSuffixPrefixCode_eq_of_selectedRow
    rate rewards C_star C_h k ids R S q s t j hs ht hrow]

/-- The real 0/1 indicator of precisely the existing original-source event. -/
def savedWrongIndicator
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) : SourceInput p → ℝ :=
  (ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
    rate rewards C_star C_h k).indicator (fun _ => 1)

theorem savedWrongIndicator_bounds
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (source : SourceInput p) :
    savedWrongIndicator rate rewards C_star C_h k source ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  by_cases h : source ∈ ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
      rate rewards C_star C_h k <;>
    simp [savedWrongIndicator, h]

/-- Borelness is produced by the admitted event theorem, without a premise. -/
theorem measurable_savedWrongIndicator
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) :
    Measurable (savedWrongIndicator rate rewards C_star C_h k) :=
  measurable_const.indicator
    (ReferenceGeneratedSavedWrongEvent.measurableSet_savedWrongSuffixPrefixEvent
      (rate := rate) rewards C_star C_h k)

/-- Pointwise indicator locality with the same full residual private arrays. -/
theorem savedWrongIndicator_eq_of_selectedRow
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (ids : IDArray p) (R S : CompleteRows p)
    (q : ReferenceInitializationIndexMixture.PrivateResidual p)
    (s t : ContinuousCategorical.Scalar) (j : Fin (M p))
    (hs : coordinatorIndex p s = j) (ht : coordinatorIndex p t = j)
    (hrow : R j = S j) :
    savedWrongIndicator rate rewards C_star C_h k
        ((ids, R), ReferenceInitializationIndexMixture.insertScalarResidual (s, q)) =
      savedWrongIndicator rate rewards C_star C_h k
        ((ids, S), ReferenceInitializationIndexMixture.insertScalarResidual (t, q)) := by
  classical
  have h := savedWrongSuffixPrefixEvent_iff_of_selectedRow
    rate rewards C_star C_h k ids R S q s t j hs ht hrow
  simp only [savedWrongIndicator, Set.indicator_apply]
  rw [h]

/-- Inserting a whole selected row leaves the actual indicator unchanged on
its original index cell. No source or raw-record equality is assumed. -/
theorem savedWrongIndicator_update_eq_on_indexCell
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (ids : IDArray p) (j : Fin (M p))
    (rows publishedRows : CompleteRows p) (e : ExtendedPrivateCoordinates p)
    (he : e ∈ indexCell p j) :
    savedWrongIndicator rate rewards C_star C_h k
        ((ids, Function.update rows j (publishedRows j)), e) =
      savedWrongIndicator rate rewards C_star C_h k ((ids, publishedRows), e) := by
  have h := savedWrongIndicator_eq_of_selectedRow rate rewards C_star C_h k ids
    (Function.update rows j (publishedRows j)) publishedRows
    (e.1.1, e.2) e.1.2 e.1.2 j he he (Function.update_self j (publishedRows j) rows)
  exact h

/-- Literal parameter integral: original nuisance rows, original normalized
J restriction, and the existing original-source event indicator. -/
def fixedRowPrivateProbability
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ)
    (ids : IDArray p) (j : Fin (M p)) (rho : CompleteRow p) : ℝ :=
  ∫ rows : CompleteRows p, ∫ e : ExtendedPrivateCoordinates p,
    savedWrongIndicator rate rewards C_star C_h k
      ((ids, Function.update rows j rho), e)
      ∂selectedIndexPrivateLaw p j ∂completeRowsMeasure p

/-- The whole-row update is jointly measurable on the actual continuous
carriers, including the full original extended private coordinate. -/
theorem measurable_updatedSavedWrongIndicator
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (j : Fin (M p)) :
    Measurable (fun z : ((IDArray p × CompleteRow p) × CompleteRows p) ×
        ExtendedPrivateCoordinates p =>
      savedWrongIndicator rate rewards C_star C_h k
        ((z.1.1.1, Function.update z.1.2 j z.1.1.2), z.2)) := by
  have hupdate : Measurable (fun z : ((IDArray p × CompleteRow p) × CompleteRows p) ×
      ExtendedPrivateCoordinates p => Function.update z.1.2 j z.1.1.2) :=
    measurable_update'.comp ((measurable_snd.comp measurable_fst).prodMk
      (measurable_snd.comp (measurable_fst.comp measurable_fst)))
  exact (measurable_savedWrongIndicator rate rewards C_star C_h k).comp
    (((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk hupdate).prodMk
      measurable_snd)

/-- The probability is jointly Borel in the original IDs and whole selected row. -/
theorem measurable_fixedRowPrivateProbability
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (j : Fin (M p)) :
    Measurable (fun z : IDArray p × CompleteRow p =>
      fixedRowPrivateProbability rate rewards C_star C_h k z.1 j z.2) := by
  have hf := (measurable_updatedSavedWrongIndicator
    rate rewards C_star C_h k j).stronglyMeasurable
  have hg := hf.integral_prod_right' (ν := selectedIndexPrivateLaw p j)
  exact (hg.integral_prod_right' (ν := completeRowsMeasure p)).measurable

/-- Every fixed public section is Borel on the original private carrier. -/
theorem measurable_savedWrongIndicator_privateSection
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (published : PublishedOutput p) :
    Measurable (fun e : ExtendedPrivateCoordinates p =>
      savedWrongIndicator rate rewards C_star C_h k (published, e)) :=
  (measurable_savedWrongIndicator rate rewards C_star C_h k).comp
    (measurable_const.prodMk measurable_id)

/-- Integrability for every fixed public output under the original private law. -/
theorem integrable_savedWrongIndicator_privateSection
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (published : PublishedOutput p) :
    Integrable (fun e : ExtendedPrivateCoordinates p =>
      savedWrongIndicator rate rewards C_star C_h k (published, e)) (extendedPrivateLaw p) := by
  apply Integrable.of_mem_Icc 0 1
    (measurable_savedWrongIndicator_privateSection rate rewards C_star C_h k published).aemeasurable
  exact ae_of_all _ fun e => savedWrongIndicator_bounds rate rewards C_star C_h k (published, e)

/-- Integrability for every normalized J section, including all null outcomes. -/
theorem integrable_savedWrongIndicator_selectedIndex
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (published : PublishedOutput p) (j : Fin (M p)) :
    Integrable (fun e : ExtendedPrivateCoordinates p =>
      savedWrongIndicator rate rewards C_star C_h k (published, e))
        (selectedIndexPrivateLaw p j) := by
  apply Integrable.of_mem_Icc 0 1
    (measurable_savedWrongIndicator_privateSection rate rewards C_star C_h k published).aemeasurable
  exact ae_of_all _ fun e => savedWrongIndicator_bounds rate rewards C_star C_h k (published, e)

private theorem selectedIndexIntegral_bounds
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (published : PublishedOutput p) (j : Fin (M p)) :
    (∫ e : ExtendedPrivateCoordinates p,
      savedWrongIndicator rate rewards C_star C_h k (published, e)
        ∂selectedIndexPrivateLaw p j) ∈ Set.Icc (0 : ℝ) 1 := by
  have hf := integrable_savedWrongIndicator_selectedIndex rate rewards C_star C_h k published j
  constructor
  · exact integral_nonneg (fun e =>
      (savedWrongIndicator_bounds rate rewards C_star C_h k (published, e)).1)
  · have h := integral_mono hf (integrable_const (1 : ℝ))
      (fun e => (savedWrongIndicator_bounds rate rewards C_star C_h k (published, e)).2)
    simpa only [integral_const, probReal_univ, one_smul] using h

/-- Integrability of the nuisance-row section for every fixed row and ID array. -/
theorem integrable_selectedIndexIntegral_updatedRows
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ)
    (ids : IDArray p) (j : Fin (M p)) (rho : CompleteRow p) :
    Integrable (fun rows : CompleteRows p => ∫ e : ExtendedPrivateCoordinates p,
      savedWrongIndicator rate rewards C_star C_h k
        ((ids, Function.update rows j rho), e) ∂selectedIndexPrivateLaw p j)
      (completeRowsMeasure p) := by
  have hupdate : Measurable (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      Function.update z.1 j rho) := measurable_update_left.comp measurable_fst
  have hf : Measurable (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      savedWrongIndicator rate rewards C_star C_h k
        ((ids, Function.update z.1 j rho), z.2)) :=
    (measurable_savedWrongIndicator rate rewards C_star C_h k).comp
      ((measurable_const.prodMk hupdate).prodMk measurable_snd)
  have hg := hf.stronglyMeasurable.integral_prod_right' (ν := selectedIndexPrivateLaw p j)
  apply Integrable.of_mem_Icc 0 1 hg.measurable.aemeasurable
  exact ae_of_all _ fun rows => selectedIndexIntegral_bounds rate rewards C_star C_h k
    (ids, Function.update rows j rho) j

/-- The literal row probability lies in [0,1] at every whole row. -/
theorem fixedRowPrivateProbability_bounds
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ)
    (ids : IDArray p) (j : Fin (M p)) (rho : CompleteRow p) :
    fixedRowPrivateProbability rate rewards C_star C_h k ids j rho ∈ Set.Icc (0 : ℝ) 1 := by
  have hf := integrable_selectedIndexIntegral_updatedRows rate rewards C_star C_h k ids j rho
  constructor
  · exact integral_nonneg (fun rows => (selectedIndexIntegral_bounds rate rewards C_star C_h k
      (ids, Function.update rows j rho) j).1)
  · have h := integral_mono hf (integrable_const (1 : ℝ))
      (fun rows => (selectedIndexIntegral_bounds rate rewards C_star C_h k
        (ids, Function.update rows j rho) j).2)
    simpa only [fixedRowPrivateProbability, integral_const, probReal_univ, one_smul] using h

/-- Every fixed-ID whole-row probability section is integrable. -/
theorem integrable_fixedRowPrivateProbability
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (ids : IDArray p) (j : Fin (M p)) :
    Integrable (fixedRowPrivateProbability rate rewards C_star C_h k ids j)
      (completeRowMeasure p) := by
  apply Integrable.of_mem_Icc 0 1
    ((measurable_fixedRowPrivateProbability rate rewards C_star C_h k j).comp
      (measurable_const.prodMk measurable_id)).aemeasurable
  exact ae_of_all _ fun rho => fixedRowPrivateProbability_bounds rate rewards C_star C_h k ids j rho

/-- Nuisance rows cancel by actual J-cell locality for every full published
row family, with no public almost-everywhere exception or sampled witness. -/
theorem fixedRowPrivateProbability_eq_fixedPublicIntegral
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (ids : IDArray p) (j : Fin (M p)) (rows : CompleteRows p) :
    fixedRowPrivateProbability rate rewards C_star C_h k ids j (rows j) =
      ∫ e : ExtendedPrivateCoordinates p,
        savedWrongIndicator rate rewards C_star C_h k ((ids, rows), e)
          ∂selectedIndexPrivateLaw p j := by
  unfold fixedRowPrivateProbability
  have heq (nuisance : CompleteRows p) :
      (∫ e : ExtendedPrivateCoordinates p,
        savedWrongIndicator rate rewards C_star C_h k
          ((ids, Function.update nuisance j (rows j)), e) ∂selectedIndexPrivateLaw p j) =
      ∫ e : ExtendedPrivateCoordinates p,
        savedWrongIndicator rate rewards C_star C_h k ((ids, rows), e)
          ∂selectedIndexPrivateLaw p j := by
    apply integral_congr_ae
    filter_upwards [ae_selectedIndexPrivateLaw_mem p j] with e he
    exact savedWrongIndicator_update_eq_on_indexCell rate rewards C_star C_h k ids j nuisance rows e he
  simp_rw [heq]
  simp only [integral_const, probReal_univ, one_smul]

/-- Exact scaled set integral under the original extended private law. -/
theorem fixedRowPrivateProbability_eq_mul_setIntegral
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (ids : IDArray p) (j : Fin (M p)) (rows : CompleteRows p) :
    fixedRowPrivateProbability rate rewards C_star C_h k ids j (rows j) =
      (M p : ℝ) * ∫ e in indexCell p j,
        savedWrongIndicator rate rewards C_star C_h k ((ids, rows), e) ∂extendedPrivateLaw p := by
  rw [fixedRowPrivateProbability_eq_fixedPublicIntegral,
    selectedIndexPrivateLaw, integral_smul_measure, smul_eq_mul,
    ENNReal.toReal_ofReal (Nat.cast_nonneg _)]

/-- Actual disjoint exhaustive J cells give the exact uniform decomposition
at every fixed complete public output, preserving every private coordinate. -/
theorem privateIntegral_eq_uniform_fixedRows
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (published : PublishedOutput p) :
    (∫ e : ExtendedPrivateCoordinates p,
      savedWrongIndicator rate rewards C_star C_h k (published, e) ∂extendedPrivateLaw p) =
      (1 / (M p : ℝ)) * ∑ j : Fin (M p),
        fixedRowPrivateProbability rate rewards C_star C_h k published.1 j (published.2 j) := by
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
      savedWrongIndicator rate rewards C_star C_h k (published, e))
    (measurableSet_indexCell p) hdisjoint
    (fun _ => (integrable_savedWrongIndicator_privateSection
      rate rewards C_star C_h k published).integrableOn)
  rw [hcover, setIntegral_univ] at hpartition
  rw [hpartition]
  simp_rw [fixedRowPrivateProbability_eq_mul_setIntegral]
  rw [← Finset.mul_sum, ← mul_assoc, one_div_mul_cancel
    (Nat.cast_ne_zero.mpr (M_pos p).ne' : (M p : ℝ) ≠ 0), one_mul]


/-- Integrability on the original joint source law, for the original-source
joint decoder-tail consumer. -/
theorem integrable_savedWrongIndicator_source
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) :
    Integrable (savedWrongIndicator rate rewards C_star C_h k) (sourceInputLaw p) := by
  apply Integrable.of_mem_Icc 0 1
    (measurable_savedWrongIndicator rate rewards C_star C_h k).aemeasurable
  exact ae_of_all _ fun source => savedWrongIndicator_bounds rate rewards C_star C_h k source

/-- Every full-family evaluation of the row probability is integrable under
the original nuisance-row product, for each fixed ID array. -/
theorem integrable_fixedRowPrivateProbability_rows
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (ids : IDArray p) (j : Fin (M p)) :
    Integrable (fun rows : CompleteRows p =>
      fixedRowPrivateProbability rate rewards C_star C_h k ids j (rows j))
      (completeRowsMeasure p) := by
  apply Integrable.of_mem_Icc 0 1
    ((measurable_fixedRowPrivateProbability rate rewards C_star C_h k j).comp
      (measurable_const.prodMk (measurable_completeRowProjection p j))).aemeasurable
  exact ae_of_all _ fun rows =>
    fixedRowPrivateProbability_bounds rate rewards C_star C_h k ids j (rows j)

/-- The actual whole-row projection law removes every unselected public row
from the row mean, without conditioning a published row. -/
theorem integral_fixedRowPrivateProbability_rows
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (ids : IDArray p) (j : Fin (M p)) :
    (∫ rows : CompleteRows p,
      fixedRowPrivateProbability rate rewards C_star C_h k ids j (rows j)
        ∂completeRowsMeasure p) =
      ∫ rho : CompleteRow p,
        fixedRowPrivateProbability rate rewards C_star C_h k ids j rho ∂completeRowMeasure p := by
  have hf : StronglyMeasurable (fixedRowPrivateProbability rate rewards C_star C_h k ids j) :=
    ((measurable_fixedRowPrivateProbability rate rewards C_star C_h k j).comp
      (measurable_const.prodMk measurable_id)).stronglyMeasurable
  have hmap := integral_map_of_stronglyMeasurable
    (μ := completeRowsMeasure p) (measurable_completeRowProjection p j) hf
  rw [map_completeRowProjection p j] at hmap
  exact hmap.symm

/-- Averaging the fixed-public decomposition over original complete rows
produces the uniform row means for each fixed ID array. This is an identity,
with no fixed-ID quantitative decoder estimate. -/
theorem rowsPrivateIntegral_eq_uniform_rowMeans
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (ids : IDArray p) :
    (∫ rows : CompleteRows p, ∫ e : ExtendedPrivateCoordinates p,
      savedWrongIndicator rate rewards C_star C_h k ((ids, rows), e)
        ∂extendedPrivateLaw p ∂completeRowsMeasure p) =
      (1 / (M p : ℝ)) * ∑ j : Fin (M p), ∫ rho : CompleteRow p,
        fixedRowPrivateProbability rate rewards C_star C_h k ids j rho ∂completeRowMeasure p := by
  simp_rw [privateIntegral_eq_uniform_fixedRows]
  rw [integral_const_mul, integral_finsetSum _ (fun j _ =>
    integrable_fixedRowPrivateProbability_rows rate rewards C_star C_h k ids j)]
  simp_rw [integral_fixedRowPrivateProbability_rows]

/-- Named original-ID-integrated row-mean identity. An independently proved
joint decoder-tail bound can be applied on the left, followed by concentration
of the measurable whole-row probabilities on the right. No bound is assumed
or asserted here. -/
theorem sourceIntegral_eq_idIntegrated_uniform_rowMeans
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) :
    (∫ source : SourceInput p,
      savedWrongIndicator rate rewards C_star C_h k source ∂sourceInputLaw p) =
      ∫ ids : IDArray p, (1 / (M p : ℝ)) * ∑ j : Fin (M p), ∫ rho : CompleteRow p,
        fixedRowPrivateProbability rate rewards C_star C_h k ids j rho
          ∂completeRowMeasure p ∂idArrayMeasure p := by
  have hf := integrable_savedWrongIndicator_source rate rewards C_star C_h k
  have hg := hf.integral_prod_left
  rw [sourceInputLaw, integral_prod _ hf, publishedOutputMeasure, integral_prod _ hg]
  apply integral_congr_ae
  exact ae_of_all _ fun ids => rowsPrivateIntegral_eq_uniform_rowMeans
    rate rewards C_star C_h k ids

end Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability

end
