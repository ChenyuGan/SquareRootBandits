/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CompletePublicTable
public import Mathlib.MeasureTheory.Integral.Prod

import Mathlib.Probability.Independence.InfinitePi

/-!
# False-row forward-slice factorization

This module splits the accepted published-output carrier into the shared ID
array, every existing continuous learning/control row, the true forward row
at `J`, and all false forward rows. Its law is the corresponding literal
product law. In particular, fixing the complete tuple consisting of the ID
array, every learning row, and the true forward row leaves the original
independent false-forward law. This is a product-factor statement about the
preprocessing law; after fixing a complete `PublishedOutput`, every bit is a
number, and no independence conditional on that complete output is asserted.

The source describes false forward slices in
`sources/zip4/manuscript/appendix_b_communication.tex:302-338` and the full
independent public-table construction in
`sources/zip4/manuscript/07_public_setup.tex:5-38`. This adapter proves no
tester-scan, private-pass, eligible-list, physical-execution, or regret claim.
-/

public section

open MeasureTheory ProbabilityTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousLearningRows

namespace Bandits.Support.FalseRowSliceFactorization

/-- The literal false-row index set, excluding only the actual row `J`. -/
abbrev FalseRow (p : ConstructorDimensions.Parameters) (J : Fin (M p)) :=
  {v : Fin (M p) // v ≠ J}

/-- The source continuous learning-row family, with no finite replacement. -/
abbrev LearningFamily (p : ConstructorDimensions.Parameters) :=
  ContinuousLearningRows.LearningRows p

/-- All false forward rows, indexed by their literal row labels. -/
abbrev FalseForwardRows (p : ConstructorDimensions.Parameters) (J : Fin (M p)) :=
  FalseRow p J → ForwardRow p

/-- The base tuple fixed before sampling the false forward rows. -/
abbrev FalseFactorBase (p : ConstructorDimensions.Parameters) :=
  IDArray p × LearningFamily p × ForwardRow p

/-- The explicit output of the false-row factorization. -/
abbrev FalseFactorOutput (p : ConstructorDimensions.Parameters) (J : Fin (M p)) :=
  FalseFactorBase p × FalseForwardRows p J

/-- The actual finite subtype of rounds in the source calendar block. -/
abbrev BlockTime (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) :=
  {t : Fin p.T // t ∈ BootstrapDimensions.calendarBlock p s}

/-- One false forward row's vector on the actual block-time subtype. -/
abbrev ForwardBlockSlice (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) :=
  BlockTime p s → Bool

/-- The literal product law of the complete base tuple. -/
@[expose] noncomputable def falseFactorBaseMeasure
    (p : ConstructorDimensions.Parameters) : Measure (FalseFactorBase p) :=
  idArrayMeasure p |>.prod (ContinuousLearningRows.learningRowsLaw p |>.prod (forwardRowMeasure p))

instance falseFactorBaseMeasure_probability (p : ConstructorDimensions.Parameters) :
    IsProbabilityMeasure (falseFactorBaseMeasure p) := by
  dsimp [falseFactorBaseMeasure]
  infer_instance

/-- The literal independent product law of all forward rows except `J`. -/
@[expose] noncomputable def falseForwardRowsMeasure
    (p : ConstructorDimensions.Parameters) (J : Fin (M p)) :
      Measure (FalseForwardRows p J) :=
  Measure.pi (fun _ : FalseRow p J => forwardRowMeasure p)

instance falseForwardRowsMeasure_probability (p : ConstructorDimensions.Parameters)
    (J : Fin (M p)) : IsProbabilityMeasure (falseForwardRowsMeasure p J) := by
  dsimp [falseForwardRowsMeasure]
  infer_instance

/-- The true-row index subtype used by Mathlib's exact pi split. -/
abbrev TrueRow (p : ConstructorDimensions.Parameters) (J : Fin (M p)) :=
  {v : Fin (M p) // v = J}

/-- The forward-family values on the singleton true-row subtype are exactly
one `ForwardRow`. -/
@[expose] noncomputable def trueRowEquiv
    (p : ConstructorDimensions.Parameters) (J : Fin (M p)) :
      (TrueRow p J → ForwardRow p) ≃ᵐ ForwardRow p where
  toEquiv :=
    { toFun := fun f => f ⟨J, rfl⟩
      invFun := fun f _ => f
      left_inv := by
        intro f
        funext v
        have hv : (⟨J, rfl⟩ : TrueRow p J) = v := Subtype.ext v.property.symm
        rw [hv]
      right_inv := by
        intro f
        rfl }
  measurable_toFun := measurable_pi_apply (⟨J, rfl⟩ : TrueRow p J)
  measurable_invFun := measurable_pi_iff.mpr fun _ => measurable_id

/-- Regroup every complete row into its existing forward and learning rows. -/
@[expose] noncomputable def publishedRowsSplitEquiv
    (p : ConstructorDimensions.Parameters) :
      CompleteRows p ≃ᵐ ForwardFamily p × LearningFamily p :=
  MeasurableEquiv.arrowProdEquivProdArrow
    (ForwardRow p) (ContinuousLearningRows.LearningRow p) (Fin (M p))

/-- Split the row-index pi space by the exact predicate `v = J`, then move its
singleton component to the literal `ForwardRow p` coordinate. -/
@[expose] noncomputable def splitRowsAtJEquiv
    (p : ConstructorDimensions.Parameters) (J : Fin (M p)) :
      ForwardFamily p ≃ᵐ ForwardRow p × FalseForwardRows p J :=
  (MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : Fin (M p) => ForwardRow p) (fun v => v = J)).trans
    (MeasurableEquiv.prodCongr (trueRowEquiv p J) (MeasurableEquiv.refl _))

/-- Reorder the ID, learning, true-row, and false-row coordinates after the
row-index pi split. -/
@[expose] noncomputable def splitOutputFactorEquiv
    (p : ConstructorDimensions.Parameters) (J : Fin (M p)) :
      IDArray p × (ForwardFamily p × LearningFamily p) ≃ᵐ FalseFactorOutput p J := by
  let idEquiv : IDArray p ≃ᵐ IDArray p := MeasurableEquiv.refl _
  let learningEquiv : LearningFamily p ≃ᵐ LearningFamily p := MeasurableEquiv.refl _
  let eSwap : IDArray p × (ForwardFamily p × LearningFamily p) ≃ᵐ
      IDArray p × (LearningFamily p × ForwardFamily p) :=
    MeasurableEquiv.prodCongr idEquiv MeasurableEquiv.prodComm
  let eSplit : IDArray p × (LearningFamily p × ForwardFamily p) ≃ᵐ
      IDArray p × (LearningFamily p × (ForwardRow p × FalseForwardRows p J)) :=
    MeasurableEquiv.prodCongr idEquiv
      (MeasurableEquiv.prodCongr learningEquiv (splitRowsAtJEquiv p J))
  let eAssoc : IDArray p × (LearningFamily p × (ForwardRow p × FalseForwardRows p J)) ≃ᵐ
      FalseFactorOutput p J :=
    (MeasurableEquiv.prodCongr idEquiv MeasurableEquiv.prodAssoc.symm).trans
      MeasurableEquiv.prodAssoc.symm
  exact eSwap.trans (eSplit.trans eAssoc)

/-- The measurable equivalence from the exact published-output carrier to the
requested base tuple paired with every false forward row. -/
@[expose] noncomputable def falseRowFactorEquiv
    (p : ConstructorDimensions.Parameters) (J : Fin (M p)) :
      PublishedOutput p ≃ᵐ FalseFactorOutput p J where
  toEquiv :=
    { toFun := fun x =>
        Prod.mk (Prod.mk x.1 (Prod.mk (fun q => (x.2 q).2) ((x.2 J).1)))
          (fun (v : FalseRow p J) => (x.2 v.1).1)
      invFun := fun y =>
        Prod.mk y.1.1 (fun q =>
          Prod.mk (if h : q = J then y.1.2.2 else y.2 ⟨q, h⟩) (y.1.2.1 q))
      left_inv := by
        intro x
        apply Prod.ext
        · rfl
        · funext q
          apply Prod.ext
          · by_cases h : q = J
            · subst q
              simp
            · simp [h]
          · rfl
      right_inv := by
        rintro ⟨⟨id, ⟨learning, trueForward⟩⟩, falseRows⟩
        apply Prod.ext
        · apply Prod.ext
          · rfl
          · apply Prod.ext
            · funext q
              rfl
            · simp
        · funext v
          have hv : v.1 ≠ J := v.property
          simp [hv] }
  measurable_toFun := by
    have hLearning : Measurable (fun x : PublishedOutput p => fun q => (x.2 q).2) := by
      apply measurable_pi_iff.mpr
      intro q
      exact measurable_snd.comp ((measurable_pi_apply q).comp measurable_snd)
    have hTrue : Measurable (fun x : PublishedOutput p => (x.2 J).1) :=
      measurable_fst.comp ((measurable_pi_apply J).comp measurable_snd)
    have hFalse : Measurable (fun x : PublishedOutput p =>
        fun (v : FalseRow p J) => (x.2 v.1).1) := by
      apply measurable_pi_iff.mpr
      intro v
      exact measurable_fst.comp ((measurable_pi_apply v.1).comp measurable_snd)
    exact (measurable_fst.prodMk (hLearning.prodMk hTrue)).prodMk hFalse
  measurable_invFun := by
    have hLearning : Measurable (fun y : FalseFactorOutput p J => y.1.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_fst)
    have hFalseForward (q : Fin (M p)) :
        Measurable (fun y : FalseFactorOutput p J =>
          if h : q = J then y.1.2.2 else y.2 ⟨q, h⟩) := by
      by_cases h : q = J
      · simp [h]
        exact measurable_snd.comp (measurable_snd.comp measurable_fst)
      · simp [h]
        exact (measurable_pi_apply (⟨q, h⟩ : FalseRow p J)).comp measurable_snd
    exact (measurable_fst.comp measurable_fst).prodMk
      (measurable_pi_iff.mpr fun q =>
        (hFalseForward q).prodMk ((measurable_pi_apply q).comp hLearning))

/-- The published output regrouped into its ID, whole forward-family, and
whole learning-family factors. -/
@[expose] noncomputable def publishedOutputSplitEquiv
    (p : ConstructorDimensions.Parameters) :
      PublishedOutput p ≃ᵐ IDArray p × (ForwardFamily p × LearningFamily p) :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (publishedRowsSplitEquiv p)

@[simp] theorem falseRowFactorEquiv_id (p : ConstructorDimensions.Parameters)
    (J : Fin (M p)) (x : PublishedOutput p) :
      (falseRowFactorEquiv p J x).1.1 = x.1 := rfl

@[simp] theorem falseRowFactorEquiv_learning (p : ConstructorDimensions.Parameters)
    (J : Fin (M p)) (x : PublishedOutput p) :
      (falseRowFactorEquiv p J x).1.2.1 = completeRowsLearning p x.2 := rfl

@[simp] theorem falseRowFactorEquiv_trueForward (p : ConstructorDimensions.Parameters)
    (J : Fin (M p)) (x : PublishedOutput p) :
      (falseRowFactorEquiv p J x).1.2.2 = (x.2 J).1 := rfl

@[simp] theorem falseRowFactorEquiv_falseForward (p : ConstructorDimensions.Parameters)
    (J : Fin (M p)) (x : PublishedOutput p) :
      (falseRowFactorEquiv p J x).2 = fun v => (x.2 v.1).1 := rfl

/-- The published-output law factors into the literal base law and the
independent false-row pi law. -/
theorem measurePreserving_falseRowFactorEquiv
    (p : ConstructorDimensions.Parameters) (J : Fin (M p)) :
      MeasurePreserving (falseRowFactorEquiv p J) (publishedOutputMeasure p)
        ((falseFactorBaseMeasure p).prod (falseForwardRowsMeasure p J)) := by
  have hPublishedOutput : MeasurePreserving (publishedOutputSplitEquiv p)
      (publishedOutputMeasure p)
      ((idArrayMeasure p).prod
        ((forwardFamilyMeasure p).prod (ContinuousLearningRows.learningRowsLaw p))) := by
    change MeasurePreserving
      (fun x : PublishedOutput p => (x.1, splitCompleteRows p x.2)) _ _
    convert ((MeasurePreserving.id (idArrayMeasure p)).prod
      (measurePreserving_splitCompleteRows p)) using 1
    all_goals rfl
  have hSwap : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (IDArray p)) MeasurableEquiv.prodComm)
      ((idArrayMeasure p).prod
        ((forwardFamilyMeasure p).prod (ContinuousLearningRows.learningRowsLaw p)))
      ((idArrayMeasure p).prod
        ((ContinuousLearningRows.learningRowsLaw p).prod (forwardFamilyMeasure p))) := by
    exact (MeasurePreserving.id (idArrayMeasure p)).prod Measure.measurePreserving_swap
  let _ : Fintype (TrueRow p J) :=
    Subtype.fintype (fun v : Fin (M p) => v = J)
  let splitPi := measurePreserving_piEquivPiSubtypeProd
    (α := fun _ : Fin (M p) => ForwardRow p)
    (μ := fun _ : Fin (M p) => forwardRowMeasure p)
    (fun v : Fin (M p) => v = J)
  have hPi : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (IDArray p))
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (LearningFamily p))
          (MeasurableEquiv.piEquivPiSubtypeProd
            (fun _ : Fin (M p) => ForwardRow p) (fun v => v = J))))
      ((idArrayMeasure p).prod
        ((ContinuousLearningRows.learningRowsLaw p).prod (forwardFamilyMeasure p)))
      ((idArrayMeasure p).prod
        ((ContinuousLearningRows.learningRowsLaw p).prod
          ((Measure.pi (fun v : TrueRow p J => forwardRowMeasure p)).prod
            (Measure.pi (fun v : FalseRow p J => forwardRowMeasure p))))) := by
    convert ((MeasurePreserving.id (idArrayMeasure p)).prod
      ((MeasurePreserving.id (ContinuousLearningRows.learningRowsLaw p)).prod splitPi)) using 1
    all_goals rfl
  have hTrue : MeasurePreserving (trueRowEquiv p J)
      (Measure.pi (fun _ : TrueRow p J => forwardRowMeasure p)) (forwardRowMeasure p) := by
    change MeasurePreserving (fun f : TrueRow p J → ForwardRow p =>
      f (⟨J, rfl⟩ : TrueRow p J)) _ _
    exact measurePreserving_eval (fun _ : TrueRow p J => forwardRowMeasure p)
      (⟨J, rfl⟩ : TrueRow p J)
  have hSingleton : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (IDArray p))
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (LearningFamily p))
          (MeasurableEquiv.prodCongr (trueRowEquiv p J) (MeasurableEquiv.refl _))))
      ((idArrayMeasure p).prod
        ((ContinuousLearningRows.learningRowsLaw p).prod
          ((Measure.pi (fun v : TrueRow p J => forwardRowMeasure p)).prod
            (Measure.pi (fun v : FalseRow p J => forwardRowMeasure p)))))
      ((idArrayMeasure p).prod
        ((ContinuousLearningRows.learningRowsLaw p).prod
          ((forwardRowMeasure p).prod (falseForwardRowsMeasure p J)))) := by
    exact (MeasurePreserving.id (idArrayMeasure p)).prod
      ((MeasurePreserving.id (ContinuousLearningRows.learningRowsLaw p)).prod
        (hTrue.prod (MeasurePreserving.id (falseForwardRowsMeasure p J))))
  have hAssocInner : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (IDArray p))
        (MeasurableEquiv.prodAssoc.symm :
          LearningFamily p × (ForwardRow p × FalseForwardRows p J) ≃ᵐ
            (LearningFamily p × ForwardRow p) × FalseForwardRows p J))
      ((idArrayMeasure p).prod
        ((ContinuousLearningRows.learningRowsLaw p).prod
          ((forwardRowMeasure p).prod (falseForwardRowsMeasure p J))))
      ((idArrayMeasure p).prod
        (((ContinuousLearningRows.learningRowsLaw p).prod (forwardRowMeasure p)).prod
          (falseForwardRowsMeasure p J))) := by
    exact (MeasurePreserving.id (idArrayMeasure p)).prod
      (measurePreserving_prodAssoc (ContinuousLearningRows.learningRowsLaw p)
        (forwardRowMeasure p) (falseForwardRowsMeasure p J)).symm
  have hAssocOuter : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm :
        IDArray p × ((LearningFamily p × ForwardRow p) × FalseForwardRows p J) ≃ᵐ
          (IDArray p × (LearningFamily p × ForwardRow p)) × FalseForwardRows p J)
      ((idArrayMeasure p).prod
        (((ContinuousLearningRows.learningRowsLaw p).prod (forwardRowMeasure p)).prod
          (falseForwardRowsMeasure p J)))
      ((falseFactorBaseMeasure p).prod (falseForwardRowsMeasure p J)) := by
    exact (measurePreserving_prodAssoc (idArrayMeasure p)
      ((ContinuousLearningRows.learningRowsLaw p).prod (forwardRowMeasure p))
      (falseForwardRowsMeasure p J)).symm
  have hFactor : MeasurePreserving (splitOutputFactorEquiv p J)
      ((idArrayMeasure p).prod
        ((forwardFamilyMeasure p).prod (ContinuousLearningRows.learningRowsLaw p)))
      ((falseFactorBaseMeasure p).prod (falseForwardRowsMeasure p J)) := by
    convert hAssocOuter.comp (hAssocInner.comp (hSingleton.comp (hPi.comp hSwap))) using 1
    all_goals rfl
  have h := hFactor.comp hPublishedOutput
  refine ⟨(falseRowFactorEquiv p J).measurable, ?_⟩
  have hfun : (falseRowFactorEquiv p J : PublishedOutput p → FalseFactorOutput p J) =
      (splitOutputFactorEquiv p J) ∘ publishedOutputSplitEquiv p := by
    funext x
    change Prod.mk (Prod.mk x.1 (Prod.mk (fun q => (x.2 q).2) ((x.2 J).1)))
        (fun (v : FalseRow p J) => (x.2 v.1).1) =
      splitOutputFactorEquiv p J (x.1, splitCompleteRows p x.2)
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · funext q
          simp [splitOutputFactorEquiv, splitRowsAtJEquiv, trueRowEquiv,
            MeasurableEquiv.prodCongr, MeasurableEquiv.prodComm,
            MeasurableEquiv.prodAssoc, MeasurableEquiv.refl,
            splitCompleteRows, completeRowsLearning, completeRowsForward,
            MeasurableEquiv.piEquivPiSubtypeProd]
        · simp [splitOutputFactorEquiv, splitRowsAtJEquiv, trueRowEquiv,
            MeasurableEquiv.prodCongr, MeasurableEquiv.prodComm,
            MeasurableEquiv.prodAssoc, MeasurableEquiv.refl,
            splitCompleteRows, completeRowsForward,
            MeasurableEquiv.piEquivPiSubtypeProd]
    · funext v
      simp [splitOutputFactorEquiv, splitRowsAtJEquiv, trueRowEquiv,
        MeasurableEquiv.prodCongr, MeasurableEquiv.prodComm,
        MeasurableEquiv.prodAssoc, MeasurableEquiv.refl,
        splitCompleteRows, completeRowsForward,
        MeasurableEquiv.piEquivPiSubtypeProd]
  rw [hfun]
  exact h.map_eq

/-- The accepted published-output law pushes forward to the literal product
of the complete base law and all false forward rows. -/
theorem map_falseRowFactorEquiv
    (p : ConstructorDimensions.Parameters) (J : Fin (M p)) :
      (publishedOutputMeasure p).map (falseRowFactorEquiv p J) =
        (falseFactorBaseMeasure p).prod (falseForwardRowsMeasure p J) :=
  (measurePreserving_falseRowFactorEquiv p J).map_eq

/-- Every coordinate of the accepted output has been recorded exactly. -/
theorem falseRowFactorEquiv_coordinates
    (p : ConstructorDimensions.Parameters) (J : Fin (M p))
    (x : PublishedOutput p) :
      (falseRowFactorEquiv p J x).1.1 = x.1 ∧
      (falseRowFactorEquiv p J x).1.2.1 = completeRowsLearning p x.2 ∧
      (falseRowFactorEquiv p J x).1.2.2 = (x.2 J).1 ∧
      (falseRowFactorEquiv p J x).2 = fun v => (x.2 v.1).1 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A measurable test on the factor space is integrable whenever it is bounded. -/
theorem integrable_bounded_factor_test
    (p : ConstructorDimensions.Parameters) (J : Fin (M p))
    (f : FalseFactorOutput p J → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ z, ‖f z‖ ≤ C) :
      Integrable f ((falseFactorBaseMeasure p).prod (falseForwardRowsMeasure p J)) := by
  exact Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)

/-- Fubini's identity for every bounded measurable function of the complete
base tuple and all false forward rows. -/
theorem integral_falseRowFactor_fubini
    (p : ConstructorDimensions.Parameters) (J : Fin (M p))
    (f : FalseFactorOutput p J → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ z, ‖f z‖ ≤ C) :
      (∫ x, f (falseRowFactorEquiv p J x) ∂publishedOutputMeasure p) =
        ∫ b, ∫ z, f (b, z) ∂falseForwardRowsMeasure p J ∂falseFactorBaseMeasure p := by
  rw [(measurePreserving_falseRowFactorEquiv p J).integral_comp' f]
  exact integral_prod f (integrable_bounded_factor_test p J f hf C hC)

/-- One literal `(false row, ID, block-time)` slice of the complete false
forward factor. -/
@[expose] noncomputable def falseForwardSlice
    (p : ConstructorDimensions.Parameters) (J : Fin (M p))
    (s : Fin (n_boot p)) (v : FalseRow p J)
    (u : Fin (BootstrapDimensions.A_id p)) :
      FalseForwardRows p J → ForwardBlockSlice p s :=
  fun rows t => rows v u t.1

/-- Original independent forward-bit law on the distinct calendar times of a
block. -/
@[expose] noncomputable def forwardBlockSliceLaw
    (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) :
      Measure (ForwardBlockSlice p s) :=
  Measure.pi (fun _ : BlockTime p s => forwardBitLaw p)

theorem measurable_falseForwardSlice
    (p : ConstructorDimensions.Parameters) (J : Fin (M p))
    (s : Fin (n_boot p)) (v : FalseRow p J)
    (u : Fin (BootstrapDimensions.A_id p)) :
      Measurable (falseForwardSlice p J s v u) := by
  apply measurable_pi_iff.mpr
  intro t
  exact (measurable_pi_apply t.1).comp
    ((measurable_pi_apply u).comp (measurable_pi_apply v))

/-- Every coordinate in a restricted false slice retains the original bit
law, and the whole block vector has its original product law. -/
theorem map_falseForwardSlice
    (p : ConstructorDimensions.Parameters) (J : Fin (M p))
    (s : Fin (n_boot p)) (v : FalseRow p J)
    (u : Fin (BootstrapDimensions.A_id p)) :
      (falseForwardRowsMeasure p J).map (falseForwardSlice p J s v u) =
        forwardBlockSliceLaw p s := by
  have hcoords := (iIndepFun_forwardRowCoordinate p).precomp
    (g := fun t : BlockTime p s => (u, t.1)) (by
      intro t t' htt
      apply Subtype.ext
      exact congrArg Prod.snd htt)
  have hmeas : ∀ t : BlockTime p s,
      AEMeasurable (fun row : ForwardRow p => row u t.1) (forwardRowMeasure p) := by
    intro t
    exact (measurable_forwardRowCoordinate p u t.1).aemeasurable
  have hrow := hcoords.map_fun_eq_pi_map hmeas
  have hproj := measurePreserving_eval
    (fun _ : FalseRow p J => forwardRowMeasure p) v
  let sliceRow : ForwardRow p → ForwardBlockSlice p s :=
    fun row t => row u t.1
  have hsliceRowMeas : Measurable sliceRow :=
    measurable_pi_iff.mpr fun t =>
      (measurable_pi_apply t.1).comp (measurable_pi_apply u)
  calc
    (falseForwardRowsMeasure p J).map (falseForwardSlice p J s v u) =
        (forwardRowMeasure p).map sliceRow := by
      change (falseForwardRowsMeasure p J).map
          (sliceRow ∘ fun rows : FalseForwardRows p J => rows v) = _
      rw [← Measure.map_map hsliceRowMeas (measurable_pi_apply v)]
      exact congrArg (fun μ : Measure (ForwardRow p) => μ.map sliceRow)
        hproj.map_eq
    _ = forwardBlockSliceLaw p s := by
      rw [forwardBlockSliceLaw]
      calc
        (forwardRowMeasure p).map sliceRow =
            Measure.pi (fun t : BlockTime p s =>
              (forwardRowMeasure p).map (fun row => row u t.1)) := hrow
        _ = Measure.pi (fun _ : BlockTime p s => forwardBitLaw p) := by
          congr 1
          funext t
          exact forwardRowCoordinate_map p u t.1

/-- Every literal false `(v,u,t)` bit retains its original forward-bit law. -/
theorem falseForwardSlice_coordinate_law
    (p : ConstructorDimensions.Parameters) (J : Fin (M p))
    (s : Fin (n_boot p)) (v : FalseRow p J)
    (u : Fin (BootstrapDimensions.A_id p)) (t : BlockTime p s) :
      (falseForwardRowsMeasure p J).map
        (fun rows => (falseForwardSlice p J s v u rows) t) = forwardBitLaw p := by
  have hEval : Measurable (fun slice : ForwardBlockSlice p s => slice t) :=
    measurable_pi_apply t
  have hSliceMap := Measure.map_map (μ := falseForwardRowsMeasure p J) hEval
    (measurable_falseForwardSlice p J s v u)
  change (falseForwardRowsMeasure p J).map
      ((fun slice : ForwardBlockSlice p s => slice t) ∘
        falseForwardSlice p J s v u) = forwardBitLaw p
  rw [hSliceMap.symm, map_falseForwardSlice, forwardBlockSliceLaw]
  exact measurePreserving_eval
    (fun _ : BlockTime p s => forwardBitLaw p) t |>.map_eq

/-- Pull back independent random variables along a measure-preserving map. -/
private theorem iIndepFun_measurePreserving_comp
    {ι Ω Ω' : Type*} [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace Ω']
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {g : Ω → Ω'} (hg : MeasurePreserving g μ ν)
    {f : ∀ i, Ω' → β i} (hf : ∀ i, Measurable (f i))
    (h : iIndepFun f ν) : iIndepFun (fun i => f i ∘ g) μ := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => ((hf i).comp hg.measurable).aemeasurable)).2
  calc
    μ.map (fun x i => f i (g x)) = ν.map (fun x i => f i x) := by
      rw [← hg.map_eq, Measure.map_map (measurable_pi_iff.mpr hf) hg.measurable]
      rfl
    _ = Measure.pi (fun i => μ.map (f i ∘ g)) := by
      rw [h.map_fun_eq_pi_map (fun i => (hf i).aemeasurable)]
      congr 1
      funext i
      rw [← hg.map_eq, Measure.map_map (hf i) hg.measurable]

/-- Independent block-slice vectors across every literal false row and ID
label. Each slice's full joint law over distinct calendar times is
`forwardBlockSliceLaw`. -/
theorem iIndepFun_falseForwardSlices
    (p : ConstructorDimensions.Parameters) (J : Fin (M p))
    (s : Fin (n_boot p)) :
      iIndepFun
        (fun vu : FalseRow p J × Fin (BootstrapDimensions.A_id p) =>
          falseForwardSlice p J s vu.1 vu.2)
        (falseForwardRowsMeasure p J) := by
  let rowSlices (row : ForwardRow p) :
      Fin (BootstrapDimensions.A_id p) → ForwardBlockSlice p s :=
    fun u t => row u t.1
  have hRowSlicesMeasurable : Measurable rowSlices := by
    apply measurable_pi_iff.mpr
    intro u
    apply measurable_pi_iff.mpr
    intro t
    exact (measurable_pi_apply t.1).comp (measurable_pi_apply u)
  have hRows : iIndepFun (fun v rows => rows v)
      (falseForwardRowsMeasure p J) :=
    iIndepFun_pi (fun _ : FalseRow p J => aemeasurable_id)
  have hOuter : iIndepFun (fun v rows => rowSlices (rows v))
      (falseForwardRowsMeasure p J) :=
    hRows.comp (fun _ => rowSlices) (fun _ => hRowSlicesMeasurable)
  have hTimes : iIndepFun
      (fun u row => fun t : BlockTime p s => row u t.1) (forwardRowMeasure p) := by
    have hU : iIndepFun (fun u row => row u)
        (Measure.pi (fun _ : Fin (BootstrapDimensions.A_id p) =>
          Measure.pi (fun _ : Fin p.T => forwardBitLaw p))) :=
      iIndepFun_pi (fun _ : Fin (BootstrapDimensions.A_id p) => aemeasurable_id)
    have hU' := hU.comp (fun _ timeRow => fun t : BlockTime p s => timeRow t.1)
      (fun _ => measurable_pi_iff.mpr fun t => measurable_pi_apply t.1)
    change iIndepFun (fun u row => fun t : BlockTime p s => row u t.1)
      (Measure.pi (fun _ : Fin (BootstrapDimensions.A_id p) =>
        Measure.pi (fun _ : Fin p.T => forwardBitLaw p)))
    exact hU'
  have hInner : ∀ v : FalseRow p J,
      iIndepFun
        (fun u rows => fun t : BlockTime p s => rows v u t.1)
        (falseForwardRowsMeasure p J) := by
    intro v
    exact iIndepFun_measurePreserving_comp
      (measurePreserving_eval (fun _ : FalseRow p J => forwardRowMeasure p) v)
      (fun u => measurable_pi_iff.mpr fun t =>
        (measurable_pi_apply t.1).comp (measurable_pi_apply u)) hTimes
  have hMeas : ∀ v u, Measurable (fun rows : FalseForwardRows p J =>
      fun t : BlockTime p s => rows v u t.1) := by
    intro v u
    exact measurable_pi_iff.mpr fun t =>
      (measurable_pi_apply t.1).comp
        ((measurable_pi_apply u).comp (measurable_pi_apply v))
  have h := iIndepFun_uncurry' hMeas hOuter hInner
  change iIndepFun
    (fun vu : FalseRow p J × Fin (BootstrapDimensions.A_id p) =>
      fun rows : FalseForwardRows p J =>
        fun t : BlockTime p s => rows vu.1 vu.2 t.1)
    (falseForwardRowsMeasure p J)
  exact h

/-- The scalar false bits are jointly independent under their literal
`(false row, ID, actual block time)` labels. -/
theorem iIndepFun_falseForwardSliceCoordinates
    (p : ConstructorDimensions.Parameters) (J : Fin (M p))
    (s : Fin (n_boot p)) :
      iIndepFun
        (fun vut : FalseRow p J ×
            (Fin (BootstrapDimensions.A_id p) × BlockTime p s) =>
          fun rows : FalseForwardRows p J => rows vut.1 vut.2.1 vut.2.2.1)
        (falseForwardRowsMeasure p J) := by
  have hRows : iIndepFun (fun v rows => rows v)
      (falseForwardRowsMeasure p J) :=
    iIndepFun_pi (fun _ : FalseRow p J => aemeasurable_id)
  let rowCoordinates (row : ForwardRow p) :
      Fin (BootstrapDimensions.A_id p) × BlockTime p s → Bool :=
    fun ut => row ut.1 ut.2.1
  have hRowCoordinatesMeasurable : Measurable rowCoordinates := by
    apply measurable_pi_iff.mpr
    intro ut
    exact (measurable_pi_apply ut.2.1).comp (measurable_pi_apply ut.1)
  have hOuter := hRows.comp (fun _ => rowCoordinates)
    (fun _ => hRowCoordinatesMeasurable)
  have hCoordinate : iIndepFun
      (fun ut : Fin (BootstrapDimensions.A_id p) × BlockTime p s =>
        fun row : ForwardRow p => row ut.1 ut.2.1)
      (forwardRowMeasure p) := by
    have hinj : Function.Injective
        (fun ut : Fin (BootstrapDimensions.A_id p) × BlockTime p s =>
          (ut.1, ut.2.1)) := by
      intro a b hab
      have hp := hab
      simp only [Prod.mk.injEq] at hp
      rcases hp with ⟨ha, ht⟩
      apply Prod.ext
      · exact ha
      · exact Subtype.ext ht
    exact (iIndepFun_forwardRowCoordinate p).precomp
      (g := fun ut : Fin (BootstrapDimensions.A_id p) × BlockTime p s =>
        (ut.1, ut.2.1)) hinj
  have hInner : ∀ v : FalseRow p J,
      iIndepFun
        (fun (ut : Fin (BootstrapDimensions.A_id p) × BlockTime p s) rows =>
          rows v ut.1 ut.2.1)
        (falseForwardRowsMeasure p J) := by
    intro v
    exact iIndepFun_measurePreserving_comp
      (ι := Fin (BootstrapDimensions.A_id p) × BlockTime p s)
      (Ω := FalseForwardRows p J)
      (Ω' := ForwardRow p)
      (β := fun _ => Bool)
      (μ := falseForwardRowsMeasure p J)
      (ν := forwardRowMeasure p)
      (g := fun rows : FalseForwardRows p J => rows v)
      (measurePreserving_eval (fun _ : FalseRow p J => forwardRowMeasure p) v)
      (f := fun ut : Fin (BootstrapDimensions.A_id p) × BlockTime p s =>
        fun row : ForwardRow p => row ut.1 ut.2.1)
      (fun (ut : Fin (BootstrapDimensions.A_id p) × BlockTime p s) =>
        measurable_forwardRowCoordinate p ut.1 ut.2.1) hCoordinate
  have hMeasurable : ∀ (v : FalseRow p J)
      (ut : Fin (BootstrapDimensions.A_id p) × BlockTime p s), Measurable
      (fun rows : FalseForwardRows p J => rows v ut.1 ut.2.1) := by
    intro v ut
    exact (measurable_pi_apply ut.2.1).comp
      ((measurable_pi_apply ut.1).comp (measurable_pi_apply v))
  have h := iIndepFun_uncurry' hMeasurable hOuter hInner
  simpa [rowCoordinates, Function.comp_apply] using h

/-- For each fixed complete base tuple, the remaining false-row law is the
same independent product law as before fixing it. -/
theorem fixedBase_falseRows_law
    (p : ConstructorDimensions.Parameters) (J : Fin (M p))
    (b : FalseFactorBase p) :
      ((Measure.dirac b).prod (falseForwardRowsMeasure p J)).map Prod.snd =
        falseForwardRowsMeasure p J :=
  measurePreserving_snd.map_eq

/-- For every fixed base tuple, each complete false block slice retains its
original joint product law over the distinct calendar times. -/
theorem fixedBase_map_falseForwardSlice
    (p : ConstructorDimensions.Parameters) (J : Fin (M p))
    (s : Fin (n_boot p)) (b : FalseFactorBase p)
    (v : FalseRow p J) (u : Fin (BootstrapDimensions.A_id p)) :
      ((Measure.dirac b).prod (falseForwardRowsMeasure p J)).map
        (fun z => falseForwardSlice p J s v u z.2) = forwardBlockSliceLaw p s := by
  have hcomp :
      ((Measure.dirac b).prod (falseForwardRowsMeasure p J)).map
        (fun z => falseForwardSlice p J s v u z.2) =
      (((Measure.dirac b).prod (falseForwardRowsMeasure p J)).map Prod.snd).map
        (falseForwardSlice p J s v u) := by
    change ((Measure.dirac b).prod (falseForwardRowsMeasure p J)).map
        (falseForwardSlice p J s v u ∘ Prod.snd) = _
    exact (Measure.map_map (measurable_falseForwardSlice p J s v u)
      measurable_snd).symm
  rw [hcomp, fixedBase_falseRows_law, map_falseForwardSlice]

/-- Fixing the base tuple preserves independence of all false `(v,u)` block
slices. -/
theorem fixedBase_iIndepFun_falseForwardSlices
    (p : ConstructorDimensions.Parameters) (J : Fin (M p))
    (s : Fin (n_boot p)) (b : FalseFactorBase p) :
      iIndepFun
        (fun vu : FalseRow p J × Fin (BootstrapDimensions.A_id p) =>
          falseForwardSlice p J s vu.1 vu.2 ∘ Prod.snd)
        ((Measure.dirac b).prod (falseForwardRowsMeasure p J)) := by
  exact iIndepFun_measurePreserving_comp measurePreserving_snd
    (fun vu => measurable_falseForwardSlice p J s vu.1 vu.2)
    (iIndepFun_falseForwardSlices p J s)

/-- Fixing any complete base tuple leaves the literal scalar false-bit family
independent under the same labels and law. -/
theorem fixedBase_iIndepFun_falseForwardSliceCoordinates
    (p : ConstructorDimensions.Parameters) (J : Fin (M p))
    (s : Fin (n_boot p)) (b : FalseFactorBase p) :
      iIndepFun
        (fun vut : FalseRow p J ×
            (Fin (BootstrapDimensions.A_id p) × BlockTime p s) =>
          fun z : FalseFactorBase p × FalseForwardRows p J =>
            z.2 vut.1 vut.2.1 vut.2.2.1)
        ((Measure.dirac b).prod (falseForwardRowsMeasure p J)) := by
  exact iIndepFun_measurePreserving_comp measurePreserving_snd
    (fun vut => (measurable_pi_apply vut.2.2.1).comp
      ((measurable_pi_apply vut.2.1).comp (measurable_pi_apply vut.1)))
    (iIndepFun_falseForwardSliceCoordinates p J s)

/-- At every fixed base tuple, each false forward bit at an actual block time
has the original `forwardBitLaw` marginal. -/
theorem fixedBase_falseForwardSlice_coordinate_law
    (p : ConstructorDimensions.Parameters) (J : Fin (M p))
    (s : Fin (n_boot p)) (b : FalseFactorBase p)
    (v : FalseRow p J) (u : Fin (BootstrapDimensions.A_id p))
    (t : BlockTime p s) :
      ((Measure.dirac b).prod (falseForwardRowsMeasure p J)).map
        (fun z => (falseForwardSlice p J s v u z.2) t) = forwardBitLaw p := by
  let coord : FalseForwardRows p J → Bool := fun rows => rows v u t.1
  have hcoord : Measurable coord :=
    (measurable_forwardRowCoordinate p u t.1).comp (measurable_pi_apply v)
  have hEval : Measurable (fun slice : ForwardBlockSlice p s => slice t) :=
    measurable_pi_apply t
  have hcomp :
      ((Measure.dirac b).prod (falseForwardRowsMeasure p J)).map
        (fun z => (falseForwardSlice p J s v u z.2) t) =
      (((Measure.dirac b).prod (falseForwardRowsMeasure p J)).map Prod.snd).map
        coord := by
    change ((Measure.dirac b).prod (falseForwardRowsMeasure p J)).map
        (coord ∘ Prod.snd) = _
    exact (Measure.map_map hcoord measurable_snd).symm
  have hEvalMap : (falseForwardRowsMeasure p J).map coord =
      ((falseForwardRowsMeasure p J).map (falseForwardSlice p J s v u)).map
        (fun slice => slice t) := by
    change (falseForwardRowsMeasure p J).map
        ((fun slice : ForwardBlockSlice p s => slice t) ∘
          falseForwardSlice p J s v u) = _
    exact (Measure.map_map hEval (measurable_falseForwardSlice p J s v u)).symm
  rw [hcomp, fixedBase_falseRows_law, hEvalMap, map_falseForwardSlice,
    forwardBlockSliceLaw]
  exact measurePreserving_eval
    (fun _ : BlockTime p s => forwardBitLaw p) t |>.map_eq

end Bandits.Support.FalseRowSliceFactorization

end
