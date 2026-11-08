/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedSelectedIndexForwardBound
public import Bandits.Support.ReferenceCompleteSelectedRowExpectation

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Fixed-ID false-forward probability bound

For every literal ID array, the original selected-index law of the actual
false-forward event has the source whole-row tail. The proof keeps the complete
learning rows, true forward row, false forward rows, and original private tuple.

Sources: `sources/zip4/manuscript/07_public_setup.tex:127-164`,
`sources/zip4/manuscript/08_main_theorem.tex:29-47`, and
`sources/zip4/manuscript/appendix_b_communication.tex:99,294-338,768-798`.
This is an internal probability composition. It proves no initialization
coupling, regret bound, or manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.FalseRowSliceFactorization
open Bandits.Support.ForwardPrefixSlice
open Bandits.Support.FalseForwardBaseTail
open Bandits.Support.GeneratedEligibleFamily
open Bandits.Support.GeneratedFalseForwardEvent
open Bandits.Support.GeneratedSelectedIndexForwardBound
open Bandits.Support.ReferenceCompleteSelectedRowExpectation
open scoped ENNReal BigOperators Classical

namespace Bandits.Support.GeneratedFixedIDSelectedIndexForwardTail

private theorem fixedID_rows_measurePreserving
    (p : ConstructorDimensions.Parameters) (j : Fin (M p)) (ids : IDArray p) :
    MeasurePreserving
      (fun rows : CompleteRows p =>
        FalseRowSliceFactorization.falseRowFactorEquiv p j (ids, rows))
      (CompletePublicTable.completeRowsMeasure p)
      (((Measure.dirac ids).prod
          ((ContinuousLearningRows.learningRowsLaw p).prod
            (CompletePublicTable.forwardRowMeasure p))).prod
          (FalseRowSliceFactorization.falseForwardRowsMeasure p j)) := by
  let learningLaw := ContinuousLearningRows.learningRowsLaw p
  let forwardLaw := CompletePublicTable.forwardRowMeasure p
  let falseLaw := FalseRowSliceFactorization.falseForwardRowsMeasure p j
  let rowBodyLaw := learningLaw.prod forwardLaw
  let rowFactorLaw := rowBodyLaw.prod falseLaw
  let rowsToFactors : CompleteRows p → (LearningFamily p × ForwardRow p) ×
      FalseForwardRows p j := fun rows =>
    MeasurableEquiv.prodAssoc.symm
      (CompletePublicTable.completeRowsLearning p rows,
        FalseRowSliceFactorization.splitRowsAtJEquiv p j
          (CompletePublicTable.completeRowsForward p rows))
  have hrows : MeasurePreserving rowsToFactors
      (CompletePublicTable.completeRowsMeasure p) rowFactorLaw := by
    have hsplit := CompletePublicTable.measurePreserving_splitCompleteRows p
    have hswap : MeasurePreserving Prod.swap
        (CompletePublicTable.forwardFamilyMeasure p |>.prod learningLaw)
        (learningLaw.prod (CompletePublicTable.forwardFamilyMeasure p)) :=
      Measure.measurePreserving_swap
    have hsplitAtJ := FalseForwardBaseTail.measurePreserving_splitRowsAtJEquiv p j
    have hwithLearning :=
      (MeasurePreserving.id learningLaw).prod hsplitAtJ
    have hassoc : MeasurePreserving
        (MeasurableEquiv.prodAssoc.symm :
          LearningFamily p × (ForwardRow p × FalseForwardRows p j) ≃ᵐ
            (LearningFamily p × ForwardRow p) × FalseForwardRows p j)
        (learningLaw.prod (forwardLaw.prod falseLaw)) rowFactorLaw :=
      (measurePreserving_prodAssoc learningLaw forwardLaw falseLaw).symm
    have hcomp := hassoc.comp (hwithLearning.comp (hswap.comp hsplit))
    refine ⟨hcomp.measurable, ?_⟩
    change Measure.map rowsToFactors (CompletePublicTable.completeRowsMeasure p) = rowFactorLaw
    have hsource := hcomp.map_eq
    simpa [rowsToFactors, CompletePublicTable.splitCompleteRows,
      CompletePublicTable.completeRowsForward, CompletePublicTable.completeRowsLearning,
      Function.comp_def] using hsource
  have hidBase : MeasurePreserving (fun z : LearningFamily p × ForwardRow p => (ids, z))
      rowBodyLaw ((Measure.dirac ids).prod rowBodyLaw) := by
    refine ⟨measurable_const.prodMk measurable_id, ?_⟩
    rw [Measure.dirac_prod]
  have hidprod := hidBase.prod (MeasurePreserving.id falseLaw)
  have hfixed := hidprod.comp hrows
  refine ⟨?_, ?_⟩
  · exact (FalseRowSliceFactorization.falseRowFactorEquiv p j).measurable.comp
      (measurable_const.prodMk measurable_id)
  · have hfun :
        (fun rows : CompleteRows p =>
          ((ids, (rowsToFactors rows).1), (rowsToFactors rows).2)) =
        (fun rows : CompleteRows p =>
          FalseRowSliceFactorization.falseRowFactorEquiv p j (ids, rows)) := by
      funext rows
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · apply Prod.ext
          · rfl
          · change (FalseRowSliceFactorization.splitRowsAtJEquiv p j
                (CompletePublicTable.completeRowsForward p rows)).1 = (rows j).1
            simp [FalseRowSliceFactorization.splitRowsAtJEquiv,
              FalseRowSliceFactorization.trueRowEquiv,
              MeasurableEquiv.prodCongr, MeasurableEquiv.refl,
              MeasurableEquiv.piEquivPiSubtypeProd,
              CompletePublicTable.completeRowsForward]
      · funext v
        change (FalseRowSliceFactorization.splitRowsAtJEquiv p j
              (CompletePublicTable.completeRowsForward p rows)).2 v = (rows v.1).1
        simp [FalseRowSliceFactorization.splitRowsAtJEquiv,
          FalseRowSliceFactorization.trueRowEquiv,
          MeasurableEquiv.prodCongr, MeasurableEquiv.refl,
          MeasurableEquiv.piEquivPiSubtypeProd,
          CompletePublicTable.completeRowsForward]
    have hmap := hfixed.map_eq
    change Measure.map
      (fun rows : CompleteRows p =>
        FalseRowSliceFactorization.falseRowFactorEquiv p j (ids, rows))
      (CompletePublicTable.completeRowsMeasure p) =
      (((Measure.dirac ids).prod rowBodyLaw).prod falseLaw)
    rw [← hfun]
    simpa [rowFactorLaw, rowBodyLaw, learningLaw, forwardLaw, falseLaw,
      rowsToFactors, Function.comp_def, Prod.map] using hmap

private theorem falseForwardSlice_integrable_and_measureReal_le
    {p : ConstructorDimensions.Parameters} {s : Fin (n_boot p)}
    {j : Fin (M p)} (v : FalseRow p j)
    (E : ForwardPrefixSlice.EligibleListFunction p s
      (ExtendedPrivateCoordinates p))
    (e : ExtendedPrivateCoordinates p) (u : Fin (A_id p)) :
    Integrable
      ({f : FalseForwardRows p j |
        ForwardPrefixSlice.privatePrefixPasses E e (fun t => f v u t)}.indicator
          (fun _ => (1 : ℝ)))
      (FalseRowSliceFactorization.falseForwardRowsMeasure p j) ∧
    (FalseRowSliceFactorization.falseForwardRowsMeasure p j).real
      {f | ForwardPrefixSlice.privatePrefixPasses E e (fun t => f v u t)} ≤
        ForwardPrefixSlice.forwardTrueProbability p ^ q_dec p := by
  classical
  let rowPass : Set (CompletePublicTable.ForwardRow p) :=
    {x | ForwardPrefixSlice.privatePrefixPasses E e (fun t => x u t)}
  let falsePass : Set (FalseForwardRows p j) :=
    {f | ForwardPrefixSlice.privatePrefixPasses E e (fun t => f v u t)}
  let times := ForwardPrefixSlice.chronologicalEligibleTimes E e
  have hrowMeas : MeasurableSet rowPass := by
    by_cases hq : q_dec p ≤ times.length
    · have hset : rowPass = {x | ∀ t ∈ times.take (q_dec p), x u t = true} := by
        ext x
        simp only [rowPass, Set.mem_ofPred_eq]
        rw [ForwardPrefixSlice.privatePrefixPasses_iff_first_q]
        simp [times, hq]
      rw [hset]
      exact ForwardPrefixSlice.measurableSet_forwardRow_allTrue_list p u
        (times.take (q_dec p))
    · have hset : rowPass = ∅ := by
        ext x
        simp only [rowPass, Set.mem_ofPred_eq]
        rw [ForwardPrefixSlice.privatePrefixPasses_iff_first_q]
        simp [times, hq]
      rw [hset]
      exact MeasurableSet.empty
  have hEval : MeasurePreserving (fun f : FalseForwardRows p j => f v)
      (FalseRowSliceFactorization.falseForwardRowsMeasure p j)
      (CompletePublicTable.forwardRowMeasure p) :=
    measurePreserving_eval _ _
  have hpre : (fun f : FalseForwardRows p j => f v) ⁻¹' rowPass = falsePass := by
    ext f
    rfl
  have hfalseMeas : MeasurableSet falsePass := by
    rw [← hpre]
    exact hrowMeas.preimage hEval.measurable
  refine ⟨(integrable_const (1 : ℝ)).indicator hfalseMeas, ?_⟩
  have hmeasure := hEval.measure_preimage hrowMeas.nullMeasurableSet
  rw [hpre] at hmeasure
  have hreal :
      (FalseRowSliceFactorization.falseForwardRowsMeasure p j).real falsePass =
        (CompletePublicTable.forwardRowMeasure p).real rowPass := by
    simp only [MeasureTheory.measureReal_def, hmeasure]
  have hintegral := integral_indicator_one
    (μ := CompletePublicTable.forwardRowMeasure p) hrowMeas
  have hslice := ForwardPrefixSlice.privatePassing_slice_integral E e u
  have hexact :
      (FalseRowSliceFactorization.falseForwardRowsMeasure p j).real falsePass =
        (if q_dec p ≤ times.length then (1 : ℝ) else 0) *
          ForwardPrefixSlice.forwardTrueProbability p ^ q_dec p := by
    calc
      _ = (CompletePublicTable.forwardRowMeasure p).real rowPass := hreal
      _ = ∫ x, rowPass.indicator (fun _ => (1 : ℝ)) x
            ∂CompletePublicTable.forwardRowMeasure p := hintegral.symm
      _ = (if q_dec p ≤ times.length then (1 : ℝ) else 0) *
            ForwardPrefixSlice.forwardTrueProbability p ^ q_dec p := by
          simpa [rowPass, times] using hslice
  have hpi : 0 ≤ ForwardPrefixSlice.forwardTrueProbability p :=
    ForwardPrefixSlice.forwardTrueProbability_nonneg p
  by_cases hq : q_dec p ≤ times.length
  · rw [hexact, ite_eq_left hq]
    simp
  · rw [hexact, ite_eq_right hq]
    simpa only [zero_mul] using pow_nonneg hpi (q_dec p)

private theorem fixedID_actualFalse_section_le
    {p : ConstructorDimensions.Parameters}
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (j : Fin (M p)) (s : Fin (n_boot p)) (i : ActiveRoundActions.Follower p.m)
    (base : FalseFactorBase p) (rho : ExtendedPrivateCoordinates p) :
    (FalseRowSliceFactorization.falseForwardRowsMeasure p j).real
      {f | ((FalseRowSliceFactorization.falseRowFactorEquiv p j).symm (base, f), rho) ∈
        GeneratedFalseForwardEvent.actualFalseForwardPrefixPassSet
          C_star C_h eta rewards j s i} ≤
      (Fintype.card (FalseRow p j) : ℝ) *
        ForwardPrefixSlice.forwardTrueProbability p ^ q_dec p := by
  classical
  let falseLaw := FalseRowSliceFactorization.falseForwardRowsMeasure p j
  let family := GeneratedEligibleFamily.family C_star C_h eta rewards j s i
  let code := GeneratedEligibleFamily.activePrivateIDCode C_star C_h eta rewards j s i
    (base, rho)
  let actual : Set (FalseForwardRows p j) :=
    {f | ((FalseRowSliceFactorization.falseRowFactorEquiv p j).symm (base, f), rho) ∈
      GeneratedFalseForwardEvent.actualFalseForwardPrefixPassSet
        C_star C_h eta rewards j s i}
  change falseLaw.real actual ≤ _
  have hfactor (f : FalseForwardRows p j) :
      FalseRowSliceFactorization.falseRowFactorEquiv p j
        ((FalseRowSliceFactorization.falseRowFactorEquiv p j).symm (base, f)) =
          (base, f) := by
    exact (FalseRowSliceFactorization.falseRowFactorEquiv p j).apply_symm_apply
      (base, f)
  have hactiveCode (f : FalseForwardRows p j) :
      GeneratedEligibleFamily.activePrivateIDCodeOnPublishedOutput
          C_star C_h eta rewards j s i
          ((FalseRowSliceFactorization.falseRowFactorEquiv p j).symm (base, f), rho) =
        code := by
    change GeneratedEligibleFamily.activePrivateIDCode C_star C_h eta rewards j s i
        ((FalseRowSliceFactorization.falseRowFactorEquiv p j
          ((FalseRowSliceFactorization.falseRowFactorEquiv p j).symm (base, f))).1,
          rho) = _
    rw [congrArg Prod.fst (hfactor f)]
  have hpi : 0 ≤ ForwardPrefixSlice.forwardTrueProbability p :=
    ForwardPrefixSlice.forwardTrueProbability_nonneg p
  by_cases hcodeNone : code = none
  · have hempty : actual = ∅ := by
      ext f
      constructor
      · intro hf
        have hmem := hf
        change ((FalseRowSliceFactorization.falseRowFactorEquiv p j).symm (base, f), rho) ∈
          GeneratedFalseForwardEvent.actualFalseForwardPrefixPassSet
            C_star C_h eta rewards j s i at hmem
        rw [GeneratedFalseForwardEvent.actualFalseForwardPrefixPassSet_eq_virtualUnion]
          at hmem
        simp only [GeneratedEligibleFamily.virtualExistsFalseForwardPrefixPassSet,
          Set.mem_iUnion] at hmem
        obtain ⟨label, hlabel⟩ := hmem
        by_cases hfalse : label.1 ≠ j
        · simp [GeneratedEligibleFamily.virtualFalseForwardLabelSet, hfalse] at hlabel
          obtain ⟨_, hlabelCode⟩ := hlabel
          rw [hactiveCode f, hcodeNone] at hlabelCode
          simp at hlabelCode
        · simp [GeneratedEligibleFamily.virtualFalseForwardLabelSet, hfalse] at hlabel
      · simp
    rw [hempty]
    simp
    positivity
  · obtain ⟨u, hcodeSome⟩ := Option.ne_none_iff_exists'.mp hcodeNone
    let candidate : FalseRow p j → Set (FalseForwardRows p j) := fun v =>
      {f | ((base, f), rho) ∈
        FalseForwardBaseTail.factorFalseForwardPassSet family j (v.1, u) v.2}
    have hsubset : actual ⊆ ⋃ v : FalseRow p j, candidate v := by
      intro f hf
      have hmem := hf
      change ((FalseRowSliceFactorization.falseRowFactorEquiv p j).symm (base, f), rho) ∈
        GeneratedFalseForwardEvent.actualFalseForwardPrefixPassSet
          C_star C_h eta rewards j s i at hmem
      rw [GeneratedFalseForwardEvent.actualFalseForwardPrefixPassSet_eq_virtualUnion]
        at hmem
      simp only [GeneratedEligibleFamily.virtualExistsFalseForwardPrefixPassSet,
        Set.mem_iUnion] at hmem
      obtain ⟨label, hlabel⟩ := hmem
      by_cases hfalse : label.1 ≠ j
      · simp [GeneratedEligibleFamily.virtualFalseForwardLabelSet, hfalse] at hlabel
        obtain ⟨hpass, hlabelCode⟩ := hlabel
        have hlabelCode' := hlabelCode
        rw [hactiveCode f, hcodeSome] at hlabelCode'
        have hid : label.2 = u := by
          have hsome : some u = some label.2 := by simpa using hlabelCode'
          exact (Option.some.inj hsome).symm
        let v : FalseRow p j := ⟨label.1, hfalse⟩
        let P : PublishedOutput p :=
          (FalseRowSliceFactorization.falseRowFactorEquiv p j).symm (base, f)
        have hP : (FalseRowSliceFactorization.falseRowFactorEquiv p j P).1 = base := by
          exact congrArg Prod.fst
            ((FalseRowSliceFactorization.falseRowFactorEquiv p j).apply_symm_apply
              (base, f))
        have hcodeP :
            GeneratedEligibleFamily.activePrivateIDCodeOnPublishedOutput
                C_star C_h eta rewards j s i (P, rho) = some label.2 := by
          rw [hactiveCode f, hcodeSome]
          exact hlabelCode'
        obtain ⟨hprocessed, hactive, hactiveFollower, hidActual⟩ :=
          (GeneratedFalseForwardEvent.activePrivateIDCodeOnPublishedOutput_eq_some_iff_actualContext
            C_star C_h eta rewards j P rho s i label.2).mp hcodeP
        have hlabelID : label.2 =
            (GeneratedForwardPrefixTests.actualPhysicalBlock
              (GeneratedEligibleFamily.referenceInputOfPublishedOutput
                C_star C_h eta rewards j (P, rho)) s hprocessed).privateId hactive.val := by
          exact hidActual.symm
        have hpassAtP :
            (FalseRowSliceFactorization.falseRowFactorEquiv p j P, rho) ∈
              FalseForwardBaseTail.factorFalseForwardPassSet
                (GeneratedEligibleFamily.family C_star C_h eta rewards j s i)
                j label hfalse := by
          simpa [P, hP, family, hid] using hpass
        have hpassAtActive :
            (FalseRowSliceFactorization.falseRowFactorEquiv p j P, rho) ∈
              FalseForwardBaseTail.factorFalseForwardPassSet
                (GeneratedEligibleFamily.family C_star C_h eta rewards j s
                  hactive.val.val) j label hfalse := by
          simpa only [hactiveFollower] using hpassAtP
        have hcandidate :=
          (GeneratedEligibleFamily.factorPass_iff_generatedFalseCandidatePasses
            C_star C_h eta rewards j P rho s hprocessed hactive label hfalse
            hlabelID).mp hpassAtActive
        have hpassAtActive' :=
          (GeneratedEligibleFamily.factorPass_iff_generatedFalseCandidatePasses
            C_star C_h eta rewards j P rho s hprocessed hactive label hfalse
            hlabelID).mpr hcandidate
        have hpassAtI :
            (FalseRowSliceFactorization.falseRowFactorEquiv p j P, rho) ∈
              FalseForwardBaseTail.factorFalseForwardPassSet
                (GeneratedEligibleFamily.family C_star C_h eta rewards j s i)
                j label hfalse := by
          simpa only [hactiveFollower] using hpassAtActive'
        have hpassBase :
            ((base, f), rho) ∈ FalseForwardBaseTail.factorFalseForwardPassSet
              family j label hfalse := by
          simpa [P, hP, family] using hpassAtI
        have hpassCandidate : f ∈ candidate v := by
          change ((base, f), rho) ∈ FalseForwardBaseTail.factorFalseForwardPassSet
            family j (label.1, label.2) hfalse at hpassBase
          rw [hid] at hpassBase
          exact hpassBase
        exact Set.mem_iUnion.mpr ⟨v, hpassCandidate⟩
      · simp [GeneratedEligibleFamily.virtualFalseForwardLabelSet, hfalse] at hlabel
    have hboundENN : falseLaw actual ≤
        ENNReal.ofReal ((Fintype.card (FalseRow p j) : ℝ) *
          ForwardPrefixSlice.forwardTrueProbability p ^ q_dec p) := by
      have hunion := measure_iUnion_fintype_le falseLaw candidate
      calc
        _ ≤ falseLaw (⋃ v : FalseRow p j, candidate v) := measure_mono hsubset
        _ ≤ ∑ v : FalseRow p j, falseLaw (candidate v) := by simpa using hunion
        _ ≤ ∑ _v : FalseRow p j,
            ENNReal.ofReal (ForwardPrefixSlice.forwardTrueProbability p ^ q_dec p) := by
              apply Finset.sum_le_sum
              intro v hv
              have hrow : candidate v =
                  {f | ForwardPrefixSlice.privatePrefixPasses
                    (FalseForwardBaseTail.baseSectionEligibleList family base (v.1, u))
                    rho (fun t => f v u t)} := by
                ext f
                rfl
              rw [hrow]
              have htail := falseForwardSlice_integrable_and_measureReal_le v
                (FalseForwardBaseTail.baseSectionEligibleList family base (v.1, u))
                rho u
              have hfinite := measure_ne_top falseLaw
                {f | ForwardPrefixSlice.privatePrefixPasses
                  (FalseForwardBaseTail.baseSectionEligibleList family base (v.1, u))
                  rho (fun t => f v u t)}
              rw [← ENNReal.ofReal_toReal hfinite]
              exact ENNReal.ofReal_le_ofReal htail.2
        _ = ENNReal.ofReal
            ((Fintype.card (FalseRow p j) : ℝ) *
              ForwardPrefixSlice.forwardTrueProbability p ^ q_dec p) := by
              rw [Finset.sum_const, nsmul_eq_mul]
              rw [← ENNReal.ofReal_natCast, Finset.card_univ]
              have hcardNonneg : 0 ≤ (Fintype.card (FalseRow p j) : ℝ) := by positivity
              rw [← ENNReal.ofReal_mul hcardNonneg]
    have hnonneg : 0 ≤ (Fintype.card (FalseRow p j) : ℝ) *
        ForwardPrefixSlice.forwardTrueProbability p ^ q_dec p :=
      mul_nonneg (by positivity) (pow_nonneg hpi _)
    exact ENNReal.toReal_le_of_le_ofReal hnonneg hboundENN

private theorem fixedIndex_fixedSection_mass_eq
    {p : ConstructorDimensions.Parameters}
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (j : Fin (M p)) :
    ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j
        (GeneratedSelectedIndexForwardBound.fixedIndexActualAnyFalseForwardPrefixPassSection
          C_star C_h eta rewards P j) =
      BootstrapPrivateRoundStreams.extendedPrivateLaw p
        (GeneratedSelectedIndexForwardBound.fixedIndexActualAnyFalseForwardPrefixPassSection
          C_star C_h eta rewards P j) := by
  classical
  let fixed := GeneratedSelectedIndexForwardBound.fixedIndexActualAnyFalseForwardPrefixPassSection
    C_star C_h eta rewards P j
  let cell := ReferenceCompleteSelectedRowExpectation.indexCell p j
  have hfactor :=
    GeneratedSelectedIndexForwardBound.fixedIndexActualAnyFalseForwardPrefixPassSection_atom_factorization
      C_star C_h eta rewards P j
  have hcellFixed : cell ∩ fixed =
      {rho | PrivateSourceStreams.coordinatorIndex p rho.1.2 = j ∧ rho ∈ fixed} := by
    ext rho
    simp [cell, ReferenceCompleteSelectedRowExpectation.indexCell]
  have hfactor' :
      BootstrapPrivateRoundStreams.extendedPrivateLaw p (cell ∩ fixed) =
        ENNReal.ofReal (1 / (M p : ℝ)) *
          BootstrapPrivateRoundStreams.extendedPrivateLaw p fixed := by
    rw [hcellFixed]
    exact hfactor
  have hMpos : (0 : ℝ) < (M p : ℝ) := Nat.cast_pos.mpr (M_pos p)
  have hcoeff : ENNReal.ofReal (M p : ℝ) * ENNReal.ofReal (1 / (M p : ℝ)) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    have hMne : (M p : ℝ) ≠ 0 := ne_of_gt hMpos
    rw [show (M p : ℝ) * (1 / (M p : ℝ)) = 1 by field_simp]
    simp
  have hfixedMass :
      ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j fixed =
        BootstrapPrivateRoundStreams.extendedPrivateLaw p fixed := by
    rw [ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw,
      Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply' (ReferenceCompleteSelectedRowExpectation.measurableSet_indexCell p j),
      Set.inter_comm, hfactor']
    calc
      ENNReal.ofReal (M p : ℝ) *
          (ENNReal.ofReal (1 / (M p : ℝ)) *
            BootstrapPrivateRoundStreams.extendedPrivateLaw p fixed) =
        (ENNReal.ofReal (M p : ℝ) * ENNReal.ofReal (1 / (M p : ℝ))) *
          BootstrapPrivateRoundStreams.extendedPrivateLaw p fixed := by
            rw [← mul_assoc]
      _ = BootstrapPrivateRoundStreams.extendedPrivateLaw p fixed := by
        rw [hcoeff, one_mul]
  exact hfixedMass

private theorem fixedID_actualAny_section_le
    {p : ConstructorDimensions.Parameters}
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (j : Fin (M p)) (base : FalseFactorBase p)
    (rho : ExtendedPrivateCoordinates p) :
    (FalseRowSliceFactorization.falseForwardRowsMeasure p j).real
      {f | ((FalseRowSliceFactorization.falseRowFactorEquiv p j).symm (base, f), rho) ∈
        GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
          C_star C_h eta rewards j} ≤
      (n_boot p : ℝ) * (p.m - 1 : ℝ) *
        (Fintype.card (FalseRow p j) : ℝ) *
          ForwardPrefixSlice.forwardTrueProbability p ^ q_dec p := by
  classical
  let falseLaw := FalseRowSliceFactorization.falseForwardRowsMeasure p j
  let indices := Fin (n_boot p) × ActiveRoundActions.Follower p.m
  let perBlock (a : indices) : Set (FalseForwardRows p j) :=
    {f | ((FalseRowSliceFactorization.falseRowFactorEquiv p j).symm (base, f), rho) ∈
      GeneratedFalseForwardEvent.actualFalseForwardPrefixPassSet
        C_star C_h eta rewards j a.1 a.2}
  let actual : Set (FalseForwardRows p j) :=
    {f | ((FalseRowSliceFactorization.falseRowFactorEquiv p j).symm (base, f), rho) ∈
      GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
        C_star C_h eta rewards j}
  change falseLaw.real actual ≤ _
  have hunion : actual = ⋃ a : indices, perBlock a := by
    ext f
    simp [actual, perBlock, indices,
      GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet,
      Prod.exists]
  have hcard : Fintype.card indices = n_boot p * (p.m - 1) := by
    change Fintype.card
      (Fin (n_boot p) × Fin (PublicDiscreteDraws.followerCount p.m)) = _
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    rfl
  let c : ℝ := (Fintype.card (FalseRow p j) : ℝ) *
    ForwardPrefixSlice.forwardTrueProbability p ^ q_dec p
  have hc : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (by positivity)
      (pow_nonneg (ForwardPrefixSlice.forwardTrueProbability_nonneg p) _)
  have hboundENN : falseLaw actual ≤
      ENNReal.ofReal ((n_boot p : ℝ) * (p.m - 1 : ℝ) * c) := by
    have hunionBound := measure_iUnion_fintype_le falseLaw perBlock
    calc
      _ ≤ falseLaw (⋃ a : indices, perBlock a) := measure_mono (by rw [hunion])
      _ ≤ ∑ a : indices, falseLaw (perBlock a) := by simpa using hunionBound
      _ ≤ ∑ _a : indices, ENNReal.ofReal c := by
            apply Finset.sum_le_sum
            intro a ha
            have htail := fixedID_actualFalse_section_le C_star C_h eta rewards
              j a.1 a.2 base rho
            have hfinite := measure_ne_top falseLaw (perBlock a)
            rw [← ENNReal.ofReal_toReal hfinite]
            have htail' : (falseLaw (perBlock a)).toReal ≤ c := by
              simpa [falseLaw, perBlock, c, MeasureTheory.measureReal_def] using htail
            exact ENNReal.ofReal_le_ofReal htail'
      _ = ENNReal.ofReal ((n_boot p : ℝ) * (p.m - 1 : ℝ) * c) := by
            have hmNat : 1 ≤ p.m := Nat.le_trans (by decide) p.two_le_m
            rw [Finset.sum_const, nsmul_eq_mul]
            rw [← ENNReal.ofReal_natCast, Finset.card_univ]
            rw [← ENNReal.ofReal_mul (by positivity)]
            rw [hcard]
            push_cast
            congr 1
            rw [show ((p.m - 1 : ℕ) : ℝ) = (p.m : ℝ) - 1 by
              rw [Nat.cast_sub hmNat]
              norm_num]
  have hm1 : 0 ≤ (p.m : ℝ) - 1 := by
    have hmNat : 1 ≤ p.m := Nat.le_trans (by decide) p.two_le_m
    have hm : (1 : ℝ) ≤ (p.m : ℝ) := by exact_mod_cast hmNat
    linarith
  have hnonneg : 0 ≤ (n_boot p : ℝ) * ((p.m : ℝ) - 1) * c :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hm1) hc
  have hreal := ENNReal.toReal_le_of_le_ofReal hnonneg hboundENN
  simpa [c, MeasureTheory.measureReal_def, mul_assoc] using hreal

private def fixedID_sourceMap
    (p : ConstructorDimensions.Parameters) (j : Fin (M p)) (ids : IDArray p) :
    CompleteRows p × ExtendedPrivateCoordinates p →
      (FalseFactorBase p × ExtendedPrivateCoordinates p) × FalseForwardRows p j :=
  fun z =>
    let factors := FalseRowSliceFactorization.falseRowFactorEquiv p j (ids, z.1)
    ((factors.1, z.2), factors.2)

private def fixedID_baseLaw
    (p : ConstructorDimensions.Parameters) (ids : IDArray p) : Measure (FalseFactorBase p) :=
  (Measure.dirac ids).prod
    ((ContinuousLearningRows.learningRowsLaw p).prod
      (CompletePublicTable.forwardRowMeasure p))

private theorem fixedID_sourceMap_measurePreserving
    (p : ConstructorDimensions.Parameters) (j : Fin (M p)) (ids : IDArray p) :
    MeasurePreserving (fixedID_sourceMap p j ids)
      ((CompletePublicTable.completeRowsMeasure p).prod
        (BootstrapPrivateRoundStreams.extendedPrivateLaw p))
      (((fixedID_baseLaw p ids).prod
        (BootstrapPrivateRoundStreams.extendedPrivateLaw p)).prod
        (FalseRowSliceFactorization.falseForwardRowsMeasure p j)) := by
  let baseLaw := (Measure.dirac ids).prod
    ((ContinuousLearningRows.learningRowsLaw p).prod
      (CompletePublicTable.forwardRowMeasure p))
  let privateLaw := BootstrapPrivateRoundStreams.extendedPrivateLaw p
  let falseLaw := FalseRowSliceFactorization.falseForwardRowsMeasure p j
  have hrows := fixedID_rows_measurePreserving p j ids
  have hrowPrivate := hrows.prod (MeasurePreserving.id privateLaw)
  have hassoc₁ : MeasurePreserving
      (MeasurableEquiv.prodAssoc :
        (FalseFactorOutput p j × ExtendedPrivateCoordinates p) ≃ᵐ
          FalseFactorBase p × FalseForwardRows p j × ExtendedPrivateCoordinates p)
      ((baseLaw.prod falseLaw).prod privateLaw)
      (baseLaw.prod (falseLaw.prod privateLaw)) :=
    measurePreserving_prodAssoc baseLaw falseLaw privateLaw
  have hswap : MeasurePreserving
      (Prod.map id Prod.swap)
      (baseLaw.prod (falseLaw.prod privateLaw))
      (baseLaw.prod (privateLaw.prod falseLaw)) :=
    (MeasurePreserving.id baseLaw).prod Measure.measurePreserving_swap
  have hassoc₂ : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm :
        FalseFactorBase p × (ExtendedPrivateCoordinates p × FalseForwardRows p j) ≃ᵐ
          (FalseFactorBase p × ExtendedPrivateCoordinates p) × FalseForwardRows p j)
      (baseLaw.prod (privateLaw.prod falseLaw))
      ((baseLaw.prod privateLaw).prod falseLaw) :=
    (measurePreserving_prodAssoc baseLaw privateLaw falseLaw).symm
  have htransport := hassoc₂.comp (hswap.comp (hassoc₁.comp hrowPrivate))
  refine ⟨htransport.measurable, ?_⟩
  have hfun :
      (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
        MeasurableEquiv.prodAssoc.symm
          ((MeasurableEquiv.prodAssoc
              (FalseRowSliceFactorization.falseRowFactorEquiv p j (ids, z.1), z.2)).1,
            (MeasurableEquiv.prodAssoc
              (FalseRowSliceFactorization.falseRowFactorEquiv p j (ids, z.1), z.2)).2.swap)) =
      fixedID_sourceMap p j ids := by
    funext z
    rfl
  change Measure.map (fixedID_sourceMap p j ids)
      ((CompletePublicTable.completeRowsMeasure p).prod privateLaw) =
    ((baseLaw.prod privateLaw).prod falseLaw)
  rw [← hfun]
  simpa [fixedID_sourceMap, baseLaw, privateLaw, falseLaw, Function.comp_def,
    Prod.map] using htransport.map_eq

private theorem fixedID_fixed_section_eq
    {p : ConstructorDimensions.Parameters}
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (ids : IDArray p) (rows : CompleteRows p) (j : Fin (M p)) :
    Prod.mk rows ⁻¹'
      {w : CompleteRows p × ExtendedPrivateCoordinates p |
        ((ids, w.1), w.2) ∈ actualAnyFalseForwardPrefixPassSet
          C_star C_h eta rewards j} =
      fixedIndexActualAnyFalseForwardPrefixPassSection
        C_star C_h eta rewards (ids, rows) j := by
  rfl

/-- Normalization uses the original scalar cell, rather than changing any
private coordinate. -/
private theorem fixedID_selected_event_measure_eq
    {p : ConstructorDimensions.Parameters}
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (ids : IDArray p) (j : Fin (M p)) :
    ((completeRowsMeasure p).prod (selectedIndexPrivateLaw p j))
        {w : CompleteRows p × ExtendedPrivateCoordinates p |
          ((ids, w.1), w.2) ∈ actualSelectedIndexAnyFalseForwardPrefixPassSet
            C_star C_h eta rewards} =
      ((completeRowsMeasure p).prod (extendedPrivateLaw p))
        {w : CompleteRows p × ExtendedPrivateCoordinates p |
          ((ids, w.1), w.2) ∈ actualAnyFalseForwardPrefixPassSet
            C_star C_h eta rewards j} := by
  let μ := completeRowsMeasure p
  let ν := extendedPrivateLaw p
  let νj := selectedIndexPrivateLaw p j
  let selected : Set (CompleteRows p × ExtendedPrivateCoordinates p) :=
    {w | ((ids, w.1), w.2) ∈ actualSelectedIndexAnyFalseForwardPrefixPassSet
      C_star C_h eta rewards}
  let fixed : Set (CompleteRows p × ExtendedPrivateCoordinates p) :=
    {w | ((ids, w.1), w.2) ∈ actualAnyFalseForwardPrefixPassSet
      C_star C_h eta rewards j}
  have hprojection : MeasurePreserving Prod.snd (μ.prod νj) νj :=
    measurePreserving_snd
  have haeCell : ∀ᵐ w ∂μ.prod νj, w.2 ∈ indexCell p j :=
    hprojection.quasiMeasurePreserving.ae (ae_selectedIndexPrivateLaw_mem p j)
  have hsame : selected =ᵐ[μ.prod νj] fixed := by
    filter_upwards [haeCell] with w hw
    apply propext
    change PrivateSourceStreams.coordinatorIndex p w.2.1.2 = j at hw
    change ((ids, w.1), w.2) ∈ actualAnyFalseForwardPrefixPassSet
      C_star C_h eta rewards (PrivateSourceStreams.coordinatorIndex p w.2.1.2) ↔
      ((ids, w.1), w.2) ∈ actualAnyFalseForwardPrefixPassSet C_star C_h eta rewards j
    rw [hw]
  have hfixed : MeasurableSet fixed :=
    (measurableSet_actualAnyFalseForwardPrefixPassSet
      C_star C_h eta rewards j).preimage
        ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  change (μ.prod νj) selected = (μ.prod ν) fixed
  calc
    _ = (μ.prod νj) fixed := measure_congr hsame
    _ = (μ.prod ν) fixed := by
      rw [Measure.prod_apply hfixed, Measure.prod_apply hfixed]
      apply lintegral_congr
      intro rows
      rw [fixedID_fixed_section_eq C_star C_h eta rewards ids rows j]
      exact fixedIndex_fixedSection_mass_eq C_star C_h eta rewards (ids, rows) j

private theorem fixedID_factor_event_measurable
    {p : ConstructorDimensions.Parameters}
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (j : Fin (M p)) :
    MeasurableSet
      {x : (FalseFactorBase p × ExtendedPrivateCoordinates p) × FalseForwardRows p j |
        ((falseRowFactorEquiv p j).symm (x.1.1, x.2), x.1.2) ∈
          actualAnyFalseForwardPrefixPassSet C_star C_h eta rewards j} := by
  have hbaseFalse : Measurable
      (fun x : (FalseFactorBase p × ExtendedPrivateCoordinates p) × FalseForwardRows p j =>
        (x.1.1, x.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hback := (falseRowFactorEquiv p j).symm.measurable.comp hbaseFalse
  exact (measurableSet_actualAnyFalseForwardPrefixPassSet
    C_star C_h eta rewards j).preimage
      (hback.prodMk (measurable_snd.comp measurable_fst))

private theorem fixedID_factor_event_measure_le
    {p : ConstructorDimensions.Parameters}
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (ids : IDArray p) (j : Fin (M p)) :
    ((((fixedID_baseLaw p ids).prod (extendedPrivateLaw p)).prod
        (falseForwardRowsMeasure p j))
      {x : (FalseFactorBase p × ExtendedPrivateCoordinates p) × FalseForwardRows p j |
        ((falseRowFactorEquiv p j).symm (x.1.1, x.2), x.1.2) ∈
          actualAnyFalseForwardPrefixPassSet C_star C_h eta rewards j}) ≤
      ENNReal.ofReal ((n_boot p : ℝ) * (p.m - 1 : ℝ) *
        (Fintype.card (FalseRow p j) : ℝ) *
          forwardTrueProbability p ^ q_dec p) := by
  let targetEvent : Set
      ((FalseFactorBase p × ExtendedPrivateCoordinates p) × FalseForwardRows p j) :=
    {x | ((falseRowFactorEquiv p j).symm (x.1.1, x.2), x.1.2) ∈
      actualAnyFalseForwardPrefixPassSet C_star C_h eta rewards j}
  let c : ℝ := (n_boot p : ℝ) * (p.m - 1 : ℝ) *
    (Fintype.card (FalseRow p j) : ℝ) * forwardTrueProbability p ^ q_dec p
  have hsection (x : FalseFactorBase p × ExtendedPrivateCoordinates p) :
      falseForwardRowsMeasure p j ((Prod.mk x) ⁻¹' targetEvent) ≤ ENNReal.ofReal c := by
    have h := fixedID_actualAny_section_le C_star C_h eta rewards j x.1 x.2
    have hfinite := measure_ne_top (falseForwardRowsMeasure p j)
      ((Prod.mk x) ⁻¹' targetEvent)
    rw [← ENNReal.ofReal_toReal hfinite]
    exact ENNReal.ofReal_le_ofReal h
  change (((fixedID_baseLaw p ids).prod (extendedPrivateLaw p)).prod
    (falseForwardRowsMeasure p j)) targetEvent ≤ ENNReal.ofReal c
  rw [Measure.prod_apply (fixedID_factor_event_measurable C_star C_h eta rewards j)]
  calc
    ∫⁻ x, falseForwardRowsMeasure p j ((Prod.mk x) ⁻¹' targetEvent)
        ∂((fixedID_baseLaw p ids).prod (extendedPrivateLaw p)) ≤
      ∫⁻ _ : FalseFactorBase p × ExtendedPrivateCoordinates p, ENNReal.ofReal c
        ∂((fixedID_baseLaw p ids).prod (extendedPrivateLaw p)) :=
      lintegral_mono hsection
    _ = ENNReal.ofReal c := by simp [fixedID_baseLaw]

private theorem fixedID_fixed_event_preimage
    {p : ConstructorDimensions.Parameters}
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (ids : IDArray p) (j : Fin (M p)) :
    fixedID_sourceMap p j ids ⁻¹'
      {x : (FalseFactorBase p × ExtendedPrivateCoordinates p) × FalseForwardRows p j |
        ((falseRowFactorEquiv p j).symm (x.1.1, x.2), x.1.2) ∈
          actualAnyFalseForwardPrefixPassSet C_star C_h eta rewards j} =
      {w : CompleteRows p × ExtendedPrivateCoordinates p |
        ((ids, w.1), w.2) ∈ actualAnyFalseForwardPrefixPassSet
          C_star C_h eta rewards j} := by
  ext w
  change ((falseRowFactorEquiv p j).symm
      ((falseRowFactorEquiv p j (ids, w.1)).1,
        (falseRowFactorEquiv p j (ids, w.1)).2), w.2) ∈
        actualAnyFalseForwardPrefixPassSet C_star C_h eta rewards j ↔ _
  rw [Prod.eta, (falseRowFactorEquiv p j).symm_apply_apply]
  rfl

private theorem fixedID_fixed_event_measure_le
    {p : ConstructorDimensions.Parameters}
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (ids : IDArray p) (j : Fin (M p)) :
    ((completeRowsMeasure p).prod (extendedPrivateLaw p))
      {w : CompleteRows p × ExtendedPrivateCoordinates p |
        ((ids, w.1), w.2) ∈ actualAnyFalseForwardPrefixPassSet
          C_star C_h eta rewards j} ≤
      ENNReal.ofReal ((n_boot p : ℝ) * (p.m - 1 : ℝ) *
        (Fintype.card (FalseRow p j) : ℝ) *
          forwardTrueProbability p ^ q_dec p) := by
  have hsource := (fixedID_sourceMap_measurePreserving p j ids).measure_preimage
    (fixedID_factor_event_measurable C_star C_h eta rewards j).nullMeasurableSet
  rw [fixedID_fixed_event_preimage C_star C_h eta rewards ids j] at hsource
  rw [hsource]
  exact fixedID_factor_event_measure_le C_star C_h eta rewards ids j

private theorem fixedID_selected_event_measureReal_le
    (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (ids : IDArray p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) :
    MeasurableSet
      {w : CompleteRows p × ExtendedPrivateCoordinates p |
        ((ids, w.1), w.2) ∈ actualSelectedIndexAnyFalseForwardPrefixPassSet
          C_star C_h rate.eta rewards} ∧
    ((completeRowsMeasure p).prod (selectedIndexPrivateLaw p j)).real
      {w : CompleteRows p × ExtendedPrivateCoordinates p |
        ((ids, w.1), w.2) ∈ actualSelectedIndexAnyFalseForwardPrefixPassSet
          C_star C_h rate.eta rewards} ≤
      (n_boot p : ℝ) * (p.m - 1 : ℝ) * (Fintype.card (FalseRow p j) : ℝ) *
        forwardTrueProbability p ^ q_dec p := by
  constructor
  · exact (measurableSet_actualSelectedIndexAnyFalseForwardPrefixPassSet
      C_star C_h rate.eta rewards).preimage
        ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  · have hbound := fixedID_fixed_event_measure_le C_star C_h rate.eta rewards ids j
    rw [← fixedID_selected_event_measure_eq C_star C_h rate.eta rewards ids j] at hbound
    have hm1 : 0 ≤ (p.m : ℝ) - 1 := by
      have hmNat : 1 ≤ p.m := Nat.le_trans (by decide) p.two_le_m
      exact sub_nonneg.mpr (by exact_mod_cast hmNat)
    have hc : 0 ≤ (n_boot p : ℝ) * (p.m - 1 : ℝ) *
        (Fintype.card (FalseRow p j) : ℝ) * forwardTrueProbability p ^ q_dec p :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hm1) (Nat.cast_nonneg _))
        (pow_nonneg (forwardTrueProbability_nonneg p) _)
    exact ENNReal.toReal_le_of_le_ofReal hc hbound

private theorem fixedID_falseForward_tail_le_inv_N_sq
    (p : ConstructorDimensions.Parameters) (j : Fin (M p)) :
    (BootstrapDimensions.n_boot p : ℝ) * (p.m - 1 : ℝ) *
        (Fintype.card (FalseRow p j) : ℝ) *
          ForwardPrefixSlice.forwardTrueProbability p ^ BootstrapDimensions.q_dec p ≤
      1 / (ConstructorDimensions.N p : ℝ) ^ 2 := by
  have hcardFalse : Fintype.card (FalseRow p j) ≤ ConstructorDimensions.M p := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      (fun v : FalseRow p j => v.1) (fun _ _ h => Subtype.ext h)
  have hKtwo : 1 ≤ p.K ^ 2 := Nat.one_le_pow _ _ (ConstructorDimensions.K_pos p)
  have hcountNat : BootstrapDimensions.n_boot p * (p.m - 1) *
      Fintype.card (FalseRow p j) ≤ ConstructorDimensions.N p ^ 6 := by
    calc
      _ ≤ BootstrapDimensions.n_boot p * (p.m - 1) * ConstructorDimensions.M p :=
        Nat.mul_le_mul_left _ hcardFalse
      _ = BootstrapDimensions.n_boot p * ConstructorDimensions.M p * (p.m - 1) := by ac_rfl
      _ ≤ (BootstrapDimensions.n_boot p * ConstructorDimensions.M p * (p.m - 1)) * p.K ^ 2 := by
        have h := Nat.mul_le_mul_left
          (BootstrapDimensions.n_boot p * ConstructorDimensions.M p * (p.m - 1)) hKtwo
        simpa using h
      _ ≤ ConstructorDimensions.N p ^ 6 :=
        FalseForwardContextBound.context_coordinate_count_le_N_six p
  have hcountReal : (BootstrapDimensions.n_boot p : ℝ) * (p.m - 1 : ℝ) *
      (Fintype.card (FalseRow p j) : ℝ) ≤ (ConstructorDimensions.N p : ℝ) ^ 6 := by
    have hmNat : 1 ≤ p.m := Nat.le_trans (by decide) p.two_le_m
    have hm : ((p.m - 1 : ℕ) : ℝ) = (p.m : ℝ) - 1 := by
      rw [Nat.cast_sub hmNat]
      norm_num
    calc
      _ = ((BootstrapDimensions.n_boot p * (p.m - 1) *
            Fintype.card (FalseRow p j) : ℕ) : ℝ) := by
          rw [← hm]
          push_cast
          ring
      _ ≤ ((ConstructorDimensions.N p ^ 6 : ℕ) : ℝ) := by exact_mod_cast hcountNat
      _ = (ConstructorDimensions.N p : ℝ) ^ 6 := by norm_num
  have hpiq := ForwardPrefixSlice.forwardTrueProbability_le_exp_bound p
  have hNpos : 0 < (ConstructorDimensions.N p : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
  have hNpow : (ConstructorDimensions.N p : ℝ) ≤
      (2 : ℝ) ^ ConstructorDimensions.b_N p := by
    have hNnat : ConstructorDimensions.N p ≤
        2 ^ ConstructorDimensions.b_N p := by
      change ConstructorDimensions.N p ≤ ConstructorDimensions.D p
      exact (ConstructorDimensions.N_lt_D p).le
    exact_mod_cast hNnat
  have hexpTwo : (2 : ℝ) ≤ Real.exp 1 := by
    calc
      (2 : ℝ) = 1 + 1 := by norm_num
      _ ≤ Real.exp 1 := Real.add_one_le_exp 1
  have hexpPow : (2 : ℝ) ^ (8 * ConstructorDimensions.b_N p) ≤
      Real.exp (8 * (ConstructorDimensions.b_N p : ℝ)) := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hexpTwo
      (8 * ConstructorDimensions.b_N p)
    have hexpeq : Real.exp (8 * (ConstructorDimensions.b_N p : ℝ)) =
        (Real.exp 1) ^ (8 * ConstructorDimensions.b_N p) := by
      rw [show 8 * (ConstructorDimensions.b_N p : ℝ) =
        ((8 * ConstructorDimensions.b_N p : ℕ) : ℝ) by norm_num]
      rw [← Real.exp_nat_mul (1 : ℝ) (8 * ConstructorDimensions.b_N p)]
      congr 1
      norm_num
    exact hpow.trans_eq hexpeq.symm
  have hNpow8 : (ConstructorDimensions.N p : ℝ) ^ 8 ≤
      (2 : ℝ) ^ (8 * ConstructorDimensions.b_N p) := by
    calc
      (ConstructorDimensions.N p : ℝ) ^ 8 ≤
          ((2 : ℝ) ^ ConstructorDimensions.b_N p) ^ 8 :=
        pow_le_pow_left₀ (by positivity) hNpow 8
      _ = (2 : ℝ) ^ (8 * ConstructorDimensions.b_N p) := by
        rw [← pow_mul]
        congr 1
        omega
  have hexpLower : (ConstructorDimensions.N p : ℝ) ^ 8 ≤
      Real.exp (8 * (ConstructorDimensions.b_N p : ℝ)) := hNpow8.trans hexpPow
  have hexpNeg : Real.exp (-8 * (ConstructorDimensions.b_N p : ℝ)) ≤
      1 / (ConstructorDimensions.N p : ℝ) ^ 8 := by
    rw [show -8 * (ConstructorDimensions.b_N p : ℝ) =
      -(8 * (ConstructorDimensions.b_N p : ℝ)) by ring]
    rw [Real.exp_neg]
    have hinv := (inv_le_inv₀ (Real.exp_pos _) (pow_pos hNpos 8)).2 hexpLower
    simpa only [one_div] using hinv
  calc
      _ ≤ (ConstructorDimensions.N p : ℝ) ^ 6 *
          ForwardPrefixSlice.forwardTrueProbability p ^ BootstrapDimensions.q_dec p :=
        mul_le_mul_of_nonneg_right hcountReal
          (pow_nonneg (ForwardPrefixSlice.forwardTrueProbability_nonneg p) _)
      _ ≤ (ConstructorDimensions.N p : ℝ) ^ 6 *
          Real.exp (-8 * (ConstructorDimensions.b_N p : ℝ)) :=
        mul_le_mul_of_nonneg_left hpiq (by positivity)
      _ ≤ (ConstructorDimensions.N p : ℝ) ^ 6 *
          (1 / (ConstructorDimensions.N p : ℝ) ^ 8) :=
        mul_le_mul_of_nonneg_left hexpNeg (by positivity)
      _ = 1 / (ConstructorDimensions.N p : ℝ) ^ 2 := by
        field_simp [ne_of_gt hNpos]

private theorem fixedID_selected_event_eq_actual
    {p : ConstructorDimensions.Parameters}
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (ids : IDArray p) :
    {w : CompleteRows p × ExtendedPrivateCoordinates p |
      ((ids, w.1), w.2) ∈ actualSelectedIndexAnyFalseForwardPrefixPassSet
        C_star C_h eta rewards} =
    {w : CompleteRows p × ExtendedPrivateCoordinates p |
      ((ids, w.1), w.2) ∈ actualAnyFalseForwardPrefixPassSet C_star C_h eta rewards
        (ActualInitializationPhysicalStep.selectedRowIndex p ((ids, w.1), w.2))} := by
  apply Set.ext
  intro w
  exact Iff.of_eq (congrArg
    (fun k : Fin (M p) => ((ids, w.1), w.2) ∈
      actualAnyFalseForwardPrefixPassSet C_star C_h eta rewards k)
    (show PrivateSourceStreams.coordinatorIndex p w.2.1.2 =
      ActualInitializationPhysicalStep.selectedRowIndex p ((ids, w.1), w.2) from rfl))

/-- Fixed-ID false-forward probability under the original selected-index
restriction. The source event is the literal actual any-false-forward prefix
pass event, and `e` retains the complete original private tuple. -/
theorem actualAnyFalseForwardPrefixPassSet_fixedID_measureReal_le_inv_N_sq
    {p : ConstructorDimensions.Parameters}
    (rate : Bandits.Support.ReferenceActivePhysicalStep.RateInput p)
    (ids : CompletePublicTable.IDArray p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (ConstructorDimensions.M p)) :
    MeasurableSet
      {w : CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p |
        (((ids, w.1), w.2) ∈
          GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
            C_star C_h rate.eta rewards
            (ActualInitializationPhysicalStep.selectedRowIndex p ((ids, w.1), w.2)))} ∧
    ((CompletePublicTable.completeRowsMeasure p).prod
        (ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j)).real
      {w : CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p |
        (((ids, w.1), w.2) ∈
          GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
            C_star C_h rate.eta rewards
            (ActualInitializationPhysicalStep.selectedRowIndex p ((ids, w.1), w.2)))} ≤
      (BootstrapDimensions.n_boot p : ℝ) * (p.m - 1 : ℝ) *
        (Fintype.card (FalseRow p j) : ℝ) *
          ForwardPrefixSlice.forwardTrueProbability p ^ BootstrapDimensions.q_dec p ∧
    (BootstrapDimensions.n_boot p : ℝ) * (p.m - 1 : ℝ) *
        (Fintype.card (FalseRow p j) : ℝ) *
          ForwardPrefixSlice.forwardTrueProbability p ^ BootstrapDimensions.q_dec p ≤
      1 / (ConstructorDimensions.N p : ℝ) ^ 2 := by
  rw [← fixedID_selected_event_eq_actual C_star C_h rate.eta rewards ids]
  have h := fixedID_selected_event_measureReal_le p rate ids rewards C_star C_h j
  have ht := fixedID_falseForward_tail_le_inv_N_sq p j
  exact ⟨h.1, h.2, ht⟩

end Bandits.Support.GeneratedFixedIDSelectedIndexForwardTail

end
