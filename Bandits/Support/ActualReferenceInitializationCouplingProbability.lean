/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedFixedIDSelectedIndexForwardTail
public import Bandits.Support.GeneratedInitializationFailureTail
public import Bandits.Support.InitializationRowEventProvenance
public import Bandits.Support.ActualReferenceInitializationHorizon

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Fixed-ID initialization coupling probability

The initialization-failure event and the incorrect-row false-forward event
are kept separate on the complete-row and original-private product. Their
literal union has the advertised near-full probability, and on its complement
the accepted actual/reference initialization theorem supplies physical
correspondence at the same published output.

Sources: `sources/zip4/manuscript/07_public_setup.tex:127-164`,
`sources/zip4/manuscript/08_main_theorem.tex:29-47,67-83`, and
`sources/zip4/manuscript/appendix_b_communication.tex:724-798`.
This is an internal probability-to-physical composition, not a manuscript
proposition or regret closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open _root_.Bandits.Support.ConstructorDimensions
open _root_.Bandits.Support.BootstrapPrivateRoundStreams
open _root_.Bandits.Support.CompletePublicTable
open _root_.Bandits.Support.PrivateSourceStreams
open Bandits.Support.InitializationRowEventProvenance
open Bandits.Support.InitializationRowObservables
open Bandits.Support.InitializationRowObservables renaming
  initializationFailureEvent → rowInitializationFailureEvent
open Bandits.Support.GeneratedInitializationFailureTail
open Bandits.Support.GeneratedInitializationFailureTail renaming
  initializationFailureEvent → generatedInitializationFailureEvent
open Bandits.Support.GeneratedFixedIDSelectedIndexForwardTail
open scoped ENNReal

namespace Bandits.Support.ActualReferenceInitializationCouplingProbability

/-- The selected-row initialization-failure event has exactly the fixed-row
operational-event mass under the original private law restricted to `J = j`.
The set keeps all complete rows and the original private tuple. -/
theorem initializationFailureEvent_measure_eq_originalLaw
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (ids : CompletePublicTable.IDArray p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (ConstructorDimensions.M p)) :
    MeasurableSet
      {w : CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p |
        InitializationFailureProvenance.operationalInitializationFailure
          (ActualReferenceInitializationBlock.referenceInput
            ((ids, w.1), w.2) rewards C_star C_h rate)} ∧
    ((CompletePublicTable.completeRowsMeasure p).prod
        (ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j))
      {w : CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p |
        InitializationFailureProvenance.operationalInitializationFailure
          (ActualReferenceInitializationBlock.referenceInput
            ((ids, w.1), w.2) rewards C_star C_h rate)} =
      GeneratedBootstrapRoundLaw.originalLaw p
        (generatedInitializationFailureEvent
          p ids rewards C_star C_h rate.eta) := by
  let Einit : Set (CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p) :=
    {w | InitializationFailureProvenance.operationalInitializationFailure
      (ActualReferenceInitializationBlock.referenceInput ((ids, w.1), w.2)
        rewards C_star C_h rate)}
  let μ : Measure (CompletePublicTable.CompleteRows p) :=
    CompletePublicTable.completeRowsMeasure p
  let ν : Measure (ExtendedPrivateCoordinates p) :=
    BootstrapPrivateRoundStreams.extendedPrivateLaw p
  let cell : Set (ExtendedPrivateCoordinates p) :=
    ReferenceCompleteSelectedRowExpectation.indexCell p j
  have hactual : Einit =
      {w : CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p |
        w.2 ∈ actualInitializationFailureEvent
          p ids rewards C_star C_h rate.eta w.1} := by
    ext w
    rcases w with ⟨rows, e⟩
    exact (actualInitializationFailureEvent_iff_operationalInitializationFailure
        p ids rewards C_star C_h rate.eta rows e).symm
  have hmeas : MeasurableSet Einit := by
    rw [hactual]
    exact measurable_actualInitializationFailureEvent_pair
      p ids rewards C_star C_h rate.eta
  have hprodRestrict :
      μ.prod (ν.restrict cell) =
        (μ.prod ν).restrict (Set.univ ×ˢ cell) := by
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := μ) (ν := ν) Set.univ cell)
  have hscale :
      (μ.prod (ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j)) Einit =
        ENNReal.ofReal (ConstructorDimensions.M p : ℝ) *
          ((μ.prod ν).restrict (Set.univ ×ˢ cell)) Einit := by
    rw [ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw,
      Measure.prod_smul_right, Measure.smul_apply, smul_eq_mul, hprodRestrict]
  have hrestrict :
      ((μ.prod ν).restrict (Set.univ ×ˢ cell)) Einit =
        (μ.prod ν) (Einit ∩ (Set.univ ×ˢ cell)) :=
    Measure.restrict_apply hmeas
  have hswap : MeasurePreserving Prod.swap (ν.prod μ) (μ.prod ν) :=
    Measure.measurePreserving_swap
  have htarget : MeasurableSet (Einit ∩ (Set.univ ×ˢ cell)) :=
    hmeas.inter (MeasurableSet.univ.prod
      (ReferenceCompleteSelectedRowExpectation.measurableSet_indexCell p j))
  have hpre : Prod.swap ⁻¹' (Einit ∩ (Set.univ ×ˢ cell)) =
      {z : ExtendedPrivateCoordinates p × CompletePublicTable.CompleteRows p |
        z.1 ∈ cell ∧ (z.2, z.1) ∈ Einit} := by
    ext z
    rcases z with ⟨e, rows⟩
    simp only [Set.mem_preimage, Prod.swap, Set.mem_inter_iff, Set.mem_prod,
      Set.mem_univ, true_and, Set.mem_ofPred_eq, and_comm]
  have hswapMass :
      (μ.prod ν) (Einit ∩ (Set.univ ×ˢ cell)) =
        SelectedIndexLaunchJointLaw.originalLaw p
          {z : SelectedIndexLaunchJointLaw.OriginalCoordinates p |
            z.1 ∈ cell ∧ (z.2, z.1) ∈ Einit} := by
    change (μ.prod ν) (Einit ∩ (Set.univ ×ˢ cell)) =
      (ν.prod μ) {z : ExtendedPrivateCoordinates p × CompletePublicTable.CompleteRows p |
        z.1 ∈ cell ∧ (z.2, z.1) ∈ Einit}
    rw [← hswap.map_eq, Measure.map_apply hswap.measurable htarget, hpre]
  have hleft :
      {z : SelectedIndexLaunchJointLaw.OriginalCoordinates p |
        z.1 ∈ cell ∧ (z.2, z.1) ∈ Einit} =
      {z : SelectedIndexLaunchJointLaw.OriginalCoordinates p |
        PrivateSourceStreams.coordinatorIndex p z.1.1.2 = j ∧
          z.1 ∈ actualInitializationFailureEvent
            p ids rewards C_star C_h rate.eta z.2} := by
    ext z
    rcases z with ⟨e, rows⟩
    change (e ∈ cell ∧ InitializationFailureProvenance.operationalInitializationFailure
        (ActualReferenceInitializationBlock.referenceInput
          ((ids, rows), e) rewards C_star C_h rate)) ↔
      (PrivateSourceStreams.coordinatorIndex p e.1.2 = j ∧
        e ∈ actualInitializationFailureEvent
          p ids rewards C_star C_h rate.eta rows)
    change (PrivateSourceStreams.coordinatorIndex p e.1.2 = j ∧
        InitializationFailureProvenance.operationalInitializationFailure
          (ActualReferenceInitializationBlock.referenceInput
            ((ids, rows), e) rewards C_star C_h rate)) ↔
      (PrivateSourceStreams.coordinatorIndex p e.1.2 = j ∧
        e ∈ actualInitializationFailureEvent
          p ids rewards C_star C_h rate.eta rows)
    exact and_congr_right fun _ =>
      (actualInitializationFailureEvent_iff_operationalInitializationFailure
          p ids rewards C_star C_h rate.eta rows e).symm
  have hright :
      generatedInitializationFailureEvent
          p ids rewards C_star C_h rate.eta =
        {z : CompletePublicTable.CompleteRow p × ExtendedPrivateCoordinates p |
          z.2 ∈ rowInitializationFailureEvent
            p ids rewards C_star C_h rate.eta z.1} := by
    exact initializationFailureEvent_eq_terminalFlagProduct p ids rewards C_star C_h rate.eta
  have hdisintegration := actualFailureEvent_selectedIndex_disintegration
      p ids rewards C_star C_h rate.eta j
  have hdisintegrationEcell :
      SelectedIndexLaunchJointLaw.originalLaw p
          {z : SelectedIndexLaunchJointLaw.OriginalCoordinates p |
            z.1 ∈ cell ∧ (z.2, z.1) ∈ Einit} =
        ENNReal.ofReal (1 / (ConstructorDimensions.M p : ℝ)) *
          GeneratedBootstrapRoundLaw.originalLaw p
            (generatedInitializationFailureEvent p ids rewards C_star C_h rate.eta) := by
    calc
      _ = SelectedIndexLaunchJointLaw.originalLaw p
          {z : SelectedIndexLaunchJointLaw.OriginalCoordinates p |
            PrivateSourceStreams.coordinatorIndex p z.1.1.2 = j ∧
              z.1 ∈ actualInitializationFailureEvent
                p ids rewards C_star C_h rate.eta z.2} := by
          rw [hleft]
      _ = ENNReal.ofReal (1 / (ConstructorDimensions.M p : ℝ)) *
          GeneratedBootstrapRoundLaw.originalLaw p
            {z : CompletePublicTable.CompleteRow p × ExtendedPrivateCoordinates p |
              z.2 ∈ rowInitializationFailureEvent p ids rewards C_star C_h rate.eta z.1} :=
          hdisintegration
      _ = ENNReal.ofReal (1 / (ConstructorDimensions.M p : ℝ)) *
          GeneratedBootstrapRoundLaw.originalLaw p
            (generatedInitializationFailureEvent p ids rewards C_star C_h rate.eta) := by
          rw [← hright]
  have hmass :
      (μ.prod (ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j)) Einit =
        ENNReal.ofReal (ConstructorDimensions.M p : ℝ) *
          (ENNReal.ofReal (1 / (ConstructorDimensions.M p : ℝ)) *
            GeneratedBootstrapRoundLaw.originalLaw p
            (generatedInitializationFailureEvent
                p ids rewards C_star C_h rate.eta)) := by
    rw [hscale, hrestrict, hswapMass, hdisintegrationEcell]
  have hM : 0 < (ConstructorDimensions.M p : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.M_pos p)
  have hcancel :
      ENNReal.ofReal (ConstructorDimensions.M p : ℝ) *
          (ENNReal.ofReal (1 / (ConstructorDimensions.M p : ℝ)) *
            GeneratedBootstrapRoundLaw.originalLaw p
            (generatedInitializationFailureEvent
                p ids rewards C_star C_h rate.eta)) =
        GeneratedBootstrapRoundLaw.originalLaw p
          (generatedInitializationFailureEvent
            p ids rewards C_star C_h rate.eta) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul hM.le,
      mul_one_div_cancel hM.ne', ENNReal.ofReal_one, one_mul]
  constructor
  · exact hmeas
  · rw [hmass, hcancel]

/-- The literal union of initialization failure and an incorrect-row false
forward pass is Borel and has real mass at most `9/(4N^2)`, hence at most
`5/N^2`. Its complement has the corresponding near-full probability. -/
theorem initializationBadUnion_probability_bounds
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (ids : CompletePublicTable.IDArray p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (ConstructorDimensions.M p))
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (hC_h : (4096 : ℝ) ≤ C_h) (hCstar : (2 : ℝ) ^ 20 ≤ C_star) :
    MeasurableSet
      ({w : CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p |
          InitializationFailureProvenance.operationalInitializationFailure
            (ActualReferenceInitializationBlock.referenceInput
              ((ids, w.1), w.2) rewards C_star C_h rate)} ∪
        {w : CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p |
          ((ids, w.1), w.2) ∈ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
            C_star C_h rate.eta rewards
            (ActualInitializationPhysicalStep.selectedRowIndex p ((ids, w.1), w.2))}) ∧
    ((CompletePublicTable.completeRowsMeasure p).prod
        (ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j)).real
      ({w : CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p |
          InitializationFailureProvenance.operationalInitializationFailure
            (ActualReferenceInitializationBlock.referenceInput
              ((ids, w.1), w.2) rewards C_star C_h rate)} ∪
        {w : CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p |
          ((ids, w.1), w.2) ∈ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
            C_star C_h rate.eta rewards
            (ActualInitializationPhysicalStep.selectedRowIndex p ((ids, w.1), w.2))}) ≤
      9 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) ∧
    ((CompletePublicTable.completeRowsMeasure p).prod
        (ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j)).real
      ({w : CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p |
          InitializationFailureProvenance.operationalInitializationFailure
            (ActualReferenceInitializationBlock.referenceInput
              ((ids, w.1), w.2) rewards C_star C_h rate)} ∪
        {w : CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p |
          ((ids, w.1), w.2) ∈ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
            C_star C_h rate.eta rewards
            (ActualInitializationPhysicalStep.selectedRowIndex p ((ids, w.1), w.2))}) ≤
      5 / (ConstructorDimensions.N p : ℝ) ^ 2 ∧
    1 - 5 / (ConstructorDimensions.N p : ℝ) ^ 2 ≤
      ((CompletePublicTable.completeRowsMeasure p).prod
        (ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j)).real
        ({w : CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p |
            InitializationFailureProvenance.operationalInitializationFailure
              (ActualReferenceInitializationBlock.referenceInput
                ((ids, w.1), w.2) rewards C_star C_h rate)} ∪
          {w : CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p |
            ((ids, w.1), w.2) ∈ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
              C_star C_h rate.eta rewards
              (ActualInitializationPhysicalStep.selectedRowIndex p ((ids, w.1), w.2))})ᶜ := by
  let μ : Measure (CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p) :=
    (CompletePublicTable.completeRowsMeasure p).prod
      (ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j)
  let Einit : Set (CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p) :=
    {w | InitializationFailureProvenance.operationalInitializationFailure
      (ActualReferenceInitializationBlock.referenceInput ((ids, w.1), w.2)
        rewards C_star C_h rate)}
  let Efwd : Set (CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p) :=
    {w | ((ids, w.1), w.2) ∈ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
      C_star C_h rate.eta rewards
      (ActualInitializationPhysicalStep.selectedRowIndex p ((ids, w.1), w.2))}
  let B := Einit ∪ Efwd
  have hinit := initializationFailureEvent_measure_eq_originalLaw
    rate ids rewards C_star C_h j
  have hforward := actualAnyFalseForwardPrefixPassSet_fixedID_measureReal_le_inv_N_sq
      rate ids rewards C_star C_h j
  have hinitBound : μ.real Einit ≤
      5 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) := by
    change ENNReal.toReal
        ((CompletePublicTable.completeRowsMeasure p).prod
          (ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j)
          Einit) ≤ _
    rw [hinit.2]
    exact (initializationFailureEvent_real_probability_bounds
      p ids rewards C_star C_h rate.eta hgood hC_h hCstar).2.1
  have hforwardBound : μ.real Efwd ≤ 1 / (ConstructorDimensions.N p : ℝ) ^ 2 := by
    exact hforward.2.1.trans hforward.2.2
  have hBorel : MeasurableSet B := by
    exact hinit.1.union hforward.1
  have hNpos : 0 < (ConstructorDimensions.N p : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
  have hdenpos : 0 < (ConstructorDimensions.N p : ℝ) ^ 2 := pow_pos hNpos 2
  have hsum :
      5 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) +
        1 / (ConstructorDimensions.N p : ℝ) ^ 2 =
          9 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) := by
    field_simp [ne_of_gt hdenpos]; ring
  have hBbound : μ.real B ≤
      9 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) := by
    calc
      μ.real B ≤ μ.real Einit + μ.real Efwd := MeasureTheory.measureReal_union_le _ _
      _ ≤ 5 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) +
          1 / (ConstructorDimensions.N p : ℝ) ^ 2 := add_le_add hinitBound hforwardBound
      _ = 9 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) := hsum
  have hBsmall : μ.real B ≤ 5 / (ConstructorDimensions.N p : ℝ) ^ 2 := by
    calc
      μ.real B ≤ 9 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) := hBbound
      _ = (9 / 4) / (ConstructorDimensions.N p : ℝ) ^ 2 := by ring
      _ ≤ 5 / (ConstructorDimensions.N p : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (by norm_num : (9 / 4 : ℝ) ≤ 5) hdenpos.le
  have hcomplement : 1 - 5 / (ConstructorDimensions.N p : ℝ) ^ 2 ≤ μ.real Bᶜ := by
    rw [MeasureTheory.probReal_compl_eq_one_sub (μ := μ) hBorel]
    exact sub_le_sub_left hBsmall 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hBorel
  · exact hBbound
  · exact hBsmall
  · exact hcomplement

/-- On the complement of the literal initialization/false-forward union, the
same actual initialized run has the accepted reference-history, counter, and
follower-carry correspondence. The launch and exhaustion branch consumers in
`ActualReferenceInitializationHorizon` retain their original terminal guards
on this same event. -/
theorem sourceInitializedRun_nearFullEvent_correspondence
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (ids : CompletePublicTable.IDArray p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (ConstructorDimensions.M p))
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (hC_h : (4096 : ℝ) ≤ C_h) (hCstar : (2 : ℝ) ^ 20 ≤ C_star) :
    MeasurableSet
      ({w : CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p |
          InitializationFailureProvenance.operationalInitializationFailure
            (ActualReferenceInitializationBlock.referenceInput
              ((ids, w.1), w.2) rewards C_star C_h rate)} ∪
        {w : CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p |
          ((ids, w.1), w.2) ∈ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
            C_star C_h rate.eta rewards
            (ActualInitializationPhysicalStep.selectedRowIndex p ((ids, w.1), w.2))}) ∧
    1 - 5 / (ConstructorDimensions.N p : ℝ) ^ 2 ≤
      ((CompletePublicTable.completeRowsMeasure p).prod
        (ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j)).real
        ({w : CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p |
            InitializationFailureProvenance.operationalInitializationFailure
              (ActualReferenceInitializationBlock.referenceInput
                ((ids, w.1), w.2) rewards C_star C_h rate)} ∪
          {w : CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p |
            ((ids, w.1), w.2) ∈ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
              C_star C_h rate.eta rewards
              (ActualInitializationPhysicalStep.selectedRowIndex p ((ids, w.1), w.2))})ᶜ ∧
    ∀ w : CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p,
      w ∉
          ({w : CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p |
              InitializationFailureProvenance.operationalInitializationFailure
                (ActualReferenceInitializationBlock.referenceInput
                  ((ids, w.1), w.2) rewards C_star C_h rate)} ∪
            {w : CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p |
              ((ids, w.1), w.2) ∈
                GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
                  C_star C_h rate.eta rewards
                  (ActualInitializationPhysicalStep.selectedRowIndex p ((ids, w.1), w.2))}) →
      let x := ActualReferenceInitializationBlock.referenceInput ((ids, w.1), w.2)
        rewards C_star C_h rate
      let result := ActualInitializationHorizon.sourceInitializedRun p rate
        ((ids, w.1), w.2) rewards C_star C_h
      ActualReferenceInitializationBlock.past_related result.records
        (ReferenceInitializationRun.output x) ∧
        result.terminalFold.phase.monitorState.counters =
          (ReferenceInitializationRun.output x).counters ∧
        (∀ i, (ReferenceInitializationRun.output x).forcedFailure i = false) ∧
        ∀ i, ActualReferenceInitializationBlock.follower_start_related
          x ((ids, w.1), w.2) rate rfl
          (ReferenceInitializationRun.output x) i
          (ActualInitializationRun.followerCarryOfBoundaryOutput rate
            (result.terminalHandoff.followers i)) := by
  let μ : Measure (CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p) :=
    (CompletePublicTable.completeRowsMeasure p).prod
      (ReferenceCompleteSelectedRowExpectation.selectedIndexPrivateLaw p j)
  let Einit : Set (CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p) :=
    {w | InitializationFailureProvenance.operationalInitializationFailure
      (ActualReferenceInitializationBlock.referenceInput ((ids, w.1), w.2)
        rewards C_star C_h rate)}
  let Efwd : Set (CompletePublicTable.CompleteRows p × ExtendedPrivateCoordinates p) :=
    {w | ((ids, w.1), w.2) ∈ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
      C_star C_h rate.eta rewards
      (ActualInitializationPhysicalStep.selectedRowIndex p ((ids, w.1), w.2))}
  let B := Einit ∪ Efwd
  have hprob := initializationBadUnion_probability_bounds
    rate ids rewards C_star C_h j hgood hC_h hCstar
  have hBorel : MeasurableSet B := by
    simpa only [Einit, Efwd, B] using hprob.1
  have hcomplement :
      1 - 5 / (ConstructorDimensions.N p : ℝ) ^ 2 ≤ μ.real Bᶜ := by
    simpa only [Einit, Efwd, B, μ] using hprob.2.2.2
  have hpointwise : ∀ w, w ∉ B →
      let x := ActualReferenceInitializationBlock.referenceInput ((ids, w.1), w.2)
        rewards C_star C_h rate
      let result := ActualInitializationHorizon.sourceInitializedRun p rate
        ((ids, w.1), w.2) rewards C_star C_h
      ActualReferenceInitializationBlock.past_related result.records
        (ReferenceInitializationRun.output x) ∧
        result.terminalFold.phase.monitorState.counters =
          (ReferenceInitializationRun.output x).counters ∧
        (∀ i, (ReferenceInitializationRun.output x).forcedFailure i = false) ∧
        ∀ i, ActualReferenceInitializationBlock.follower_start_related
          x ((ids, w.1), w.2) rate rfl
          (ReferenceInitializationRun.output x) i
          (ActualInitializationRun.followerCarryOfBoundaryOutput rate
            (result.terminalHandoff.followers i)) := by
    intro w hw
    have hnot : w ∉ Einit ∧ w ∉ Efwd := by
      change w ∉ Einit ∪ Efwd at hw
      exact not_or.mp hw
    have hinit : ¬ InitializationFailureProvenance.operationalInitializationFailure
        (ActualReferenceInitializationBlock.referenceInput ((ids, w.1), w.2)
          rewards C_star C_h rate) := by
      simpa only [Einit, Set.mem_ofPred_eq] using hnot.1
    have hfalse : ((ids, w.1), w.2) ∉
        GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
          C_star C_h rate.eta rewards
          (ActualInitializationPhysicalStep.selectedRowIndex p ((ids, w.1), w.2)) := by
      simpa only [Efwd, Set.mem_ofPred_eq] using hnot.2
    dsimp only
    have hrelated := ActualReferenceInitializationHorizon.sourceInitializedRun_output_related
      p rate ((ids, w.1), w.2) rewards C_star C_h hinit hfalse
    exact ⟨hrelated.2.1, hrelated.2.2.1, hrelated.2.2.2.1, hrelated.2.2.2.2⟩
  refine ⟨?_, ?_, hpointwise⟩
  · simpa only [Einit, Efwd, B] using hBorel
  · simpa only [Einit, Efwd, B, μ] using hcomplement

end Bandits.Support.ActualReferenceInitializationCouplingProbability

end
