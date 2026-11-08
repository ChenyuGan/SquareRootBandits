/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLivePastPairKernelTransport

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Original-source first-LIVE observed-kernel mixture

Assemble the two unnormalized original-source transports with the actual
same-family observed slice kernel. The strict-past overflow test is computed
from the retained remainder on both sides; the complete calendar past,
current affine family, full auxiliary array, and correlated recorder/FAST
pair remain in the tested output.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Bandits.Support.ReferenceFirstLiveObservedKernelSourceLaw

open ReferenceFirstLivePastPairKernelTransport
open ReferenceFirstLiveCanonicalProposalJointLaw
open ReferenceFirstLiveChronologicalPrefixCausality
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLivePostUpdateProposalLaw hiding LiveRemainder
open ReferenceFirstLiveRecordingSourceCylinder
open ReferenceFirstLiveEmptyPendingMarkerLaw

variable {p : ConstructorDimensions.Parameters}

abbrev RateInput := ReferenceFirstLivePastPairKernelTransport.RateInput
abbrev RewardTable := ReferenceFirstLivePastPairKernelTransport.RewardTable
abbrev AuxiliaryArray := ReferenceFirstLivePastPairKernelTransport.AuxiliaryArray
abbrev LiveRemainder (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) :=
  ReferenceFirstLivePastPairKernelTransport.LiveRemainder
    rate rewards C_star C_h q t s hs control0
abbrev PastObservationPair (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) :=
  ReferenceFirstLivePastPairKernelTransport.PastObservationPair
    rate rewards C_star C_h q t s hs control0

variable (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p)

private theorem integral_slice_family_aux_swap
    (f : ContinuousControlSlice.Slice p.m p.K →
      ContinuousLearningRows.AffineSamples p → AuxiliaryArray p → ℝ)
    (hf : Measurable (fun z :
      (ContinuousControlSlice.Slice p.m p.K × ContinuousLearningRows.AffineSamples p) ×
        AuxiliaryArray p => f z.1.1 z.1.2 z.2))
    (C : ℝ)
    (hC : ∀ slice family aux, ‖f slice family aux‖ ≤ C) :
    (∫ slice, ∫ family, ∫ aux, f slice family aux
      ∂ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
      ∂ContinuousLearningRows.affineSamplesLaw p
      ∂ContinuousControlSlice.sliceLaw p.m p.K) =
    ∫ family, ∫ aux, ∫ slice, f slice family aux
      ∂ContinuousControlSlice.sliceLaw p.m p.K
      ∂ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
      ∂ContinuousLearningRows.affineSamplesLaw p := by
  let slices := ContinuousControlSlice.sliceLaw p.m p.K
  let families := ContinuousLearningRows.affineSamplesLaw p
  let auxLaw := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  have hfull : Integrable (fun z :
      (ContinuousControlSlice.Slice p.m p.K × ContinuousLearningRows.AffineSamples p) ×
        AuxiliaryArray p => f z.1.1 z.1.2 z.2) ((slices.prod families).prod auxLaw) :=
    Integrable.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun z => hC z.1.1 z.1.2 z.2)
  let g := fun slice : ContinuousControlSlice.Slice p.m p.K =>
    fun family : ContinuousLearningRows.AffineSamples p =>
      ∫ aux, f slice family aux ∂auxLaw
  have hGint : Integrable (fun z :
      ContinuousControlSlice.Slice p.m p.K × ContinuousLearningRows.AffineSamples p =>
        ∫ aux, f z.1 z.2 aux ∂auxLaw) (slices.prod families) :=
    hfull.integral_prod_left
  have hswap := MeasureTheory.integral_integral_swap (f := g) hGint
  have hinner (family : ContinuousLearningRows.AffineSamples p) :
      ∫ slice, ∫ aux, f slice family aux ∂auxLaw ∂slices =
        ∫ aux, ∫ slice, f slice family aux ∂slices ∂auxLaw := by
    let sectionMap := fun z : ContinuousControlSlice.Slice p.m p.K × AuxiliaryArray p =>
      ((z.1, family), z.2)
    have hsection : Measurable (fun z :
        ContinuousControlSlice.Slice p.m p.K × AuxiliaryArray p =>
          f z.1 family z.2) := by
      have hm : Measurable sectionMap :=
        ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
      exact (hf.comp hm)
    let gInner := fun slice : ContinuousControlSlice.Slice p.m p.K =>
      fun aux : AuxiliaryArray p => f slice family aux
    have hsectionInt : Integrable (fun z :
        ContinuousControlSlice.Slice p.m p.K × AuxiliaryArray p =>
          f z.1 family z.2) (slices.prod auxLaw) :=
      Integrable.of_bound hsection.aestronglyMeasurable C
        (Filter.Eventually.of_forall fun z => hC z.1 family z.2)
    exact MeasureTheory.integral_integral_swap (f := gInner) hsectionInt
  calc
    _ = ∫ family, ∫ slice, ∫ aux, f slice family aux
        ∂auxLaw ∂slices ∂families := hswap
    _ = ∫ family, ∫ aux, ∫ slice, f slice family aux
        ∂slices ∂auxLaw ∂families := by
          apply integral_congr_ae
          filter_upwards with family
          exact hinner family

private theorem fixedFamily_observed_test_integral
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0)
    (family : ContinuousLearningRows.AffineSamples p)
    (aux : AuxiliaryArray p)
    (F : PastObservationPair rate rewards C_star C_h q t s hs control0 → ℝ)
    (hF : Measurable F) :
    (∫ slice,
      (if (liveNumericalPast rate rewards C_star C_h q t s hs control0 x).2.1 = false
        then F (recorderFastPastObservation rate rewards C_star C_h q t s hs control0
          (x, (family, aux)),
          liveMarkerFastPair rate rewards C_star C_h q t s hs control0
            (x, (slice, family))) else 0)
      ∂ContinuousControlSlice.sliceLaw p.m p.K) =
    ∫ slice,
      (if (liveNumericalPast rate rewards C_star C_h q t s hs control0 x).2.1 = false
        then F (recorderFastPastObservation rate rewards C_star C_h q t s hs control0
          (x, (family, aux)),
          liveMarkerFastPair rate rewards C_star C_h q t s hs control0
            (x, (slice, control0.2))) else 0)
      ∂ContinuousControlSlice.sliceLaw p.m p.K := by
  let observation := recorderFastPastObservation rate rewards C_star C_h q t s hs control0
    (x, (family, aux))
  let clear := (liveNumericalPast rate rewards C_star C_h q t s hs control0 x).2.1 = false
  let promote := fun pair : RecorderFastPair (p := p) => (observation, pair)
  let actualPair := fun slice : ContinuousControlSlice.Slice p.m p.K =>
    liveMarkerFastPair rate rewards C_star C_h q t s hs control0 (x, (slice, family))
  let baselinePair := fun slice : ContinuousControlSlice.Slice p.m p.K =>
    liveMarkerFastPair rate rewards C_star C_h q t s hs control0 (x, (slice, control0.2))
  let actualMap := promote ∘ actualPair
  let baselineMap := promote ∘ baselinePair
  let test := fun y : PastObservationPair rate rewards C_star C_h q t s hs control0 =>
    if clear then F y else 0
  have hpromote : Measurable promote := measurable_const.prodMk measurable_id
  have hactualPair : Measurable actualPair := by
    exact (measurable_liveMarkerFastPair rate rewards C_star C_h q t s hs control0).comp
      (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have hbaselinePair : Measurable baselinePair := by
    exact (measurable_liveMarkerFastPair rate rewards C_star C_h q t s hs control0).comp
      (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have htest : Measurable test := by
    by_cases hc : clear
    · simpa [test, hc] using hF
    · simp [test, hc]
  have hpair := liveRemainder_fixedFamily_pair_map
    rate rewards C_star C_h q t s hs control0 x family
  have hmap :
      (ContinuousControlSlice.sliceLaw p.m p.K).map actualMap =
        (ContinuousControlSlice.sliceLaw p.m p.K).map baselineMap := by
    calc
      _ = ((ContinuousControlSlice.sliceLaw p.m p.K).map actualPair).map promote :=
        (Measure.map_map hpromote hactualPair).symm
      _ = ((ContinuousControlSlice.sliceLaw p.m p.K).map baselinePair).map promote :=
        congrArg (fun μ : Measure (RecorderFastPair (p := p)) => μ.map promote) hpair
      _ = _ := Measure.map_map hpromote hbaselinePair
  have hactualMap : Measurable actualMap := hpromote.comp hactualPair
  have hbaselineMap : Measurable baselineMap := hpromote.comp hbaselinePair
  change (∫ slice, test (actualMap slice) ∂ContinuousControlSlice.sliceLaw p.m p.K) =
    ∫ slice, test (baselineMap slice) ∂ContinuousControlSlice.sliceLaw p.m p.K
  calc
    _ = ∫ y, test y ∂((ContinuousControlSlice.sliceLaw p.m p.K).map actualMap) :=
      (MeasureTheory.integral_map_of_stronglyMeasurable hactualMap
        htest.stronglyMeasurable).symm
    _ = ∫ y, test y ∂((ContinuousControlSlice.sliceLaw p.m p.K).map baselineMap) := by
      rw [hmap]
    _ = _ := MeasureTheory.integral_map_of_stronglyMeasurable hbaselineMap
      htest.stronglyMeasurable

private theorem reference_observed_kernel_integral_join
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν]
    (tag : α → LiveRemainder rate rewards C_star C_h q t s hs control0)
    (htag : Measurable tag)
    (F : PastObservationPair rate rewards C_star C_h q t s hs control0 → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ y, ‖F y‖ ≤ C) :
    let reference := (((ν.prod (ContinuousLearningRows.timeControlLaw p)).map
      (fun xu : α × ContinuousLearningRows.TimeControl p =>
        ((tag xu.1, xu.2.2), liveMarkerFastPair rate rewards C_star C_h q t s hs control0
          (tag xu.1, (xu.2.1, control0.2))))).prod
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).map
        (attachPastObservation rate rewards C_star C_h q t s hs control0)
    let kernelTest := fun z : α ×
        (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p) =>
      ∫ y, (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
          (tag z.1)).2.1 = false then F y else 0)
        ∂actualObservedSlicePairKernel rate rewards C_star C_h q t s hs control0
          (tag z.1, z.2)
    Measurable kernelTest ∧ Integrable kernelTest
      (ν.prod ((ContinuousLearningRows.affineSamplesLaw p).prod
        (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p))) ∧
    (∫ y, (if y.1.2.2.2.2.1 = false then F y else 0) ∂reference) =
      ∫ x, ∫ family, ∫ aux, ∫ y,
        (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
            (tag x)).2.1 = false then F y else 0)
        ∂actualObservedSlicePairKernel rate rewards C_star C_h q t s hs control0
          (tag x, (family, aux))
        ∂ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
        ∂ContinuousLearningRows.affineSamplesLaw p ∂ν := by
  classical
  let slices := ContinuousControlSlice.sliceLaw p.m p.K
  let families := ContinuousLearningRows.affineSamplesLaw p
  let auxLaw := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  let timeLaw := ContinuousLearningRows.timeControlLaw p
  let outClear := fun y : PastObservationPair rate rewards C_star C_h q t s hs control0 =>
    y.1.2.2.2.2.1 = false
  let sourceTest := fun y : PastObservationPair rate rewards C_star C_h q t s hs control0 =>
    if outClear y then F y else 0
  let refMap := fun xu : α × ContinuousLearningRows.TimeControl p =>
    ((tag xu.1, xu.2.2), liveMarkerFastPair rate rewards C_star C_h q t s hs control0
      (tag xu.1, (xu.2.1, control0.2)))
  let outputMap := fun z : (α × ContinuousLearningRows.TimeControl p) × AuxiliaryArray p =>
    attachPastObservation rate rewards C_star C_h q t s hs control0 (refMap z.1, z.2)
  let reference := (((ν.prod timeLaw).map refMap).prod auxLaw).map
    (attachPastObservation rate rewards C_star C_h q t s hs control0)
  let rawTest := fun z : (α × ContinuousLearningRows.TimeControl p) × AuxiliaryArray p =>
    sourceTest (outputMap z)
  let kernelTest := fun z : α × (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p) =>
    ∫ y, (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
        (tag z.1)).2.1 = false then F y else 0)
      ∂actualObservedSlicePairKernel rate rewards C_star C_h q t s hs control0 (tag z.1, z.2)
  have htestMeas : Measurable sourceTest := by
    have hflag : Measurable (fun y : PastObservationPair rate rewards C_star C_h q t s hs control0 =>
        y.1.2.2.2.2.1) := by fun_prop
    have hset : MeasurableSet {y : PastObservationPair rate rewards C_star C_h q t s hs control0 |
        outClear y} := measurableSet_eq_fun hflag measurable_const
    exact Measurable.ite hset hF measurable_const
  have htestBound : ∀ y, ‖sourceTest y‖ ≤ C + 1 := by
    intro y
    by_cases hy : outClear y
    · simp only [sourceTest, hy, ↓reduceIte]
      exact le_trans (hC y) (by linarith)
    · simp only [sourceTest, hy, ↓reduceIte, norm_zero]
      have hCnonneg : 0 ≤ C := le_trans (norm_nonneg (F y)) (hC y)
      linarith
  have htagCurrent : Measurable (fun xu : α × ContinuousLearningRows.TimeControl p =>
      (tag xu.1, (xu.2.1, control0.2))) :=
    (htag.comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_snd).prodMk measurable_const)
  have hrefPair : Measurable (fun xu : α × ContinuousLearningRows.TimeControl p =>
      liveMarkerFastPair rate rewards C_star C_h q t s hs control0
        (tag xu.1, (xu.2.1, control0.2))) :=
    (measurable_liveMarkerFastPair rate rewards C_star C_h q t s hs control0).comp htagCurrent
  have hrefMap : Measurable refMap := by
    exact ((htag.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)).prodMk
      hrefPair
  have houtputInput : Measurable (fun z :
      (α × ContinuousLearningRows.TimeControl p) × AuxiliaryArray p =>
        (refMap z.1, z.2)) := (hrefMap.comp measurable_fst).prodMk measurable_snd
  have houtput : Measurable outputMap :=
    (measurable_attachPastObservation rate rewards C_star C_h q t s hs control0).comp
      houtputInput
  have hraw : Measurable rawTest := htestMeas.comp houtput
  have hrawBound : ∀ z, ‖rawTest z‖ ≤ C + 1 := fun z => htestBound (outputMap z)
  have hrawInt : Integrable rawTest ((ν.prod timeLaw).prod auxLaw) :=
    Integrable.of_bound hraw.aestronglyMeasurable (C + 1)
      (Filter.Eventually.of_forall hrawBound)
  have hmapProd : ((ν.prod timeLaw).map refMap).prod auxLaw =
      ((ν.prod timeLaw).prod auxLaw).map (fun z => (refMap z.1, z.2)) := by
    calc
      ((ν.prod timeLaw).map refMap).prod auxLaw =
          ((ν.prod timeLaw).map refMap).prod (auxLaw.map id) := by rw [Measure.map_id]
      _ = ((ν.prod timeLaw).prod auxLaw).map (Prod.map refMap id) :=
        Measure.map_prod_map _ _ hrefMap measurable_id
      _ = _ := rfl
  have hprodMap : Measurable (fun z :
      (α × ContinuousLearningRows.TimeControl p) × AuxiliaryArray p =>
        (refMap z.1, z.2)) := (hrefMap.comp measurable_fst).prodMk measurable_snd
  have hattach : Measurable
      (attachPastObservation rate rewards C_star C_h q t s hs control0) :=
    measurable_attachPastObservation rate rewards C_star C_h q t s hs control0
  have hreference : reference = ((ν.prod timeLaw).prod auxLaw).map outputMap := by
    dsimp [reference, timeLaw, auxLaw]
    rw [hmapProd]
    rw [Measure.map_map hattach hprodMap]
    rfl
  have hreferenceIntegral :
      (∫ y, sourceTest y ∂reference) = ∫ z, rawTest z ∂((ν.prod timeLaw).prod auxLaw) := by
    rw [hreference]
    exact MeasureTheory.integral_map_of_stronglyMeasurable houtput
      htestMeas.stronglyMeasurable
  have hauxTail : Integrable (fun xu : α × ContinuousLearningRows.TimeControl p =>
      ∫ aux, rawTest (xu, aux) ∂auxLaw) (ν.prod timeLaw) := hrawInt.integral_prod_left
  have hauxTailMeas : StronglyMeasurable (fun xu : α × ContinuousLearningRows.TimeControl p =>
      ∫ aux, rawTest (xu, aux) ∂auxLaw) :=
    hraw.stronglyMeasurable.integral_prod_right'
  have hauxTailBound (xu : α × ContinuousLearningRows.TimeControl p) :
      ‖∫ aux, rawTest (xu, aux) ∂auxLaw‖ ≤ C + 1 := by
    have h := norm_integral_le_of_norm_le_const (μ := auxLaw) (C := C + 1)
      (f := fun aux => rawTest (xu, aux))
      (Filter.Eventually.of_forall fun aux => hrawBound (xu, aux))
    simpa [auxLaw, probReal_univ] using h
  have hxuBound : ∀ xu, ‖∫ aux, rawTest (xu, aux) ∂auxLaw‖ ≤ C + 1 := hauxTailBound
  have hxuMeas : Measurable (fun xu : α × ContinuousLearningRows.TimeControl p =>
      ∫ aux, rawTest (xu, aux) ∂auxLaw) := hauxTailMeas.measurable
  have hxuSection (x : α) : Integrable (fun u : ContinuousLearningRows.TimeControl p =>
      ∫ aux, rawTest ((x, u), aux) ∂auxLaw) timeLaw :=
    Integrable.of_bound
      (hxuMeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (C + 1)
      (Filter.Eventually.of_forall fun u => hxuBound (x, u))
  have hrawProduct :
      (∫ z, rawTest z ∂((ν.prod timeLaw).prod auxLaw)) =
        ∫ x, ∫ u, ∫ aux, rawTest ((x, u), aux) ∂auxLaw ∂timeLaw ∂ν := by
    rw [MeasureTheory.integral_prod _ hrawInt,
      MeasureTheory.integral_prod _ hauxTail]
  have htimeSplit (x : α) :
      (∫ u, ∫ aux, rawTest ((x, u), aux) ∂auxLaw ∂timeLaw) =
        ∫ slice, ∫ family, ∫ aux,
          rawTest ((x, (slice, family)), aux) ∂auxLaw
            ∂families ∂slices := by
    change (∫ u, ∫ aux, rawTest ((x, u), aux) ∂auxLaw
      ∂(slices.prod families)) = _
    exact MeasureTheory.integral_prod _ (hxuSection x)
  have hrawIterated :
      (∫ z, rawTest z ∂((ν.prod timeLaw).prod auxLaw)) =
        ∫ x, ∫ slice, ∫ family, ∫ aux,
          rawTest ((x, (slice, family)), aux) ∂auxLaw
            ∂families ∂slices ∂ν := by
    rw [hrawProduct]
    apply integral_congr_ae
    filter_upwards with x
    exact htimeSplit x
  let baseline := fun x slice family aux =>
    rawTest ((x, (slice, family)), aux)
  have hbaselineMeas (x : α) : Measurable (fun z :
      (ContinuousControlSlice.Slice p.m p.K × ContinuousLearningRows.AffineSamples p) ×
        AuxiliaryArray p => baseline x z.1.1 z.1.2 z.2) := by
    exact hraw.comp (((measurable_const.prodMk
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.comp measurable_fst))).prodMk measurable_snd))
  have hbaselineBound (x : α) (slice : ContinuousControlSlice.Slice p.m p.K)
      (family : ContinuousLearningRows.AffineSamples p) (aux : AuxiliaryArray p) :
      ‖baseline x slice family aux‖ ≤ C + 1 := hrawBound ((x, (slice, family)), aux)
  have hbaseReordered (x : α) :
      (∫ slice, ∫ family, ∫ aux, baseline x slice family aux
        ∂auxLaw ∂families ∂slices) =
      ∫ family, ∫ aux, ∫ slice, baseline x slice family aux
        ∂slices ∂auxLaw ∂families :=
    integral_slice_family_aux_swap (baseline x) (hbaselineMeas x) (C + 1)
      (hbaselineBound x)
  have hreferenceIterated :
      (∫ y, sourceTest y ∂reference) =
        ∫ x, ∫ family, ∫ aux, ∫ slice,
          baseline x slice family aux ∂slices ∂auxLaw ∂families ∂ν := by
    rw [hreferenceIntegral, hrawIterated]
    apply integral_congr_ae
    filter_upwards with x
    exact hbaseReordered x
  let kernelOutput := fun z :
      (α × (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p)) ×
        ContinuousControlSlice.Slice p.m p.K =>
          (recorderFastPastObservation rate rewards C_star C_h q t s hs control0
              (tag z.1.1, (z.1.2.1, z.1.2.2)),
            liveMarkerFastPair rate rewards C_star C_h q t s hs control0
              (tag z.1.1, (z.2, z.1.2.1)))
  have hkernelJointInput : Measurable (fun z :
      (α × (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p)) ×
        ContinuousControlSlice.Slice p.m p.K =>
          (tag z.1.1, (z.2, z.1.2.1))) := by
    exact (htag.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.prodMk (measurable_fst.comp (measurable_snd.comp measurable_fst)))
  have hkernelObservation : Measurable (fun z :
      (α × (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p)) ×
        ContinuousControlSlice.Slice p.m p.K =>
          recorderFastPastObservation rate rewards C_star C_h q t s hs control0
            (tag z.1.1, (z.1.2.1, z.1.2.2))) := by
    exact (measurable_recorderFastPastObservation rate rewards C_star C_h q t s hs control0).comp
      ((htag.comp (measurable_fst.comp measurable_fst)).prodMk
        ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
          (measurable_snd.comp (measurable_snd.comp measurable_fst))))
  have hkernelPair : Measurable (fun z :
      (α × (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p)) ×
        ContinuousControlSlice.Slice p.m p.K =>
          liveMarkerFastPair rate rewards C_star C_h q t s hs control0
            (tag z.1.1, (z.2, z.1.2.1))) :=
    (measurable_liveMarkerFastPair rate rewards C_star C_h q t s hs control0).comp
      hkernelJointInput
  have hkernelClearBool : Measurable (fun z :
      (α × (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p)) ×
        ContinuousControlSlice.Slice p.m p.K =>
          (liveNumericalPast rate rewards C_star C_h q t s hs control0
            (tag z.1.1)).2.1) := by
    exact (measurable_fst.comp (measurable_snd.comp
      ((measurable_liveNumericalPast rate rewards C_star C_h q t s hs control0).comp
        (htag.comp (measurable_fst.comp measurable_fst)))))
  have hkernelOutput : Measurable kernelOutput :=
    hkernelObservation.prodMk hkernelPair
  let kernelClearBool := fun z :
      (α × (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p)) ×
        ContinuousControlSlice.Slice p.m p.K =>
          (liveNumericalPast rate rewards C_star C_h q t s hs control0
            (tag z.1.1)).2.1
  have hkernelJoint : Measurable (fun z :
      (α × (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p)) ×
        ContinuousControlSlice.Slice p.m p.K =>
          if kernelClearBool z = false then F (kernelOutput z) else 0) := by
    have hset : MeasurableSet {z :
        (α × (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p)) ×
          ContinuousControlSlice.Slice p.m p.K |
            kernelClearBool z = false} :=
      measurableSet_eq_fun hkernelClearBool measurable_const
    exact Measurable.ite hset (hF.comp hkernelOutput) measurable_const
  have hkernelJointBound : ∀ z,
      ‖(if kernelClearBool z = false then F (kernelOutput z) else 0)‖ ≤ C + 1 := by
    intro z
    by_cases hz : kernelClearBool z = false
    · simp only [hz, ↓reduceIte]
      exact le_trans (hC (kernelOutput z)) (by linarith)
    · cases hb : kernelClearBool z with
      | false => exact False.elim (hz hb)
      | true =>
          have hCnonneg : 0 ≤ C := le_trans (norm_nonneg (F (kernelOutput z)))
            (hC (kernelOutput z))
          have hbound : 0 ≤ C + 1 := by linarith
          simpa [hb] using hbound
  let kernelSliceTest := fun z :
      (α × (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p)) ×
        ContinuousControlSlice.Slice p.m p.K =>
          if kernelClearBool z = false then F (kernelOutput z) else 0
  have hkernelSliceInt : Integrable kernelSliceTest
      ((ν.prod (families.prod auxLaw)).prod slices) :=
    Integrable.of_bound hkernelJoint.aestronglyMeasurable (C + 1)
      (Filter.Eventually.of_forall hkernelJointBound)
  have hkernelIntegralStrong : StronglyMeasurable (fun z :
      α × (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p) =>
        ∫ slice, kernelSliceTest (z, slice) ∂slices) :=
    hkernelJoint.stronglyMeasurable.integral_prod_right'
  have hkernelIntegralInt : Integrable (fun z :
      α × (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p) =>
        ∫ slice, kernelSliceTest (z, slice) ∂slices)
      (ν.prod (families.prod auxLaw)) := hkernelSliceInt.integral_prod_left
  have hkernelEval : kernelTest = fun z =>
      ∫ slice, kernelSliceTest (z, slice) ∂slices := by
    funext z
    let G := fun y : PastObservationPair rate rewards C_star C_h q t s hs control0 =>
      if (liveNumericalPast rate rewards C_star C_h q t s hs control0 (tag z.1)).2.1 = false
        then F y else 0
    have hG : Measurable G := by
      by_cases hc : (liveNumericalPast rate rewards C_star C_h q t s hs control0
          (tag z.1)).2.1 = false
      · simpa [G, hc] using hF
      · simp [G, hc]
    have hsliceMap : Measurable (fun slice : ContinuousControlSlice.Slice p.m p.K =>
        (recorderFastPastObservation rate rewards C_star C_h q t s hs control0
            (tag z.1, z.2),
          liveMarkerFastPair rate rewards C_star C_h q t s hs control0
            (tag z.1, (slice, z.2.1)))) :=
      (measurable_const.prodMk
        ((measurable_liveMarkerFastPair rate rewards C_star C_h q t s hs control0).comp
          (measurable_const.prodMk (measurable_id.prodMk measurable_const))))
    change (∫ y, G y ∂(ContinuousControlSlice.sliceLaw p.m p.K).map
        (fun slice =>
          (recorderFastPastObservation rate rewards C_star C_h q t s hs control0
              (tag z.1, z.2),
            liveMarkerFastPair rate rewards C_star C_h q t s hs control0
              (tag z.1, (slice, z.2.1))))) = _
    rw [← actualObservedSlicePairKernel]
    exact MeasureTheory.integral_map_of_stronglyMeasurable hsliceMap
      hG.stronglyMeasurable
  have hkernelMeas : Measurable kernelTest := by
    rw [hkernelEval]
    exact hkernelIntegralStrong.measurable
  have hkernelInt : Integrable kernelTest
      (ν.prod (families.prod auxLaw)) := by
    rw [hkernelEval]
    exact hkernelIntegralInt
  have hkernelTailEq (x : α) (family : ContinuousLearningRows.AffineSamples p)
      (aux : AuxiliaryArray p) :
      (∫ slice, baseline x slice family aux ∂slices) =
        ∫ y, (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
            (tag x)).2.1 = false then F y else 0)
          ∂actualObservedSlicePairKernel rate rewards C_star C_h q t s hs control0
            (tag x, (family, aux)) := by
    have hfixed := fixedFamily_observed_test_integral rate rewards C_star C_h q t s hs
      control0 (tag x) family aux F hF
    have hfixed' := by simpa [slices] using hfixed
    have hclearBaseline (slice : ContinuousControlSlice.Slice p.m p.K) :
        outClear (outputMap ((x, (slice, family)), aux)) =
          ((liveNumericalPast rate rewards C_star C_h q t s hs control0 (tag x)).2.1 = false) := by
      rfl
    have hbase : (∫ slice, baseline x slice family aux ∂slices) =
        ∫ slice, (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
          (tag x)).2.1 = false then
            F (recorderFastPastObservation rate rewards C_star C_h q t s hs control0
                (tag x, (family, aux)),
              liveMarkerFastPair rate rewards C_star C_h q t s hs control0
                (tag x, (slice, control0.2))) else 0) ∂slices := by
      apply integral_congr_ae
      filter_upwards with slice
      change (if outClear (outputMap ((x, (slice, family)), aux)) then
        F (attachPastObservation rate rewards C_star C_h q t s hs control0
          (refMap (x, (slice, family)), aux)) else 0) = _
      simp [hclearBaseline slice, attachPastObservation, refMap]
    have hactualMap : Measurable (fun slice : ContinuousControlSlice.Slice p.m p.K =>
        (recorderFastPastObservation rate rewards C_star C_h q t s hs control0
            (tag x, (family, aux)),
          liveMarkerFastPair rate rewards C_star C_h q t s hs control0
            (tag x, (slice, family)))) :=
      measurable_const.prodMk
        ((measurable_liveMarkerFastPair rate rewards C_star C_h q t s hs control0).comp
          (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
    let G := fun y : PastObservationPair rate rewards C_star C_h q t s hs control0 =>
      if (liveNumericalPast rate rewards C_star C_h q t s hs control0 (tag x)).2.1 = false
        then F y else 0
    have hG : Measurable G := by
      by_cases hc : (liveNumericalPast rate rewards C_star C_h q t s hs control0
          (tag x)).2.1 = false
      · simpa [G, hc] using hF
      · simp [G, hc]
    calc
      _ = ∫ slice, (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
          (tag x)).2.1 = false then
            F (recorderFastPastObservation rate rewards C_star C_h q t s hs control0
                (tag x, (family, aux)),
              liveMarkerFastPair rate rewards C_star C_h q t s hs control0
                (tag x, (slice, control0.2))) else 0) ∂slices := hbase
      _ = ∫ slice, (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
          (tag x)).2.1 = false then
            F (recorderFastPastObservation rate rewards C_star C_h q t s hs control0
                (tag x, (family, aux)),
              liveMarkerFastPair rate rewards C_star C_h q t s hs control0
                (tag x, (slice, family))) else 0) ∂slices := hfixed'.symm
      _ = ∫ y, G y ∂actualObservedSlicePairKernel rate rewards C_star C_h q t s hs control0
            (tag x, (family, aux)) := by
        rw [actualObservedSlicePairKernel]
        simpa [slices] using
          (MeasureTheory.integral_map_of_stronglyMeasurable
            (μ := ContinuousControlSlice.sliceLaw p.m p.K) hactualMap
            hG.stronglyMeasurable).symm
      _ = _ := rfl
  have hreferenceToKernel :
      (∫ y, sourceTest y ∂reference) =
        ∫ x, ∫ family, ∫ aux,
          ∫ y, (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
              (tag x)).2.1 = false then F y else 0)
            ∂actualObservedSlicePairKernel rate rewards C_star C_h q t s hs control0
              (tag x, (family, aux))
          ∂auxLaw ∂families ∂ν := by
    rw [hreferenceIterated]
    apply integral_congr_ae
    filter_upwards with x
    apply integral_congr_ae
    filter_upwards with family
    apply integral_congr_ae
    filter_upwards with aux
    exact hkernelTailEq x family aux
  refine ⟨?_, ?_, ?_⟩
  · simpa only [kernelTest, families, auxLaw] using hkernelMeas
  · simpa only [kernelTest, families, auxLaw] using hkernelInt
  · simpa only [reference, sourceTest, outClear] using hreferenceToKernel

theorem continuingSource_clear_observed_kernel_integral
    (F : PastObservationPair rate rewards C_star C_h q t s hs control0 → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ y, ‖F y‖ ≤ C) :
    let μ := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
      rate rewards C_star C_h q t s hs control0
    let ν := ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure
      rate rewards C_star C_h q t s hs control0
    let aux := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
    Integrable (fun za =>
      if (continuingPastPairTestMap rate rewards C_star C_h q t s hs control0 za).1.2.2.2.2.1 = false
      then F (continuingPastPairTestMap rate rewards C_star C_h q t s hs control0 za) else 0)
      (μ.prod aux) ∧
    Measurable (fun z : ReferenceFirstLiveRecordingReadoutMeasurability.XPlus
        rate rewards C_star C_h q t s hs control0 ×
          (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p) =>
      ∫ y, (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
          (Sum.inl z.1 : LiveRemainder rate rewards C_star C_h q t s hs control0)).2.1 = false
        then F y else 0)
        ∂actualObservedSlicePairKernel rate rewards C_star C_h q t s hs control0
          (Sum.inl z.1, z.2)) ∧
    Integrable (fun z : ReferenceFirstLiveRecordingReadoutMeasurability.XPlus
        rate rewards C_star C_h q t s hs control0 ×
          (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p) =>
      ∫ y, (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
          (Sum.inl z.1 : LiveRemainder rate rewards C_star C_h q t s hs control0)).2.1 = false
        then F y else 0)
        ∂actualObservedSlicePairKernel rate rewards C_star C_h q t s hs control0
          (Sum.inl z.1, z.2))
      (ν.prod ((ContinuousLearningRows.affineSamplesLaw p).prod aux)) ∧
    (∫ za, (if (continuingPastPairTestMap rate rewards C_star C_h q t s hs control0 za).1.2.2.2.2.1 = false
        then F (continuingPastPairTestMap rate rewards C_star C_h q t s hs control0 za) else 0)
      ∂(μ.prod aux)) =
    ∫ x, ∫ family, ∫ a, ∫ y,
      (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
          (Sum.inl x : LiveRemainder rate rewards C_star C_h q t s hs control0)).2.1 = false
        then F y else 0)
      ∂actualObservedSlicePairKernel rate rewards C_star C_h q t s hs control0
        (Sum.inl x, (family, a))
      ∂aux ∂ContinuousLearningRows.affineSamplesLaw p ∂ν := by
  let μ := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
    rate rewards C_star C_h q t s hs control0
  let ν := ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure
    rate rewards C_star C_h q t s hs control0
  let aux := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  let tag := fun x : ReferenceFirstLiveRecordingReadoutMeasurability.XPlus
      rate rewards C_star C_h q t s hs control0 =>
    (Sum.inl x : LiveRemainder rate rewards C_star C_h q t s hs control0)
  have htag : Measurable tag := measurable_inl
  have hsource := continuingSource_clear_bounded_past_pair_test
    rate rewards C_star C_h q t s hs control0 F hF C hC
  have hjoin := reference_observed_kernel_integral_join rate rewards C_star C_h q t s hs
    control0 ν tag htag F hF C hC
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [μ, aux] using hsource.1
  · simpa only [ν, tag] using hjoin.1
  · simpa only [ν, tag, aux] using hjoin.2.1
  · simpa only [μ, ν, aux, tag] using hsource.2.2.trans hjoin.2.2

theorem emptySource_clear_observed_kernel_integral
    (F : PastObservationPair rate rewards C_star C_h q t s hs control0 → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ y, ‖F y‖ ≤ C) :
    let μ := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
      rate rewards C_star C_h q t s hs control0
    let ν := ReferenceFirstLiveEmptyPendingMarkerLaw.nuEmpty
      rate rewards C_star C_h q t s hs control0
    let aux := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
    Integrable (fun za =>
      if (emptyPastPairTestMap rate rewards C_star C_h q t s hs control0 za).1.2.2.2.2.1 = false
      then F (emptyPastPairTestMap rate rewards C_star C_h q t s hs control0 za) else 0)
      (μ.prod aux) ∧
    Measurable (fun z : ReferenceFirstLiveEmptyPendingMarkerLaw.Xempty
        rate rewards C_star C_h q t s hs control0 ×
          (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p) =>
      ∫ y, (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
          (Sum.inr z.1 : LiveRemainder rate rewards C_star C_h q t s hs control0)).2.1 = false
        then F y else 0)
        ∂actualObservedSlicePairKernel rate rewards C_star C_h q t s hs control0
          (Sum.inr z.1, z.2)) ∧
    Integrable (fun z : ReferenceFirstLiveEmptyPendingMarkerLaw.Xempty
        rate rewards C_star C_h q t s hs control0 ×
          (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p) =>
      ∫ y, (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
          (Sum.inr z.1 : LiveRemainder rate rewards C_star C_h q t s hs control0)).2.1 = false
        then F y else 0)
        ∂actualObservedSlicePairKernel rate rewards C_star C_h q t s hs control0
          (Sum.inr z.1, z.2))
      (ν.prod ((ContinuousLearningRows.affineSamplesLaw p).prod aux)) ∧
    (∫ za, (if (emptyPastPairTestMap rate rewards C_star C_h q t s hs control0 za).1.2.2.2.2.1 = false
        then F (emptyPastPairTestMap rate rewards C_star C_h q t s hs control0 za) else 0)
      ∂(μ.prod aux)) =
    ∫ x, ∫ family, ∫ a, ∫ y,
      (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
          (Sum.inr x : LiveRemainder rate rewards C_star C_h q t s hs control0)).2.1 = false
        then F y else 0)
      ∂actualObservedSlicePairKernel rate rewards C_star C_h q t s hs control0
        (Sum.inr x, (family, a))
      ∂aux ∂ContinuousLearningRows.affineSamplesLaw p ∂ν := by
  let μ := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
    rate rewards C_star C_h q t s hs control0
  let ν := ReferenceFirstLiveEmptyPendingMarkerLaw.nuEmpty
    rate rewards C_star C_h q t s hs control0
  let aux := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  let tag := fun x : ReferenceFirstLiveEmptyPendingMarkerLaw.Xempty
      rate rewards C_star C_h q t s hs control0 =>
    (Sum.inr x : LiveRemainder rate rewards C_star C_h q t s hs control0)
  have htag : Measurable tag := measurable_inr
  have hsource := emptySource_clear_bounded_past_pair_test
    rate rewards C_star C_h q t s hs control0 F hF C hC
  have hjoin := reference_observed_kernel_integral_join rate rewards C_star C_h q t s hs
    control0 ν tag htag F hF C hC
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [μ, aux] using hsource.1
  · simpa only [ν, tag] using hjoin.1
  · simpa only [ν, tag, aux] using hjoin.2.1
  · simpa only [μ, ν, aux, tag] using hsource.2.2.trans hjoin.2.2

end Bandits.Support.ReferenceFirstLiveObservedKernelSourceLaw

end
