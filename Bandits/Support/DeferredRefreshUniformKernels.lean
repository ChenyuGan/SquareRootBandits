/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
All rights reserved. Released under Apache 2.0 license.
-/
module

public import Bandits.Support.ReferenceFirstCollectionDeferredCalendarProduct
public import Bandits.Support.DeferredRefreshWindow

/-!
# One-step uniform samplers for the recorded refresh kernel

The sampler uses the actual normalized residual mass on the supported slow-set
carrier and the existing continuous uniform scalar law.  It treats one fixed
queue step only; chronological iteration and the physical source law are
separate constructions.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:176-187`,
`sources/zip4/manuscript/06_interruptions.tex:399-408`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-44`.
-/

public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Bandits.Support.DeferredRefreshUniformKernels

open Bandits.Support

private instance recordListMeasurableSingleton :
    MeasurableSingletonClass (List (Bool × ℕ)) where
  measurableSet_singleton records := by
    let : MeasurableSingletonClass (Unit ⊕ (Bool × ℕ)) := ⟨fun z => by
      cases z with
      | inl u =>
          simpa only [Set.image_singleton] using
            (MeasurableSet.singleton u).inl_image
      | inr entry =>
          simpa only [Set.image_singleton] using
            (MeasurableSet.singleton entry).inr_image⟩
    have hinj : Function.Injective
        (ReferenceActiveHorizonMeasurability.listObservationCoordinates
          (α := Bool × ℕ)) := by
      intro left right h
      have hlen : left.length = right.length := congrArg Prod.fst h
      apply List.ext_getElem hlen
      intro i hi hj
      have he := congrFun (congrArg Prod.snd h) i
      simpa only [ReferenceActiveHorizonMeasurability.listObservationCoordinates,
        ReferenceActiveHorizonMeasurability.listObservationAt,
        List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
        Sum.inr.injEq] using he
    have hcoordinates :=
      ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
        (α := Bool × ℕ)
    have hsingleton := hcoordinates
      (MeasurableSet.singleton
        (ReferenceActiveHorizonMeasurability.listObservationCoordinates records))
    convert hsingleton using 1
    ext z
    simp only [Set.mem_singleton_iff, Set.mem_preimage, hinj.eq_iff]

abbrev SlowSet (p : ConstructorDimensions.Parameters) :=
  CanonicalOrientedSetLaw.SlowSet p.K p.m

/-- The size of the actual supported slow-set subtype. -/
@[expose] def residualEnumerationSize (p : ConstructorDimensions.Parameters) : ℕ :=
  Fintype.card (SlowSet p)

/-- The actual slow-set support supplies a positive enumeration size. -/
theorem residualEnumerationSize_pos (p : ConstructorDimensions.Parameters) :
    0 < residualEnumerationSize p := by
  classical
  have hmLarge : 1 < p.m := lt_of_lt_of_le (by omega : 1 < 2) p.two_le_m
  have hm : 0 < p.m - 1 := Nat.sub_pos_of_lt hmLarge
  have hmK : p.m - 1 < p.K := lt_of_le_of_lt (Nat.sub_le _ _) p.m_lt_K
  obtain ⟨U, hU⟩ := ProductSetLaw.support_nonempty hm hmK
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨U, hU⟩⟩

/-- Fixed increasing order on the supported slow-set subtype. -/
@[expose] noncomputable def residualOrder (p : ConstructorDimensions.Parameters) :
    Fin (residualEnumerationSize p) ≃ SlowSet p :=
  (Fintype.equivFin (SlowSet p)).symm

/-- Residual masses in the fixed finite order used by the inverse CDF. -/
@[expose] noncomputable def residualEnumMass
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (i : Fin (residualEnumerationSize p)) : ℝ :=
  RecordedSlowRefresh.residualMass p q state round anchor hanchor (residualOrder p i)

/-- The existing residual normalization, reindexed by the finite enumeration. -/
theorem residualEnumMass_sum
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a) :
    (∑ i, residualEnumMass p q state round anchor hanchor i) = 1 := by
  change (∑ i, RecordedSlowRefresh.residualMass p q state round anchor hanchor
    (residualOrder p i)) = 1
  rw [Equiv.sum_comp]
  exact RecordedSlowRefresh.residualMass_sum_eq_one p q state round anchor hanchor

/-- Every enumerated residual coordinate is a genuine nonnegative mass. -/
theorem residualEnumMass_nonneg
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (i : Fin (residualEnumerationSize p)) :
    0 ≤ residualEnumMass p q state round anchor hanchor i :=
  RecordedSlowRefresh.residualMass_nonneg p q state round anchor hanchor
    (residualOrder p i)

/-- Draw from the actual residual law using the accepted increasing-order
inverse-cumulative sampler on the second scalar coordinate. -/
@[expose] noncomputable def sampleResidual
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (beta : ContinuousControlSlice.Scalar) : SlowSet p :=
  residualOrder p (ContinuousCategorical.sample (residualEnumerationSize_pos p)
    (residualEnumMass p q state round anchor hanchor)
    (residualEnumMass_sum p q state round anchor hanchor) beta)

/-- The literal half-open cumulative fibre for each supported slow set. -/
theorem sampleResidual_eq_iff
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (beta : ContinuousControlSlice.Scalar) (U : SlowSet p) :
    sampleResidual p q state round anchor hanchor beta = U ↔
      ContinuousCategorical.lower (residualEnumMass p q state round anchor hanchor)
          ((residualOrder p).symm U) ≤ beta.val ∧
        beta.val < ContinuousCategorical.upper
          (residualEnumMass p q state round anchor hanchor) ((residualOrder p).symm U) := by
  have heq : residualOrder p
      (ContinuousCategorical.sample (residualEnumerationSize_pos p)
        (residualEnumMass p q state round anchor hanchor)
        (residualEnumMass_sum p q state round anchor hanchor) beta) = U ↔
      ContinuousCategorical.sample (residualEnumerationSize_pos p)
        (residualEnumMass p q state round anchor hanchor)
        (residualEnumMass_sum p q state round anchor hanchor) beta =
          (residualOrder p).symm U :=
    ((residualOrder p).eq_symm_apply).symm
  rw [sampleResidual, heq]
  exact ContinuousCategorical.sample_eq_iff (residualEnumerationSize_pos p)
    (fun i => residualEnumMass_nonneg p q state round anchor hanchor i)
    (residualEnumMass_sum p q state round anchor hanchor) beta ((residualOrder p).symm U)

/-- A zero residual mass has an empty pointwise sampler fibre. -/
theorem sampleResidual_fibre_eq_empty_of_zero
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (U : SlowSet p)
    (hzero : RecordedSlowRefresh.residualMass p q state round anchor hanchor U = 0) :
    sampleResidual p q state round anchor hanchor ⁻¹' {U} = ∅ := by
  have hset : sampleResidual p q state round anchor hanchor ⁻¹' {U} =
      ContinuousCategorical.sample (residualEnumerationSize_pos p)
        (residualEnumMass p q state round anchor hanchor)
        (residualEnumMass_sum p q state round anchor hanchor) ⁻¹'
          {(residualOrder p).symm U} := by
    ext beta
    simp only [Set.mem_preimage, Set.mem_singleton_iff, sampleResidual]
    exact ((residualOrder p).eq_symm_apply).symm
  rw [hset]
  exact ContinuousCategorical.sample_fibre_eq_empty_of_zero
    (residualEnumerationSize_pos p)
    (fun i => residualEnumMass_nonneg p q state round anchor hanchor i)
    (residualEnumMass_sum p q state round anchor hanchor)
    ((residualOrder p).symm U) (by simpa [residualEnumMass] using hzero)

/-- Measurability in the genuine scalar subtype. -/
theorem measurable_sampleResidual
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a) :
    Measurable (sampleResidual p q state round anchor hanchor) :=
  (measurable_of_finite (residualOrder p)).comp
    (ContinuousCategorical.measurable_sample (residualEnumerationSize_pos p)
      (fun i => residualEnumMass_nonneg p q state round anchor hanchor i)
      (residualEnumMass_sum p q state round anchor hanchor))

/-- Pushforward of the fixed-step residual sampler is the existing PMF itself. -/
theorem sampleResidual_map
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a) :
    ContinuousControlSlice.scalarLaw.map
        (sampleResidual p q state round anchor hanchor) =
      (RecordedSlowRefresh.residualPMF p q state round anchor hanchor).toMeasure := by
  classical
  let masses := residualEnumMass p q state round anchor hanchor
  have hp : ∀ i, 0 ≤ masses i := fun i => residualEnumMass_nonneg p q state round anchor hanchor i
  have hsum : ∑ i, masses i = 1 := residualEnumMass_sum p q state round anchor hanchor
  have hfin := ContinuousCategorical.uniform_map_sample (residualEnumerationSize_pos p) hp hsum
  have htransport :
      ContinuousCategorical.uniform.map (sampleResidual p q state round anchor hanchor) =
        ((ContinuousCategorical.massPMF masses hp hsum).toMeasure).map (residualOrder p) := by
    change ContinuousCategorical.uniform.map
      (fun beta => residualOrder p (ContinuousCategorical.sample
        (residualEnumerationSize_pos p) masses hsum beta)) = _
    change ContinuousCategorical.uniform.map
      (residualOrder p ∘ fun beta =>
        ContinuousCategorical.sample (residualEnumerationSize_pos p) masses hsum beta) = _
    rw [← Measure.map_map (measurable_of_finite (residualOrder p))
      (ContinuousCategorical.measurable_sample (residualEnumerationSize_pos p) hp hsum)]
    exact congrArg (fun μ : Measure (Fin (residualEnumerationSize p)) => μ.map (residualOrder p)) hfin
  have htarget :
      ((ContinuousCategorical.massPMF masses hp hsum).toMeasure).map (residualOrder p) =
        (RecordedSlowRefresh.residualPMF p q state round anchor hanchor).toMeasure := by
    apply Measure.ext_of_singleton
    intro U
    rw [Measure.map_apply (measurable_of_finite (residualOrder p))
      (measurableSet_singleton U)]
    have hpre : (residualOrder p) ⁻¹' {U} = {(residualOrder p).symm U} := by
      ext i
      simp [Equiv.eq_symm_apply]
    rw [hpre,
      PMF.toMeasure_apply_singleton _ ((residualOrder p).symm U)
        (measurableSet_singleton _),
      PMF.toMeasure_apply_singleton _ U (measurableSet_singleton _)]
    rw [ContinuousCategorical.massPMF_apply, RecordedSlowRefresh.residualPMF_apply]
    change ENNReal.ofReal
      (RecordedSlowRefresh.residualMass p q state round anchor hanchor
        (residualOrder p ((residualOrder p).symm U))) = _
    rw [Equiv.apply_symm_apply]
  change ContinuousCategorical.uniform.map
    (sampleResidual p q state round anchor hanchor) = _
  rw [htransport, htarget]

/-- The literal strict-threshold region for one proposal scalar. -/
def proposalSet (probability : ℝ) : Set ContinuousControlSlice.Scalar :=
  {alpha | FollowerCutoffScan.thresholdProposalBit alpha probability = true}

theorem proposalSet_measurable (probability : ℝ) :
    MeasurableSet (proposalSet probability) := by
  have hset : proposalSet probability =
      (Subtype.val : ContinuousControlSlice.Scalar → ℝ) ⁻¹' Set.Iio probability := by
    ext alpha
    simp [proposalSet, FollowerCutoffScan.thresholdProposalBit, Set.mem_Iio]
  rw [hset]
  exact measurableSet_Iio.preimage measurable_subtype_coe

/-- Exact Bernoulli mass of the accepted strict proposal threshold. -/
theorem proposalSet_measure {probability : ℝ} (hprobability_le_one : probability ≤ 1) :
    ContinuousControlSlice.scalarLaw (proposalSet probability) =
      ENNReal.ofReal probability := by
  have hset : proposalSet probability =
      (Subtype.val : ContinuousControlSlice.Scalar → ℝ) ⁻¹' Set.Iio probability := by
    ext alpha
    simp [proposalSet, FollowerCutoffScan.thresholdProposalBit, Set.mem_Iio]
  change ContinuousCategorical.uniform (proposalSet probability) = _
  rw [hset, ContinuousCategorical.uniform_preimage_val]
  have hinter : Set.Iio probability ∩ Set.Ico (0 : ℝ) 1 = Set.Ico 0 probability := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ico]
    constructor
    · rintro ⟨hxp, hinterval⟩
      exact ⟨hinterval.1, hxp⟩
    · rintro ⟨hx0, hxp⟩
      exact ⟨hxp, ⟨hx0, lt_of_lt_of_le hxp hprobability_le_one⟩⟩
  rw [hinter, Real.volume_Ico]
  simp

/-- The inactive threshold has the complementary Bernoulli mass. -/
theorem proposalSet_compl_measure {probability : ℝ} (hprobability_nonneg : 0 ≤ probability)
    (hprobability_le_one : probability ≤ 1) :
    ContinuousControlSlice.scalarLaw (proposalSet probability)ᶜ =
      ENNReal.ofReal (1 - probability) := by
  rw [MeasureTheory.measure_compl (proposalSet_measurable probability)
    (measure_ne_top _ _), measure_univ,
    proposalSet_measure hprobability_le_one]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hprobability_nonneg]

/-- The literal one-step refresh map on two independent uniform scalars. -/
@[expose] noncomputable def sampleRecordedRefresh
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (current : SlowSet p)
    (coordinates : ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar) : SlowSet p :=
  if FollowerCutoffScan.thresholdProposalBit coordinates.1
      (RecordedSlowRefresh.proposalProbability p q state round) then
    sampleResidual p q state round anchor hanchor coordinates.2
  else current

/-- Measurability of the fixed-parameter two-scalar refresh map. -/
theorem measurable_sampleRecordedRefresh
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (current : SlowSet p) :
    Measurable (sampleRecordedRefresh p q state round anchor hanchor current) := by
  have hthreshold : MeasurableSet
      {z : ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar |
        FollowerCutoffScan.thresholdProposalBit z.1
          (RecordedSlowRefresh.proposalProbability p q state round) = true} := by
    have hset : {z : ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar |
        FollowerCutoffScan.thresholdProposalBit z.1
          (RecordedSlowRefresh.proposalProbability p q state round) = true} =
        (fun z : ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar => z.1.val) ⁻¹'
          Set.Iio (RecordedSlowRefresh.proposalProbability p q state round) := by
      ext z
      simp [FollowerCutoffScan.thresholdProposalBit, Set.mem_Iio]
    rw [hset]
    exact measurableSet_Iio.preimage (measurable_subtype_coe.comp measurable_fst)
  exact Measurable.ite hthreshold
    ((measurable_sampleResidual p q state round anchor hanchor).comp measurable_snd)
    measurable_const

/-- The inactive step is retained for every pair of scalar values. -/
theorem sampleRecordedRefresh_eq_current_of_inactive
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (current : SlowSet p)
    (hinactive : round.enabled = false ∨ state.overflow = true)
    (coordinates : ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar) :
    sampleRecordedRefresh p q state round anchor hanchor current coordinates = current := by
  have hzero : RecordedSlowRefresh.proposalProbability p q state round = 0 := by
    rcases hinactive with hdisabled | hoverflow
    · exact RecordedSlowRefresh.proposalProbability_zero_of_disabled p q state round hdisabled
    · exact RecordedSlowRefresh.proposalProbability_zero_of_overflow p q state round hoverflow
  simp [sampleRecordedRefresh, FollowerCutoffScan.thresholdProposalBit, hzero,
    coordinates.1.property.1]

/-- A fresh residual atom has its actual fixed-step PMF probability. -/
theorem sampleResidual_atom
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a) (U : SlowSet p) :
    ContinuousControlSlice.scalarLaw
      (sampleResidual p q state round anchor hanchor ⁻¹' {U}) =
      ENNReal.ofReal (RecordedSlowRefresh.residualMass p q state round anchor hanchor U) := by
  calc
    _ = ContinuousControlSlice.scalarLaw.map
        (sampleResidual p q state round anchor hanchor) {U} := by
          symm
          exact Measure.map_apply (measurable_sampleResidual p q state round anchor hanchor)
            (measurableSet_singleton U)
    _ = (RecordedSlowRefresh.residualPMF p q state round anchor hanchor).toMeasure {U} := by
          rw [sampleResidual_map]
    _ = RecordedSlowRefresh.residualPMF p q state round anchor hanchor U :=
          (RecordedSlowRefresh.residualPMF p q state round anchor hanchor).toMeasure_apply_singleton
            U (measurableSet_singleton U)
    _ = _ := RecordedSlowRefresh.residualPMF_apply p q state round anchor hanchor U

/-- The exact one-step law of the Bernoulli proposal plus fresh residual draw. -/
theorem sampleRecordedRefresh_map
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (current : SlowSet p) :
    (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw).map
        (sampleRecordedRefresh p q state round anchor hanchor current) =
      (RecordedSlowRefresh.recordedRefreshKernel p q state round anchor hanchor
        hcap current).toMeasure := by
  classical
  let probability := RecordedSlowRefresh.proposalProbability p q state round
  let proposal := proposalSet probability
  let fresh (V : SlowSet p) := sampleResidual p q state round anchor hanchor ⁻¹' {V}
  have hprobability_nonneg : 0 ≤ probability :=
    RecordedSlowRefresh.proposalProbability_nonneg p q state round
  have hprobability_le_one : probability ≤ 1 :=
    RecordedSlowRefresh.proposalProbability_le_one p q state round hcap
  have hproposal : MeasurableSet proposal := proposalSet_measurable probability
  have hproposal_mass : ContinuousControlSlice.scalarLaw proposal =
      ENNReal.ofReal probability :=
    proposalSet_measure hprobability_le_one
  have hproposal_compl_mass : ContinuousControlSlice.scalarLaw proposalᶜ =
      ENNReal.ofReal (1 - probability) :=
    proposalSet_compl_measure hprobability_nonneg hprobability_le_one
  have hfresh_mass (V : SlowSet p) :
      ContinuousControlSlice.scalarLaw (fresh V) =
        ENNReal.ofReal (RecordedSlowRefresh.residualMass p q state round anchor hanchor V) :=
    sampleResidual_atom p q state round anchor hanchor V
  have hmapmeas := measurable_sampleRecordedRefresh p q state round anchor hanchor current
  apply Measure.ext_of_singleton
  intro V
  rw [Measure.map_apply hmapmeas (measurableSet_singleton V)]
  let retain : Set (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar) :=
    proposalᶜ ×ˢ Set.univ
  let draw : Set (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar) :=
    proposal ×ˢ fresh V
  have hfibre :
      sampleRecordedRefresh p q state round anchor hanchor current ⁻¹' {V} =
        (if V = current then retain else ∅) ∪ draw := by
    ext z
    rcases z with ⟨alpha, beta⟩
    have hsample : sampleRecordedRefresh p q state round anchor hanchor current
        (alpha, beta) = if alpha ∈ proposal then
          sampleResidual p q state round anchor hanchor beta else current := by
      simp [sampleRecordedRefresh, proposal, proposalSet, probability,
        FollowerCutoffScan.thresholdProposalBit]
    change sampleRecordedRefresh p q state round anchor hanchor current (alpha, beta) = V ↔
      (alpha, beta) ∈ (if V = current then retain else ∅) ∪ draw
    rw [hsample]
    by_cases ha : alpha ∈ proposal <;>
      simp [ha, retain, draw, fresh, proposal, eq_comm]
  have hdisjoint : Disjoint retain draw := by
    rw [Set.disjoint_left]
    intro z hzret hzdra
    exact hzret.1 hzdra.1
  have hdraw_meas : MeasurableSet draw := hproposal.prod (by
    exact (measurable_sampleResidual p q state round anchor hanchor)
      (measurableSet_singleton V))
  rw [hfibre]
  by_cases hcurrent : V = current
  · rw [ite_eq_left hcurrent, measure_union hdisjoint hdraw_meas,
      Measure.prod_prod, Measure.prod_prod, hproposal_compl_mass, measure_univ,
      hproposal_mass, hfresh_mass V]
    rw [PMF.toMeasure_apply_singleton _ V (measurableSet_singleton V),
      RecordedSlowRefresh.recordedRefreshKernel_apply,
      RecordedSlowRefresh.residualPMF_apply]
    simp [hcurrent, probability]
  · rw [ite_eq_right hcurrent, empty_union, Measure.prod_prod, hproposal_mass, hfresh_mass V]
    rw [PMF.toMeasure_apply_singleton _ V (measurableSet_singleton V),
      RecordedSlowRefresh.recordedRefreshKernel_apply,
      RecordedSlowRefresh.residualPMF_apply]
    simp [hcurrent, probability]

/-- Exact atom probability of the Bernoulli proposal followed by the fresh
residual draw, including the retained-current atom. -/
theorem sampleRecordedRefresh_atom
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (current V : SlowSet p) :
    (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)
        (sampleRecordedRefresh p q state round anchor hanchor current ⁻¹' {V}) =
      (if V = current then ENNReal.ofReal
        (1 - RecordedSlowRefresh.proposalProbability p q state round) else 0) +
        ENNReal.ofReal (RecordedSlowRefresh.proposalProbability p q state round) *
          ENNReal.ofReal
            (RecordedSlowRefresh.residualMass p q state round anchor hanchor V) := by
  calc
    _ = ((ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw).map
        (sampleRecordedRefresh p q state round anchor hanchor current)) {V} := by
          symm
          exact Measure.map_apply
            (measurable_sampleRecordedRefresh p q state round anchor hanchor current)
            (measurableSet_singleton V)
    _ = (RecordedSlowRefresh.recordedRefreshKernel p q state round anchor hanchor
        hcap current).toMeasure {V} := by
          rw [sampleRecordedRefresh_map]
    _ = RecordedSlowRefresh.recordedRefreshKernel p q state round anchor hanchor
        hcap current V :=
          (RecordedSlowRefresh.recordedRefreshKernel p q state round anchor hanchor
            hcap current).toMeasure_apply_singleton V (measurableSet_singleton V)
    _ = _ := by
          rw [RecordedSlowRefresh.recordedRefreshKernel_apply,
            RecordedSlowRefresh.residualPMF_apply]

/-- The exact product carrier used for an actual numerical round readout. -/
abbrev NumericalCoordinates (p : ConstructorDimensions.Parameters) :=
  Bool × (Option (Fin p.K) × ((Fin p.K → ℝ) × (Fin p.K → ℝ)))

/-- Literal quantized arrivals from the four recorded numerical coordinates. -/
noncomputable def queueArrivalsFromNumerical (q : RecordedQueueRun.Parameters)
    {p : ConstructorDimensions.Parameters} (z : NumericalCoordinates p) :
    Bool × (Fin p.K → ℕ) :=
  (z.1, fun a => if z.2.1 = some a then
    Nat.floor ((q.n : ℝ) * z.2.2.1 a / z.2.2.2 a) else 0)

/-- Borelness of the literal comparison, division and natural floor. -/
theorem measurable_queueArrivalsFromNumerical
    (q : RecordedQueueRun.Parameters) (p : ConstructorDimensions.Parameters) :
    Measurable (queueArrivalsFromNumerical q (p := p)) := by
  classical
  apply measurable_fst.prodMk
  apply Measurable.of_eval
  intro a
  have hmarker : Measurable (fun z : NumericalCoordinates p => z.2.1) :=
    measurable_fst.comp measurable_snd
  have hreward : Measurable (fun z : NumericalCoordinates p => z.2.2.1 a) :=
    (measurable_pi_apply a).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hrate : Measurable (fun z : NumericalCoordinates p => z.2.2.2 a) :=
    (measurable_pi_apply a).comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  change Measurable (fun z : NumericalCoordinates p =>
    if z.2.1 = some a then Nat.floor ((q.n : ℝ) * z.2.2.1 a / z.2.2.2 a) else 0)
  exact Measurable.ite (hmarker.eq_const (some a)).setOf
    (Nat.measurable_floor.comp ((measurable_const.mul hreward).div hrate)) measurable_const

private theorem measurable_stepReadoutFromCoordinates
    {Ω : Type*} [MeasurableSpace Ω]
    (q : RecordedQueueRun.Parameters) (p : ConstructorDimensions.Parameters)
    (state : Ω → RecordedQueueRun.RunState p.K)
    (round : Ω → RecordedQueueRun.RoundInput p.K)
    (hs : Measurable (fun x =>
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout (state x)))
    (hc : Measurable (fun x =>
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates (round x))) :
    Measurable (fun x => ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
      (RecordedQueueRun.step q (state x) (round x))) := by
  classical
  have hreg := measurable_fst.comp hs
  have hflag := measurable_fst.comp (measurable_snd.comp hs)
  have hrecords := measurable_snd.comp (measurable_snd.comp hs)
  have henabled := measurable_fst.comp hc
  have harrivals := measurable_snd.comp
    ((measurable_queueArrivalsFromNumerical q p).comp hc)
  have hrecs : Measurable (fun x => fun j : Fin p.K =>
      RecordedQueueRun.acceptedRecord q (state x) (round x) j) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_of_countable (fun v : Bool × (Bool × ℕ) =>
      if v.1 then (false, 0) else if v.2.1 then (true, v.2.2) else (false, 0))).comp
        (hflag.prodMk (henabled.prodMk ((measurable_pi_apply j).comp harrivals)))
  have hnext : Measurable (fun x => fun j : Fin p.K =>
      QueueReplay.transition (4 * q.n) ((state x).registers j)
        (RecordedQueueRun.acceptedRecord q (state x) (round x) j)) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_of_countable (fun v : (ℕ × ℕ) × (Bool × ℕ) =>
      QueueReplay.transition (4 * q.n) v.1 v.2)).comp
        (((measurable_pi_apply j).comp hreg).prodMk ((measurable_pi_apply j).comp hrecs))
  have hover : Measurable (fun x => (state x).overflow ||
      decide (∃ j : Fin p.K, 32 *
        (QueueReplay.transition (4 * q.n) ((state x).registers j)
          (RecordedQueueRun.acceptedRecord q (state x) (round x) j)).2 > q.D)) :=
    (measurable_of_countable (fun v : Bool × (Fin p.K → ℕ × ℕ) =>
      v.1 || decide (∃ j, 32 * (v.2 j).2 > q.D))).comp (hflag.prodMk hnext)
  have hhistory : Measurable (fun x => fun j : Fin p.K => (state x).records j ++
      [RecordedQueueRun.acceptedRecord q (state x) (round x) j]) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_of_countable (fun v : List (Bool × ℕ) × (Bool × ℕ) =>
      v.1 ++ [v.2])).comp
        (((measurable_pi_apply j).comp hrecords).prodMk ((measurable_pi_apply j).comp hrecs))
  exact hnext.prodMk (hover.prodMk hhistory)

/-- Measurability of each actual canonical slow-set mass from the state
readout. The score powers and finite canonical sums, products and divisions
remain the defining operations. -/
private theorem measurable_recordedSlowMass_ofReadout
    {Ω : Type*} [MeasurableSpace Ω]
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : Ω → RecordedQueueRun.RunState p.K) (anchor : Fin p.K → ℝ)
    (hanchor : ∀ a, 0 < anchor a)
    (hs : Measurable (fun x =>
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout (state x)))
    (U : SlowSet p) :
    Measurable (fun x => RecordedSlowRefresh.recordedSlowMass p q (state x) anchor hanchor U) := by
  have hregisters := measurable_fst.comp hs
  have hweights : Measurable (fun x => fun a : Fin p.K =>
      RecordedQueueRun.scoreWeight q (state x) a) := by
    apply measurable_pi_iff.mpr
    intro a
    change Measurable (fun x => ScoreWeights.scoreWeight
      (1 + 1 / (q.D : ℝ)) ((state x).registers a).1)
    exact (measurable_of_countable (fun r : ℕ × ℕ =>
      ScoreWeights.scoreWeight (1 + 1 / (q.D : ℝ)) r.1)).comp
        ((measurable_pi_apply a).comp hregisters)
  change Measurable (fun x => CanonicalOrientedSetLaw.slowMarginal
    (fun a => RecordedQueueRun.scoreWeight q (state x) a) anchor p.two_le_m p.m_lt_K
    (fun a => RecordedSlowRefresh.scoreWeight_pos q (state x) a) hanchor U)
  fun_prop [CanonicalOrientedSetLaw.slowMarginal,
    FiniteOrientationDisintegration.slowMarginal,
    FiniteOrientationDisintegration.orientedJointMass,
    FiniteOrientationDisintegration.orientationProbability,
    FiniteOrientationDisintegration.partitionFunction]

/-- Every actual residual-mass coordinate is measurable under the queue-state
readout and the numerical round carrier used by the collection observation. -/
theorem measurable_residualMass_coordinate
    {Ω : Type*} [MeasurableSpace Ω]
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : Ω → RecordedQueueRun.RunState p.K)
    (round : Ω → RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (hs : Measurable (fun x =>
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout (state x)))
    (hc : Measurable (fun x =>
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates (round x)))
    (U : SlowSet p) :
    Measurable (fun x =>
      RecordedSlowRefresh.residualMass p q (state x) (round x) anchor hanchor U) := by
  have hnow := measurable_recordedSlowMass_ofReadout p q state anchor hanchor hs U
  have hnextReadout := measurable_stepReadoutFromCoordinates q p state round hs hc
  have hnext := measurable_recordedSlowMass_ofReadout p q
    (fun x => RecordedQueueRun.step q (state x) (round x)) anchor hanchor hnextReadout U
  change Measurable (fun x =>
    (RecordedSlowRefresh.recordedSlowMass p q
        (RecordedQueueRun.step q (state x) (round x)) anchor hanchor U -
      (1 - RecordedSlowRefresh.hazard p q) *
        RecordedSlowRefresh.recordedSlowMass p q (state x) anchor hanchor U) /
      RecordedSlowRefresh.hazard p q)
  exact (hnext.sub ((measurable_const.sub measurable_const).mul hnow)).div_const _

/-- Measurability of the true pre-state gated proposal coordinate. -/
theorem measurable_proposalProbability_coordinate
    {Ω : Type*} [MeasurableSpace Ω]
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : Ω → RecordedQueueRun.RunState p.K)
    (round : Ω → RecordedQueueRun.RoundInput p.K)
    (hs : Measurable (fun x =>
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout (state x)))
    (hc : Measurable (fun x =>
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates (round x))) :
    Measurable (fun x =>
      RecordedSlowRefresh.proposalProbability p q (state x) (round x)) := by
  have hoverflow := measurable_fst.comp (measurable_snd.comp hs)
  have henabled := measurable_fst.comp hc
  change Measurable (fun x => if (state x).overflow = false ∧
    (round x).enabled = true then RecordedSlowRefresh.hazard p q else 0)
  exact (measurable_of_countable (fun gates : Bool × Bool =>
    if gates.1 = false ∧ gates.2 = true then RecordedSlowRefresh.hazard p q else 0)).comp
      (hoverflow.prodMk henabled)

/-- A scalar-valued input jointly with varying actual queue and round data
gives a measurable residual inverse-cumulative sample. -/
theorem measurable_sampleResidual_joint
    {Ω : Type*} [MeasurableSpace Ω]
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : Ω → RecordedQueueRun.RunState p.K)
    (round : Ω → RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (hs : Measurable (fun x =>
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout (state x)))
    (hc : Measurable (fun x =>
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates (round x)))
    (beta : Ω → ContinuousControlSlice.Scalar)
    (hbeta : Measurable beta) :
    Measurable (fun x =>
      sampleResidual p q (state x) (round x) anchor hanchor (beta x)) := by
  classical
  apply measurable_to_countable'
  intro U
  have heq : (fun x =>
      sampleResidual p q (state x) (round x) anchor hanchor (beta x)) ⁻¹' {U} =
      {x | ContinuousCategorical.lower
          (residualEnumMass p q (state x) (round x) anchor hanchor)
          ((residualOrder p).symm U) ≤ (beta x).val ∧
        (beta x).val < ContinuousCategorical.upper
          (residualEnumMass p q (state x) (round x) anchor hanchor)
          ((residualOrder p).symm U)} := by
    ext x
    exact sampleResidual_eq_iff p q (state x) (round x) anchor hanchor (beta x) U
  rw [heq]
  have hbetaVal : Measurable (fun x => (beta x).val) :=
    measurable_subtype_coe.comp hbeta
  have hmass (V : SlowSet p) : Measurable (fun x =>
      RecordedSlowRefresh.residualMass p q (state x) (round x) anchor hanchor V) :=
    measurable_residualMass_coordinate p q state round anchor hanchor hs hc V
  have hlo : Measurable (fun x => ContinuousCategorical.lower
      (residualEnumMass p q (state x) (round x) anchor hanchor)
      ((residualOrder p).symm U)) := by
    unfold ContinuousCategorical.lower residualEnumMass
    exact Finset.measurable_sum _ (fun i _ => hmass ((residualOrder p) i))
  have hup : Measurable (fun x => ContinuousCategorical.upper
      (residualEnumMass p q (state x) (round x) anchor hanchor)
      ((residualOrder p).symm U)) := by
    unfold ContinuousCategorical.upper residualEnumMass
    exact Finset.measurable_sum _ (fun i _ => hmass ((residualOrder p) i))
  exact (measurableSet_le hlo hbetaVal).inter (measurableSet_lt hbetaVal hup)

/-- Joint measurability of the actual two-scalar Bernoulli refresh, including
the measurable current slow set. The proposal uses the true pre-state gate. -/
theorem measurable_sampleRecordedRefresh_joint
    {Ω : Type*} [MeasurableSpace Ω]
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : Ω → RecordedQueueRun.RunState p.K)
    (round : Ω → RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (hs : Measurable (fun x =>
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout (state x)))
    (hc : Measurable (fun x =>
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates (round x)))
    (coordinates : Ω → ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar)
    (hcoordinates : Measurable coordinates)
    (current : Ω → SlowSet p) (hcurrent : Measurable current) :
    Measurable (fun x => sampleRecordedRefresh p q (state x) (round x)
      anchor hanchor (current x) (coordinates x)) := by
  have hprobability := measurable_proposalProbability_coordinate p q state round hs hc
  have hthreshold : MeasurableSet {x |
      FollowerCutoffScan.thresholdProposalBit (coordinates x).1
        (RecordedSlowRefresh.proposalProbability p q (state x) (round x)) = true} := by
    have hset : {x |
        FollowerCutoffScan.thresholdProposalBit (coordinates x).1
          (RecordedSlowRefresh.proposalProbability p q (state x) (round x)) = true} =
        {x | (coordinates x).1.val <
          RecordedSlowRefresh.proposalProbability p q (state x) (round x)} := by
      ext x
      simp [FollowerCutoffScan.thresholdProposalBit]
    rw [hset]
    exact measurableSet_lt
      (measurable_subtype_coe.comp (measurable_fst.comp hcoordinates)) hprobability
  have hfresh := measurable_sampleResidual_joint p q state round anchor hanchor hs hc
    (fun x => (coordinates x).2) (measurable_snd.comp hcoordinates)
  exact Measurable.ite hthreshold hfresh hcurrent

end Bandits.Support.DeferredRefreshUniformKernels

end
