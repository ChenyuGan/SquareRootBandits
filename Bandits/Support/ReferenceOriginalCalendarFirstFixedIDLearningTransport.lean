/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalCalendarFirstWeightedTransport
public import Bandits.Support.ReferenceFirstCollectionRenewalFixedIDOriginalPrefixLearning

import Mathlib.Tactic

/-!
# First-branch learning transport on original fixed-ID sections

These observations keep the original fixed-ID source section and the actual
first selector. The first queue update is included, including when it detects
overflow.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceOriginalCalendarFirstFixedIDLearningTransport

open ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open CompletePublicTable (IDArray)
open ActualInitializationPhysicalStep (GridRewardTable)
open ContinuousLearningRows (TimeControl)
open ProductSetLaw (ProductSet)

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)
  (control0 : TimeControl p)
  (ids : IDArray p) (S : ProductSet p.K p.m)

local notation "X" => SourceInput p
local notation "μ" => sourceInputLaw p
local notation "D" => ReferenceFixedIDSourceSection.fixedIDSourceSection ids
local notation "B" =>
  ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent
    rate rewards C_star C_h
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "theta0" => ProductSetLaw.theta p.m (fun _ : Fin p.K => (1 : ℝ))
local notation "cBirth" =>
  CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)

/-- The accepted first-branch integer arrival, normalized by the queue scale,
and zero when either the first selector or its actual cell is absent. -/
public def firstAcceptedArrival (t : Fin p.T) (i : Fin p.K) : X → ℝ :=
  (B t).indicator (fun z =>
    match ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
        rate rewards C_star C_h t z with
    | none => 0
    | some c => RecordedRoundMoments.rawEstimate Q (RecordedQueueRun.initialState p.K) c i)

/-- The same full-prefix marginal weighted sum of accepted first arrivals. -/
public def firstWeightedArrival (t : Fin p.T) : X → ℝ :=
  fun z => ∑ i : Fin p.K,
    ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt
        rate rewards C_star C_h t.val i z *
      firstAcceptedArrival rate rewards C_star C_h t i z

/-- The comparator-minus-observer gap in the accepted first raw estimates. -/
public def firstRawComparatorGap (t : Fin p.T) : X → ℝ :=
  fun z => (∑ i ∈ S.1, firstAcceptedArrival rate rewards C_star C_h t i z) -
    firstWeightedArrival rate rewards C_star C_h t z

/-- The signed rounded-reward comparator-minus-observer gap on the same
first-selector branch. -/
public def firstRoundedRewardGap (t : Fin p.T) : X → ℝ :=
  (B t).indicator (fun z =>
    (∑ i ∈ S.1,
      ((rewards t i).val : ℝ) / (ConstructorDimensions.D p : ℝ)) -
      ∑ i : Fin p.K,
        ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt
          rate rewards C_star C_h t.val i z *
          (((rewards t i).val : ℝ) / (ConstructorDimensions.D p : ℝ)))

/-- The actual first-cell service-rate floor charged to the comparator, zero
when the first selector or its actual cell is absent. -/
public def firstServiceFloor (t : Fin p.T) : X → ℝ :=
  (B t).indicator (fun z =>
    match ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
        rate rewards C_star C_h t z with
    | none => 0
    | some c => ∑ i ∈ S.1, c.rate i / (rate.n : ℝ))

private abbrev sourceStratum (t : Fin p.T) (j : Fin (M p)) :=
  ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
    (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j t)

private abbrev sourceStratumEvent (t : Fin p.T) (j : Fin (M p)) : Set X :=
  ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
    (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j t)

private abbrev sourceStratumLaw (t : Fin p.T) (j : Fin (M p)) : Measure (sourceStratum rate rewards C_star C_h t j) :=
  ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
    (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j t)

private abbrev idStratum (t : Fin p.T) (j : Fin (M p)) : Set (sourceStratum rate rewards C_star C_h t j) :=
  {z | z.val.1.1 = ids}

include control0 in
private theorem firstSelector_eq_birthStrata (t : Fin p.T) :
    B t = ⋃ j : Fin (M p), sourceStratumEvent rate rewards C_star C_h t j := by
  rw [ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent_eq_sourcePhase
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0) (q := t) (a := ⟨0, K_pos p⟩),
    ReferenceFirstLiveCalendarIntegralAssembly.sourcePhase_birth_iUnion]

include control0 in
private theorem idStratum_integral_eq
    (t : Fin p.T) (j : Fin (M p)) (f : X → ℝ) :
    (∫ z in D ∩ sourceStratumEvent rate rewards C_star C_h t j,
      f z ∂μ) =
    (∫ z in idStratum rate rewards C_star C_h ids t j,
      f z.val ∂sourceStratumLaw rate rewards C_star C_h t j) := by
  let Z := sourceStratum rate rewards C_star C_h t j
  let Zset := sourceStratumEvent rate rewards C_star C_h t j
  let DZ : Set Z := idStratum rate rewards C_star C_h ids t j
  have hZ : MeasurableSet Zset :=
    ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
      rate rewards C_star C_h t control0
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j t)
  have hD : MeasurableSet D :=
    ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids
  have hDZ : MeasurableSet DZ := by
    exact hD.preimage measurable_subtype_coe
  have hsub :
      (∫ z : Z,
        Set.indicator (ReferenceFixedIDSourceSection.fixedIDSourceSection ids) f z.val ∂
          sourceStratumLaw rate rewards C_star C_h t j) =
        ∫ z in Zset,
          Set.indicator (ReferenceFixedIDSourceSection.fixedIDSourceSection ids) f z ∂μ := by
    simpa only [Z, Zset, sourceStratumLaw, sourceStratum, sourceStratumEvent,
      ReferenceTotalSourceDisintegration.sourceStratumMeasure] using
      (integral_subtype_comap hZ
        (Set.indicator (ReferenceFixedIDSourceSection.fixedIDSourceSection ids) f))
  have hleft :
      (∫ z : Z,
        Set.indicator (ReferenceFixedIDSourceSection.fixedIDSourceSection ids) f z.val ∂
          sourceStratumLaw rate rewards C_star C_h t j) =
        ∫ z in DZ, f z.val ∂sourceStratumLaw rate rewards C_star C_h t j := by
    calc
      (∫ z : Z,
          Set.indicator (ReferenceFixedIDSourceSection.fixedIDSourceSection ids) f z.val ∂
            sourceStratumLaw rate rewards C_star C_h t j) =
        ∫ z : Z, Set.indicator DZ (fun x => f x.val) z ∂
          sourceStratumLaw rate rewards C_star C_h t j := by
          congr 1
      _ = _ := integral_indicator hDZ
  have hright :
      (∫ z in Zset,
        Set.indicator (ReferenceFixedIDSourceSection.fixedIDSourceSection ids) f z ∂μ) =
        ∫ z in D ∩ Zset, f z ∂μ := by
    calc
      (∫ z in Zset,
        Set.indicator (ReferenceFixedIDSourceSection.fixedIDSourceSection ids) f z ∂μ) =
          ∫ z, Set.indicator (ReferenceFixedIDSourceSection.fixedIDSourceSection ids) f z ∂
            ((sourceInputLaw p).restrict Zset) := rfl
      _ = ∫ z in D, f z ∂((sourceInputLaw p).restrict Zset) := integral_indicator hD
      _ = ∫ z in D ∩ Zset, f z ∂μ := by
        rw [Measure.restrict_restrict hD]
  calc
    _ = ∫ z in Zset,
        Set.indicator (ReferenceFixedIDSourceSection.fixedIDSourceSection ids) f z ∂μ := hright.symm
    _ = ∫ z : Z,
        Set.indicator (ReferenceFixedIDSourceSection.fixedIDSourceSection ids) f z.val ∂
          sourceStratumLaw rate rewards C_star C_h t j := hsub.symm
    _ = _ := hleft

include control0 in
private theorem sourceStratum_mass_eq
    (t : Fin p.T) (j : Fin (M p)) :
    (sourceStratumLaw rate rewards C_star C_h t j).real
        (idStratum rate rewards C_star C_h ids t j) =
      (sourceInputLaw p).real (D ∩ sourceStratumEvent rate rewards C_star C_h t j) := by
  let Z := sourceStratum rate rewards C_star C_h t j
  let Zset := sourceStratumEvent rate rewards C_star C_h t j
  let DZ := idStratum rate rewards C_star C_h ids t j
  have hZ : MeasurableSet Zset :=
    ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
      rate rewards C_star C_h t control0
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j t)
  have hD : MeasurableSet D :=
    ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids
  have hDZ : MeasurableSet DZ := by
    exact hD.preimage measurable_subtype_coe
  have hmap := ReferenceTotalSourceDisintegration.sourceStratumMeasure_map
    rate rewards C_star C_h t control0
    (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j t)
  have hmass :
      sourceStratumLaw rate rewards C_star C_h t j DZ = μ (D ∩ Zset) := by
    have h := congrArg (fun η : Measure X => η D) hmap
    have hpre : (Subtype.val : Z → X) ⁻¹' D = DZ := by
      ext z
      change z.val ∈ D ↔ z.val ∈ D
      rfl
    rw [Measure.map_apply
        (measurable_subtype_coe : Measurable ((Subtype.val) : Z → X)) hD,
      hpre, Measure.restrict_apply hD] at h
    simpa [Z, Zset, DZ, sourceStratum, sourceStratumEvent, sourceStratumLaw,
      ReferenceTotalSourceDisintegration.sourceStratumMeasure] using h
  exact congrArg ENNReal.toReal hmass

include control0 in
private theorem firstID_domain_eq (t : Fin p.T) :
    D ∩ B t = ⋃ j : Fin (M p),
      D ∩ sourceStratumEvent rate rewards C_star C_h t j := by
  rw [firstSelector_eq_birthStrata
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (t := t)]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨hzD, j, hzj⟩
    exact ⟨j, hzD, hzj⟩
  · rintro ⟨j, hzD, hzj⟩
    exact ⟨hzD, j, hzj⟩

include control0 in
private theorem firstID_piece_measurable (t : Fin p.T) (j : Fin (M p)) :
    MeasurableSet (D ∩ sourceStratumEvent rate rewards C_star C_h t j) := by
  exact (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).inter
    (ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
      rate rewards C_star C_h t control0
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j t))

private theorem firstID_piece_disjoint (t : Fin p.T) :
    Pairwise (fun j k : Fin (M p) =>
      Disjoint (D ∩ sourceStratumEvent rate rewards C_star C_h t j)
        (D ∩ sourceStratumEvent rate rewards C_star C_h t k)) := by
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro z hz hk
  apply (Set.disjoint_left.mp
    (ReferenceTotalSourcePairCoupling.sourceStratumEvent_disjoint
      rate rewards C_star C_h t
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j t)
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex k t) (by
        intro h
        apply hjk
        exact congrArg Prod.fst h))) hz.2 hk.2

include control0 in
private theorem firstID_mass_eq_sum (t : Fin p.T) :
    (∑ j : Fin (M p),
      (sourceInputLaw p).real (D ∩ sourceStratumEvent rate rewards C_star C_h t j)) =
        (sourceInputLaw p).real (D ∩ B t) := by
  rw [firstID_domain_eq
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (ids := ids) (t := t)]
  symm
  exact measureReal_iUnion_fintype
    (firstID_piece_disjoint rate rewards C_star C_h ids t)
    (firstID_piece_measurable rate rewards C_star C_h control0 ids t)
    (fun _ => by finiteness)

include control0 in
private theorem integrableOn_sourceStratum_piece
    (t : Fin p.T) (j : Fin (M p)) (f : X → ℝ)
    (g : sourceStratum rate rewards C_star C_h t j → ℝ)
    (heq : ∀ z, f z.val = g z)
    (hg : Integrable g (sourceStratumLaw rate rewards C_star C_h t j)) :
    IntegrableOn f
      (D ∩ sourceStratumEvent rate rewards C_star C_h t j) μ := by
  have hset := ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
    rate rewards C_star C_h t control0
    (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j t)
  have hpull : Integrable (fun z : sourceStratum rate rewards C_star C_h t j => f z.val)
      (sourceStratumLaw rate rewards C_star C_h t j) := by
    convert hg using 1
    funext z
    exact heq z
  have hwhole : IntegrableOn f (sourceStratumEvent rate rewards C_star C_h t j) μ :=
    (integrableOn_iff_comap_subtypeVal hset).2 (by
      change Integrable
        (fun z : {x : X // x ∈ sourceStratumEvent rate rewards C_star C_h t j} =>
          f z.val) ((sourceInputLaw p).comap Subtype.val)
      exact hpull)
  exact hwhole.mono_set (Set.inter_subset_right)

include control0 in
private theorem integrableOn_firstID_domain
    (t : Fin p.T) (f : X → ℝ)
    (hpiece : ∀ j : Fin (M p),
      IntegrableOn f (D ∩ sourceStratumEvent rate rewards C_star C_h t j) μ) :
    IntegrableOn f (D ∩ B t) μ := by
  rw [firstID_domain_eq
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (ids := ids) (t := t)]
  apply integrableOn_iUnion_of_summable_integral_norm
  · exact hpiece
  · exact Summable.of_finite

include control0 in
private theorem firstTheta_eq_unit_on_stratum
    (t : Fin p.T) (j : Fin (M p))
    (z : sourceStratum rate rewards C_star C_h t j) (i : Fin p.K) :
    ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt
        rate rewards C_star C_h t.val i z.val = theta0 i := by
  exact (ReferenceOriginalCalendarFirstWeightedTransport.source_first_weighted_facts
    rate rewards C_star C_h control0 t j z).2.2.2.1 i

private theorem firstRawEstimate_eq_readout_on_stratum
    (t : Fin p.T) (j : Fin (M p))
    (z : sourceStratum rate rewards C_star C_h t j) (i : Fin p.K) :
    RecordedRoundMoments.rawEstimate Q (RecordedQueueRun.initialState p.K)
        (ReferenceFirstLaunchCommonUpdateSource.firstCell
          rate rewards C_star C_h j t control0 z) i =
      ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
        rate rewards C_star C_h j t control0 z i := by
  let cell := ReferenceFirstLaunchCommonUpdateSource.firstCell
    rate rewards C_star C_h j t control0 z
  let update := ReferenceFirstLaunchCommonUpdateSource.firstUpdate
    rate rewards C_star C_h j t control0 z
  have htransport := ReferenceOriginalCalendarFirstWeightedTransport.source_first_transport
    rate rewards C_star C_h control0 t j z
  have hstep := ReferenceFirstLaunchCommonUpdateSource.source_first_update
    rate rewards C_star C_h j t control0 z
  have htotal : (update.registers i).1 + (update.registers i).2 =
      ReferenceFirstLaunchCommonUpdateSource.firstArrival
        rate rewards C_star C_h j t control0 z i := (hstep.1 i).2.2
  have hreadout :
      ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
          rate rewards C_star C_h j t control0 z i =
        (ReferenceFirstLaunchCommonUpdateSource.firstArrival
          rate rewards C_star C_h j t control0 z i : ℝ) /
          (rate.eta.val * (ConstructorDimensions.D p : ℝ)) := by
    change ((((update.registers i).1 + (update.registers i).2 : ℕ) : ℝ) /
      (rate.eta.val * (ConstructorDimensions.D p : ℝ))) = _
    rw [htotal]
  rw [RecordedRoundMoments.rawEstimate_eq_normalizedQuantizedArrival_of_enabled
      Q (RecordedQueueRun.initialState p.K) cell i htransport.2.2.2.2 rfl,
    RecordedRoundMoments.normalizedQuantizedArrival]
  change (RecordedQueueRun.quantizedArrival Q cell i : ℝ) / ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) = _
  have harrival : RecordedQueueRun.quantizedArrival Q cell i =
      ReferenceFirstLaunchCommonUpdateSource.firstArrival
        rate rewards C_star C_h j t control0 z i := rfl
  have hn : ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) = (rate.n : ℝ) := by
    rfl
  rw [harrival, hn, rate.n_scale, hreadout]

private theorem firstAcceptedArrival_on_stratum
    (t : Fin p.T) (j : Fin (M p))
    (z : sourceStratum rate rewards C_star C_h t j) (i : Fin p.K) :
    firstAcceptedArrival rate rewards C_star C_h t i z.val =
      ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
        rate rewards C_star C_h j t control0 z i := by
  have hunion := firstSelector_eq_birthStrata
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (t := t)
  have hB : z.val ∈ B t := by
    rw [hunion]
    exact Set.mem_iUnion.mpr ⟨j, z.property⟩
  have hactual := (ReferenceOriginalCalendarFirstWeightedTransport.source_first_transport
    rate rewards C_star C_h control0 t j z).2.1
  simp only [firstAcceptedArrival, Set.indicator_of_mem hB, hactual]
  exact firstRawEstimate_eq_readout_on_stratum rate rewards C_star C_h control0 t j z i

include control0 in
private theorem firstWeightedArrival_on_stratum
    (t : Fin p.T) (j : Fin (M p))
    (z : sourceStratum rate rewards C_star C_h t j) :
    firstWeightedArrival rate rewards C_star C_h t z.val =
      ReferenceOriginalCalendarFirstWeightedTransport.firstWeightedArrival
        rate rewards C_star C_h t z.val := by
  have htheta := firstTheta_eq_unit_on_stratum rate rewards C_star C_h control0 t j z
  have hunion := firstSelector_eq_birthStrata
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (t := t)
  have hB : z.val ∈ B t := by
    rw [hunion]
    exact Set.mem_iUnion.mpr ⟨j, z.property⟩
  calc
    firstWeightedArrival rate rewards C_star C_h t z.val =
        ∑ i : Fin p.K, theta0 i *
          ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
            rate rewards C_star C_h j t control0 z i := by
      simp only [firstWeightedArrival]
      apply Finset.sum_congr rfl
      intro i hi
      rw [htheta i, firstAcceptedArrival_on_stratum
        rate rewards C_star C_h control0 t j z i]
    _ = ReferenceOriginalCalendarFirstWeightedTransport.firstWeightedArrival
          rate rewards C_star C_h t z.val :=
      (ReferenceOriginalCalendarFirstWeightedTransport.first_arrival_on_sourceStratum
        rate rewards C_star C_h control0 t j z).symm

include control0 in
private theorem firstWeightedArrival_eq_accepted_root (t : Fin p.T) :
    firstWeightedArrival rate rewards C_star C_h t =
      ReferenceOriginalCalendarFirstWeightedTransport.firstWeightedArrival
        rate rewards C_star C_h t := by
  funext z
  by_cases hz : z ∈ B t
  · have hunion := firstSelector_eq_birthStrata
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0) (t := t)
    rw [hunion] at hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
    exact firstWeightedArrival_on_stratum rate rewards C_star C_h control0 t j ⟨z, hj⟩
  · simp [firstWeightedArrival, firstAcceptedArrival,
      ReferenceOriginalCalendarFirstWeightedTransport.firstWeightedArrival, hz]

include control0 in
private theorem firstWeightedArrival_integrable (t : Fin p.T) :
    Integrable (firstWeightedArrival rate rewards C_star C_h t) μ := by
  rw [firstWeightedArrival_eq_accepted_root
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (t := t)]
  exact ReferenceOriginalCalendarFirstWeightedTransport.firstWeightedArrival_integrable
    rate rewards C_star C_h control0 t

include control0 in
private theorem firstRawComparatorGap_on_stratum
    (t : Fin p.T) (j : Fin (M p))
    (z : sourceStratum rate rewards C_star C_h t j) :
    firstRawComparatorGap rate rewards C_star C_h S t z.val =
      (∑ i ∈ S.1,
        ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
          rate rewards C_star C_h j t control0 z i) -
      ∑ i : Fin p.K, theta0 i *
        ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
          rate rewards C_star C_h j t control0 z i := by
  unfold firstRawComparatorGap
  calc
    (∑ i ∈ S.1, firstAcceptedArrival rate rewards C_star C_h t i z.val) -
        firstWeightedArrival rate rewards C_star C_h t z.val =
      (∑ i ∈ S.1,
        ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
          rate rewards C_star C_h j t control0 z i) -
        ReferenceOriginalCalendarFirstWeightedTransport.firstWeightedArrival
          rate rewards C_star C_h t z.val := by
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          exact firstAcceptedArrival_on_stratum rate rewards C_star C_h control0 t j z i
        · exact firstWeightedArrival_on_stratum
            rate rewards C_star C_h control0 t j z
    _ = _ := by
      congr 1
      simpa only [] using
        (ReferenceOriginalCalendarFirstWeightedTransport.first_arrival_on_sourceStratum
          rate rewards C_star C_h control0 t j z)

include control0 in
private theorem firstRoundedRewardGap_on_stratum
    (t : Fin p.T) (j : Fin (M p))
    (z : sourceStratum rate rewards C_star C_h t j) :
    firstRoundedRewardGap rate rewards C_star C_h S t z.val =
      (∑ i ∈ S.1,
        ((rewards t i).val : ℝ) / (ConstructorDimensions.D p : ℝ)) -
      ∑ i : Fin p.K, theta0 i *
        (((rewards t i).val : ℝ) / (ConstructorDimensions.D p : ℝ)) := by
  have htheta := firstTheta_eq_unit_on_stratum rate rewards C_star C_h control0 t j z
  have hunion := firstSelector_eq_birthStrata
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (t := t)
  have hB : z.val ∈ B t := by
    rw [hunion]
    exact Set.mem_iUnion.mpr ⟨j, z.property⟩
  simp [firstRoundedRewardGap, hB, htheta]

include control0 in
private theorem firstServiceFloor_on_stratum
    (t : Fin p.T) (j : Fin (M p))
    (z : sourceStratum rate rewards C_star C_h t j) :
    firstServiceFloor rate rewards C_star C_h S t z.val =
      ∑ i ∈ S.1,
        CanonicalRecordingRates.xi p rate.eta.val (fun _ : Fin p.K => (1 : ℝ)) i /
          (rate.n : ℝ) := by
  have hunion := firstSelector_eq_birthStrata
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (t := t)
  have hB : z.val ∈ B t := by
    rw [hunion]
    exact Set.mem_iUnion.mpr ⟨j, z.property⟩
  have hactual := (ReferenceOriginalCalendarFirstWeightedTransport.source_first_transport
    rate rewards C_star C_h control0 t j z).2.1
  let coords := ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
    rate rewards C_star C_h j t control0 z
  let cell := ReferenceFirstLaunchCommonUpdateSource.firstCell
    rate rewards C_star C_h j t control0 z
  have hrate (i : Fin p.K) : cell.rate i =
      CanonicalRecordingRates.xi p rate.eta.val (fun _ : Fin p.K => (1 : ℝ)) i := by
    simpa only [cell, ReferenceFirstLaunchCommonUpdateSource.firstCell, coords,
      ReferenceFirstLaunchRecordingPhysicalMarker.numericalCell,
      ReferenceFirstWindowNumericalStream.sourceCell] using
      (ReferenceFirstLaunchRecordingPhysicalMarker.payload_rate
        rate rewards C_star C_h j t control0 coords.1 coords.2.1 coords.2.2 i)
  simp only [firstServiceFloor, Set.indicator_of_mem hB, hactual]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hrate i]

include control0 in
private theorem incomingEnergy_zero_on_firstSelector
    (t : Fin p.T) (z : X) (hz : z ∈ B t) :
    ReferenceOriginalCalendarLiveCollectionWeightedDrift.C
      rate rewards C_star C_h t.val z = 0 := by
  have hunion := firstSelector_eq_birthStrata
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (t := t)
  rw [hunion] at hz
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
  exact (ReferenceOriginalCalendarFirstWeightedTransport.source_first_weighted_facts
    rate rewards C_star C_h control0 t j ⟨z, hj⟩).2.1

include control0 in
private theorem firstRawComparatorGap_integrableOn (t : Fin p.T) :
    IntegrableOn (firstRawComparatorGap rate rewards C_star C_h S t)
      (D ∩ B t) μ := by
  apply integrableOn_firstID_domain
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (ids := ids) (t := t)
  intro j
  let Z := sourceStratum rate rewards C_star C_h t j
  let μZ := sourceStratumLaw rate rewards C_star C_h t j
  let readout := fun (i : Fin p.K) (z : Z) =>
    ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
      rate rewards C_star C_h j t control0 z i
  have hreadout (i : Fin p.K) : Integrable (readout i) μZ := by
    exact (ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
      rate rewards C_star C_h j t control0 i Set.univ Set.univ
      MeasurableSet.univ MeasurableSet.univ).2.2.1
  have hselected : Integrable (fun z : Z => ∑ i ∈ S.1, readout i z) μZ := by
    exact integrable_finsetSum S.1 (fun i hi => hreadout i)
  have hobserver : Integrable (fun z : Z =>
      ∑ i : Fin p.K, theta0 i * readout i z) μZ := by
    exact integrable_finsetSum Finset.univ
      (fun i hi => (hreadout i).const_mul (theta0 i))
  have hgap : Integrable (fun z : Z =>
      (∑ i ∈ S.1, readout i z) - ∑ i : Fin p.K, theta0 i * readout i z) μZ :=
    hselected.sub hobserver
  have hpull : Integrable
      (fun z : Z => firstRawComparatorGap rate rewards C_star C_h S t z.val) μZ := by
    have heq :
        (fun z : Z => firstRawComparatorGap rate rewards C_star C_h S t z.val) =
          fun z => (∑ i ∈ S.1, readout i z) -
            ∑ i : Fin p.K, theta0 i * readout i z := by
      funext z
      exact firstRawComparatorGap_on_stratum
        rate rewards C_star C_h control0 S t j z
    rw [heq]
    exact hgap
  exact integrableOn_sourceStratum_piece
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (ids := ids) t j
    (firstRawComparatorGap rate rewards C_star C_h S t)
    (fun z => (∑ i ∈ S.1, readout i z) -
      ∑ i : Fin p.K, theta0 i * readout i z)
    (fun z => firstRawComparatorGap_on_stratum
      rate rewards C_star C_h control0 S t j z) hgap

include control0 in
private theorem firstRoundedRewardGap_integrableOn (t : Fin p.T) :
    IntegrableOn (firstRoundedRewardGap rate rewards C_star C_h S t)
      (D ∩ B t) μ := by
  apply integrableOn_firstID_domain
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (ids := ids) (t := t)
  intro j
  let Z := sourceStratum rate rewards C_star C_h t j
  let c : ℝ :=
    (∑ i ∈ S.1, ((rewards t i).val : ℝ) / (ConstructorDimensions.D p : ℝ)) -
      ∑ i : Fin p.K, theta0 i *
        (((rewards t i).val : ℝ) / (ConstructorDimensions.D p : ℝ))
  have hconst : Integrable (fun _ : Z => c)
      (sourceStratumLaw rate rewards C_star C_h t j) := integrable_const c
  have hpull : Integrable
      (fun z : Z => firstRoundedRewardGap rate rewards C_star C_h S t z.val)
      (sourceStratumLaw rate rewards C_star C_h t j) := by
    have heq :
        (fun z : Z => firstRoundedRewardGap rate rewards C_star C_h S t z.val) =
          fun _ => c := by
      funext z
      exact firstRoundedRewardGap_on_stratum
        rate rewards C_star C_h control0 S t j z
    rw [heq]
    exact hconst
  exact integrableOn_sourceStratum_piece
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (ids := ids) t j
    (firstRoundedRewardGap rate rewards C_star C_h S t) (fun _ => c)
    (fun z => firstRoundedRewardGap_on_stratum
      rate rewards C_star C_h control0 S t j z) hconst

include control0 in
private theorem firstServiceFloor_integrableOn (t : Fin p.T) :
    IntegrableOn (firstServiceFloor rate rewards C_star C_h S t)
      (D ∩ B t) μ := by
  apply integrableOn_firstID_domain
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (ids := ids) (t := t)
  intro j
  let Z := sourceStratum rate rewards C_star C_h t j
  let c : ℝ := ∑ i ∈ S.1,
      CanonicalRecordingRates.xi p rate.eta.val (fun _ : Fin p.K => (1 : ℝ)) i /
        (rate.n : ℝ)
  have hconst : Integrable (fun _ : Z => c)
      (sourceStratumLaw rate rewards C_star C_h t j) := integrable_const c
  have hpull : Integrable
      (fun z : Z => firstServiceFloor rate rewards C_star C_h S t z.val)
      (sourceStratumLaw rate rewards C_star C_h t j) := by
    have heq :
        (fun z : Z => firstServiceFloor rate rewards C_star C_h S t z.val) =
          fun _ => c := by
      funext z
      exact firstServiceFloor_on_stratum
        rate rewards C_star C_h control0 S t j z
    rw [heq]
    exact hconst
  exact integrableOn_sourceStratum_piece
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (ids := ids) t j
    (firstServiceFloor rate rewards C_star C_h S t) (fun _ => c)
    (fun z => firstServiceFloor_on_stratum
      rate rewards C_star C_h control0 S t j z) hconst

include control0 in
private theorem first_square_stratum_budget (t : Fin p.T) (j : Fin (M p)) :
    (∫ z in D ∩ sourceStratumEvent rate rewards C_star C_h t j,
      ReferenceOriginalCalendarLiveCollectionWeightedDrift.deltaV
        rate rewards C_star C_h t z ∂μ) ≤
      cBirth * (sourceInputLaw p).real (D ∩ sourceStratumEvent rate rewards C_star C_h t j) := by
  let Z := sourceStratum rate rewards C_star C_h t j
  let μZ := sourceStratumLaw rate rewards C_star C_h t j
  let DZ := idStratum rate rewards C_star C_h ids t j
  have hDZ : MeasurableSet DZ :=
    (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage
      measurable_subtype_coe
  have hbudget :=
    ReferenceFirstCollectionFixedIDWeightedCostBudget.fixedIDBirthEnergyBudget
      rate rewards C_star C_h control0 ids j t
  calc
    _ = ∫ z in DZ,
        ReferenceOriginalCalendarLiveCollectionWeightedDrift.deltaV
          rate rewards C_star C_h t z.val ∂μZ :=
      idStratum_integral_eq rate rewards C_star C_h control0 ids t j _
    _ = ∫ z in DZ,
        ReferenceFirstLaunchEnergyInitialization.birthPotential
          rate rewards C_star C_h j t control0 z ∂μZ := by
      apply setIntegral_congr_fun hDZ
      intro z hz
      exact ReferenceOriginalCalendarFirstWeightedTransport.source_first_delta_eq_birthPotential
        rate rewards C_star C_h control0 t j z
    _ ≤ cBirth * μZ.real DZ := by
      simpa [Z, DZ, μZ, sourceStratum, sourceStratumLaw, idStratum,
        ReferenceTotalSourceDisintegration.sourceStratumMeasure] using hbudget
    _ = cBirth * (sourceInputLaw p).real (D ∩ sourceStratumEvent rate rewards C_star C_h t j) := by
      rw [sourceStratum_mass_eq
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (control0 := control0) (ids := ids) (t := t) (j := j)]

include control0 in
private theorem first_arrival_stratum_budget (t : Fin p.T) (j : Fin (M p)) :
    (∫ z in D ∩ sourceStratumEvent rate rewards C_star C_h t j,
      firstWeightedArrival rate rewards C_star C_h t z ∂μ) ≤
      (p.m : ℝ) * (sourceInputLaw p).real (D ∩ sourceStratumEvent rate rewards C_star C_h t j) := by
  let Z := sourceStratum rate rewards C_star C_h t j
  let μZ := sourceStratumLaw rate rewards C_star C_h t j
  let DZ := idStratum rate rewards C_star C_h ids t j
  have hDZ : MeasurableSet DZ :=
    (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage
      measurable_subtype_coe
  have hformula :
      (fun z : Z => firstWeightedArrival rate rewards C_star C_h t z.val) =
        fun z => ∑ i : Fin p.K,
          theta0 i * ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
            rate rewards C_star C_h j t control0 z i := by
    funext z
    calc
      firstWeightedArrival rate rewards C_star C_h t z.val =
          ReferenceOriginalCalendarFirstWeightedTransport.firstWeightedArrival
            rate rewards C_star C_h t z.val :=
        firstWeightedArrival_on_stratum rate rewards C_star C_h control0 t j z
      _ = ∑ i : Fin p.K,
          theta0 i * ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
            rate rewards C_star C_h j t control0 z i :=
        ReferenceOriginalCalendarFirstWeightedTransport.first_arrival_on_sourceStratum
          rate rewards C_star C_h control0 t j z
  have hbudget :=
    ReferenceFirstCollectionFixedIDWeightedArrivalBudget.fixedID_birth_stratum_weightedArrival_le
      rate rewards C_star C_h control0 ids j t
  calc
    _ = ∫ z in DZ, firstWeightedArrival rate rewards C_star C_h t z.val ∂μZ :=
      idStratum_integral_eq rate rewards C_star C_h control0 ids t j _
    _ ≤ (p.m : ℝ) * μZ.real DZ := by
      calc
        _ = ∫ z in DZ,
            ∑ i : Fin p.K,
              theta0 i * ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
                rate rewards C_star C_h j t control0 z i ∂μZ := by
              apply setIntegral_congr_fun hDZ
              intro z hz
              exact congrFun hformula z
        _ ≤ (p.m : ℝ) * μZ.real DZ := by
          simpa [DZ, μZ, Z, sourceStratum, sourceStratumLaw, idStratum,
            ReferenceTotalSourceDisintegration.sourceStratumMeasure] using hbudget
    _ = (p.m : ℝ) * (sourceInputLaw p).real (D ∩ sourceStratumEvent rate rewards C_star C_h t j) := by
      rw [sourceStratum_mass_eq
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (control0 := control0) (ids := ids) (t := t) (j := j)]

include control0 in
private theorem first_signed_stratum_estimate (t : Fin p.T) (j : Fin (M p)) :
    (∫ z in D ∩ sourceStratumEvent rate rewards C_star C_h t j,
      firstRoundedRewardGap rate rewards C_star C_h S t z ∂μ) ≤
    (∫ z in D ∩ sourceStratumEvent rate rewards C_star C_h t j,
      firstRawComparatorGap rate rewards C_star C_h S t z ∂μ) +
    (∫ z in D ∩ sourceStratumEvent rate rewards C_star C_h t j,
      firstServiceFloor rate rewards C_star C_h S t z ∂μ) := by
  let Z := sourceStratum rate rewards C_star C_h t j
  let μZ := sourceStratumLaw rate rewards C_star C_h t j
  let DZ := idStratum rate rewards C_star C_h ids t j
  let Xr := ReferenceFirstLaunchRecordingPhysicalMarker.RetainedStart
    rate rewards C_star C_h j t control0
  let μC := ReferenceRetainedSourceCoupling.retainedRemainderMeasure
    rate rewards C_star C_h j t t.val le_rfl control0
  let coords := ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
    rate rewards C_star C_h j t control0
  let Aset : Set Xr := {x | x.val.1.1 = ids}
  let mass : ℝ := μC.real Aset
  let rhoArm : Fin p.K → ℝ := fun i =>
    ((rewards t i).val : ℝ) / (ConstructorDimensions.D p : ℝ)
  let xiArm : Fin p.K → ℝ := fun i =>
    CanonicalRecordingRates.xi p rate.eta.val (fun _ => (1 : ℝ)) i
  let valueArm : Fin p.K → ℝ := fun i =>
    QuantizedRecordingMoments.quantizedValue (ConstructorDimensions.D p)
      rate.eta.val (xiArm i) (rhoArm i)
  let comparator : ℝ := ∑ i ∈ S.1, rhoArm i
  let observer : ℝ := ∑ i : Fin p.K, theta0 i * rhoArm i
  let floor : ℝ := ∑ i ∈ S.1, xiArm i / (rate.n : ℝ)
  let gap := comparator - observer
  have hDZ : MeasurableSet DZ :=
    (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage
      measurable_subtype_coe
  have hAset : MeasurableSet Aset :=
    (measurableSet_singleton ids).preimage
      ((measurable_fst.comp measurable_fst).comp measurable_subtype_coe)
  have hmap := congrArg (fun ν => ν
      (Aset ×ˢ (Set.univ : Set
        (ReferenceFirstLaunchRecordingPhysicalMarker.AssignmentVector p ×
          ReferenceFirstLaunchRecordingPhysicalMarker.NonAssignmentControl p))))
    (ReferenceFirstLaunchRecordingSourceLaw.map_sourceCoordinates
      rate rewards C_star C_h j t control0)
  rw [Measure.map_apply
      (ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceCoordinates
        rate rewards C_star C_h j t control0)
      (hAset.prod MeasurableSet.univ), Measure.prod_prod] at hmap
  have hdom : coords ⁻¹' (Aset ×ˢ (Set.univ : Set
      (ReferenceFirstLaunchRecordingPhysicalMarker.AssignmentVector p ×
        ReferenceFirstLaunchRecordingPhysicalMarker.NonAssignmentControl p))) = DZ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, Aset, DZ,
      idStratum]
    change (coords z).1.val.1.1 = ids ↔ z.val.1.1 = ids
    rw [ReferenceFirstLiveRetainedIDExponentialStep.sourceCoordinates_originalID
      rate rewards C_star C_h j t control0 z]
  rw [hdom] at hmap
  have hMass : μZ DZ = μC Aset := by
    simpa only [measure_univ, mul_one] using hmap
  have hMassReal : μZ.real DZ = mass := by
    exact congrArg ENNReal.toReal hMass
  have hmoment (i : Fin p.K) :
      (∫ z in DZ,
        ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
          rate rewards C_star C_h j t control0 z i ∂μZ) =
        mass * (xiArm i * valueArm i) := by
    have hmom := ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
      rate rewards C_star C_h j t control0 i Aset Set.univ hAset MeasurableSet.univ
    have hfirst := hmom.2.2.2.2.1
    have hcoordset :
        {z : Z | (coords z).1 ∈ Aset ∧ (coords z).2.1 ∈
          (Set.univ : Set (ReferenceFirstLaunchRecordingPhysicalMarker.AssignmentVector p))} = DZ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, and_true, Aset, DZ, idStratum]
      change (coords z).1.val.1.1 = ids ↔ z.val.1.1 = ids
      rw [ReferenceFirstLiveRetainedIDExponentialStep.sourceCoordinates_originalID
        rate rewards C_star C_h j t control0 z]
    rw [hcoordset] at hfirst
    simp only [measure_univ, ENNReal.toReal_one, mul_one] at hfirst
    calc
      _ = μC.real Aset * (xiArm i * valueArm i) := by
        simpa [xiArm, valueArm, rhoArm, μC, μZ, Z, sourceStratum, sourceStratumLaw,
          ReferenceTotalSourceDisintegration.sourceStratumMeasure, Measure.real,
          mul_assoc] using hfirst
      _ = mass * (xiArm i * valueArm i) := by rfl
  have hreadoutInt (i : Fin p.K) : Integrable
      (fun z : Z => ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
        rate rewards C_star C_h j t control0 z i) μZ := by
    exact (ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
      rate rewards C_star C_h j t control0 i Set.univ Set.univ
      MeasurableSet.univ MeasurableSet.univ).2.2.1
  have hselectedInt : Integrable (fun z : Z =>
      ∑ i ∈ S.1,
        ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
          rate rewards C_star C_h j t control0 z i) μZ :=
    integrable_finsetSum S.1 (fun i hi => hreadoutInt i)
  have hobserverInt : Integrable (fun z : Z =>
      ∑ i : Fin p.K, theta0 i *
        ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
          rate rewards C_star C_h j t control0 z i) μZ :=
    integrable_finsetSum Finset.univ
      (fun i hi => (hreadoutInt i).const_mul (theta0 i))
  have hcoeff (i : Fin p.K) :
      rhoArm i - xiArm i / (rate.n : ℝ) ≤ xiArm i * valueArm i ∧
        xiArm i * valueArm i ≤ rhoArm i := by
    have hc :=
      ReferenceFirstLaunchCommonUpdateSource.first_update_moment_coefficients_bounds
        rate rewards t i
    constructor
    · simpa [rhoArm, xiArm, valueArm, rate.n_scale] using hc.1
    · simpa [rhoArm, xiArm, valueArm] using hc.2.1
  have hrawSelected :
      (∫ z in DZ,
        ∑ i ∈ S.1,
          ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
            rate rewards C_star C_h j t control0 z i ∂μZ) =
        ∑ i ∈ S.1, mass * (xiArm i * valueArm i) := by
    rw [integral_finsetSum S.1 (fun i hi => (hreadoutInt i).integrableOn)]
    apply Finset.sum_congr rfl
    intro i hi
    simpa [mul_assoc] using hmoment i
  have hrawObserver :
      (∫ z in DZ,
        ∑ i : Fin p.K, theta0 i *
          ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
            rate rewards C_star C_h j t control0 z i ∂μZ) =
        ∑ i : Fin p.K, theta0 i * (mass * (xiArm i * valueArm i)) := by
    rw [integral_finsetSum Finset.univ
      (fun i hi => ((hreadoutInt i).const_mul (theta0 i)).integrableOn)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul, hmoment i]
  have hmassNonneg : 0 ≤ mass := MeasureTheory.measureReal_nonneg
  have hthetaNonneg (i : Fin p.K) : 0 ≤ theta0 i :=
    (ProductSetLaw.theta_pos (fun _ : Fin p.K => (1 : ℝ)) i
      (ConstructorDimensions.m_pos p) p.m_lt_K (by intro a; norm_num)).le
  have hselectedLower :
      mass * (comparator - floor) ≤
        (∫ z in DZ,
          ∑ i ∈ S.1,
            ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
              rate rewards C_star C_h j t control0 z i ∂μZ) := by
    rw [hrawSelected]
    calc
      mass * (comparator - floor) =
          ∑ i ∈ S.1, mass * (rhoArm i - xiArm i / (rate.n : ℝ)) := by
        dsimp [comparator, floor]
        calc
          mass * ((∑ i ∈ S.1, rhoArm i) - (∑ i ∈ S.1, xiArm i / (rate.n : ℝ))) =
              mass * ∑ i ∈ S.1, rhoArm i - mass * ∑ i ∈ S.1, xiArm i / (rate.n : ℝ) := by
                rw [mul_sub]
          _ = (∑ i ∈ S.1, mass * rhoArm i) -
              (∑ i ∈ S.1, mass * (xiArm i / (rate.n : ℝ))) := by
                rw [Finset.mul_sum, Finset.mul_sum]
          _ = ∑ i ∈ S.1, (mass * rhoArm i - mass * (xiArm i / (rate.n : ℝ))) := by
                rw [← Finset.sum_sub_distrib]
          _ = ∑ i ∈ S.1, mass * (rhoArm i - xiArm i / (rate.n : ℝ)) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
      _ ≤ ∑ i ∈ S.1, mass * (xiArm i * valueArm i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hcoeff i).1 hmassNonneg
      _ = ∑ i ∈ S.1, mass * (xiArm i * valueArm i) := rfl
  have hobserverUpper :
      (∫ z in DZ,
        ∑ i : Fin p.K, theta0 i *
          ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
            rate rewards C_star C_h j t control0 z i ∂μZ) ≤
        mass * observer := by
    rw [hrawObserver]
    calc
      ∑ i : Fin p.K, theta0 i * (mass * (xiArm i * valueArm i)) ≤
          ∑ i : Fin p.K, theta0 i * (mass * rhoArm i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hcoeff i).2 hmassNonneg) (hthetaNonneg i)
      _ = mass * observer := by
        dsimp [observer]
        calc
          ∑ i : Fin p.K, theta0 i * (mass * rhoArm i) =
              ∑ i : Fin p.K, mass * (theta0 i * rhoArm i) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
          _ = mass * ∑ i : Fin p.K, theta0 i * rhoArm i := by
                rw [← Finset.mul_sum]
  have hR :
      (∫ z in D ∩ sourceStratumEvent rate rewards C_star C_h t j,
        firstRoundedRewardGap rate rewards C_star C_h S t z ∂μ) =
        μZ.real DZ * gap := by
    rw [idStratum_integral_eq rate rewards C_star C_h control0 ids t j _]
    have hconst :
        (fun z : Z => firstRoundedRewardGap rate rewards C_star C_h S t z.val) =
          fun _ => gap := by
      funext z
      exact firstRoundedRewardGap_on_stratum
        rate rewards C_star C_h control0 S t j z
    rw [hconst]
    change (∫ _ : Z, gap ∂(μZ.restrict DZ)) = μZ.real DZ * gap
    rw [integral_const]
    simp [smul_eq_mul, Measure.real]
  have hG :
      (∫ z in D ∩ sourceStratumEvent rate rewards C_star C_h t j,
        firstRawComparatorGap rate rewards C_star C_h S t z ∂μ) =
        (∫ z in DZ,
          ∑ i ∈ S.1,
            ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
              rate rewards C_star C_h j t control0 z i ∂μZ) -
        (∫ z in DZ,
          ∑ i : Fin p.K, theta0 i *
            ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
              rate rewards C_star C_h j t control0 z i ∂μZ) := by
    rw [idStratum_integral_eq rate rewards C_star C_h control0 ids t j _]
    calc
      _ = ∫ z in DZ,
          (∑ i ∈ S.1,
            ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
              rate rewards C_star C_h j t control0 z i) -
          ∑ i : Fin p.K, theta0 i *
            ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
              rate rewards C_star C_h j t control0 z i ∂μZ := by
        apply setIntegral_congr_fun hDZ
        intro z hz
        exact firstRawComparatorGap_on_stratum
          rate rewards C_star C_h control0 S t j z
      _ = _ := integral_sub hselectedInt.integrableOn hobserverInt.integrableOn
  have hF :
      (∫ z in D ∩ sourceStratumEvent rate rewards C_star C_h t j,
        firstServiceFloor rate rewards C_star C_h S t z ∂μ) =
        μZ.real DZ * floor := by
    rw [idStratum_integral_eq rate rewards C_star C_h control0 ids t j _]
    have hconst :
        (fun z : Z => firstServiceFloor rate rewards C_star C_h S t z.val) =
          fun _ => floor := by
      funext z
      exact firstServiceFloor_on_stratum
        rate rewards C_star C_h control0 S t j z
    rw [hconst]
    change (∫ _ : Z, floor ∂(μZ.restrict DZ)) = μZ.real DZ * floor
    rw [integral_const]
    simp [smul_eq_mul, Measure.real]
  calc
    _ = μZ.real DZ * gap := hR
    _ = μZ.real DZ * (comparator - observer) := by rfl
    _ ≤ (∫ z in DZ,
          ∑ i ∈ S.1,
            ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
              rate rewards C_star C_h j t control0 z i ∂μZ) -
        (∫ z in DZ,
          ∑ i : Fin p.K, theta0 i *
            ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
              rate rewards C_star C_h j t control0 z i ∂μZ) +
        μZ.real DZ * floor := by
      rw [hMassReal]
      linarith [hselectedLower, hobserverUpper]
    _ = _ := by rw [← hG, ← hF]

include control0 in
private theorem firstID_integral_eq_sum
    (t : Fin p.T) (f : X → ℝ)
    (hf : IntegrableOn f (D ∩ B t) μ) :
    (∫ z in D ∩ B t, f z ∂μ) =
      ∑ j : Fin (M p),
        ∫ z in D ∩ sourceStratumEvent rate rewards C_star C_h t j,
          f z ∂μ := by
  rw [firstID_domain_eq
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (ids := ids) (t := t)]
  exact integral_iUnion_fintype
    (firstID_piece_measurable rate rewards C_star C_h control0 ids t)
    (firstID_piece_disjoint rate rewards C_star C_h ids t)
    (fun j => hf.mono_set (by
      intro z hz
      refine ⟨hz.1, ?_⟩
      rw [firstSelector_eq_birthStrata
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (control0 := control0) (t := t)]
      exact Set.mem_iUnion.mpr ⟨j, hz.2⟩))

include control0 in
/-- The actual FIRST selector on every original fixed-ID section has the
ID-local square, weighted-arrival, and signed rounded/raw estimates. The
same literal full-prefix observers and actual first cell are used throughout.
-/
public theorem first_fixedID_source_transport (t : Fin p.T) :
    IntegrableOn
        (ReferenceOriginalCalendarLiveCollectionWeightedDrift.deltaV
          rate rewards C_star C_h t)
        (D ∩ B t) μ ∧
    IntegrableOn (firstWeightedArrival rate rewards C_star C_h t)
        (D ∩ B t) μ ∧
    IntegrableOn (firstRawComparatorGap rate rewards C_star C_h S t)
        (D ∩ B t) μ ∧
    IntegrableOn (firstRoundedRewardGap rate rewards C_star C_h S t)
        (D ∩ B t) μ ∧
    IntegrableOn (firstServiceFloor rate rewards C_star C_h S t)
        (D ∩ B t) μ ∧
    (∫ z in D ∩ B t,
      ReferenceOriginalCalendarLiveCollectionWeightedDrift.deltaV
        rate rewards C_star C_h t z ∂μ) ≤
      cBirth * (sourceInputLaw p).real (D ∩ B t) ∧
    (∫ z in D ∩ B t,
      firstWeightedArrival rate rewards C_star C_h t z ∂μ) ≤
      (p.m : ℝ) * (sourceInputLaw p).real (D ∩ B t) ∧
    (∫ z in D ∩ B t,
      firstRoundedRewardGap rate rewards C_star C_h S t z ∂μ) ≤
      (∫ z in D ∩ B t,
        firstRawComparatorGap rate rewards C_star C_h S t z ∂μ) +
      (∫ z in D ∩ B t,
        firstServiceFloor rate rewards C_star C_h S t z ∂μ) ∧
    ∀ z, z ∈ D ∩ B t →
      ReferenceOriginalCalendarLiveCollectionWeightedDrift.C
        rate rewards C_star C_h t.val z = 0 := by
  have hdelta : Integrable
      (ReferenceOriginalCalendarLiveCollectionWeightedDrift.deltaV
        rate rewards C_star C_h t) μ := by
    change Integrable
      (ReferenceOriginalCalendarLiveCollectionWeightedDrift.V rate rewards C_star C_h
        (t.val + 1) -
        ReferenceOriginalCalendarLiveCollectionWeightedDrift.V rate rewards C_star C_h
          t.val) μ
    exact (ReferenceOriginalCalendarLiveCollectionWeightedDrift.V_integrable
        rate rewards C_star C_h (t.val + 1)).sub
      (ReferenceOriginalCalendarLiveCollectionWeightedDrift.V_integrable
        rate rewards C_star C_h t.val)
  have hArrival : Integrable
      (firstWeightedArrival rate rewards C_star C_h t) μ :=
    firstWeightedArrival_integrable
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0) (t := t)
  have hRaw : IntegrableOn
      (firstRawComparatorGap rate rewards C_star C_h S t) (D ∩ B t) μ :=
    firstRawComparatorGap_integrableOn
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0) (ids := ids) (S := S) (t := t)
  have hRound : IntegrableOn
      (firstRoundedRewardGap rate rewards C_star C_h S t) (D ∩ B t) μ :=
    firstRoundedRewardGap_integrableOn
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0) (ids := ids) (S := S) (t := t)
  have hFloor : IntegrableOn
      (firstServiceFloor rate rewards C_star C_h S t) (D ∩ B t) μ :=
    firstServiceFloor_integrableOn
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0) (ids := ids) (S := S) (t := t)
  have hdeltaOn : IntegrableOn
      (ReferenceOriginalCalendarLiveCollectionWeightedDrift.deltaV
        rate rewards C_star C_h t) (D ∩ B t) μ := hdelta.integrableOn
  have hArrivalOn : IntegrableOn
      (firstWeightedArrival rate rewards C_star C_h t) (D ∩ B t) μ := hArrival.integrableOn
  have hSquare :
      (∫ z in D ∩ B t,
        ReferenceOriginalCalendarLiveCollectionWeightedDrift.deltaV
          rate rewards C_star C_h t z ∂μ) ≤ cBirth * (sourceInputLaw p).real (D ∩ B t) := by
    rw [firstID_integral_eq_sum
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0) (ids := ids) t _ hdeltaOn]
    calc
      _ ≤ ∑ j : Fin (M p),
          cBirth * (sourceInputLaw p).real (D ∩ sourceStratumEvent rate rewards C_star C_h t j) :=
        Finset.sum_le_sum (fun j _ =>
          first_square_stratum_budget rate rewards C_star C_h control0 ids t j)
      _ = cBirth * (sourceInputLaw p).real (D ∩ B t) := by
        rw [← Finset.mul_sum,
          firstID_mass_eq_sum
            (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
            (control0 := control0) (ids := ids) (t := t)]
  have hArrivalBound :
      (∫ z in D ∩ B t,
        firstWeightedArrival rate rewards C_star C_h t z ∂μ) ≤
          (p.m : ℝ) * (sourceInputLaw p).real (D ∩ B t) := by
    rw [firstID_integral_eq_sum
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0) (ids := ids) t _ hArrivalOn]
    calc
      _ ≤ ∑ j : Fin (M p),
          (p.m : ℝ) * (sourceInputLaw p).real (D ∩ sourceStratumEvent rate rewards C_star C_h t j) :=
        Finset.sum_le_sum (fun j _ =>
          first_arrival_stratum_budget rate rewards C_star C_h control0 ids t j)
      _ = (p.m : ℝ) * (sourceInputLaw p).real (D ∩ B t) := by
        rw [← Finset.mul_sum,
          firstID_mass_eq_sum
            (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
            (control0 := control0) (ids := ids) (t := t)]
  have hSigned :
      (∫ z in D ∩ B t,
        firstRoundedRewardGap rate rewards C_star C_h S t z ∂μ) ≤
      (∫ z in D ∩ B t,
        firstRawComparatorGap rate rewards C_star C_h S t z ∂μ) +
      (∫ z in D ∩ B t,
        firstServiceFloor rate rewards C_star C_h S t z ∂μ) := by
    rw [firstID_integral_eq_sum
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (control0 := control0) (ids := ids) t _ hRound,
      firstID_integral_eq_sum
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (control0 := control0) (ids := ids) t _ hRaw,
      firstID_integral_eq_sum
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (control0 := control0) (ids := ids) t _ hFloor]
    calc
      _ ≤ ∑ j : Fin (M p),
          ((∫ z in D ∩ sourceStratumEvent rate rewards C_star C_h t j,
              firstRawComparatorGap rate rewards C_star C_h S t z ∂μ) +
            ∫ z in D ∩ sourceStratumEvent rate rewards C_star C_h t j,
              firstServiceFloor rate rewards C_star C_h S t z ∂μ) :=
        Finset.sum_le_sum (fun j _ =>
          first_signed_stratum_estimate rate rewards C_star C_h control0 ids S t j)
      _ = _ := Finset.sum_add_distrib
  have hC (z : X) (hz : z ∈ D ∩ B t) :=
    incomingEnergy_zero_on_firstSelector
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0) (t := t) z hz.2
  exact ⟨hdeltaOn, hArrivalOn, hRaw, hRound, hFloor,
    hSquare, hArrivalBound, hSigned, hC⟩

end Bandits.Support.ReferenceOriginalCalendarFirstFixedIDLearningTransport

end
