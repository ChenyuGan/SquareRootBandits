/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionOriginalPrefixLearning
public import Bandits.Support.ReferenceFirstCollectionPrecallFixedIDMean

import Mathlib.Tactic

/-!
# Fixed-ID first-invocation weighted-arrival budget

The estimates in this module are integrated on the original source-input law
over the literal fixed-ID cylinder. The continuous complete rows, original
private arrays, and original source coordinates remain unchanged.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionFixedIDWeightedArrivalBudget

open ConstructorDimensions (Parameters)
open ReferenceActivePhysicalStep (RateInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)

variable {p : Parameters}
  (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (control0 : TimeControl p)
  (ids : CompletePublicTable.IDArray p)

local notation "S" => SourceInput p
local notation "μ" => sourceInputLaw p
local notation "Dset" => ReferenceFixedIDSourceSection.fixedIDSourceSection ids

local instance sourceInputMeasurableSpace : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local notation "phase" => ReferenceFirstLiveSourcePhasePartition.sourcePhase
  rate rewards C_star C_h
local notation "P234" t:max =>
  phase t 2 ∪ phase t 3 ∪ phase t 4
local notation "oldGate" t:max =>
  ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h t
local notation "currentGate" u:max t:max =>
  ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t

include control0

/-- At one date, all actual first-live, OLD, and first-call gate masses inside
the same ID cylinder fit that cylinder's original unnormalized mass. -/
public theorem fixedID_local_gate_mass_le (t : Fin p.T) :
    (μ).real (Dset ∩ P234 t) + (μ).real (Dset ∩ oldGate t) +
      ∑ u : Fin p.T, (μ).real (Dset ∩ currentGate u t) ≤ (μ).real Dset := by
  let P := P234 t
  let O := oldGate t
  let Q := fun u : Fin p.T => currentGate u t
  have hD : MeasurableSet Dset :=
    ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids
  have hprob : IsProbabilityMeasure μ :=
    BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  have hmuFinite : IsFiniteMeasure μ := ⟨by
    rw [hprob.measure_univ]
    exact ENNReal.one_lt_top⟩
  let := hmuFinite
  have hP : MeasurableSet P :=
    ReferenceFirstCollectionPrecallLiveOldMass.measurableSet_sourcePhase234
      rate rewards C_star C_h t control0
  have hO : MeasurableSet O :=
    ReferenceFirstCollectionPrecallLiveOldMass.measurableSet_G_ambient
      rate rewards C_star C_h t control0
  have hQ : ∀ u : Fin p.T, MeasurableSet (Q u) := by
    intro u
    exact ReferenceFirstCollectionPrecallFirstCallMassBudget.measurableSet_currentRetainedGate_ambient
      rate rewards C_star C_h t control0 u
  have hPO : Disjoint (Dset ∩ P) (Dset ∩ O) := by
    apply Set.disjoint_left.mpr
    intro z hzP hzO
    have hzE : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.E
        rate rewards C_star C_h t := hzO.2.1.1
    exact (Set.disjoint_left.mp
      (ReferenceFirstCollectionPrecallLiveOldMass.old_event_disjoint_source_phases
        rate rewards C_star C_h t control0)) hzE hzP.2
  have hPQ : Disjoint (Dset ∩ P) (Dset ∩ ⋃ u : Fin p.T, Q u) := by
    apply Set.disjoint_left.mpr
    intro z hzP hzQ
    obtain ⟨u, hzu⟩ := Set.mem_iUnion.mp hzQ.2
    exact (Set.disjoint_left.mp
      (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourcePhase234_disjoint_currentRetainedGateUnion
        rate rewards C_star C_h t control0)) hzP.2 hzQ.2
  have hOQ : Disjoint (Dset ∩ O) (Dset ∩ ⋃ u : Fin p.T, Q u) := by
    apply Set.disjoint_left.mpr
    intro z hzO hzQ
    obtain ⟨u, hzu⟩ := Set.mem_iUnion.mp hzQ.2
    exact (Set.disjoint_left.mp
      (ReferenceFirstCollectionPrecallFirstCallMassBudget.oldG_disjoint_currentRetainedGateUnion
        rate rewards C_star C_h t)) hzO.2 hzQ.2
  have hcurrentSet : (⋃ u : Fin p.T, Dset ∩ Q u) =
      Dset ∩ ⋃ u : Fin p.T, Q u := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨u, hzD, hzQ⟩
      exact ⟨hzD, u, hzQ⟩
    · rintro ⟨hzD, u, hzQ⟩
      exact ⟨u, hzD, hzQ⟩
  have hcurrent :
      ∑ u : Fin p.T, (μ).real (Dset ∩ Q u) = (μ).real (Dset ∩ ⋃ u : Fin p.T, Q u) := by
    calc
      _ = (μ).real (⋃ u : Fin p.T, Dset ∩ Q u) :=
        (measureReal_iUnion_fintype
          (fun u v huv => by
            apply Set.disjoint_left.mpr
            intro z hzu hzv
            exact (Set.disjoint_left.mp
              (ReferenceFirstCollectionPrecallFirstCallMassBudget.currentRetainedGate_pairwise_disjoint
                rate rewards C_star C_h t huv)) hzu.2 hzv.2)
          (fun u => hD.inter (hQ u))
          (fun u => by
            apply ne_of_lt
            calc
              μ (Dset ∩ Q u) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
              _ = 1 := hprob.measure_univ
              _ < ⊤ := ENNReal.one_lt_top)).symm
      _ = (μ).real (Dset ∩ ⋃ u : Fin p.T, Q u) :=
        congrArg (fun E : Set S => (μ).real E) hcurrentSet
  have hfirst :
      (μ).real (Dset ∩ P) + (μ).real (Dset ∩ O) =
        (μ).real ((Dset ∩ P) ∪ (Dset ∩ O)) := by
    rw [measureReal_union hPO (hD.inter hO)]
  have hlast : Disjoint ((Dset ∩ P) ∪ (Dset ∩ O))
      (Dset ∩ ⋃ u : Fin p.T, Q u) := by
    apply Set.disjoint_left.mpr
    intro z hz hzQ
    rcases hz with hzP | hzO
    · exact (Set.disjoint_left.mp hPQ) hzP hzQ
    · exact (Set.disjoint_left.mp hOQ) hzO hzQ
  have hmass :
      (μ).real ((Dset ∩ P) ∪ (Dset ∩ O)) +
        (μ).real (Dset ∩ ⋃ u : Fin p.T, Q u) =
          (μ).real (((Dset ∩ P) ∪ (Dset ∩ O)) ∪
            (Dset ∩ ⋃ u : Fin p.T, Q u)) :=
    (measureReal_union hlast (hD.inter (MeasurableSet.iUnion hQ))).symm
  calc
    _ = (μ).real (((Dset ∩ P) ∪ (Dset ∩ O)) ∪
        (Dset ∩ ⋃ u : Fin p.T, Q u)) := by
      rw [hfirst, hcurrent, hmass]
    _ ≤ (μ).real Dset := measureReal_mono (by
      rintro z (hz | hz)
      · rcases hz with hz | hz
        · exact hz.1
        · exact hz.1
      · exact hz.1)

omit control0 in
/-- The fixed-ID cylinder has exactly the mass of its literal original ID
atom, without imposing a good-ID or positive-mass premise. -/
public theorem fixedID_source_mass_eq_idAtom :
    (μ).real Dset = (CompletePublicTable.idArrayMeasure p).real {ids} :=
  ReferenceFixedIDSourceSection.sourceInputLaw_real_fixedIDSourceSection ids

/-- The original first-update first moment remains localized to the same ID
in each actual launch stratum. -/
public theorem fixedID_birth_stratum_weightedArrival_le
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) :
    (∫ z in {z : ReferenceTotalSourceDisintegration.SourceStratum
        rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t) |
        z.val.1.1 = ids},
      ∑ j : Fin p.K,
        ProductSetLaw.theta p.m (fun _ : Fin p.K => (1 : ℝ)) j *
          ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
            rate rewards C_star C_h q t control0 z j ∂
      ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)) ≤
      (p.m : ℝ) * (ReferenceTotalSourceDisintegration.sourceStratumMeasure
        rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)).real
        {z | z.val.1.1 = ids} := by
  let Z := ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
    (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
  let μB := ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
    (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
  let X := ReferenceFirstLaunchRecordingPhysicalMarker.RetainedStart
    rate rewards C_star C_h q t control0
  let μC := ReferenceRetainedSourceCoupling.retainedRemainderMeasure
    rate rewards C_star C_h q t t.val le_rfl control0
  let coords := ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
    rate rewards C_star C_h q t control0
  let Dq : Set Z := {z | z.val.1.1 = ids}
  let Aset : Set X := {x | x.val.1.1 = ids}
  have hA : MeasurableSet Aset := (measurableSet_singleton ids).preimage
    ((measurable_fst.comp measurable_fst).comp measurable_subtype_coe)
  have hmap := congrArg (fun ν => ν (Aset ×ˢ (Set.univ : Set
      (ReferenceFirstLaunchRecordingPhysicalMarker.AssignmentVector p ×
        ReferenceFirstLaunchRecordingPhysicalMarker.NonAssignmentControl p))))
    (ReferenceFirstLaunchRecordingSourceLaw.map_sourceCoordinates
      rate rewards C_star C_h q t control0)
  rw [Measure.map_apply
    (ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceCoordinates
      rate rewards C_star C_h q t control0) (hA.prod MeasurableSet.univ),
    Measure.prod_prod] at hmap
  have hdomMeasure : coords ⁻¹' (Aset ×ˢ (Set.univ : Set
      (ReferenceFirstLaunchRecordingSourceLaw.AssignmentVector p ×
        ReferenceFirstLaunchRecordingSourceLaw.NonAssignmentControl p))) = Dq := by
    ext z
    have hcoord := ReferenceFirstLiveRetainedIDExponentialStep.sourceCoordinates_originalID
      rate rewards C_star C_h q t control0 z
    change (coords z).1.val.1.1 = z.val.1.1 at hcoord
    change (((coords z).1.val.1.1 = ids) ∧ (coords z).2 ∈ Set.univ) ↔
      z.val.1.1 = ids
    simp [hcoord]
  rw [hdomMeasure] at hmap
  have hMass : μB Dq = μC Aset := by
    simpa only [measure_univ, mul_one] using hmap
  have hMoment (j : Fin p.K) :
      (∫ z in Dq,
        ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
          rate rewards C_star C_h q t control0 z j ∂μB) =
      (μC).real Aset *
        CanonicalRecordingRates.xi p rate.eta.val (fun _ => (1 : ℝ)) j *
        QuantizedRecordingMoments.quantizedValue (ConstructorDimensions.D p)
          rate.eta.val
          (CanonicalRecordingRates.xi p rate.eta.val (fun _ => (1 : ℝ)) j)
          (((rewards t j).val : ℝ) / (ConstructorDimensions.D p : ℝ)) := by
    have hmom := ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
      rate rewards C_star C_h q t control0 j Aset Set.univ hA MeasurableSet.univ
    have hfirst := hmom.2.2.2.2.1
    have hdom' : {z : Z | (coords z).1 ∈ Aset ∧
        (coords z).2.1 ∈ (Set.univ : Set
          (ReferenceFirstLaunchRecordingSourceLaw.AssignmentVector p))} = Dq := by
      ext z
      have hcoord := ReferenceFirstLiveRetainedIDExponentialStep.sourceCoordinates_originalID
        rate rewards C_star C_h q t control0 z
      change (coords z).1.val.1.1 = z.val.1.1 at hcoord
      change (((coords z).1.val.1.1 = ids) ∧ (coords z).2.1 ∈ Set.univ) ↔
        z.val.1.1 = ids
      simp [hcoord]
    rw [hdom'] at hfirst
    simp only [measure_univ, ENNReal.toReal_one, mul_one] at hfirst
    simpa [Measure.real] using hfirst
  have hMassReal : (μB).real Dq = (μC).real Aset := by
    exact congrArg ENNReal.toReal hMass
  have hArm (j : Fin p.K) :
      (∫ z in Dq,
        ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
          rate rewards C_star C_h q t control0 z j ∂μB) ≤ (μB).real Dq := by
    rw [hMoment j, hMassReal]
    have hcoeff := (ReferenceFirstLaunchCommonUpdateSource.first_update_moment_coefficients_bounds
      rate rewards t j).2.1
    have hrho : ((rewards t j).val : ℝ) / (ConstructorDimensions.D p : ℝ) ≤ 1 := by
      apply (div_le_one (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))).2
      exact_mod_cast Nat.le_of_lt_succ (rewards t j).isLt
    have hcoeff' : CanonicalRecordingRates.xi p rate.eta.val
        (fun _ : Fin p.K => (1 : ℝ)) j *
          QuantizedRecordingMoments.quantizedValue (ConstructorDimensions.D p)
            rate.eta.val
            (CanonicalRecordingRates.xi p rate.eta.val (fun _ : Fin p.K => (1 : ℝ)) j)
            (((rewards t j).val : ℝ) / (ConstructorDimensions.D p : ℝ)) ≤ 1 :=
      hcoeff.trans hrho
    calc
      _ = (μC).real Aset *
          (CanonicalRecordingRates.xi p rate.eta.val (fun _ : Fin p.K => (1 : ℝ)) j *
            QuantizedRecordingMoments.quantizedValue (ConstructorDimensions.D p)
              rate.eta.val
              (CanonicalRecordingRates.xi p rate.eta.val (fun _ : Fin p.K => (1 : ℝ)) j)
              (((rewards t j).val : ℝ) / (ConstructorDimensions.D p : ℝ))) := by ring
      _ ≤ (μC).real Aset := mul_le_of_le_one_right measureReal_nonneg hcoeff'
  have htheta (j : Fin p.K) :
      0 ≤ ProductSetLaw.theta p.m (fun _ : Fin p.K => (1 : ℝ)) j :=
    (ProductSetLaw.theta_pos (fun _ : Fin p.K => (1 : ℝ)) j
      (ConstructorDimensions.m_pos p) p.m_lt_K (by intro a; norm_num)).le
  have hInt (j : Fin p.K) : Integrable
      (fun z : Z => ProductSetLaw.theta p.m (fun _ : Fin p.K => (1 : ℝ)) j *
        ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
          rate rewards C_star C_h q t control0 z j) μB := by
    exact ((ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
      rate rewards C_star C_h q t control0 j Aset Set.univ hA MeasurableSet.univ).2.2.1
        ).const_mul _
  rw [integral_finsetSum Finset.univ (fun j _ => (hInt j).integrableOn)]
  calc
    _ ≤ ∑ j : Fin p.K,
        ProductSetLaw.theta p.m (fun _ : Fin p.K => (1 : ℝ)) j * (μB).real Dq := by
      apply Finset.sum_le_sum
      intro j hj
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hArm j) (htheta j)
    _ = (p.m : ℝ) * (μB).real Dq := by
      rw [← Finset.sum_mul, ProductSetLaw.sum_theta_eq_card
        (fun _ : Fin p.K => (1 : ℝ)) (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)
        ) p.m_lt_K (by intro a; norm_num)]

/-- The fixed-ID birth-stratum estimate is the actual calendar arrival, with
the original birth update and unnormalized stratum mass. -/
public theorem fixedID_birth_stratum_calendarWeightedArrival_le
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) :
    (∫ z in {z : ReferenceTotalSourceDisintegration.SourceStratum
        rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t) |
        z.val.1.1 = ids},
      ∑ j : Fin p.K,
        ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta
            rate rewards C_star C_h t j z.val *
          ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
            rate rewards C_star C_h t j z.val ∂
      ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)) ≤
      (p.m : ℝ) * (ReferenceTotalSourceDisintegration.sourceStratumMeasure
        rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)).real
        {z | z.val.1.1 = ids} := by
  simpa only [ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta_birth
      rate rewards C_star C_h q t,
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival_birth
      rate rewards C_star C_h q t control0] using
    fixedID_birth_stratum_weightedArrival_le rate rewards C_star C_h control0 ids q t

/-- The retained nonempty first-live branch has its actual ID-local first
moment bound on the original unnormalized branch measure. -/
public theorem fixedID_nonempty_stratum_weightedArrival_le
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) :
    (∫ z in {z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
        rate rewards C_star C_h q t s hs control0 |
        z.val.val.1.1 = ids},
      ∑ j : Fin p.K,
        ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore
            rate rewards C_star C_h q t s hs control0 j z *
          ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
            rate rewards C_star C_h q t s hs control0 j z ∂
      ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
        rate rewards C_star C_h q t s hs control0) ≤
      (p.m : ℝ) * (ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
        rate rewards C_star C_h q t s hs control0).real
        {z | z.val.val.1.1 = ids} := by
  let Z := ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
    rate rewards C_star C_h q t s hs control0
  let ν := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
    rate rewards C_star C_h q t s hs control0
  let G := ReferenceFirstLiveAllArmPrefixAdaptation.strictPastOverflowFalseSet
    rate rewards C_star C_h q t s hs control0
  let Dplus : Set Z := {z | z.val.val.1.1 = ids}
  let θ := ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore
    rate rewards C_star C_h q t s hs control0
  let A := ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
    rate rewards C_star C_h q t s hs control0
  let c := ReferenceFirstLiveAllArmPrefixAdaptation.firstCoefficientPlus
    rate rewards C_star C_h q t s hs control0
  let w (j : Fin p.K) : Z → ℝ := fun z => θ j z *
    Dplus.indicator (fun _ : Z => (1 : ℝ)) z
  have hFle : ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField
      rate rewards C_star C_h q t s hs control0 ≤
      (inferInstance : MeasurableSpace
        (ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
          rate rewards C_star C_h q t s hs control0)) :=
    ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
      rate rewards C_star C_h q t s hs control0
  let : IsFiniteMeasure ν :=
    ReferenceFirstLiveAllArmPrefixAdaptation.isFiniteMeasure_branchSourceMeasure
      rate rewards C_star C_h q t s hs control0
  let : IsFiniteMeasure ((ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
      rate rewards C_star C_h q t s hs control0).trim hFle) :=
    ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_trim_finite
      rate rewards C_star C_h q t s hs control0
  have hDfield : MeasurableSet[ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField
      rate rewards C_star C_h q t s hs control0] Dplus := by
    exact ReferenceFirstLiveRetainedIDExponentialStep.measurableSet_originalIDSet_nonempty
      rate rewards C_star C_h q t s hs control0 {ids} (measurableSet_singleton ids)
  have hD : MeasurableSet Dplus := hFle _ hDfield
  have hGfield : MeasurableSet[ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField
      rate rewards C_star C_h q t s hs control0] G :=
    ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet
      rate rewards C_star C_h q t s hs control0
  have hG : MeasurableSet G := hFle _ hGfield
  have hU : MeasurableSet (Dplus ∩ G) := hD.inter hG
  have hDind : Measurable[ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField
      rate rewards C_star C_h q t s hs control0]
      (Dplus.indicator (fun _ : Z => (1 : ℝ))) :=
    measurable_const.indicator hDfield
  have htheta (j : Fin p.K) (z : Z) : 0 ≤ θ j z ∧ θ j z ≤ 1 :=
    ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore_bounds
      rate rewards C_star C_h q t s hs control0 j z
  have hw (j : Fin p.K) : Measurable[ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField
      rate rewards C_star C_h q t s hs control0] (w j) := by
    exact (ReferenceFirstLiveQueueEnergyEnvelope.measurable_thetaBefore_field
      rate rewards C_star C_h q t s hs control0 j).mul hDind
  have hwBound (j : Fin p.K) (z : Z) : ‖w j z‖ ≤ 1 := by
    by_cases hz : z ∈ Dplus
    · simp [w, Set.indicator_of_mem hz, Real.norm_eq_abs,
        abs_of_nonneg (htheta j z).1, (htheta j z).2]
    · simp [w, Set.indicator_of_notMem hz]
  have hAint (j : Fin p.K) : Integrable (A j) ν :=
    ReferenceFirstLiveAllArmAcceptedConditionalMoments.integrable_acceptedA
      rate rewards C_star C_h q t s hs control0 j
  have hwAint (j : Fin p.K) : Integrable (fun z : Z => w j z * A j z) ν := by
    exact (hAint j).bdd_mul
      ((hw j).mono hFle le_rfl).aestronglyMeasurable
      (Filter.Eventually.of_forall (hwBound j))
  have hce (j : Fin p.K) :
      ν[(fun z : Z => w j z * A j z) |
        ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField
          rate rewards C_star C_h q t s hs control0] =ᵐ[ν]
        fun z => w j z * G.indicator (c j) z := by
    have hmul := condExp_mul_of_aestronglyMeasurable_left
      (hw j).aestronglyMeasurable (hwAint j) (hAint j)
    have hAcond := ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA_condExp_firstMoment
      rate rewards C_star C_h q t s hs control0 j
    filter_upwards [hmul, hAcond] with z hmul hz
    calc
      _ = (w j * ν[A j |
          ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField
            rate rewards C_star C_h q t s hs control0]) z := hmul
      _ = w j z * G.indicator (c j) z := by
        calc
          _ = w j z * ν[A j |
              ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField
                rate rewards C_star C_h q t s hs control0] z := rfl
          _ = _ := by rw [hz]
  have hcoeffInt (j : Fin p.K) : Integrable
      (fun z : Z => w j z * G.indicator (c j) z) ν := by
    have hceInt : Integrable
        (ν[(fun z : Z => w j z * A j z) |
          ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField
            rate rewards C_star C_h q t s hs control0]) ν := integrable_condExp
    exact hceInt.congr (hce j)
  have hIntEq (j : Fin p.K) :
      (∫ z : Z, w j z * A j z ∂ν) =
        ∫ z : Z, w j z * G.indicator (c j) z ∂ν := by
    calc
      _ = ∫ z : Z,
          ν[(fun z : Z => w j z * A j z) |
            ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField
              rate rewards C_star C_h q t s hs control0] z ∂ν :=
        (integral_condExp (f := fun z : Z => w j z * A j z) hFle).symm
      _ = _ := integral_congr_ae (hce j)
  have hsumInt : Integrable (fun z : Z => ∑ j : Fin p.K, w j z * A j z) ν :=
    integrable_finsetSum Finset.univ (fun j _ => hwAint j)
  have hcoeffSumInt : Integrable (fun z : Z =>
      ∑ j : Fin p.K, w j z * G.indicator (c j) z) ν :=
    integrable_finsetSum Finset.univ (fun j _ => hcoeffInt j)
  have hconst : Integrable (fun _ : Z => (p.m : ℝ)) ν := integrable_const _
  have hgateInt : Integrable ((Dplus ∩ G).indicator
      (fun _ : Z => (p.m : ℝ))) ν := hconst.indicator hU
  have hpoint (z : Z) :
      (∑ j : Fin p.K, w j z * G.indicator (c j) z) ≤
        (Dplus ∩ G).indicator (fun _ : Z => (p.m : ℝ)) z := by
    by_cases hzD : z ∈ Dplus
    · by_cases hzG : z ∈ G
      · rw [Set.indicator_of_mem (s := Dplus ∩ G) ⟨hzD, hzG⟩]
        simp only [w, Set.indicator_of_mem hzD, Set.indicator_of_mem hzG]
        have hsum := ReferenceFirstLiveQueueEnergyEnvelope.sum_thetaBefore_eq_m
          rate rewards C_star C_h q t s hs control0 z
        calc
          _ ≤ ∑ j : Fin p.K, θ j z * 1 := by
            apply Finset.sum_le_sum
            intro j hj
            have hc := ReferenceFirstLiveAllArmPrefixAdaptation.firstCoefficientPlus_bounds
              rate rewards C_star C_h q t s hs control0 j z
            simpa [c, mul_one] using
              mul_le_mul_of_nonneg_left (hc.2.2.1.trans hc.2.2.2)
                (htheta j z).1
          _ = (p.m : ℝ) := by simpa only [mul_one] using hsum
      · rw [Set.indicator_of_notMem (s := Dplus ∩ G) (by intro h; exact hzG h.2)]
        simp [w, Set.indicator_of_mem hzD, Set.indicator_of_notMem hzG]
    · rw [Set.indicator_of_notMem (s := Dplus ∩ G) (by intro h; exact hzD h.1)]
      simp [w, Set.indicator_of_notMem hzD]
  have hlocalized :
      (∫ z in Dplus, ∑ j : Fin p.K, θ j z * A j z ∂ν) ≤
        (p.m : ℝ) * ν.real (Dplus ∩ G) := by
    have hconvert :
        (∫ z in Dplus, ∑ j : Fin p.K, θ j z * A j z ∂ν) =
          ∫ z : Z, ∑ j : Fin p.K, w j z * A j z ∂ν := by
      calc
        _ = ∫ z : Z, Dplus.indicator
            (fun z => ∑ j : Fin p.K, θ j z * A j z) z ∂ν :=
          (integral_indicator hD).symm
        _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun z => by
          by_cases hz : z ∈ Dplus
          · simp [w, Set.indicator_of_mem hz]
          · simp [w, Set.indicator_of_notMem hz])
    calc
      _ = ∫ z : Z, ∑ j : Fin p.K, w j z * A j z ∂ν := hconvert
      _ = ∫ z : Z, ∑ j : Fin p.K, w j z * G.indicator (c j) z ∂ν := by
        rw [integral_finsetSum Finset.univ (fun j _ => hwAint j),
          integral_finsetSum Finset.univ (fun j _ => hcoeffInt j)]
        exact Finset.sum_congr rfl fun j _ => hIntEq j
      _ ≤ ∫ z : Z, (Dplus ∩ G).indicator
          (fun _ : Z => (p.m : ℝ)) z ∂ν := integral_mono hcoeffSumInt hgateInt hpoint
      _ = (p.m : ℝ) * ν.real (Dplus ∩ G) := by
        rw [integral_indicator_const (p.m : ℝ) hU]
        simp only [smul_eq_mul, mul_comm]
  calc
    _ ≤ (p.m : ℝ) * ν.real Dplus :=
      hlocalized.trans (mul_le_mul_of_nonneg_left
        (measureReal_mono Set.inter_subset_left) (Nat.cast_nonneg p.m))
    _ = _ := by rfl

/-- The fixed-ID nonempty-carrier estimate transports to the actual original
calendar readout on that same branch carrier. -/
public theorem fixedID_nonempty_stratum_calendarWeightedArrival_le
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) :
    (∫ z in {z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
        rate rewards C_star C_h q t s hs control0 |
        z.val.val.1.1 = ids},
      ∑ j : Fin p.K,
        ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta
            rate rewards C_star C_h t j z.val.val *
          ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
            rate rewards C_star C_h t j z.val.val ∂
      ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
        rate rewards C_star C_h q t s hs control0) ≤
      (p.m : ℝ) * (ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
        rate rewards C_star C_h q t s hs control0).real
        {z | z.val.val.1.1 = ids} := by
  simpa only [ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta_nonempty
      rate rewards C_star C_h q t s hs control0,
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival_nonempty
      rate rewards C_star C_h q t s hs control0] using
    fixedID_nonempty_stratum_weightedArrival_le rate rewards C_star C_h control0 ids q t s hs

/-- The retained empty-pending first-live branch has its actual ID-local
first moment bound on its original unnormalized source measure. -/
public theorem fixedID_empty_stratum_weightedArrival_le
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) :
    (∫ z in {z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
        rate rewards C_star C_h q t s hs control0 |
        z.val.val.1.1 = ids},
      ∑ j : Fin p.K,
        ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore
            rate rewards C_star C_h q t s hs control0 j z *
          ReferenceFirstLiveEmptyPendingAcceptedMoments.acceptedA
            rate rewards C_star C_h q t s hs control0 j z ∂
      ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
        rate rewards C_star C_h q t s hs control0) ≤
      (p.m : ℝ) * (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
        rate rewards C_star C_h q t s hs control0).real
        {z | z.val.val.1.1 = ids} := by
  let Z := ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
    rate rewards C_star C_h q t s hs control0
  let ν := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
    rate rewards C_star C_h q t s hs control0
  let G := ReferenceFirstLiveEmptyPendingAcceptedMoments.G
    rate rewards C_star C_h q t s hs control0
  let Dempty : Set Z := {z | z.val.val.1.1 = ids}
  let θ := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore
    rate rewards C_star C_h q t s hs control0
  let A := ReferenceFirstLiveEmptyPendingAcceptedMoments.acceptedA
    rate rewards C_star C_h q t s hs control0
  let c := ReferenceFirstLiveEmptyPendingAcceptedMoments.firstCoefficient
    rate rewards C_star C_h q t s hs control0
  let w (j : Fin p.K) : Z → ℝ := fun z => θ j z *
    Dempty.indicator (fun _ : Z => (1 : ℝ)) z
  have hFle : ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty
      rate rewards C_star C_h q t s hs control0 ≤
      (inferInstance : MeasurableSpace
        (ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
          rate rewards C_star C_h q t s hs control0)) :=
    ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
      rate rewards C_star C_h q t s hs control0
  let : IsFiniteMeasure ν :=
    ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty_finite
      rate rewards C_star C_h q t s hs control0
  let : IsFiniteMeasure (ν.trim hFle) := by infer_instance
  have hDfield : MeasurableSet[ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty
      rate rewards C_star C_h q t s hs control0] Dempty :=
    ReferenceFirstLiveRetainedIDExponentialStep.measurableSet_originalIDSet_empty
      rate rewards C_star C_h q t s hs control0 {ids} (measurableSet_singleton ids)
  have hD : MeasurableSet Dempty := hFle _ hDfield
  have hGfield : MeasurableSet[ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty
      rate rewards C_star C_h q t s hs control0] G :=
    ReferenceFirstLiveEmptyPendingAcceptedMoments.measurableSet_G
      rate rewards C_star C_h q t s hs control0
  have hG : MeasurableSet G := hFle _ hGfield
  have hU : MeasurableSet (Dempty ∩ G) := hD.inter hG
  have hDind : Measurable[ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty
      rate rewards C_star C_h q t s hs control0]
      (Dempty.indicator (fun _ : Z => (1 : ℝ))) := measurable_const.indicator hDfield
  have htheta (j : Fin p.K) (z : Z) : 0 ≤ θ j z ∧ θ j z ≤ 1 :=
    ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore_bounds
      rate rewards C_star C_h q t s hs control0 j z
  have hw (j : Fin p.K) : Measurable[ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty
      rate rewards C_star C_h q t s hs control0] (w j) := by
    exact (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.measurable_thetaBefore_field
      rate rewards C_star C_h q t s hs control0 j).mul hDind
  have hwBound (j : Fin p.K) (z : Z) : ‖w j z‖ ≤ 1 := by
    by_cases hz : z ∈ Dempty
    · simp [w, Set.indicator_of_mem hz, Real.norm_eq_abs,
        abs_of_nonneg (htheta j z).1, (htheta j z).2]
    · simp [w, Set.indicator_of_notMem hz]
  have hAint (j : Fin p.K) : Integrable (A j) ν :=
    ReferenceFirstLiveEmptyPendingAcceptedMoments.integrable_acceptedA
      rate rewards C_star C_h q t s hs control0 j
  have hwAint (j : Fin p.K) : Integrable (fun z : Z => w j z * A j z) ν := by
    exact (hAint j).bdd_mul
      ((hw j).mono hFle le_rfl).aestronglyMeasurable
      (Filter.Eventually.of_forall (hwBound j))
  have hce (j : Fin p.K) :
      ν[(fun z : Z => w j z * A j z) |
        ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty
          rate rewards C_star C_h q t s hs control0] =ᵐ[ν]
        fun z => w j z * G.indicator (c j) z := by
    have hmul := condExp_mul_of_aestronglyMeasurable_left
      (hw j).aestronglyMeasurable (hwAint j) (hAint j)
    have hAcond := ReferenceFirstLiveEmptyPendingAcceptedMoments.acceptedA_condExp_firstMoment
      rate rewards C_star C_h q t s hs control0 j
    filter_upwards [hmul, hAcond] with z hmul hz
    calc
      _ = (w j * ν[A j |
          ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty
            rate rewards C_star C_h q t s hs control0]) z := hmul
      _ = w j z * G.indicator (c j) z := by
        calc
          _ = w j z * ν[A j |
              ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty
                rate rewards C_star C_h q t s hs control0] z := rfl
          _ = _ := by
            change ν[A j |
              ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty
                rate rewards C_star C_h q t s hs control0] z =
              G.indicator (c j) z at hz
            rw [hz]
  have hcoeffInt (j : Fin p.K) : Integrable
      (fun z : Z => w j z * G.indicator (c j) z) ν := by
    have hceInt : Integrable
        (ν[(fun z : Z => w j z * A j z) |
          ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty
            rate rewards C_star C_h q t s hs control0]) ν := integrable_condExp
    exact hceInt.congr (hce j)
  have hIntEq (j : Fin p.K) :
      (∫ z : Z, w j z * A j z ∂ν) =
        ∫ z : Z, w j z * G.indicator (c j) z ∂ν := by
    calc
      _ = ∫ z : Z,
          ν[(fun z : Z => w j z * A j z) |
            ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty
              rate rewards C_star C_h q t s hs control0] z ∂ν :=
        (integral_condExp (f := fun z : Z => w j z * A j z) hFle).symm
      _ = _ := integral_congr_ae (hce j)
  have hsumInt : Integrable (fun z : Z => ∑ j : Fin p.K, w j z * A j z) ν :=
    integrable_finsetSum Finset.univ (fun j _ => hwAint j)
  have hcoeffIntSum : Integrable (fun z : Z =>
      ∑ j : Fin p.K, w j z * G.indicator (c j) z) ν :=
    integrable_finsetSum Finset.univ (fun j _ => hcoeffInt j)
  have hconst : Integrable (fun _ : Z => (p.m : ℝ)) ν := integrable_const _
  have hgateInt : Integrable ((Dempty ∩ G).indicator
      (fun _ : Z => (p.m : ℝ))) ν := hconst.indicator hU
  have hpoint (z : Z) :
      (∑ j : Fin p.K, w j z * G.indicator (c j) z) ≤
        (Dempty ∩ G).indicator (fun _ : Z => (p.m : ℝ)) z := by
    by_cases hzD : z ∈ Dempty
    · by_cases hzG : z ∈ G
      · rw [Set.indicator_of_mem (s := Dempty ∩ G) ⟨hzD, hzG⟩]
        simp only [w, Set.indicator_of_mem hzD, Set.indicator_of_mem hzG]
        have hsum := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.sum_thetaBefore_eq_m
          rate rewards C_star C_h q t s hs control0 z
        calc
          _ ≤ ∑ j : Fin p.K, θ j z * 1 := by
            apply Finset.sum_le_sum
            intro j hj
            have hc := ReferenceFirstLiveEmptyPendingAcceptedMoments.firstCoefficient_bounds
              rate rewards C_star C_h q t s hs control0 j z
            simpa [c, mul_one] using
              mul_le_mul_of_nonneg_left (hc.2.2.1.trans hc.2.2.2)
                (htheta j z).1
          _ = (p.m : ℝ) := by simpa only [mul_one] using hsum
      · rw [Set.indicator_of_notMem (s := Dempty ∩ G) (by intro h; exact hzG h.2)]
        simp [w, Set.indicator_of_mem hzD, Set.indicator_of_notMem hzG]
    · rw [Set.indicator_of_notMem (s := Dempty ∩ G) (by intro h; exact hzD h.1)]
      simp [w, Set.indicator_of_notMem hzD]
  have hlocalized :
      (∫ z in Dempty, ∑ j : Fin p.K, θ j z * A j z ∂ν) ≤
        (p.m : ℝ) * ν.real (Dempty ∩ G) := by
    have hconvert :
        (∫ z in Dempty, ∑ j : Fin p.K, θ j z * A j z ∂ν) =
          ∫ z : Z, ∑ j : Fin p.K, w j z * A j z ∂ν := by
      calc
        _ = ∫ z : Z, Dempty.indicator
            (fun z => ∑ j : Fin p.K, θ j z * A j z) z ∂ν :=
          (integral_indicator hD).symm
        _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun z => by
          by_cases hz : z ∈ Dempty
          · simp [w, Set.indicator_of_mem hz]
          · simp [w, Set.indicator_of_notMem hz])
    calc
      _ = ∫ z : Z, ∑ j : Fin p.K, w j z * A j z ∂ν := hconvert
      _ = ∫ z : Z, ∑ j : Fin p.K, w j z * G.indicator (c j) z ∂ν := by
        rw [integral_finsetSum Finset.univ (fun j _ => hwAint j),
          integral_finsetSum Finset.univ (fun j _ => hcoeffInt j)]
        exact Finset.sum_congr rfl fun j _ => hIntEq j
      _ ≤ ∫ z : Z, (Dempty ∩ G).indicator
          (fun _ : Z => (p.m : ℝ)) z ∂ν := integral_mono hcoeffIntSum hgateInt hpoint
      _ = (p.m : ℝ) * ν.real (Dempty ∩ G) := by
        rw [integral_indicator_const (p.m : ℝ) hU]
        simp only [smul_eq_mul, mul_comm]
  calc
    _ ≤ (p.m : ℝ) * ν.real Dempty :=
      hlocalized.trans (mul_le_mul_of_nonneg_left
        (measureReal_mono Set.inter_subset_left) (Nat.cast_nonneg p.m))
    _ = _ := by rfl

/-- The empty-pending carrier estimate is the actual original calendar
readout on that same carrier. -/
public theorem fixedID_empty_stratum_calendarWeightedArrival_le
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) :
    (∫ z in {z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
        rate rewards C_star C_h q t s hs control0 |
        z.val.val.1.1 = ids},
      ∑ j : Fin p.K,
        ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta
            rate rewards C_star C_h t j z.val.val *
          ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
            rate rewards C_star C_h t j z.val.val ∂
      ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
        rate rewards C_star C_h q t s hs control0) ≤
      (p.m : ℝ) * (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
        rate rewards C_star C_h q t s hs control0).real
        {z | z.val.val.1.1 = ids} := by
  simpa only [ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta_empty
      rate rewards C_star C_h q t s hs control0,
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival_empty
      rate rewards C_star C_h q t s hs control0] using
    fixedID_empty_stratum_weightedArrival_le rate rewards C_star C_h control0 ids q t s hs

/-- The OLD weighted arrivals obey their actual gate budget after integrating
over this fixed-ID cylinder under the original source law. -/
public theorem fixedID_oldCalendarWeightedArrival_setIntegral_le
    (t : Fin p.T) :
    (∫ z in Dset,
      ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldCalendarWeightedArrival
        rate rewards C_star C_h t z ∂μ) ≤
      (p.m : ℝ) * (μ).real (Dset ∩ oldGate t) := by
  have hFle : ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1) ≤ (inferInstance : MeasurableSpace S) :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (t.val + 1)
  have hDpre : MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)] Dset :=
    ReferenceFirstCollectionPrecallFixedIDMean.measurableSet_fixedIDSourceSection_prefix
      control0 ids t.val
  have hD : MeasurableSet[(inferInstance : MeasurableSpace S)] Dset :=
    ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids
  have hG : MeasurableSet[(inferInstance : MeasurableSpace S)] (oldGate t) :=
    ReferenceFirstCollectionPrecallLiveOldMass.measurableSet_G_ambient
      rate rewards C_star C_h t control0
  have hprodInt (i : Fin p.K) : Integrable (fun z : S =>
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i z *
      (oldGate t).indicator
        (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
          rate rewards C_star C_h t i) z) μ :=
    ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldWeightedArrival_integrable
      rate rewards C_star C_h control0 t i
  have hmomentInt (i : Fin p.K) : Integrable (fun z : S =>
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i z *
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
        rate rewards C_star C_h t i z) μ := by
    have hce := ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldWeightedArrival_condExp
      rate rewards C_star C_h control0 t i
    have hceInt : Integrable
        (μ[(fun z : S =>
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        (oldGate t).indicator
          (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
            rate rewards C_star C_h t i) z) |
          ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
            control0 (t.val + 1)]) μ := by
      exact integrable_condExp
        (f := fun z : S =>
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          (oldGate t).indicator
            (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
              rate rewards C_star C_h t i) z)
    exact hceInt.congr hce
  have hterm (i : Fin p.K) :
      (∫ z in Dset, ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        (oldGate t).indicator
          (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
            rate rewards C_star C_h t i) z ∂μ) =
        ∫ z in Dset,
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
            rate rewards C_star C_h t i z ∂μ := by
    have hce := ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldWeightedArrival_condExp
      rate rewards C_star C_h control0 t i
    have hceOnD : ∀ᵐ z ∂μ, z ∈ Dset →
        μ[(fun z : S =>
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          (oldGate t).indicator
            (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
            rate rewards C_star C_h t i) z) |
          ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
            control0 (t.val + 1)] z =
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
            rate rewards C_star C_h t i z :=
      hce.mono fun z hz _ => hz
    calc
      _ = ∫ z in Dset,
          μ[(fun z : S =>
            ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
              rate rewards C_star C_h t i z *
            (oldGate t).indicator
              (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
                rate rewards C_star C_h t i) z) |
              ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
                control0 (t.val + 1)] z ∂μ :=
        (setIntegral_condExp hFle (hprodInt i) hDpre).symm
      _ = _ := setIntegral_congr_ae hD hceOnD
  have hmomentSumInt : Integrable (fun z : S =>
      ∑ i : Fin p.K,
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
          rate rewards C_star C_h t i z) μ :=
    integrable_finsetSum Finset.univ (fun i _ => hmomentInt i)
  have hconst : Integrable (fun _ : S => (p.m : ℝ)) μ := integrable_const _
  have hgateInt : Integrable
      ((Dset ∩ oldGate t).indicator (fun _ : S => (p.m : ℝ))) μ :=
    hconst.indicator (hD.inter hG)
  have hpoint (z : S) :
      Set.indicator Dset (fun z : S =>
        ∑ i : Fin p.K,
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
            rate rewards C_star C_h t i z) z ≤
        (Dset ∩ oldGate t).indicator (fun _ : S => (p.m : ℝ)) z := by
    by_cases hzD : z ∈ Dset
    · rw [Set.indicator_of_mem hzD]
      by_cases hzG : z ∈ oldGate t
      · rw [Set.indicator_of_mem (s := Dset ∩ oldGate t) ⟨hzD, hzG⟩]
        have hzE : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.E
            rate rewards C_star C_h t := hzG.1.1
        have hsum :=
          ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldIncomingTheta_sum_on_E
            rate rewards C_star C_h t z hzE
        calc
          _ ≤ ∑ i : Fin p.K,
              ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
                rate rewards C_star C_h t i z * 1 := by
            apply Finset.sum_le_sum
            intro i hi
            have htheta :=
              (ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldIncomingTheta_predictable_bounds
                rate rewards C_star C_h control0 t i).2 z
            have hmoment :=
              (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_retainedRaw_sq_condExp
                rate rewards C_star C_h control0 t i).2.2.1 z
            have hmoment' :
                0 ≤ ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
                    rate rewards C_star C_h t i z ∧
                ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
                    rate rewards C_star C_h t i z ≤ 1 := by
              simpa [ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne,
                Set.indicator_of_mem hzG] using hmoment
            exact mul_le_mul_of_nonneg_left hmoment'.2 htheta.1
          _ = (p.m : ℝ) := by simpa only [mul_one] using hsum
      · have hzero (i : Fin p.K) :
            ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
              rate rewards C_star C_h t i z = 0 := by
          have hmoment' :
              0 ≤ ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
                  rate rewards C_star C_h t i z ∧
              ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
                  rate rewards C_star C_h t i z ≤ 0 := by
            simp [ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne,
              Set.indicator_of_notMem hzG]
          exact le_antisymm hmoment'.2 hmoment'.1
        rw [Set.indicator_of_notMem (s := Dset ∩ oldGate t)
          (by intro h; exact hzG h.2)]
        simp [hzero]
    · rw [Set.indicator_of_notMem hzD]
      simp [Set.indicator_of_notMem (s := Dset ∩ oldGate t)
        (by intro h; exact hzD h.1)]
  have htransport :
      (∫ z in Dset,
        ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldCalendarWeightedArrival
          rate rewards C_star C_h t z ∂μ) =
      ∫ z in Dset, ∑ i : Fin p.K,
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
          rate rewards C_star C_h t i z ∂μ := by
    unfold ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldCalendarWeightedArrival
    calc
      _ = ∑ i : Fin p.K, ∫ z in Dset,
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          (oldGate t).indicator
            (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
              rate rewards C_star C_h t i) z ∂μ :=
        integral_finsetSum Finset.univ (fun i _ => (hprodInt i).integrableOn)
      _ = ∑ i : Fin p.K, ∫ z in Dset,
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
            rate rewards C_star C_h t i z ∂μ :=
        Finset.sum_congr rfl fun i _ => hterm i
      _ = ∫ z in Dset, ∑ i : Fin p.K,
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
            rate rewards C_star C_h t i z ∂μ :=
        (integral_finsetSum Finset.univ (fun i _ => (hmomentInt i).integrableOn)).symm
  calc
    _ = ∫ z in Dset, ∑ i : Fin p.K,
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
          rate rewards C_star C_h t i z ∂μ := htransport
    _ = ∫ z : S, Set.indicator Dset (fun z : S =>
        ∑ i : Fin p.K,
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
            rate rewards C_star C_h t i z) z ∂μ := (integral_indicator hD).symm
    _ ≤ ∫ z : S, (Dset ∩ oldGate t).indicator
        (fun _ : S => (p.m : ℝ)) z ∂μ := integral_mono
          (hmomentSumInt.indicator hD) hgateInt hpoint
    _ = (p.m : ℝ) * (μ).real (Dset ∩ oldGate t) := by
      rw [integral_indicator_const (p.m : ℝ) (hD.inter hG), smul_eq_mul]
      ring

/-- One CURRENT invocation's weighted arrivals obey its actual first-call
gate budget after integration over the same original-source ID cylinder. -/
public theorem fixedID_currentCalendarWeightedArrival_setIntegral_le
    (u t : Fin p.T) :
    (∫ z in Dset,
      ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentCalendarWeightedArrival
        rate rewards C_star C_h u t z ∂μ) ≤
      (p.m : ℝ) * (μ).real (Dset ∩ currentGate u t) := by
  have hFle : ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1) ≤ (inferInstance : MeasurableSpace S) :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (t.val + 1)
  have hDpre : MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)] Dset :=
    ReferenceFirstCollectionPrecallFixedIDMean.measurableSet_fixedIDSourceSection_prefix
      control0 ids t.val
  have hD : MeasurableSet[(inferInstance : MeasurableSpace S)] Dset :=
    ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids
  have hG : MeasurableSet[(inferInstance : MeasurableSpace S)] (currentGate u t) :=
    ReferenceFirstCollectionPrecallFirstCallMassBudget.measurableSet_currentRetainedGate_ambient
      rate rewards C_star C_h t control0 u
  have hprodInt (i : Fin p.K) : Integrable (fun z : S =>
      ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
        rate rewards C_star C_h u t i z *
      ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
        rate rewards C_star C_h u t i z) μ :=
    ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentWeightedArrival_integrable
      rate rewards C_star C_h control0 u t i
  have hmomentInt (i : Fin p.K) : Integrable (fun z : S =>
      ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
        rate rewards C_star C_h u t i z *
      ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne
        rate rewards C_star C_h u t i z) μ := by
    have hce := ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentWeightedArrival_condExp
      rate rewards C_star C_h control0 u t i
    have hceInt : Integrable
        (μ[(fun z : S =>
        ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
          rate rewards C_star C_h u t i z *
        ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
          rate rewards C_star C_h u t i z) |
          ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
            control0 (t.val + 1)]) μ := by
      exact integrable_condExp
        (f := fun z : S =>
          ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
            rate rewards C_star C_h u t i z *
          ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
            rate rewards C_star C_h u t i z)
    exact hceInt.congr hce
  have hterm (i : Fin p.K) :
      (∫ z in Dset,
        ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
          rate rewards C_star C_h u t i z *
        ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
          rate rewards C_star C_h u t i z ∂μ) =
      ∫ z in Dset,
        ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
          rate rewards C_star C_h u t i z *
        ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne
          rate rewards C_star C_h u t i z ∂μ := by
    have hce := ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentWeightedArrival_condExp
      rate rewards C_star C_h control0 u t i
    have hceOnD : ∀ᵐ z ∂μ, z ∈ Dset →
        μ[(fun z : S =>
          ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
            rate rewards C_star C_h u t i z *
          ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
            rate rewards C_star C_h u t i z) |
          ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
            control0 (t.val + 1)] z =
          ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
            rate rewards C_star C_h u t i z *
          ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne
            rate rewards C_star C_h u t i z := hce.mono fun z hz _ => hz
    calc
      _ = ∫ z in Dset,
          μ[(fun z : S =>
            ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
              rate rewards C_star C_h u t i z *
            ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
              rate rewards C_star C_h u t i z) |
            ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
              control0 (t.val + 1)] z ∂μ :=
        (setIntegral_condExp hFle (hprodInt i) hDpre).symm
      _ = _ := setIntegral_congr_ae hD hceOnD
  have hmomentSumInt : Integrable (fun z : S =>
      ∑ i : Fin p.K,
        ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
          rate rewards C_star C_h u t i z *
        ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne
          rate rewards C_star C_h u t i z) μ :=
    integrable_finsetSum Finset.univ (fun i _ => hmomentInt i)
  have hconst : Integrable (fun _ : S => (p.m : ℝ)) μ := integrable_const _
  have hgateInt : Integrable
      ((Dset ∩ currentGate u t).indicator (fun _ : S => (p.m : ℝ))) μ :=
    hconst.indicator (hD.inter hG)
  have hpoint (z : S) :
      Set.indicator Dset (fun z : S =>
        ∑ i : Fin p.K,
          ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
            rate rewards C_star C_h u t i z *
          ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne
            rate rewards C_star C_h u t i z) z ≤
        (Dset ∩ currentGate u t).indicator (fun _ : S => (p.m : ℝ)) z := by
    by_cases hzD : z ∈ Dset
    · rw [Set.indicator_of_mem hzD]
      by_cases hzG : z ∈ currentGate u t
      · rw [Set.indicator_of_mem (s := Dset ∩ currentGate u t) ⟨hzD, hzG⟩]
        have hsum := ReferenceFirstCollectionCurrentQueueEnergy.sum_thetaMinus
          rate rewards C_star C_h u t z
        have hsum' :
            (∑ i : Fin p.K,
              ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
                rate rewards C_star C_h u t i z) = (p.m : ℝ) := by
          change (∑ i : Fin p.K,
            ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
              rate rewards C_star C_h u t i z) =
              (p.m : ℝ) *
                (ReferenceCalendarCollectionCallControlLaw.firstCell
                  rate rewards C_star C_h u t).indicator
                  (fun _ : S => (1 : ℝ)) z
              at hsum
          rw [Set.indicator_of_mem hzG.1] at hsum
          simpa using hsum
        calc
          _ ≤ ∑ i : Fin p.K,
              ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
                rate rewards C_star C_h u t i z * 1 := by
            apply Finset.sum_le_sum
            intro i hi
            obtain ⟨_, _, _, hnonneg, _, hleOne, _, _, _⟩ :=
              ReferenceFirstCollectionCurrentRetainedMoments.retainedMoment_bounds_on_G
                rate rewards C_star C_h u t i z hzG
            exact mul_le_mul_of_nonneg_left hleOne
              (ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus_bounds
                rate rewards C_star C_h u t i z).1
          _ = (p.m : ℝ) := by simpa only [mul_one] using hsum'
      · have hzero (i : Fin p.K) :
            ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne
              rate rewards C_star C_h u t i z = 0 :=
          ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne_eq_zero_of_not_mem_G
            rate rewards C_star C_h u t i z hzG
        rw [Set.indicator_of_notMem (by intro h; exact hzG h.2)]
        simp [hzero]
    · rw [Set.indicator_of_notMem hzD]
      simp [Set.indicator_of_notMem (s := Dset ∩ currentGate u t)
        (by intro h; exact hzD h.1)]
  have htransport :
      (∫ z in Dset,
        ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentCalendarWeightedArrival
          rate rewards C_star C_h u t z ∂μ) =
      ∫ z in Dset, ∑ i : Fin p.K,
        ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
          rate rewards C_star C_h u t i z *
        ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne
          rate rewards C_star C_h u t i z ∂μ := by
    unfold ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentCalendarWeightedArrival
    calc
      _ = ∑ i : Fin p.K, ∫ z in Dset,
          ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
            rate rewards C_star C_h u t i z *
          ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
            rate rewards C_star C_h u t i z ∂μ :=
        integral_finsetSum Finset.univ (fun i _ => (hprodInt i).integrableOn)
      _ = ∑ i : Fin p.K, ∫ z in Dset,
          ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
            rate rewards C_star C_h u t i z *
          ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne
            rate rewards C_star C_h u t i z ∂μ :=
        Finset.sum_congr rfl fun i _ => hterm i
      _ = ∫ z in Dset, ∑ i : Fin p.K,
          ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
            rate rewards C_star C_h u t i z *
          ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne
            rate rewards C_star C_h u t i z ∂μ :=
        (integral_finsetSum Finset.univ (fun i _ => (hmomentInt i).integrableOn)).symm
  calc
    _ = ∫ z in Dset, ∑ i : Fin p.K,
        ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
          rate rewards C_star C_h u t i z *
        ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne
          rate rewards C_star C_h u t i z ∂μ := htransport
    _ = ∫ z : S, Set.indicator Dset (fun z : S =>
        ∑ i : Fin p.K,
          ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
            rate rewards C_star C_h u t i z *
          ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne
            rate rewards C_star C_h u t i z) z ∂μ := (integral_indicator hD).symm
    _ ≤ ∫ z : S, (Dset ∩ currentGate u t).indicator
        (fun _ : S => (p.m : ℝ)) z ∂μ := integral_mono
          (hmomentSumInt.indicator hD) hgateInt hpoint
    _ = (p.m : ℝ) * (μ).real (Dset ∩ currentGate u t) := by
      rw [integral_indicator_const (p.m : ℝ) (hD.inter hG), smul_eq_mul]
      ring

/-- The combined actual OLD and CURRENT contributions retain their own
fixed-ID gate masses before the LIVE source phases are added. -/
public theorem fixedID_oldCurrentCalendarWeightedArrival_setIntegral_le
    (t : Fin p.T) :
    (∫ z in Dset,
      ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldCalendarWeightedArrival
          rate rewards C_star C_h t z +
        ∑ u : Fin p.T,
          ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentCalendarWeightedArrival
            rate rewards C_star C_h u t z ∂μ) ≤
      (p.m : ℝ) * ((μ).real (Dset ∩ oldGate t) +
        ∑ u : Fin p.T, (μ).real (Dset ∩ currentGate u t)) := by
  have hOld : Integrable
      (ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldCalendarWeightedArrival
        rate rewards C_star C_h t) μ :=
    ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldCalendarWeightedArrival_integrable
      rate rewards C_star C_h control0 t
  have hCurrent (u : Fin p.T) : Integrable
      (ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentCalendarWeightedArrival
        rate rewards C_star C_h u t) μ :=
    ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentCalendarWeightedArrival_integrable
      rate rewards C_star C_h control0 u t
  have hCurrentSum : Integrable (fun z : S =>
      ∑ u : Fin p.T,
        ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentCalendarWeightedArrival
          rate rewards C_star C_h u t z) μ :=
    integrable_finsetSum Finset.univ (fun u _ => hCurrent u)
  rw [integral_add hOld.integrableOn hCurrentSum.integrableOn,
    integral_finsetSum Finset.univ (fun u _ => (hCurrent u).integrableOn),
    mul_add, Finset.mul_sum]
  exact add_le_add
    (fixedID_oldCalendarWeightedArrival_setIntegral_le rate rewards C_star C_h control0 ids t)
    (Finset.sum_le_sum (fun u _ =>
      fixedID_currentCalendarWeightedArrival_setIntegral_le rate rewards C_star C_h control0 ids u t))

section LiveAssembly

variable (t : Fin p.T)

local notation "BirthZ" => fun q => ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
  (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
local notation "muB" => fun q => ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
  (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
local notation "PlusZ" => fun q (v : Fin (t.val + 1)) =>
  ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h q t (Fin.val v)
    (Nat.lt_succ_iff.mp (Fin.isLt v)) control0
local notation "muP" => fun q (v : Fin (t.val + 1)) =>
  ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t (Fin.val v)
    (Nat.lt_succ_iff.mp (Fin.isLt v)) control0
local notation "EmptyZ" => fun q (v : Fin (t.val + 1)) =>
  ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t (Fin.val v)
    (Nat.lt_succ_iff.mp (Fin.isLt v)) control0
local notation "muE" => fun q (v : Fin (t.val + 1)) =>
  ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t (Fin.val v)
    (Nat.lt_succ_iff.mp (Fin.isLt v)) control0

private theorem integral_original_components (f : S → ℝ) (hf : Integrable f μ)
    (hzero : ∀ z, z ∈ phase t 0 ∨ z ∈ phase t 1 ∨ z ∈ phase t 5 → f z = 0) :
    (∫ z, f z ∂μ) = (∑ q, ∫ z : BirthZ q, f z.val ∂muB q) +
      ∑ q, ∑ v : Fin (t.val + 1),
        ((∫ z : PlusZ q v, f z.val.val ∂muP q v) +
          ∫ z : EmptyZ q v, f z.val.val ∂muE q v) := by
  let embB q := MeasurableEmbedding.subtype_coe
    (ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
      rate rewards C_star C_h t control0 (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t))
  let embP q (v : Fin (t.val + 1)) :=
    ReferenceFirstLiveBranchIntegralTransport.measurableEmbedding_forgetBranch
      rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0
  let embE q (v : Fin (t.val + 1)) :=
    ReferenceFirstLiveSourcePhasePartition.measurableEmbedding_forgetEmpty
      rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0
  let b q := (muB q).map (Subtype.val : BirthZ q → S)
  let c q v := (muP q v).map
    (ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t
      v.val (Nat.lt_succ_iff.mp v.isLt) control0) +
    (muE q v).map (ReferenceFirstLiveSourcePhasePartition.forgetEmpty rate rewards C_star C_h q t
      v.val (Nat.lt_succ_iff.mp v.isLt) control0)
  have hdecomp : μ = (μ).restrict (phase t 0) + (μ).restrict (phase t 1) +
      (μ).restrict (phase t 5) + (∑ q, b q) + ∑ q, ∑ v, c q v :=
    ReferenceFirstLiveCalendarIntegralAssembly.original_source_measure_decomposition
      rate rewards C_star C_h t control0
  have hfi := hf
  rw [hdecomp] at hfi
  have hcss := hfi.right_of_add_measure
  have h015b := hfi.left_of_add_measure
  have hbs := h015b.right_of_add_measure
  have h015 := h015b.left_of_add_measure
  have h5 := h015.right_of_add_measure
  have h01 := h015.left_of_add_measure
  have h0 := h01.left_of_add_measure
  have h1 := h01.right_of_add_measure
  have hbi q := integrable_finsetSum_measure.mp hbs q (Finset.mem_univ q)
  have hcs q := integrable_finsetSum_measure.mp hcss q (Finset.mem_univ q)
  have hci q v := integrable_finsetSum_measure.mp (hcs q) v (Finset.mem_univ v)
  have hz (i : Fin 6) (hi : i = 0 ∨ i = 1 ∨ i = 5) :
      f =ᵐ[(μ).restrict (phase t i)] 0 := by
    filter_upwards [ae_restrict_mem
      (ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
        rate rewards C_star C_h t control0 i)] with z hz
    rcases hi with rfl | rfl | rfl
    · exact hzero z (Or.inl hz)
    · exact hzero z (Or.inr (Or.inl hz))
    · exact hzero z (Or.inr (Or.inr hz))
  rw [hdecomp, integral_add_measure h015b hcss, integral_add_measure h015 hbs,
    integral_add_measure h01 h5, integral_add_measure h0 h1,
    integral_congr_ae (hz 0 (by simp)), integral_congr_ae (hz 1 (by simp)),
    integral_congr_ae (hz 5 (by simp))]
  simp only [Pi.zero_apply, integral_zero, zero_add]
  rw [integral_finsetSum_measure (fun q _ => hbi q),
    integral_finsetSum_measure (fun q _ => hcs q)]
  congr 1
  · exact Finset.sum_congr rfl (fun q _ => (embB q).integral_map f)
  · apply Finset.sum_congr rfl
    intro q hq
    rw [integral_finsetSum_measure (fun v _ => hci q v)]
    apply Finset.sum_congr rfl
    intro v hv
    rw [integral_add_measure (hci q v).left_of_add_measure (hci q v).right_of_add_measure]
    exact congrArg₂ (· + ·) ((embP q v).integral_map f) ((embE q v).integral_map f)

omit control0 in
private theorem localized_cell_bound {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (φ : X → S) (hφ : Measurable φ)
    (hphase : ∀ x, φ x ∈ P234 t) (f : S → ℝ)
    (hbound : (∫ x in φ ⁻¹' Dset, f (φ x) ∂ν) ≤
      (p.m : ℝ) * ν.real (φ ⁻¹' Dset)) :
    (∫ x, (Dset).indicator f (φ x) ∂ν) ≤
      ∫ x, (Dset ∩ P234 t).indicator (fun _ : S => (p.m : ℝ)) (φ x) ∂ν := by
  have hD := (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage hφ
  have heq : (fun x => (Dset ∩ P234 t).indicator (fun _ : S => (p.m : ℝ)) (φ x)) =
      (φ ⁻¹' Dset).indicator (fun _ : X => (p.m : ℝ)) := by
    funext x
    simp only [Set.indicator, Set.mem_inter_iff, hphase x, and_true, Set.mem_preimage]
  rw [heq, integral_indicator_const (p.m : ℝ) hD]
  rw [show (fun x => (Dset).indicator f (φ x)) =
      (φ ⁻¹' Dset).indicator (fun x => f (φ x)) from rfl, integral_indicator hD]
  simpa only [smul_eq_mul, mul_comm] using hbound

/-- LIVE integration on the original source retains the mass of its actual
birth/nonempty/empty phases intersected with the literal ID cylinder. -/
public theorem fixedID_liveCalendarWeightedArrival_setIntegral_le :
    (∫ z in Dset,
      ReferenceFirstCollectionOriginalWeightedArrivalBudget.liveCalendarWeightedArrival
        rate rewards C_star C_h t z ∂μ) ≤ (p.m : ℝ) * (μ).real (Dset ∩ P234 t) := by
  let f := ReferenceFirstCollectionOriginalWeightedArrivalBudget.liveCalendarWeightedArrival
    rate rewards C_star C_h t
  let g := (Dset ∩ P234 t).indicator (fun _ : S => (p.m : ℝ))
  have hD := ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids
  have hP := ReferenceFirstCollectionPrecallLiveOldMass.measurableSet_sourcePhase234
    rate rewards C_star C_h t control0
  let : IsProbabilityMeasure μ := BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  have hf : Integrable ((Dset).indicator f) μ :=
    (ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarWeightedArrival_moments
      rate rewards C_star C_h t control0).1.indicator hD
  have hg : Integrable g μ := (integrable_const (p.m : ℝ)).indicator (hD.inter hP)
  have hz : ∀ z, z ∈ phase t 0 ∨ z ∈ phase t 1 ∨ z ∈ phase t 5 → f z = 0 := by
    intro z hz
    have hA (j : Fin p.K) :
        ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
          rate rewards C_star C_h t j z = 0 := by
      rcases hz with hz | hz | hz
      · have hnil := (ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
          rate rewards C_star C_h z hz).2.1
        simp only [ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival,
          ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells, hnil,
          List.getElem?_nil, ite_self]
      · exact ite_eq_right (Nat.not_le_of_lt hz.2)
      · have hlen := (ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveCells_length
          rate rewards C_star C_h z).trans_le hz.2.2
        change (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells
          rate rewards C_star C_h z).length ≤ t.val -
            ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart
              rate rewards C_star C_h z at hlen
        unfold ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
        rw [List.getElem?_eq_none hlen]
        simp only [ite_self]
    simp only [f, ReferenceFirstCollectionOriginalWeightedArrivalBudget.liveCalendarWeightedArrival,
      hA, mul_zero, Finset.sum_const_zero]
  have hgz : ∀ z, z ∈ phase t 0 ∨ z ∈ phase t 1 ∨ z ∈ phase t 5 → g z = 0 := by
    intro z hz
    apply Set.indicator_of_notMem
    intro hzP
    have hd := ReferenceFirstLiveSourcePhasePartition.source_phases_disjoint rate rewards C_star C_h t
    rcases hzP.2 with (h2 | h3) | h4 <;> rcases hz with h0 | h1 | h5
    all_goals first
      | exact Set.disjoint_left.mp (hd (by decide : (2 : Fin 6) ≠ 0)) h2 h0
      | exact Set.disjoint_left.mp (hd (by decide : (2 : Fin 6) ≠ 1)) h2 h1
      | exact Set.disjoint_left.mp (hd (by decide : (2 : Fin 6) ≠ 5)) h2 h5
      | exact Set.disjoint_left.mp (hd (by decide : (3 : Fin 6) ≠ 0)) h3 h0
      | exact Set.disjoint_left.mp (hd (by decide : (3 : Fin 6) ≠ 1)) h3 h1
      | exact Set.disjoint_left.mp (hd (by decide : (3 : Fin 6) ≠ 5)) h3 h5
      | exact Set.disjoint_left.mp (hd (by decide : (4 : Fin 6) ≠ 0)) h4 h0
      | exact Set.disjoint_left.mp (hd (by decide : (4 : Fin 6) ≠ 1)) h4 h1
      | exact Set.disjoint_left.mp (hd (by decide : (4 : Fin 6) ≠ 5)) h4 h5
  have hb q : ∀ z : BirthZ q, z.val ∈ P234 t := by
    intro z
    exact Or.inl (Or.inl ((ReferenceFirstLiveCalendarIntegralAssembly.sourcePhase_birth_iUnion
      rate rewards C_star C_h t).symm ▸ Set.mem_iUnion.mpr ⟨q, z.property⟩))
  have hp q v : ∀ z : PlusZ q v, z.val.val ∈ P234 t := by
    intro z
    apply Or.inl ∘ Or.inr
    rw [ReferenceFirstLiveCalendarIntegralAssembly.sourcePhase_nonempty_iUnion
      rate rewards C_star C_h t control0]
    exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨v, z.val, z.property, rfl⟩⟩
  have he q v : ∀ z : EmptyZ q v, z.val.val ∈ P234 t := by
    intro z
    apply Or.inr
    rw [ReferenceFirstLiveCalendarIntegralAssembly.sourcePhase_empty_iUnion
      rate rewards C_star C_h t control0]
    exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨v, z.val, z.property, rfl⟩⟩
  have hle : (∫ z, (Dset).indicator f z ∂μ) ≤ ∫ z, g z ∂μ := by
    rw [integral_original_components rate rewards C_star C_h control0 t _ hf
      (fun z hz' => by by_cases hzD : z ∈ Dset <;> simp [Set.indicator, hzD, hz z hz']),
      integral_original_components rate rewards C_star C_h control0 t _ hg hgz]
    apply add_le_add
    · apply Finset.sum_le_sum
      intro q hq
      exact localized_cell_bound rate rewards C_star C_h ids t (muB q)
        Subtype.val measurable_subtype_coe (hb q) f
        (fixedID_birth_stratum_calendarWeightedArrival_le rate rewards C_star C_h control0 ids q t)
    · apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro v hv
      apply add_le_add
      · exact localized_cell_bound rate rewards C_star C_h ids t (muP q v)
          (fun z => z.val.val) (measurable_subtype_coe.comp measurable_subtype_coe) (hp q v) f
          (fixedID_nonempty_stratum_calendarWeightedArrival_le rate rewards C_star C_h control0 ids
            q t v.val (Nat.lt_succ_iff.mp v.isLt))
      · exact localized_cell_bound rate rewards C_star C_h ids t (muE q v)
          (fun z => z.val.val) (measurable_subtype_coe.comp measurable_subtype_coe) (he q v) f
          (fixedID_empty_stratum_calendarWeightedArrival_le rate rewards C_star C_h control0 ids
            q t v.val (Nat.lt_succ_iff.mp v.isLt))
  rw [integral_indicator hD] at hle
  simpa only [g, integral_indicator_const (p.m : ℝ) (hD.inter hP), smul_eq_mul, mul_comm] using hle

end LiveAssembly

/-- At each date the LIVE, OLD, and CURRENT local masses are combined before
using the single fixed-ID mass budget. -/
public theorem fixedID_calendarWeightedArrival_setIntegral_le (t : Fin p.T) :
    (∫ z in Dset,
      ReferenceFirstCollectionOriginalWeightedArrivalBudget.calendarWeightedArrival
        rate rewards C_star C_h t z ∂μ) ≤
      (CompletePublicTable.idArrayMeasure p).real {ids} * (p.m : ℝ) := by
  have hLive := (ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarWeightedArrival_moments
    rate rewards C_star C_h t control0).1
  change Integrable
    (ReferenceFirstCollectionOriginalWeightedArrivalBudget.liveCalendarWeightedArrival
      rate rewards C_star C_h t) μ at hLive
  have hRest :=
    (ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldCalendarWeightedArrival_integrable
      rate rewards C_star C_h control0 t).add
    (integrable_finsetSum Finset.univ (fun u _ =>
      ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentCalendarWeightedArrival_integrable
        rate rewards C_star C_h control0 u t))
  change Integrable (fun z : S =>
    ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldCalendarWeightedArrival
      rate rewards C_star C_h t z + ∑ u : Fin p.T,
      ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentCalendarWeightedArrival
        rate rewards C_star C_h u t z) μ at hRest
  change (∫ z in Dset,
    ReferenceFirstCollectionOriginalWeightedArrivalBudget.liveCalendarWeightedArrival
      rate rewards C_star C_h t z +
      (ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldCalendarWeightedArrival
        rate rewards C_star C_h t z + ∑ u : Fin p.T,
        ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentCalendarWeightedArrival
          rate rewards C_star C_h u t z) ∂μ) ≤ _
  rw [integral_add hLive.integrableOn hRest.integrableOn]
  calc
    _ ≤ (p.m : ℝ) * (μ).real (Dset ∩ P234 t) +
        (p.m : ℝ) * ((μ).real (Dset ∩ oldGate t) +
          ∑ u : Fin p.T, (μ).real (Dset ∩ currentGate u t)) :=
      add_le_add (fixedID_liveCalendarWeightedArrival_setIntegral_le
        rate rewards C_star C_h control0 ids t)
        (fixedID_oldCurrentCalendarWeightedArrival_setIntegral_le
          rate rewards C_star C_h control0 ids t)
    _ = (p.m : ℝ) * ((μ).real (Dset ∩ P234 t) + (μ).real (Dset ∩ oldGate t) +
        ∑ u : Fin p.T, (μ).real (Dset ∩ currentGate u t)) := by ring
    _ ≤ (p.m : ℝ) * (μ).real Dset := mul_le_mul_of_nonneg_left
      (fixedID_local_gate_mass_le rate rewards C_star C_h control0 ids t) (Nat.cast_nonneg p.m)
    _ = _ := by rw [fixedID_source_mass_eq_idAtom ids]; ring

/-- Integrability on every literal fixed-ID cylinder follows from the actual
original-source first-invocation integrability, with no supplied moment premise. -/
public theorem firstInvocationWeightedArrival_integrableOn_fixedID :
    IntegrableOn
      (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
        rate rewards C_star C_h) Dset μ :=
  (ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationWeightedArrival_integrable
    rate rewards C_star C_h control0).integrableOn

/-- The actual first invocation's weighted arrivals have the atom-scaled budget
on each literal ID cylinder of the original source law, over the full horizon. -/
public theorem firstInvocationWeightedArrival_setIntegral_fixedID_le :
    (∫ z in Dset,
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
        rate rewards C_star C_h z ∂μ) ≤
      (CompletePublicTable.idArrayMeasure p).real {ids} * (p.m : ℝ) * (p.T : ℝ) := by
  let W := ReferenceFirstCollectionOriginalWeightedArrivalBudget.calendarWeightedArrival
    rate rewards C_star C_h
  let A : ℕ → S → ℝ := fun n z =>
    ∑ k ∈ Finset.range n, if hk : k < p.T then W ⟨k, hk⟩ z else 0
  have hA0 (z : S) : A 0 z = 0 := by simp only [A, Finset.range_zero, Finset.sum_empty]
  have hstep (t : Fin p.T) (z : S) : A (t.val + 1) z - A t.val z = W t z := by
    dsimp only [A]
    rw [Finset.sum_range_succ, dite_eq_left t.isLt]
    exact add_sub_cancel_left _ _
  have hAT (z : S) : A p.T z = ∑ t : Fin p.T, W t z := by
    have htel := Finset.sum_range_sub (fun n => A n z) p.T
    rw [← Fin.sum_univ_eq_sum_range] at htel
    simp_rw [hstep] at htel
    simpa only [hA0, sub_zero] using htel.symm
  calc
    _ = ∫ z in Dset, A p.T z ∂μ := by
      apply setIntegral_congr_fun (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids)
      intro z hz
      rw [hAT, ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationWeightedArrival_eq_calendar]
      rfl
    _ = ∑ t : Fin p.T, ∫ z in Dset,
        ReferenceFirstCollectionOriginalWeightedArrivalBudget.calendarWeightedArrival
          rate rewards C_star C_h t z ∂μ := by
      simp_rw [hAT]
      exact integral_finsetSum Finset.univ (fun t _ =>
        (ReferenceFirstCollectionOriginalWeightedArrivalBudget.calendarWeightedArrival_integrable
          rate rewards C_star C_h control0 t).integrableOn)
    _ ≤ ∑ _t : Fin p.T, (CompletePublicTable.idArrayMeasure p).real {ids} * (p.m : ℝ) :=
      Finset.sum_le_sum (fun t _ => fixedID_calendarWeightedArrival_setIntegral_le
        rate rewards C_star C_h control0 ids t)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end Bandits.Support.ReferenceFirstCollectionFixedIDWeightedArrivalBudget

end
