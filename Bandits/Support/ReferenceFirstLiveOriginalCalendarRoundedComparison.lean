/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveOriginalCalendarArrivalMoments
public import Bandits.Support.ReferenceFirstLiveRawPotentialBound

import Mathlib.Tactic

/-!
# Rounded comparison on the actual first-live calendar

The comparison retains the original source law, the actual current calendar
rates, the exact positive floor loss, and the same first-live cell list used by
the raw potential gap.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstLiveOriginalCalendarRoundedComparison

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ)

local notation "mu" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "Q" => ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveQueue rate
local notation "L" => ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells rate rewards C_star C_h
local notation "a" => ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart rate rewards C_star C_h
local notation "u" => ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveRunAt rate rewards C_star C_h
local notation "K" => ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent rate rewards C_star C_h
local notation "scale" => rate.eta.val * (ConstructorDimensions.D p : ℝ)

/-- The literal raw comparator gap on calendar round `t`. -/
def calendarRawGap (t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m)
    (omega : SourceInput p) : ℝ :=
  (∑ j ∈ S.val, ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
      rate rewards C_star C_h t j omega) -
    ∑ j : Fin p.K, ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta
      rate rewards C_star C_h t j omega *
        ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
          rate rewards C_star C_h t j omega

/-- The actual retained rounded comparator gap, zero off retained enabled cells. -/
def calendarRoundedGap (t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m)
    (omega : SourceInput p) : ℝ :=
  Set.indicator (K t) (fun omega =>
    (∑ j ∈ S.val, ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward
        rewards t j) -
      ∑ j : Fin p.K, ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta
        rate rewards C_star C_h t j omega *
          ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j) omega

/-- The exact positive floor-loss term on the same retained enabled cells. -/
def calendarFloorLoss (t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m)
    (omega : SourceInput p) : ℝ :=
  Set.indicator (K t) (fun omega =>
    ∑ j ∈ S.val, ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRate
      rate rewards C_star C_h t j omega / scale) omega

private theorem scale_pos : 0 < scale := by
  exact mul_pos rate.eta.property (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))

private theorem productSet_card (S : ProductSetLaw.ProductSet p.K p.m) : S.1.card = p.m := by
  exact (Finset.mem_powersetCard.mp S.2).2

theorem integrable_calendarRawGap (t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m)
    (control0 : TimeControl p) : Integrable (calendarRawGap rate rewards C_star C_h t S) mu := by
  change Integrable (fun omega : SourceInput p =>
    (∑ j ∈ S.val,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
        rate rewards C_star C_h t j omega) -
      ∑ j : Fin p.K,
        ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta
          rate rewards C_star C_h t j omega *
        ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
          rate rewards C_star C_h t j omega) mu
  exact ReferenceFirstLiveOriginalCalendarArrivalMoments.integrable_calendarRawGap
    rate rewards C_star C_h t control0 S

theorem integrable_calendarRoundedGap (t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m)
    (control0 : TimeControl p) : Integrable (calendarRoundedGap rate rewards C_star C_h t S) mu := by
  change Integrable ((ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
    rate rewards C_star C_h t).indicator (fun omega : SourceInput p =>
      (∑ j ∈ S.val,
        ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j) -
      ∑ j : Fin p.K,
        ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta
          rate rewards C_star C_h t j omega *
        ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j)) mu
  exact ReferenceFirstLiveOriginalCalendarArrivalMoments.integrable_calendarRoundedGap
    rate rewards C_star C_h t control0 S

theorem integrable_calendarFloorLoss (t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m)
    (control0 : TimeControl p) : Integrable (calendarFloorLoss rate rewards C_star C_h t S) mu := by
  change Integrable ((ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
    rate rewards C_star C_h t).indicator (fun omega : SourceInput p =>
      ∑ j ∈ S.val,
        ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRate
          rate rewards C_star C_h t j omega /
          (rate.eta.val * (ConstructorDimensions.D p : ℝ)))) mu
  exact ReferenceFirstLiveOriginalCalendarArrivalMoments.integrable_calendarFloorLoss
    rate rewards C_star C_h t control0 S

section OriginalMeasure

variable (t : Fin p.T) (control0 : TimeControl p)

local notation "phase" => ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t
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

include control0 in
private theorem not_retained_on_exception (omega : SourceInput p)
    (h : omega ∈ phase 0 ∨ omega ∈ phase 1 ∨ omega ∈ phase 5) : omega ∉ K t := by
  intro hk
  rw [ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent_eq_phaseRestriction
    rate rewards C_star C_h t control0] at hk
  obtain ⟨i, hi, hωi⟩ : ∃ i : Fin 6, (i = 0 ∨ i = 1 ∨ i = 5) ∧ omega ∈ phase i := by
    rcases h with h | h | h
    · exact ⟨0, Or.inl rfl, h⟩
    · exact ⟨1, Or.inr (Or.inl rfl), h⟩
    · exact ⟨5, Or.inr (Or.inr rfl), h⟩
  obtain ⟨j, hj, hωj⟩ : ∃ j : Fin 6, (j = 2 ∨ j = 3 ∨ j = 4) ∧ omega ∈ phase j := by
    rcases hk.1 with h | h | h
    · exact ⟨2, Or.inl rfl, h⟩
    · exact ⟨3, Or.inr (Or.inl rfl), h⟩
    · exact ⟨4, Or.inr (Or.inr rfl), h⟩
  have hij : i ≠ j := by
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> decide
  exact Set.disjoint_left.mp
    (ReferenceFirstLiveSourcePhasePartition.source_phases_disjoint rate rewards C_star C_h t hij)
      hωi hωj

private theorem calendarArrival_zero_on_exception (j : Fin p.K) (omega : SourceInput p)
    (h : omega ∈ phase 0 ∨ omega ∈ phase 1 ∨ omega ∈ phase 5) :
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
      rate rewards C_star C_h t j omega = 0 := by
  rcases h with h | h | h
  · have hL := (ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
      rate rewards C_star C_h omega h).2.1
    unfold ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
    simp only [ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells,
      hL, List.getElem?_nil, ite_self]
  · have hfuture : t.val < a omega := h.2
    unfold ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
    exact ite_eq_right (Nat.not_le_of_lt hfuture)
  · have hlen : (L omega).length ≤ t.val - a omega := by
      exact (ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveCells_length
        rate rewards C_star C_h omega).trans_le h.2.2
    unfold ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
    rw [List.getElem?_eq_none hlen]
    simp

private theorem integral_original_components (f : SourceInput p → ℝ)
    (hzero : ∀ omega, omega ∈ phase 0 ∨ omega ∈ phase 1 ∨ omega ∈ phase 5 → f omega = 0)
    (hb : ∀ q, Integrable (fun z : BirthZ q => f z.val) (muB q))
    (hp : ∀ q v, Integrable (fun z : PlusZ q v => f z.val.val) (muP q v))
    (he : ∀ q v, Integrable (fun z : EmptyZ q v => f z.val.val) (muE q v)) :
    (∫ omega, f omega ∂mu) =
      (∑ q, ∫ z : BirthZ q, f z.val ∂muB q) +
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
  let b q := (muB q).map (Subtype.val : BirthZ q → SourceInput p)
  let c q v := (muP q v).map
    (ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t
      v.val (Nat.lt_succ_iff.mp v.isLt) control0) +
    (muE q v).map (ReferenceFirstLiveSourcePhasePartition.forgetEmpty rate rewards C_star C_h q t
      v.val (Nat.lt_succ_iff.mp v.isLt) control0)
  have hbi q : Integrable f (b q) := (embB q).integrable_map_iff.mpr (hb q)
  have hpi q v : Integrable f ((muP q v).map
      (ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t
        v.val (Nat.lt_succ_iff.mp v.isLt) control0)) := (embP q v).integrable_map_iff.mpr (hp q v)
  have hei q v : Integrable f ((muE q v).map
      (ReferenceFirstLiveSourcePhasePartition.forgetEmpty rate rewards C_star C_h q t
        v.val (Nat.lt_succ_iff.mp v.isLt) control0)) := (embE q v).integrable_map_iff.mpr (he q v)
  have hci q v : Integrable f (c q v) := (hpi q v).add_measure (hei q v)
  have hbs : Integrable f (∑ q, b q) := integrable_finsetSum_measure.mpr (fun q _ => hbi q)
  have hcs q : Integrable f (∑ v, c q v) := integrable_finsetSum_measure.mpr (fun v _ => hci q v)
  have hcss : Integrable f (∑ q, ∑ v, c q v) :=
    integrable_finsetSum_measure.mpr (fun q _ => hcs q)
  have hz (i : Fin 6) (hi : i = 0 ∨ i = 1 ∨ i = 5) :
      f =ᵐ[(mu).restrict (phase i)] 0 := by
    filter_upwards [ae_restrict_mem
      (ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
        rate rewards C_star C_h t control0 i)] with omega homega
    rcases hi with rfl | rfl | rfl
    · exact hzero omega (Or.inl homega)
    · exact hzero omega (Or.inr (Or.inl homega))
    · exact hzero omega (Or.inr (Or.inr homega))
  have h0 : Integrable f ((mu).restrict (phase 0)) :=
    (integrable_const (0 : ℝ)).congr (hz 0 (by simp)).symm
  have h1 : Integrable f ((mu).restrict (phase 1)) :=
    (integrable_const (0 : ℝ)).congr (hz 1 (by simp)).symm
  have h5 : Integrable f ((mu).restrict (phase 5)) :=
    (integrable_const (0 : ℝ)).congr (hz 5 (by simp)).symm
  have h01 := h0.add_measure h1
  have h015 := h01.add_measure h5
  have h015b := h015.add_measure hbs
  have hdecomp : mu = (mu).restrict (phase 0) + (mu).restrict (phase 1) +
      (mu).restrict (phase 5) + (∑ q, b q) + ∑ q, ∑ v, c q v :=
    ReferenceFirstLiveCalendarIntegralAssembly.original_source_measure_decomposition
      rate rewards C_star C_h t control0
  rw [hdecomp, integral_add_measure h015b hcss, integral_add_measure h015 hbs,
    integral_add_measure h01 h5, integral_add_measure h0 h1,
    integral_congr_ae (hz 0 (by simp)), integral_congr_ae (hz 1 (by simp)),
    integral_congr_ae (hz 5 (by simp))]
  simp only [Pi.zero_apply, integral_zero, zero_add]
  rw [integral_finsetSum_measure (fun q _ => hbi q),
    integral_finsetSum_measure (fun q _ => hcs q)]
  congr 1
  · apply Finset.sum_congr rfl
    intro q hq
    exact (embB q).integral_map f
  · apply Finset.sum_congr rfl
    intro q hq
    rw [integral_finsetSum_measure (fun v _ => hci q v)]
    apply Finset.sum_congr rfl
    intro v hv
    rw [integral_add_measure (hpi q v) (hei q v)]
    exact congrArg₂ (· + ·) ((embP q v).integral_map f) ((embE q v).integral_map f)

include control0 in
private theorem rounded_zero_on_exception (S : ProductSetLaw.ProductSet p.K p.m)
    (omega : SourceInput p)
    (h : omega ∈ phase 0 ∨ omega ∈ phase 1 ∨ omega ∈ phase 5) :
    calendarRoundedGap rate rewards C_star C_h t S omega = 0 := by
  simp [calendarRoundedGap, not_retained_on_exception rate rewards C_star C_h t control0 omega h]

include control0 in
private theorem floor_zero_on_exception (S : ProductSetLaw.ProductSet p.K p.m)
    (omega : SourceInput p)
    (h : omega ∈ phase 0 ∨ omega ∈ phase 1 ∨ omega ∈ phase 5) :
    calendarFloorLoss rate rewards C_star C_h t S omega = 0 := by
  simp [calendarFloorLoss, not_retained_on_exception rate rewards C_star C_h t control0 omega h]

private theorem raw_zero_on_exception (S : ProductSetLaw.ProductSet p.K p.m)
    (omega : SourceInput p)
    (h : omega ∈ phase 0 ∨ omega ∈ phase 1 ∨ omega ∈ phase 5) :
    calendarRawGap rate rewards C_star C_h t S omega = 0 := by
  have hS : (∑ j ∈ S.val,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
        rate rewards C_star C_h t j omega) = 0 :=
    Finset.sum_eq_zero fun j hj => by
      rw [calendarArrival_zero_on_exception rate rewards C_star C_h t j omega h]
  have hK : (∑ j : Fin p.K,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta rate rewards C_star C_h t j omega *
        ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
          rate rewards C_star C_h t j omega) = 0 :=
    Finset.sum_eq_zero fun j hj => by
      rw [calendarArrival_zero_on_exception rate rewards C_star C_h t j omega h]
      simp
  simp [calendarRawGap, hS, hK]

include control0 in
private theorem birth_rounded_le_raw_add_floor
    (S : ProductSetLaw.ProductSet p.K p.m) (q : Fin (ConstructorDimensions.M p)) :
    (∫ z : BirthZ q, calendarRoundedGap rate rewards C_star C_h t S z.val ∂muB q) ≤
      (∫ z : BirthZ q, calendarRawGap rate rewards C_star C_h t S z.val ∂muB q) +
      ∫ z : BirthZ q, calendarFloorLoss rate rewards C_star C_h t S z.val ∂muB q := by
  let theta0 := ProductSetLaw.theta p.m (fun _ : Fin p.K => (1 : ℝ))
  let xi := fun j : Fin p.K => CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j
  have hrounded (j : Fin p.K) :=
    ReferenceFirstLiveOriginalCalendarArrivalMoments.integral_birthArrival_bounds
      rate rewards C_star C_h q t control0 j
  have htheta (j : Fin p.K) : 0 ≤ theta0 j :=
    (ProductSetLaw.theta_pos (fun _ : Fin p.K => (1 : ℝ)) j
      (ConstructorDimensions.m_pos p) p.m_lt_K (fun _ => by norm_num)).le
  have hYint (j : Fin p.K) :
      Integrable (fun z : BirthZ q =>
        ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
          rate rewards C_star C_h q t control0 z j) (muB q) :=
    (ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
      rate rewards C_star C_h q t control0 j Set.univ Set.univ
      MeasurableSet.univ MeasurableSet.univ).2.2.1
  have hroundInt :
      (∫ z : BirthZ q, calendarRoundedGap rate rewards C_star C_h t S z.val ∂muB q) =
        (muB q).real Set.univ *
          ((∑ j ∈ S.val, ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward
              rewards t j) -
            ∑ j : Fin p.K, theta0 j *
              ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j) := by
    have hfun : (fun z : BirthZ q => calendarRoundedGap rate rewards C_star C_h t S z.val) =
        fun _ => (∑ j ∈ S.val,
          ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j) -
          ∑ j : Fin p.K, theta0 j *
            ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j := by
      funext z
      simp [calendarRoundedGap,
        ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRetained_birth
          rate rewards C_star C_h q t control0,
        ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta_birth
          rate rewards C_star C_h q t, theta0]
    rw [hfun, integral_const, smul_eq_mul]
  have hrawInt :
      (∫ z : BirthZ q, calendarRawGap rate rewards C_star C_h t S z.val ∂muB q) =
        (∑ j ∈ S.val, ∫ z : BirthZ q,
          ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
            rate rewards C_star C_h q t control0 z j ∂muB q) -
          ∑ j : Fin p.K, theta0 j *
            ∫ z : BirthZ q, ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
              rate rewards C_star C_h q t control0 z j ∂muB q := by
    have hfun : (fun z : BirthZ q => calendarRawGap rate rewards C_star C_h t S z.val) =
        fun z => (∑ j ∈ S.val,
          ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
            rate rewards C_star C_h q t control0 z j) -
          ∑ j : Fin p.K, theta0 j *
            ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
              rate rewards C_star C_h q t control0 z j := by
      funext z
      simp [calendarRawGap,
        ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival_birth
          rate rewards C_star C_h q t control0,
        ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta_birth
          rate rewards C_star C_h q t, theta0]
    rw [hfun, integral_sub]
    · rw [integral_finsetSum _ (fun j _ => hYint j),
        integral_finsetSum _ (fun j _ => (hYint j).const_mul (theta0 j))]
      simp only [integral_const_mul]
    · exact integrable_finsetSum _ (fun j _ => hYint j)
    · exact integrable_finsetSum _ (fun j _ => (hYint j).const_mul (theta0 j))
  have hfloorInt :
      (∫ z : BirthZ q, calendarFloorLoss rate rewards C_star C_h t S z.val ∂muB q) =
        (muB q).real Set.univ * (∑ j ∈ S.val, xi j / scale) := by
    have hfun : (fun z : BirthZ q => calendarFloorLoss rate rewards C_star C_h t S z.val) =
        fun _ => ∑ j ∈ S.val, xi j / scale := by
      funext z
      simp [calendarFloorLoss,
        ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRetained_birth
          rate rewards C_star C_h q t control0,
        ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRate_birth
          rate rewards C_star C_h q t control0, xi]
    rw [hfun, integral_const, smul_eq_mul]
  have hlower : (muB q).real Set.univ *
      (∑ j ∈ S.val, ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j) ≤
      (∑ j ∈ S.val, ∫ z : BirthZ q,
        ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
          rate rewards C_star C_h q t control0 z j ∂muB q) +
        (muB q).real Set.univ * (∑ j ∈ S.val, xi j / scale) := by
    calc
      _ = ∑ j ∈ S.val, (muB q).real Set.univ *
          ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j := by
        rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ S.val,
          ((∫ z : BirthZ q, ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
              rate rewards C_star C_h q t control0 z j ∂muB q) +
            (muB q).real Set.univ * (xi j / scale)) := by
        apply Finset.sum_le_sum
        intro j hj
        have h := (hrounded j).1
        dsimp [xi] at h ⊢
        nlinarith [h]
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hupper :
      (∑ j : Fin p.K, theta0 j *
        ∫ z : BirthZ q, ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
          rate rewards C_star C_h q t control0 z j ∂muB q) ≤
        (muB q).real Set.univ *
          ∑ j : Fin p.K, theta0 j *
            ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j := by
    calc
      _ ≤ ∑ j : Fin p.K, theta0 j *
          ((muB q).real Set.univ *
            ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hrounded j).2 (htheta j)
      _ = _ := by
        calc
          _ = ∑ j : Fin p.K, (muB q).real Set.univ *
                (theta0 j *
                  ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
          _ = _ := by rw [Finset.mul_sum]
  rw [hroundInt, hrawInt, hfloorInt]
  nlinarith [hlower, hupper]

end OriginalMeasure

private theorem firstLiveCell_rate_le_one (omega : SourceInput p)
    (k : Fin (L omega).length) (j : Fin p.K) :
    (L omega)[k.val].rate j ≤ 1 := by
  classical
  let boundary := ReferenceCompletePhysicalHistory.generatedBoundary
    rate omega rewards C_star C_h
  cases hcross : boundary.crossing with
  | none =>
      have hno := ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
        rate rewards C_star C_h omega (by simpa [boundary] using hcross)
      have hL : L omega = [] := by
        simpa [ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells] using hno.2.1
      rw [hL] at k
      exact Fin.elim0 k
  | some crossing =>
      have hc : (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput omega rewards C_star C_h rate)).crossing.isSome = true := by
        simpa [boundary, ReferenceCompletePhysicalHistory.generatedBoundary,
          ReferenceCompletePhysicalHistory.generatedInput] using
          (show boundary.crossing.isSome = true by simp [hcross])
      let start := ReferenceInitializationRun.elapsed p boundary.completed
      have hstart : a omega = start := by rfl
      have hstartLe : start ≤ p.T := by
        rw [← hstart]
        exact ReferenceCompletePhysicalHistory.physicalStart_le_T rate omega rewards C_star C_h
      let sf : Fin (p.T + 1) := ⟨start, Nat.lt_succ_of_le hstartLe⟩
      let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h start :=
        ⟨omega, ⟨hc, rfl⟩⟩
      let count := p.T - start
      let hspanFiber := ReferenceFirstLiveOverflowReadout.maximal_span sf
      have hwhole := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
        rate rewards C_star C_h sf x
      have hspan := ReferenceFirstLiveOverflowReadout.launch_span
        rate rewards C_star C_h start count hspanFiber x
      have hcellsActual : L omega =
          ReferenceFirstWindowNumericalStream.actualLiveSourceCells
            rate omega rewards C_star C_h hc count hspan := by
        simpa [ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells,
          ReferenceFirstLiveOverflowReadout.firstLiveCells, count, hspanFiber] using hwhole.2
      have hlenCells : (L omega).length =
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
            rate omega rewards C_star C_h hc count hspan).length :=
        congrArg List.length hcellsActual
      have hkActual : k.val <
          (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
            rate omega rewards C_star C_h hc count hspan).length := by
        calc
          k.val < (L omega).length := k.isLt
          _ = (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
              rate omega rewards C_star C_h hc count hspan).length := hlenCells
          _ = (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
              rate omega rewards C_star C_h hc count hspan).length :=
            ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
              rate omega rewards C_star C_h hc count hspan
      let kActual : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
          rate omega rewards C_star C_h hc count hspan).length := ⟨k.val, hkActual⟩
      let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
        rate omega rewards C_star C_h hc count hspan kActual
      have hfacts := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt_facts
        rate omega rewards C_star C_h hc count hspan kActual
      dsimp only at hfacts
      rcases hfacts with ⟨_, _, _, _, _, _, hrate, _, _⟩
      have hsourceGet := ReferenceFirstWindowNumericalStream.actualLiveSourceCells_get
        rate omega rewards C_star C_h hc count hspan kActual
      have hgetActual :
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
            rate omega rewards C_star C_h hc count hspan)[k.val]'(by
              rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
                rate omega rewards C_star C_h hc count hspan]
              exact kActual.isLt) = cell.input := by
        simpa [cell, kActual] using hsourceGet
      have hgetOption := congrArg
        (fun cells : List (RecordedQueueRun.RoundInput p.K) => cells[k.val]?) hcellsActual
      have hactualIndex : k.val <
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
            rate omega rewards C_star C_h hc count hspan).length := by
        calc
          k.val < (L omega).length := k.isLt
          _ = (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
              rate omega rewards C_star C_h hc count hspan).length := hlenCells
      rw [List.getElem?_eq_getElem k.isLt,
        List.getElem?_eq_getElem hactualIndex] at hgetOption
      have hget : (L omega)[k.val] =
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
            rate omega rewards C_star C_h hc count hspan)[k.val] :=
        Option.some.inj hgetOption
      change ((L omega)[k.val]'k.isLt).rate j ≤ 1
      rw [hget, hgetActual, hrate, cell.selected.view.payload.rate_eq_canonical]
      have hxi := CanonicalRecordingRates.xi_le_one_div_16mK p rate.eta.property
        rate.sourceCap cell.selected.view.payload.anchor
        cell.selected.view.payload.anchor_pos j
      have hm : (1 : ℝ) ≤ (p.m : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt (ConstructorDimensions.m_pos p))
      have hKnat : 1 ≤ p.K :=
        Nat.le_trans (Nat.succ_le_of_lt (ConstructorDimensions.m_pos p))
          (Nat.le_of_lt p.m_lt_K)
      have hK : (1 : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast hKnat
      have hmk : (1 : ℝ) ≤ (p.m : ℝ) * (p.K : ℝ) := by
        calc
          1 = 1 * 1 := by ring
          _ ≤ (p.m : ℝ) * (p.K : ℝ) :=
            mul_le_mul hm hK (by norm_num) (by positivity)
      have hden : (1 : ℝ) ≤ 16 * (p.m : ℝ) * (p.K : ℝ) := by nlinarith [hmk]
      have hdenPos : 0 < 16 * (p.m : ℝ) * (p.K : ℝ) := by positivity
      have hsmall : 1 / (16 * (p.m : ℝ) * (p.K : ℝ)) ≤ 1 :=
        (div_le_one hdenPos).2 hden
      exact hxi.trans hsmall

private theorem calendarRate_le_one (t : Fin p.T) (j : Fin p.K)
    (omega : SourceInput p) :
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRate
      rate rewards C_star C_h t j omega ≤ 1 := by
  unfold ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRate
  by_cases hstart : a omega ≤ t.val
  · rw [ite_eq_left hstart]
    cases hcell : (L omega)[t.val - a omega]? with
    | none => simp
    | some cell =>
        rcases List.getElem?_eq_some_iff.mp hcell with ⟨hidx, hget⟩
        let k : Fin (L omega).length := ⟨t.val - a omega, hidx⟩
        have hrate := firstLiveCell_rate_le_one rate rewards C_star C_h omega k j
        simpa only [k, hget] using hrate
  · simp [hstart]

private theorem calendarFloorLoss_le (t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m)
    (omega : SourceInput p) :
    calendarFloorLoss rate rewards C_star C_h t S omega ≤ (p.m : ℝ) / scale := by
  have hscale := scale_pos rate
  have hcard : S.val.card = p.m := productSet_card S
  by_cases hret : omega ∈ K t
  · simp only [calendarFloorLoss, Set.indicator_of_mem hret]
    have hsum :
        (∑ j ∈ S.val, ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRate
          rate rewards C_star C_h t j omega / scale) ≤ (p.m : ℝ) / scale := by
      calc
        _ ≤ ∑ j ∈ S.val, (1 : ℝ) / scale := by
          apply Finset.sum_le_sum
          intro j hj
          exact div_le_div_of_nonneg_right
            (calendarRate_le_one rate rewards C_star C_h t j omega) hscale.le
        _ = (S.val.card : ℝ) * (1 / scale) := by simp
        _ = (p.m : ℝ) / scale := by rw [hcard]; ring
    exact hsum
  · simp [calendarFloorLoss, hret]
    positivity

/-- The exact positive floor loss is pointwise bounded using each actual
payload's canonical rate, without imposing a rate hypothesis on the source. -/
theorem integral_calendarFloorLoss_le (t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) (control0 : TimeControl p) :
    (∫ omega : SourceInput p, calendarFloorLoss rate rewards C_star C_h t S omega ∂mu) ≤
      (p.m : ℝ) / scale := by
  have hfloor := integrable_calendarFloorLoss rate rewards C_star C_h t S control0
  have hconst : Integrable (fun _ : SourceInput p => (p.m : ℝ) / scale) mu := integrable_const _
  calc
    _ ≤ ∫ _omega : SourceInput p, (p.m : ℝ) / scale ∂mu := by
      apply integral_mono hfloor hconst
      intro omega
      exact calendarFloorLoss_le rate rewards C_star C_h t S omega
    _ = (p.m : ℝ) / scale := by simp

theorem integrable_sum_calendarRoundedGap (S : ProductSetLaw.ProductSet p.K p.m)
    (control0 : TimeControl p) :
    Integrable (fun omega : SourceInput p =>
      ∑ t : Fin p.T, calendarRoundedGap rate rewards C_star C_h t S omega) mu := by
  exact integrable_finsetSum Finset.univ (fun t _ =>
    integrable_calendarRoundedGap rate rewards C_star C_h t S control0)

theorem integrable_sum_calendarFloorLoss (S : ProductSetLaw.ProductSet p.K p.m)
    (control0 : TimeControl p) :
    Integrable (fun omega : SourceInput p =>
      ∑ t : Fin p.T, calendarFloorLoss rate rewards C_star C_h t S omega) mu := by
  exact integrable_finsetSum Finset.univ (fun t _ =>
    integrable_calendarFloorLoss rate rewards C_star C_h t S control0)

theorem sum_calendarAcceptedArrival_eq_firstWindow (S : ProductSetLaw.ProductSet p.K p.m)
    (omega : SourceInput p) :
    (∑ t : Fin p.T, ∑ j ∈ S.val,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
        rate rewards C_star C_h t j omega) =
      ∑ k : Fin (L omega).length, ∑ j ∈ S.val,
        ReferenceFirstLiveRawPotentialBound.firstWindowAcceptedArrival
          rate rewards C_star C_h omega k j := by
  let f := fun t : Fin p.T => ∑ j ∈ S.val,
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
      rate rewards C_star C_h t j omega
  let kept := Finset.univ.filter (fun t : Fin p.T =>
    a omega ≤ t.val ∧ t.val - a omega < (L omega).length)
  have hrestrict : (∑ t ∈ kept, f t) = ∑ t : Fin p.T, f t := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro t ht hnot
    have hnot' : ¬ (a omega ≤ t.val ∧ t.val - a omega < (L omega).length) := by
      simpa only [kept, Finset.mem_filter, Finset.mem_univ, true_and] using hnot
    apply Finset.sum_eq_zero
    intro j hj
    unfold ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
    by_cases hstart : a omega ≤ t.val
    · have hidx : (L omega).length ≤ t.val - a omega := by
        by_contra hn
        exact hnot' ⟨hstart, Nat.lt_of_not_ge hn⟩
      rw [ite_eq_left hstart, List.getElem?_eq_none hidx]
    · rw [ite_eq_right hstart]
  rw [← hrestrict]
  apply Finset.sum_bij
    (fun t ht => (⟨t.val - a omega, (Finset.mem_filter.mp ht).2.2⟩ : Fin (L omega).length))
  · intro t ht
    exact Finset.mem_univ _
  · intro t ht v hv heq
    have ht' := (Finset.mem_filter.mp ht).2.1
    have hv' := (Finset.mem_filter.mp hv).2.1
    have heq' := congrArg Fin.val heq
    apply Fin.ext
    dsimp only at heq'
    omega
  · intro k hk
    let t : Fin p.T := ⟨a omega + k.val, by
      have hspan := ReferenceFirstLiveOriginalCalendarArrivalMoments.firstLiveStart_add_length_le_T
        rate rewards C_star C_h omega
      omega⟩
    refine ⟨t, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        dsimp only [t]
        rw [Nat.add_sub_cancel_left]
        exact ⟨Nat.le_add_right _ _, k.isLt⟩⟩
    · apply Fin.ext
      exact Nat.add_sub_cancel_left _ _
  · intro t ht
    have hstart := (Finset.mem_filter.mp ht).2.1
    have hidx := (Finset.mem_filter.mp ht).2.2
    dsimp only [f]
    apply Finset.sum_congr rfl
    intro j hj
    unfold ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
      ReferenceFirstLiveRawPotentialBound.firstWindowAcceptedArrival
    rw [ite_eq_left hstart, List.getElem?_eq_getElem hidx]
    simp [ReferenceFirstLiveRawPotentialBound.firstWindowRun,
      ReferenceFirstLiveRawPotentialBound.firstWindowQueue,
      ReferenceFirstLiveRawPotentialBound.firstWindowCells,
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveRunAt,
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart,
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells]

theorem sum_calendarRawGap_eq_firstWindowRawGap (S : ProductSetLaw.ProductSet p.K p.m)
    (omega : SourceInput p) :
    (∑ t : Fin p.T, calendarRawGap rate rewards C_star C_h t S omega) =
      ReferenceFirstLiveRawPotentialBound.firstWindowRawGap rate rewards C_star C_h omega S := by
  unfold calendarRawGap ReferenceFirstLiveRawPotentialBound.firstWindowRawGap
  conv_lhs => rw [Finset.sum_sub_distrib]
  conv_rhs => rw [Finset.sum_sub_distrib]
  rw [
    sum_calendarAcceptedArrival_eq_firstWindow rate rewards C_star C_h S omega,
    ReferenceFirstLiveOriginalCalendarArrivalMoments.sum_calendarWeightedArrival_eq_firstWindow
      rate rewards C_star C_h omega]
  simp [ReferenceFirstLiveRawPotentialBound.firstWindowMarginal,
    ReferenceFirstLiveRawPotentialBound.firstWindowAcceptedArrival,
    ReferenceFirstLiveRawPotentialBound.firstWindowRun,
    ReferenceFirstLiveRawPotentialBound.firstWindowQueue,
    ReferenceFirstLiveRawPotentialBound.firstWindowCells,
    ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveQueue,
    ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells]
  congr 1

theorem integrable_firstWindowRawGap (S : ProductSetLaw.ProductSet p.K p.m)
    (control0 : TimeControl p) :
    Integrable (fun omega : SourceInput p =>
      ReferenceFirstLiveRawPotentialBound.firstWindowRawGap rate rewards C_star C_h omega S) mu := by
  have hsum : Integrable (fun omega : SourceInput p =>
      ∑ t : Fin p.T, calendarRawGap rate rewards C_star C_h t S omega) mu :=
    integrable_finsetSum Finset.univ (fun t _ =>
      integrable_calendarRawGap rate rewards C_star C_h t S control0)
  exact hsum.congr (Filter.Eventually.of_forall fun omega =>
    sum_calendarRawGap_eq_firstWindowRawGap rate rewards C_star C_h S omega)

section OriginalMeasureComparison

variable (t : Fin p.T) (control0 : TimeControl p)

local notation "phase" => ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t
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

include control0 in
private theorem rounded_integrable_birth (S : ProductSetLaw.ProductSet p.K p.m)
    (q : Fin (ConstructorDimensions.M p)) :
    Integrable (fun z : BirthZ q => calendarRoundedGap rate rewards C_star C_h t S z.val)
      (muB q) := by
  let theta0 := ProductSetLaw.theta p.m (fun _ : Fin p.K => (1 : ℝ))
  have hfun : (fun z : BirthZ q => calendarRoundedGap rate rewards C_star C_h t S z.val) =
      fun _ => (∑ j ∈ S.val,
        ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j) -
        ∑ j : Fin p.K, theta0 j *
          ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j := by
    funext z
    simp [calendarRoundedGap,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRetained_birth
        rate rewards C_star C_h q t control0,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta_birth
        rate rewards C_star C_h q t, theta0]
  rw [hfun]
  exact integrable_const _

include control0 in
private theorem raw_integrable_birth (S : ProductSetLaw.ProductSet p.K p.m)
    (q : Fin (ConstructorDimensions.M p)) :
    Integrable (fun z : BirthZ q => calendarRawGap rate rewards C_star C_h t S z.val)
      (muB q) := by
  let theta0 := ProductSetLaw.theta p.m (fun _ : Fin p.K => (1 : ℝ))
  have hYint (j : Fin p.K) :
      Integrable (fun z : BirthZ q =>
        ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
          rate rewards C_star C_h q t control0 z j) (muB q) :=
    (ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
      rate rewards C_star C_h q t control0 j Set.univ Set.univ
      MeasurableSet.univ MeasurableSet.univ).2.2.1
  have hfun : (fun z : BirthZ q => calendarRawGap rate rewards C_star C_h t S z.val) =
      fun z => (∑ j ∈ S.val,
        ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
          rate rewards C_star C_h q t control0 z j) -
        ∑ j : Fin p.K, theta0 j *
          ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
            rate rewards C_star C_h q t control0 z j := by
    funext z
    simp [calendarRawGap,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival_birth
        rate rewards C_star C_h q t control0,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta_birth
        rate rewards C_star C_h q t, theta0]
  rw [hfun]
  exact (integrable_finsetSum _ fun j _ => hYint j).sub
    (integrable_finsetSum _ fun j _ => (hYint j).const_mul (theta0 j))

include control0 in
private theorem floor_integrable_birth (S : ProductSetLaw.ProductSet p.K p.m)
    (q : Fin (ConstructorDimensions.M p)) :
    Integrable (fun z : BirthZ q => calendarFloorLoss rate rewards C_star C_h t S z.val)
      (muB q) := by
  let xi := fun j : Fin p.K => CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j
  have hfun : (fun z : BirthZ q => calendarFloorLoss rate rewards C_star C_h t S z.val) =
      fun _ => ∑ j ∈ S.val, xi j / scale := by
    funext z
    simp [calendarFloorLoss,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRetained_birth
        rate rewards C_star C_h q t control0,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRate_birth
        rate rewards C_star C_h q t control0, xi]
  rw [hfun]
  exact integrable_const _

private theorem rounded_integrable_nonempty (S : ProductSetLaw.ProductSet p.K p.m)
    (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)) :
    Integrable (fun z : PlusZ q v => calendarRoundedGap rate rewards C_star C_h t S z.val.val)
      (muP q v) := by
  have hfun : (fun z : PlusZ q v => calendarRoundedGap rate rewards C_star C_h t S z.val.val) =
      fun z =>
        (ReferenceFirstLiveAllArmPrefixAdaptation.strictPastOverflowFalseSet
          rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0).indicator
          (fun z =>
            (∑ j ∈ S.val,
              ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j) -
              ∑ j : Fin p.K,
                ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore rate rewards C_star C_h q t
                  v.val (Nat.lt_succ_iff.mp v.isLt) control0 j z *
                  ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j) z := by
    funext z
    simp only [calendarRoundedGap, Set.indicator,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRetained_nonempty
        rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 z,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta_nonempty
        rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0]
  rw [hfun]
  exact ReferenceFirstLiveOriginalCalendarArrivalMoments.integrable_nonemptyRoundedGap
    rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 S

private theorem raw_integrable_nonempty (S : ProductSetLaw.ProductSet p.K p.m)
    (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)) :
    Integrable (fun z : PlusZ q v => calendarRawGap rate rewards C_star C_h t S z.val.val)
      (muP q v) := by
  have hfun : (fun z : PlusZ q v => calendarRawGap rate rewards C_star C_h t S z.val.val) =
      fun z =>
        (∑ j ∈ S.val,
          ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
            rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 j z) -
        ∑ j : Fin p.K,
          ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore rate rewards C_star C_h q t v.val
            (Nat.lt_succ_iff.mp v.isLt) control0 j z *
          ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
            rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 j z := by
    funext z
    simp only [calendarRawGap,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival_nonempty
        rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta_nonempty
        rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0]
  rw [hfun]
  exact ReferenceFirstLiveOriginalCalendarArrivalMoments.integrable_nonemptyRawGap
    rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 S

private theorem floor_integrable_nonempty (S : ProductSetLaw.ProductSet p.K p.m)
    (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)) :
    Integrable (fun z : PlusZ q v => calendarFloorLoss rate rewards C_star C_h t S z.val.val)
      (muP q v) := by
  have hfun : (fun z : PlusZ q v => calendarFloorLoss rate rewards C_star C_h t S z.val.val) =
      fun z =>
        (ReferenceFirstLiveAllArmPrefixAdaptation.strictPastOverflowFalseSet
          rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0).indicator
          (fun z => ∑ j ∈ S.val,
            ReferenceFirstLiveAllArmPrefixAdaptation.markerRatePlus rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0 j z / scale) z := by
    funext z
    simp only [calendarFloorLoss, Set.indicator,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRetained_nonempty
        rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 z,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRate_nonempty
        rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0]
  rw [hfun]
  exact ReferenceFirstLiveOriginalCalendarArrivalMoments.integrable_nonemptyFloorLoss
    rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 S

private theorem rounded_integrable_empty (S : ProductSetLaw.ProductSet p.K p.m)
    (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)) :
    Integrable (fun z : EmptyZ q v => calendarRoundedGap rate rewards C_star C_h t S z.val.val)
      (muE q v) := by
  have hfun : (fun z : EmptyZ q v => calendarRoundedGap rate rewards C_star C_h t S z.val.val) =
      fun z =>
        (ReferenceFirstLiveEmptyPendingAcceptedMoments.G rate rewards C_star C_h q t v.val
          (Nat.lt_succ_iff.mp v.isLt) control0).indicator
          (fun z =>
            (∑ j ∈ S.val,
              ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j) -
              ∑ j : Fin p.K,
                ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore rate rewards C_star C_h
                  q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 j z *
                  ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j) z := by
    funext z
    simp only [calendarRoundedGap, Set.indicator,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRetained_empty
        rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 z,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta_empty
        rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0]
  rw [hfun]
  exact ReferenceFirstLiveOriginalCalendarArrivalMoments.integrable_emptyRoundedGap
    rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 S

private theorem raw_integrable_empty (S : ProductSetLaw.ProductSet p.K p.m)
    (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)) :
    Integrable (fun z : EmptyZ q v => calendarRawGap rate rewards C_star C_h t S z.val.val)
      (muE q v) := by
  have hfun : (fun z : EmptyZ q v => calendarRawGap rate rewards C_star C_h t S z.val.val) =
      fun z =>
        (∑ j ∈ S.val,
          ReferenceFirstLiveEmptyPendingAcceptedMoments.acceptedA
            rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 j z) -
        ∑ j : Fin p.K,
          ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore rate rewards C_star C_h q t
            v.val (Nat.lt_succ_iff.mp v.isLt) control0 j z *
          ReferenceFirstLiveEmptyPendingAcceptedMoments.acceptedA
            rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 j z := by
    funext z
    simp only [calendarRawGap,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival_empty
        rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta_empty
        rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0]
  rw [hfun]
  exact ReferenceFirstLiveOriginalCalendarArrivalMoments.integrable_emptyRawGap
    rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 S

private theorem floor_integrable_empty (S : ProductSetLaw.ProductSet p.K p.m)
    (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)) :
    Integrable (fun z : EmptyZ q v => calendarFloorLoss rate rewards C_star C_h t S z.val.val)
      (muE q v) := by
  have hfun : (fun z : EmptyZ q v => calendarFloorLoss rate rewards C_star C_h t S z.val.val) =
      fun z =>
        (ReferenceFirstLiveEmptyPendingAcceptedMoments.G rate rewards C_star C_h q t v.val
          (Nat.lt_succ_iff.mp v.isLt) control0).indicator
          (fun z => ∑ j ∈ S.val,
            ReferenceFirstLiveEmptyPendingMarkerLaw.xiEmpty rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0
              (ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty rate rewards C_star C_h q t
                v.val (Nat.lt_succ_iff.mp v.isLt) control0 z) j / scale) z := by
    funext z
    simp only [calendarFloorLoss, Set.indicator,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRetained_empty
        rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 z,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRate_empty
        rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0]
  rw [hfun]
  exact ReferenceFirstLiveOriginalCalendarArrivalMoments.integrable_emptyFloorLoss
    rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 S

private theorem rounded_le_raw_add_floor_nonempty (S : ProductSetLaw.ProductSet p.K p.m)
    (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)) :
    (∫ z : PlusZ q v, calendarRoundedGap rate rewards C_star C_h t S z.val.val ∂muP q v) ≤
      (∫ z : PlusZ q v, calendarRawGap rate rewards C_star C_h t S z.val.val ∂muP q v) +
      ∫ z : PlusZ q v, calendarFloorLoss rate rewards C_star C_h t S z.val.val ∂muP q v := by
  simpa only [calendarRoundedGap, calendarRawGap, calendarFloorLoss, Set.indicator,
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRetained_nonempty
      rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0,
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival_nonempty
      rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0,
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta_nonempty
      rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0,
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRate_nonempty
      rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0] using
    ReferenceFirstLiveOriginalCalendarArrivalMoments.integral_nonemptyRoundedGap_le_raw
      rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 S

private theorem rounded_le_raw_add_floor_empty (S : ProductSetLaw.ProductSet p.K p.m)
    (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)) :
    (∫ z : EmptyZ q v, calendarRoundedGap rate rewards C_star C_h t S z.val.val ∂muE q v) ≤
      (∫ z : EmptyZ q v, calendarRawGap rate rewards C_star C_h t S z.val.val ∂muE q v) +
      ∫ z : EmptyZ q v, calendarFloorLoss rate rewards C_star C_h t S z.val.val ∂muE q v := by
  simpa only [calendarRoundedGap, calendarRawGap, calendarFloorLoss, Set.indicator,
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRetained_empty
      rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0,
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival_empty
      rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0,
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta_empty
      rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0,
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRate_empty
      rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0] using
    ReferenceFirstLiveOriginalCalendarArrivalMoments.integral_emptyRoundedGap_le_raw
      rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 S

theorem integral_calendarRoundedGap_le_raw_add_floor (t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) (control0 : TimeControl p) :
    (∫ omega : SourceInput p, calendarRoundedGap rate rewards C_star C_h t S omega ∂mu) ≤
      (∫ omega : SourceInput p, calendarRawGap rate rewards C_star C_h t S omega ∂mu) +
      ∫ omega : SourceInput p, calendarFloorLoss rate rewards C_star C_h t S omega ∂mu := by
  let fR := calendarRoundedGap rate rewards C_star C_h t S
  let fA := calendarRawGap rate rewards C_star C_h t S
  let fF := calendarFloorLoss rate rewards C_star C_h t S
  have hR := integral_original_components rate rewards C_star C_h t control0 fR
    (fun omega h => rounded_zero_on_exception rate rewards C_star C_h t control0 S omega h)
    (fun q => by simpa only [fR] using rounded_integrable_birth rate rewards C_star C_h t control0 S q)
    (fun q v => by
      simpa only [fR] using rounded_integrable_nonempty rate rewards C_star C_h t control0 S q v)
    (fun q v => by
      simpa only [fR] using rounded_integrable_empty rate rewards C_star C_h t control0 S q v)
  have hA := integral_original_components rate rewards C_star C_h t control0 fA
    (fun omega h => raw_zero_on_exception rate rewards C_star C_h t S omega h)
    (fun q => by simpa only [fA] using raw_integrable_birth rate rewards C_star C_h t control0 S q)
    (fun q v => by
      simpa only [fA] using raw_integrable_nonempty rate rewards C_star C_h t control0 S q v)
    (fun q v => by
      simpa only [fA] using raw_integrable_empty rate rewards C_star C_h t control0 S q v)
  have hF := integral_original_components rate rewards C_star C_h t control0 fF
    (fun omega h => floor_zero_on_exception rate rewards C_star C_h t control0 S omega h)
    (fun q => by simpa only [fF] using floor_integrable_birth rate rewards C_star C_h t control0 S q)
    (fun q v => by
      simpa only [fF] using floor_integrable_nonempty rate rewards C_star C_h t control0 S q v)
    (fun q v => by
      simpa only [fF] using floor_integrable_empty rate rewards C_star C_h t control0 S q v)
  have hB (q : Fin (ConstructorDimensions.M p)) :
      (∫ z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t),
        fR z.val ∂ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)) ≤
        (∫ z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t),
          fA z.val ∂ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)) +
          ∫ z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
              (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t),
            fF z.val ∂ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
              (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t) := by
    simpa only [fR, fA, fF] using
      birth_rounded_le_raw_add_floor rate rewards C_star C_h t control0 S q
  have hP (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)) :
      (∫ z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0,
        fR z.val.val ∂ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
          rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0) ≤
        (∫ z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h q t
            v.val (Nat.lt_succ_iff.mp v.isLt) control0,
          fA z.val.val ∂ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
            rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0) +
          ∫ z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0,
            fF z.val.val ∂ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
              rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 := by
    simpa only [fR, fA, fF] using
      rounded_le_raw_add_floor_nonempty rate rewards C_star C_h t control0 S q v
  have hE (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)) :
      (∫ z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0,
        fR z.val.val ∂ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
          rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0) ≤
        (∫ z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t
            v.val (Nat.lt_succ_iff.mp v.isLt) control0,
          fA z.val.val ∂ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
            rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0) +
          ∫ z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0,
            fF z.val.val ∂ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
              rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 := by
    simpa only [fR, fA, fF] using
      rounded_le_raw_add_floor_empty rate rewards C_star C_h t control0 S q v
  rw [hR, hA, hF]
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun q hq => hB q)
  rw [Finset.sum_add_distrib] at hb
  have hcPoint (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)) :=
    add_le_add (hP q v) (hE q v)
  have hc := Finset.sum_le_sum (s := Finset.univ) (fun q hq =>
    Finset.sum_le_sum (s := Finset.univ) (fun v hv => hcPoint q v))
  simp_rw [Finset.sum_add_distrib] at hb hc ⊢
  linarith [hb, hc]

end OriginalMeasureComparison

theorem integral_sum_calendarRoundedGap_le_firstWindowRawGap_add_floor
    (S : ProductSetLaw.ProductSet p.K p.m) (control0 : TimeControl p) :
    (∫ omega : SourceInput p,
      ∑ t : Fin p.T, calendarRoundedGap rate rewards C_star C_h t S omega ∂mu) ≤
      (∫ omega : SourceInput p,
        ReferenceFirstLiveRawPotentialBound.firstWindowRawGap rate rewards C_star C_h omega S ∂mu) +
      ∫ omega : SourceInput p,
        ∑ t : Fin p.T, calendarFloorLoss rate rewards C_star C_h t S omega ∂mu := by
  have hR := integrable_sum_calendarRoundedGap rate rewards C_star C_h S control0
  have hF := integrable_sum_calendarFloorLoss rate rewards C_star C_h S control0
  have hrawSum : Integrable (fun omega : SourceInput p =>
      ∑ t : Fin p.T, calendarRawGap rate rewards C_star C_h t S omega) mu :=
    integrable_finsetSum Finset.univ (fun t _ =>
      integrable_calendarRawGap rate rewards C_star C_h t S control0)
  have hRaw := integrable_firstWindowRawGap rate rewards C_star C_h S control0
  have hRawEq : (∫ omega : SourceInput p,
      ∑ t : Fin p.T, calendarRawGap rate rewards C_star C_h t S omega ∂mu) =
      ∫ omega : SourceInput p,
        ReferenceFirstLiveRawPotentialBound.firstWindowRawGap rate rewards C_star C_h omega S ∂mu := by
    exact integral_congr_ae (Filter.Eventually.of_forall fun omega =>
      sum_calendarRawGap_eq_firstWindowRawGap rate rewards C_star C_h S omega)
  rw [integral_finsetSum _ (fun t _ =>
      integrable_calendarRoundedGap rate rewards C_star C_h t S control0),
    integral_finsetSum _ (fun t _ =>
      integrable_calendarFloorLoss rate rewards C_star C_h t S control0)]
  calc
    _ ≤ ∑ t : Fin p.T,
        ((∫ omega, calendarRawGap rate rewards C_star C_h t S omega ∂mu) +
          ∫ omega, calendarFloorLoss rate rewards C_star C_h t S omega ∂mu) := by
      apply Finset.sum_le_sum
      intro t ht
      exact integral_calendarRoundedGap_le_raw_add_floor rate rewards C_star C_h t S control0
    _ = (∑ t : Fin p.T,
          ∫ omega, calendarRawGap rate rewards C_star C_h t S omega ∂mu) +
        ∑ t : Fin p.T,
          ∫ omega, calendarFloorLoss rate rewards C_star C_h t S omega ∂mu :=
      Finset.sum_add_distrib
    _ = _ := by
      rw [← integral_finsetSum _ (fun t _ =>
          integrable_calendarRawGap rate rewards C_star C_h t S control0), hRawEq]

theorem integral_sum_calendarFloorLoss_le (S : ProductSetLaw.ProductSet p.K p.m)
    (control0 : TimeControl p) :
    (∫ omega : SourceInput p,
      ∑ t : Fin p.T, calendarFloorLoss rate rewards C_star C_h t S omega ∂mu) ≤
      (p.m : ℝ) * (p.T : ℝ) / scale := by
  rw [integral_finsetSum _ (fun t _ =>
    integrable_calendarFloorLoss rate rewards C_star C_h t S control0)]
  calc
    _ ≤ ∑ _t : Fin p.T, (p.m : ℝ) / scale := by
      apply Finset.sum_le_sum
      intro t ht
      exact integral_calendarFloorLoss_le rate rewards C_star C_h t S control0
    _ = (p.T : ℝ) * ((p.m : ℝ) / scale) := by simp
    _ = (p.m : ℝ) * (p.T : ℝ) / scale := by ring

theorem integral_sum_calendarRoundedGap_le_firstWindowRawGap_add_coarseFloor
    (S : ProductSetLaw.ProductSet p.K p.m) (control0 : TimeControl p) :
    (∫ omega : SourceInput p,
      ∑ t : Fin p.T, calendarRoundedGap rate rewards C_star C_h t S omega ∂mu) ≤
      (∫ omega : SourceInput p,
        ReferenceFirstLiveRawPotentialBound.firstWindowRawGap rate rewards C_star C_h omega S ∂mu) +
      (p.m : ℝ) * (p.T : ℝ) / scale := by
  calc
    _ ≤ (∫ omega : SourceInput p,
          ReferenceFirstLiveRawPotentialBound.firstWindowRawGap rate rewards C_star C_h omega S ∂mu) +
        ∫ omega : SourceInput p,
          ∑ t : Fin p.T, calendarFloorLoss rate rewards C_star C_h t S omega ∂mu :=
      integral_sum_calendarRoundedGap_le_firstWindowRawGap_add_floor
        rate rewards C_star C_h S control0
    _ ≤ _ := add_le_add_right
      (integral_sum_calendarFloorLoss_le rate rewards C_star C_h S control0)
      (∫ omega : SourceInput p,
        ReferenceFirstLiveRawPotentialBound.firstWindowRawGap rate rewards C_star C_h omega S ∂mu)

end Bandits.Support.ReferenceFirstLiveOriginalCalendarRoundedComparison

end
