/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionOldConditionalWeightedEnergyDrift

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Original OLD comparator rounding bounds

This module proves the lower floor estimate for the actual retained OLD
recorder on the original source law. The comparator uses the same whole reward
table, incoming payload, retained gate, and fixed supported product set as the
OLD conditional weighted-energy step.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionOldOriginalComparatorRounding

open ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ActualInitializationPhysicalStep (GridRewardTable)
open ContinuousLearningRows (TimeControl)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefixFiltration)

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)

local instance sourceInputMeasurableSpace : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Option α) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

local notation "μ" => sourceInputLaw p

private theorem integrable_of_bounded_measurable
    {f : SourceInput p → ℝ} (hf : Measurable f) (C : ℝ)
    (_hC : 0 ≤ C) (hbound : ∀ z, ‖f z‖ ≤ C) : Integrable f μ := by
  have hconst : Integrable (fun _ : SourceInput p => C) μ := integrable_const C
  refine hconst.mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with z
  simpa [Real.norm_eq_abs, abs_of_nonneg _hC] using hbound z

/-- The original retained OLD raw comparator arrival over the fixed set. -/
public def oldComparatorRaw (t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) (z : SourceInput p) : ℝ :=
  ∑ i ∈ S.1,
    (ReferenceFirstCollectionOldCalendarExponentialStep.G
      rate rewards C_star C_h t).indicator
        (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
          rate rewards C_star C_h t i) z

/-- The original rounded comparator reward on the retained OLD gate. -/
public def oldComparatorRounded (t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) (z : SourceInput p) : ℝ :=
  (ReferenceFirstCollectionOldCalendarExponentialStep.G
    rate rewards C_star C_h t).indicator (fun _ =>
      ∑ i ∈ S.1,
        ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) z

/-- The literal OLD floor loss from the same incoming rates and gate. -/
public def oldComparatorFloorLoss (t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) (z : SourceInput p) : ℝ :=
  (ReferenceFirstCollectionOldCalendarExponentialStep.G
    rate rewards C_star C_h t).indicator (fun z =>
      ∑ i ∈ S.1,
        (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
          rate rewards C_star C_h t z).getD (fun _ => 0) i /
            (rate.eta.val * (D p : ℝ))) z

private theorem payload_on_gate (t : Fin p.T)
    (i : Fin p.K) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.G
      rate rewards C_star C_h t) :
    ∃ payload : ReferenceActivePhysicalStep.Payload rate,
      ReferenceFirstCollectionOldRecorderFoundation.incomingPayload?
        rate rewards C_star C_h t z = some payload ∧
      ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
        rate rewards C_star C_h t z = some payload.rate ∧
      ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
        rate rewards C_star C_h t i z = some
          (QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
            (payload.rate i)
            (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i)) ∧
      0 < payload.rate i ∧ payload.rate i ≤ 1 := by
  have hzE : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.E
      rate rewards C_star C_h t := by
    have h := hz
    change z ∈
      (ReferenceFirstCollectionOldCalendarExponentialStep.E
        rate rewards C_star C_h t ∩
        ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t) ∩
      {z | ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled?
        rate rewards C_star C_h t z = some true} at h
    exact h.1.1
  obtain ⟨payload, c, hp, hc, hrate, _hmarker⟩ :=
    ReferenceFirstCollectionOldRecorderFoundation.oldCell_recordingMap
      rate rewards C_star C_h t z hzE
  have hrateMap := ReferenceFirstCollectionOldRecorderFoundation.oldCell_rates_eq_incoming
    rate rewards C_star C_h t z hzE
  rw [hc, Option.map_some, hrate] at hrateMap
  have hAmplitude := show
      ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
        rate rewards C_star C_h t i z = some
          (QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
            (payload.rate i)
            (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i)) by
    simp [ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?, hp]
  have hratePos :=
    (CanonicalRecordingRates.beta_pos p rate.eta.property).trans_le
      (AssignmentStartPayload.Input.beta_le_rate payload i)
  have hmNat : 1 ≤ p.m := le_trans (by decide) p.two_le_m
  have hKNat : 1 ≤ p.K :=
    Nat.succ_le_iff.mpr (ConstructorDimensions.K_pos p)
  have hm : (1 : ℝ) ≤ (p.m : ℝ) := by exact_mod_cast hmNat
  have hK : (1 : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast hKNat
  have hmK : (1 : ℝ) ≤ (p.m : ℝ) * (p.K : ℝ) := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ (p.m : ℝ) * 1 := mul_le_mul_of_nonneg_right hm (by norm_num)
      _ ≤ (p.m : ℝ) * (p.K : ℝ) :=
        mul_le_mul_of_nonneg_left hK (by positivity)
  have hcap : (1 : ℝ) ≤ 16 * (p.m : ℝ) * (p.K : ℝ) := by
    calc
      1 ≤ (p.m : ℝ) * (p.K : ℝ) := hmK
      _ = 1 * ((p.m : ℝ) * (p.K : ℝ)) := by ring
      _ ≤ 16 * ((p.m : ℝ) * (p.K : ℝ)) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = 16 * (p.m : ℝ) * (p.K : ℝ) := by ring
  have hcapPos : 0 < 16 * (p.m : ℝ) * (p.K : ℝ) :=
    lt_of_lt_of_le zero_lt_one hcap
  have hrateLeOne : payload.rate i ≤ 1 := by
    exact (AssignmentStartPayload.Input.rate_le_source_bound payload i).trans
      ((div_le_one hcapPos).2 hcap)
  exact ⟨payload, hp, hrateMap.symm, hAmplitude, hratePos, hrateLeOne⟩

/-- The accepted OLD conditional coefficient is nonnegative and bounded above
by the original rounded reward, then by one, on the same retained gate. -/
public theorem old_retained_moment_one_reward_bounds
    (t : Fin p.T) (i : Fin p.K) (z : SourceInput p) :
    0 ≤ ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
        rate rewards C_star C_h t i z ∧
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
        rate rewards C_star C_h t i z ≤
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t).indicator
            (fun _ => ReferenceFirstCollectionOldRecorderFoundation.roundedReward
              rewards t i) z ∧
      (ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t).indicator
          (fun _ => ReferenceFirstCollectionOldRecorderFoundation.roundedReward
            rewards t i) z ≤
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t).indicator (fun _ => (1 : ℝ)) z := by
  let g := ReferenceFirstCollectionOldCalendarExponentialStep.G
    rate rewards C_star C_h t
  by_cases hz : z ∈ g
  · have hzE : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.E
        rate rewards C_star C_h t := by
      have h := hz
      change z ∈
        (ReferenceFirstCollectionOldCalendarExponentialStep.E
          rate rewards C_star C_h t ∩
          ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t) ∩
        {z | ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled?
          rate rewards C_star C_h t z = some true} at h
      exact h.1.1
    have hz' : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t := by simpa [g] using hz
    obtain ⟨payload, hp, hnonneg, hmean, hreward⟩ :=
      ReferenceFirstCollectionOldRecorderFoundation.oldCell_firstMean_le_reward
        rate rewards C_star C_h t i z hzE
    have hmoment :
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
          rate rewards C_star C_h t i z = payload.rate i *
            (ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
              rate rewards C_star C_h t i z).getD 0 := by
      simp [ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne,
        ReferenceFirstCollectionOldRecorderFoundation.incomingRates?, hp, g, hz]
    have hrewardLe :=
      (ReferenceFirstCollectionOldRecorderFoundation.roundedReward_bounds rewards t i).2
    refine ⟨?_, ?_, ?_⟩
    · rw [hmoment]
      exact hnonneg
    · rw [hmoment]
      simpa only [Set.indicator_of_mem hz'] using hmean
    · simp only [Set.indicator_of_mem hz']
      exact hrewardLe
  · have hmoment :
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
          rate rewards C_star C_h t i z = 0 := by
      simp [ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne, g, hz]
    have hreward :
        (g.indicator (fun _ =>
          ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) z) = 0 :=
      by simp [g, hz]
    have hone : (g.indicator (fun _ => (1 : ℝ)) z) = 0 :=
      by simp [g, hz]
    rw [hmoment, hreward, hone]
    exact ⟨le_rfl, le_rfl, le_rfl⟩

/-- The retained per-arm OLD coefficient includes the sharp explicit floor
loss from its actual incoming rate. -/
public theorem old_retained_arm_lower
    (t : Fin p.T) (i : Fin p.K) (z : SourceInput p) :
    (ReferenceFirstCollectionOldCalendarExponentialStep.G
      rate rewards C_star C_h t).indicator (fun z =>
        ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i -
          (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
            rate rewards C_star C_h t z).getD (fun _ => 0) i /
              (rate.eta.val * (D p : ℝ))) z ≤
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
        rate rewards C_star C_h t i z := by
  let g := ReferenceFirstCollectionOldCalendarExponentialStep.G
    rate rewards C_star C_h t
  by_cases hz : z ∈ g
  · obtain ⟨payload, hp, hrate, hamp, hxi, _hxiLe⟩ :=
      payload_on_gate rate rewards C_star C_h t i z hz
    have hz' : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t := by simpa [g] using hz
    have hxiEq :
        (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
          rate rewards C_star C_h t z).getD (fun _ => 0) i = payload.rate i := by
      rw [hrate]
      rfl
    have hampVal :
        (ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
          rate rewards C_star C_h t i z).getD 0 =
            QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
              (payload.rate i)
              (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) := by
      rw [hamp]
      rfl
    have hD : 0 < D p := ConstructorDimensions.D_pos p
    have heta : 0 < rate.eta.val := rate.eta.property
    have hr := ReferenceFirstCollectionOldRecorderFoundation.roundedReward_bounds
      rewards t i
    have hfloor := QuantizedRecordingMoments.quantizedIndex_floorBounds
      (D p) rate.eta.val (payload.rate i)
      (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i)
      hD heta hxi hr.1
    have hnum :
        (D p : ℝ) * rate.eta.val *
            ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i <
          payload.rate i *
            ((QuantizedRecordingMoments.quantizedIndex (D p) rate.eta.val
              (payload.rate i)
              (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) : ℝ) + 1) := by
      nlinarith only [(div_lt_iff₀ hxi).mp hfloor.2]
    have hnum' :
        (D p : ℝ) * rate.eta.val *
            ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i -
            payload.rate i <
          payload.rate i *
            (QuantizedRecordingMoments.quantizedIndex (D p) rate.eta.val
              (payload.rate i)
              (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) : ℝ) := by
      calc
        _ < payload.rate i *
            ((QuantizedRecordingMoments.quantizedIndex (D p) rate.eta.val
              (payload.rate i)
              (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) : ℝ) + 1) -
              payload.rate i := sub_lt_sub_right hnum _
        _ = _ := by ring
    have hnum'' :
        (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) *
            rate.eta.val * (D p : ℝ) - payload.rate i <
          payload.rate i *
            (QuantizedRecordingMoments.quantizedIndex (D p) rate.eta.val
              (payload.rate i)
              (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) : ℝ) := by
      calc
        _ = (D p : ℝ) * rate.eta.val *
            ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i -
              payload.rate i := by ring
        _ < _ := hnum'
    have hidx :
        (QuantizedRecordingMoments.quantizedIndex (D p) rate.eta.val
          (payload.rate i)
          (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) : ℝ) =
          (Nat.floor
            (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i *
              rate.eta.val * (D p : ℝ) / payload.rate i) : ℝ) := by
      unfold QuantizedRecordingMoments.quantizedIndex
      apply congrArg (fun n : ℕ => (n : ℝ))
      apply congrArg Nat.floor
      ring
    have hden : 0 < rate.eta.val * (D p : ℝ) :=
      mul_pos heta (Nat.cast_pos.mpr hD)
    have hscaled :
        ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i -
            payload.rate i / (rate.eta.val * (D p : ℝ)) <
          payload.rate i * QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
            (payload.rate i)
            (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) := by
      rw [QuantizedRecordingMoments.quantizedValue,
        QuantizedRecordingMoments.quantizedIndex]
      field_simp [ne_of_gt hden]
      rw [hidx] at hnum''
      linarith [hnum'']
    simp only [ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne,
      Set.indicator_of_mem hz']
    rw [hxiEq, hampVal]
    exact le_of_lt hscaled
  · have hz' : z ∉ ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t := by simpa [g] using hz
    simp only [ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne,
      Set.indicator_of_notMem hz']
    exact le_rfl

private theorem product_set_card (S : ProductSetLaw.ProductSet p.K p.m) :
    S.1.card = p.m := by
  exact (Finset.mem_powersetCard.mp S.2).2

private theorem incoming_rate_value_measurable (control0 : TimeControl p)
    (t : Fin p.T) (i : Fin p.K) :
    Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (fun z =>
        (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
          rate rewards C_star C_h t z).getD (fun _ => 0) i) := by
  let e := Equiv.optionEquivSumPUnit (Fin p.K → ℝ)
  have he : Measurable e := comap_measurable _
  have hs : Measurable (Sum.elim (fun v : Fin p.K → ℝ => v i)
      (fun _ : PUnit => (0 : ℝ))) :=
    (measurable_pi_apply i).sumElim measurable_const
  have h := hs.comp (he.comp
    (ReferenceFirstCollectionOldRecorderFoundation.incomingRates_measurable
      rate rewards C_star C_h control0 t))
  convert h using 1
  funext z
  dsimp only [Function.comp_apply]
  cases ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
      rate rewards C_star C_h t z <;> rfl

private theorem old_gate_measurable_set (control0 : TimeControl p) (t : Fin p.T) :
    MeasurableSet
      (ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t) := by
  exact (sourcePrefixFiltration control0).le' (t.val + 1) _
    (ReferenceFirstCollectionOldCalendarExponentialStep.measurableSet_G
      rate rewards C_star C_h control0 t)

/-- Original-law integrability of the retained raw comparator sum. -/
public theorem old_comparator_raw_integrable (control0 : TimeControl p) (t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (oldComparatorRaw rate rewards C_star C_h t S) (sourceInputLaw p) := by
  unfold oldComparatorRaw
  apply integrable_finsetSum
  intro i hi
  exact (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_retainedRaw_sq_condExp
    rate rewards C_star C_h control0 t i).2.2.2.2.1

/-- Original-law integrability of the rounded OLD comparator readout. -/
public theorem old_comparator_rounded_integrable (control0 : TimeControl p)
    (t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (oldComparatorRounded rate rewards C_star C_h t S) (sourceInputLaw p) := by
  have hF :=
    ReferenceFirstCollectionOldCalendarExponentialStep.measurableSet_G
      rate rewards C_star C_h control0 t
  have hmeas :
      Measurable[sourcePrefixFiltration control0 (t.val + 1)]
        (oldComparatorRounded rate rewards C_star C_h t S) := by
    unfold oldComparatorRounded
    exact Measurable.indicator measurable_const hF
  have hle := (sourcePrefixFiltration control0).le' (t.val + 1)
  have hcard := product_set_card S
  have hsumNonneg :
      0 ≤ ∑ i ∈ S.1,
        ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i :=
    Finset.sum_nonneg fun i hi =>
      (ReferenceFirstCollectionOldRecorderFoundation.roundedReward_bounds rewards t i).1
  have hsumUpper :
      (∑ i ∈ S.1,
        ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) ≤
          (p.m : ℝ) := by
    calc
      _ ≤ ∑ i ∈ S.1, (1 : ℝ) :=
        Finset.sum_le_sum fun i hi =>
          (ReferenceFirstCollectionOldRecorderFoundation.roundedReward_bounds
            rewards t i).2
      _ = (S.1.card : ℝ) := by simp
      _ = (p.m : ℝ) := by exact_mod_cast hcard
  apply integrable_of_bounded_measurable
    (Measurable.mono hmeas hle le_rfl) (p.m : ℝ) (by positivity)
  intro z
  by_cases hz : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.G
      rate rewards C_star C_h t
  · simp only [oldComparatorRounded, Set.indicator_of_mem hz,
      Real.norm_eq_abs, abs_of_nonneg hsumNonneg]
    exact hsumUpper
  · simp only [oldComparatorRounded, Set.indicator_of_notMem hz, norm_zero]
    positivity

private theorem old_comparator_floor_loss_measurable (control0 : TimeControl p)
    (t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m) :
    Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (oldComparatorFloorLoss rate rewards C_star C_h t S) := by
  have hterm (i : Fin p.K) (_hi : i ∈ S.1) :
      Measurable[sourcePrefixFiltration control0 (t.val + 1)]
        (fun z =>
          (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
            rate rewards C_star C_h t z).getD (fun _ => 0) i /
              (rate.eta.val * (D p : ℝ))) :=
    (incoming_rate_value_measurable rate rewards C_star C_h control0 t i).div_const _
  unfold oldComparatorFloorLoss
  exact Measurable.indicator
    (Finset.measurable_fun_sum _ hterm)
    (ReferenceFirstCollectionOldCalendarExponentialStep.measurableSet_G
      rate rewards C_star C_h control0 t)

/-- The explicit floor loss is nonnegative and bounded by its retained-event
mass coefficient, with no horizon-wide budget spent at this date. -/
public theorem old_comparator_floor_loss_bounds
    (t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m) (z : SourceInput p) :
    0 ≤ oldComparatorFloorLoss rate rewards C_star C_h t S z ∧
      oldComparatorFloorLoss rate rewards C_star C_h t S z ≤
        (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) *
          (ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h t).indicator (fun _ => (1 : ℝ)) z := by
  let g := ReferenceFirstCollectionOldCalendarExponentialStep.G
    rate rewards C_star C_h t
  let scale := rate.eta.val * (D p : ℝ)
  have hscale : 0 < scale :=
    mul_pos rate.eta.property (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))
  have hcard := product_set_card S
  by_cases hz : z ∈ g
  · have hxi i (hi : i ∈ S.1) :
        0 ≤ (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
          rate rewards C_star C_h t z).getD (fun _ => 0) i ∧
        (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
          rate rewards C_star C_h t z).getD (fun _ => 0) i ≤ 1 := by
      obtain ⟨payload, _hp, hrate, _hamp, hpos, hle⟩ :=
        payload_on_gate rate rewards C_star C_h t i z hz
      have hEq :
          (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
            rate rewards C_star C_h t z).getD (fun _ => 0) i = payload.rate i := by
        rw [hrate]
        rfl
      rw [hEq]
      exact ⟨hpos.le, hle⟩
    have hz' : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t := by simpa [g] using hz
    have hsumNonneg :
        0 ≤ ∑ i ∈ S.1,
          (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
            rate rewards C_star C_h t z).getD (fun _ => 0) i :=
      Finset.sum_nonneg fun i hi => (hxi i hi).1
    have hsumUpper :
        (∑ i ∈ S.1,
          (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
            rate rewards C_star C_h t z).getD (fun _ => 0) i) ≤ (p.m : ℝ) := by
      calc
        _ ≤ ∑ i ∈ S.1, (1 : ℝ) :=
          Finset.sum_le_sum fun i hi => (hxi i hi).2
        _ = (S.1.card : ℝ) := by simp
        _ = (p.m : ℝ) := by exact_mod_cast hcard
    constructor
    · simp only [oldComparatorFloorLoss, Set.indicator_of_mem hz']
      calc
        0 ≤ (∑ i ∈ S.1,
          (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
            rate rewards C_star C_h t z).getD (fun _ => 0) i) / scale :=
          div_nonneg hsumNonneg hscale.le
        _ = ∑ i ∈ S.1,
            (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
              rate rewards C_star C_h t z).getD (fun _ => 0) i / scale := by
          rw [Finset.sum_div]
    · simp only [oldComparatorFloorLoss, Set.indicator_of_mem hz']
      calc
        ∑ i ∈ S.1,
            (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
              rate rewards C_star C_h t z).getD (fun _ => 0) i / scale =
          (∑ i ∈ S.1,
            (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
              rate rewards C_star C_h t z).getD (fun _ => 0) i) / scale := by
          rw [Finset.sum_div]
      _ ≤ (p.m : ℝ) / scale := div_le_div_of_nonneg_right hsumUpper hscale.le
      _ = (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) * 1 := by
        simp [scale]
  · have hz' : z ∉ ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t := by simpa [g] using hz
    simp only [oldComparatorFloorLoss, Set.indicator_of_notMem hz']
    exact ⟨le_rfl, by simp⟩

/-- Original-law integrability of the literal OLD floor loss. -/
public theorem old_comparator_floor_loss_integrable (control0 : TimeControl p)
    (t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (oldComparatorFloorLoss rate rewards C_star C_h t S) (sourceInputLaw p) := by
  have hmeas := old_comparator_floor_loss_measurable rate rewards C_star C_h control0 t S
  have hle := (sourcePrefixFiltration control0).le' (t.val + 1)
  have hscale : 0 < rate.eta.val * (D p : ℝ) :=
    mul_pos rate.eta.property (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))
  have hbound (z : SourceInput p) :
      ‖oldComparatorFloorLoss rate rewards C_star C_h t S z‖ ≤
        (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) := by
    have hnonneg := old_comparator_floor_loss_bounds rate rewards C_star C_h t S z
    have hgate :
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t).indicator (fun _ => (1 : ℝ)) z ≤ 1 := by
      by_cases hz : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t
      · simp [Set.indicator_of_mem hz]
      · simp [Set.indicator_of_notMem hz]
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg.1]
    have hC : 0 ≤ (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) :=
      div_nonneg (Nat.cast_nonneg _) hscale.le
    calc
      oldComparatorFloorLoss rate rewards C_star C_h t S z ≤
          (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) *
            (ReferenceFirstCollectionOldCalendarExponentialStep.G
              rate rewards C_star C_h t).indicator (fun _ => (1 : ℝ)) z := hnonneg.2
      _ ≤ (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hgate hC
  apply integrable_of_bounded_measurable
    (Measurable.mono hmeas hle le_rfl)
    _ (div_nonneg (Nat.cast_nonneg _) hscale.le) hbound

/-- The datewise floor loss pays only its actual retained OLD event mass. -/
public theorem old_comparator_floor_loss_integral_le_gate_mass (control0 : TimeControl p)
    (t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z, oldComparatorFloorLoss rate rewards C_star C_h t S z ∂sourceInputLaw p) ≤
      (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) *
        (sourceInputLaw p).real
          (ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h t) := by
  let g := ReferenceFirstCollectionOldCalendarExponentialStep.G
    rate rewards C_star C_h t
  let c := (p.m : ℝ) / (rate.eta.val * (D p : ℝ))
  have hG := old_gate_measurable_set rate rewards C_star C_h control0 t
  have hi := old_comparator_floor_loss_integrable rate rewards C_star C_h control0 t S
  have hc : Integrable (g.indicator (fun _ : SourceInput p => c)) (sourceInputLaw p) :=
    (integrable_const c).indicator hG
  have hpoint (z : SourceInput p) :
      oldComparatorFloorLoss rate rewards C_star C_h t S z ≤
        g.indicator (fun _ => c) z := by
    have hb := old_comparator_floor_loss_bounds rate rewards C_star C_h t S z
    by_cases hz : z ∈ g
    · have hz' : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t := by simpa [g] using hz
      simpa [g, c, Set.indicator_of_mem hz'] using hb.2
    · have hz' : z ∉ ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t := by simpa [g] using hz
      simpa [g, c, Set.indicator_of_notMem hz'] using hb.2
  have hmono := integral_mono_ae hi hc (ae_of_all _ hpoint)
  calc
    (∫ z, oldComparatorFloorLoss rate rewards C_star C_h t S z ∂sourceInputLaw p) ≤
        ∫ z, g.indicator (fun _ => c) z ∂sourceInputLaw p := hmono
    _ = c * (sourceInputLaw p).real g := by
      rw [integral_indicator_const c hG, smul_eq_mul]
      dsimp [c]
      ring

private theorem old_comparator_coefficient_lower
    (t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m) (z : SourceInput p) :
    oldComparatorRounded rate rewards C_star C_h t S z -
        oldComparatorFloorLoss rate rewards C_star C_h t S z ≤
      ∑ i ∈ S.1,
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
          rate rewards C_star C_h t i z := by
  let g := ReferenceFirstCollectionOldCalendarExponentialStep.G
    rate rewards C_star C_h t
  by_cases hz : z ∈ g
  · have hz' : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t := by simpa [g] using hz
    simp only [oldComparatorRounded, oldComparatorFloorLoss,
      Set.indicator_of_mem hz']
    have hsumId :
        (∑ i ∈ S.1,
          ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) -
          ∑ i ∈ S.1,
            (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
              rate rewards C_star C_h t z).getD (fun _ => 0) i /
                (rate.eta.val * (D p : ℝ)) =
          ∑ i ∈ S.1,
          (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i -
            (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
              rate rewards C_star C_h t z).getD (fun _ => 0) i /
                (rate.eta.val * (D p : ℝ))) := by
      rw [Finset.sum_sub_distrib]
    have hArm (i : Fin p.K) (hi : i ∈ S.1) :
        ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i -
            (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
              rate rewards C_star C_h t z).getD (fun _ => 0) i /
                (rate.eta.val * (D p : ℝ)) ≤
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
            rate rewards C_star C_h t i z := by
      simpa only [Set.indicator_of_mem hz'] using
        old_retained_arm_lower rate rewards C_star C_h t i z
    calc
      _ = ∑ i ∈ S.1,
          (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i -
            (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
              rate rewards C_star C_h t z).getD (fun _ => 0) i /
                (rate.eta.val * (D p : ℝ))) := hsumId
      _ ≤ ∑ i ∈ S.1,
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
            rate rewards C_star C_h t i z :=
          Finset.sum_le_sum fun i hi => hArm i hi
  · have hzero (i : Fin p.K) :
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
          rate rewards C_star C_h t i z = 0 := by
      simp [ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne, g, hz]
    have hz' : z ∉ ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t := by simpa [g] using hz
    simp [oldComparatorRounded, oldComparatorFloorLoss, hzero, hz']

/-- The original OLD comparator's rounded-minus-floor readout is bounded by
the conditional expectation of its retained raw comparator, under the
original source law and the actual pre-choice source-prefix filtration. -/
public theorem old_comparator_cond_exp_rounded_sub_floor_le_raw
    (control0 : TimeControl p) (t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    oldComparatorRounded rate rewards C_star C_h t S -
        oldComparatorFloorLoss rate rewards C_star C_h t S ≤ᵐ[sourceInputLaw p]
      (sourceInputLaw p)[oldComparatorRaw rate rewards C_star C_h t S |
        sourcePrefixFiltration control0 (t.val + 1)] := by
  let F := sourcePrefixFiltration control0 (t.val + 1)
  let rawArm : Fin p.K → SourceInput p → ℝ := fun i z =>
    (ReferenceFirstCollectionOldCalendarExponentialStep.G
      rate rewards C_star C_h t).indicator
        (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
          rate rewards C_star C_h t i) z
  have hsum := condExp_finsetSum (s := S.1)
    (f := rawArm) (fun i hi =>
      (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_retainedRaw_sq_condExp
        rate rewards C_star C_h control0 t i).2.2.2.2.1) F
  have harg : oldComparatorRaw rate rewards C_star C_h t S =
      ∑ i ∈ S.1, rawArm i := by
    funext z
    simp [oldComparatorRaw, rawArm, Finset.sum_apply]
  have hsumArg :
      μ[oldComparatorRaw rate rewards C_star C_h t S | F] =ᵐ[μ]
        μ[∑ i ∈ S.1, rawArm i | F] :=
    condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun harg z)
  have hsum' := hsumArg.trans hsum
  have hce :
      μ[oldComparatorRaw rate rewards C_star C_h t S | F] =ᵐ[μ]
        (fun z => ∑ i ∈ S.1, μ[rawArm i | F] z) := by
    filter_upwards [hsum'] with z hz
    simpa only [Finset.sum_apply] using hz
  have hterms : ∀ᵐ z ∂μ, ∀ i ∈ S.1,
      μ[rawArm i | F] z =
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
          rate rewards C_star C_h t i z := by
    apply S.1.eventually_all.mpr
    intro i hi
    exact (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_retainedRaw_sq_condExp
      rate rewards C_star C_h control0 t i).1
  filter_upwards [hce, hterms] with z hcez htermsz
  rw [hcez]
  calc
    oldComparatorRounded rate rewards C_star C_h t S z -
        oldComparatorFloorLoss rate rewards C_star C_h t S z ≤
      ∑ i ∈ S.1,
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
          rate rewards C_star C_h t i z :=
      old_comparator_coefficient_lower rate rewards C_star C_h t S z
    _ = ∑ i ∈ S.1, μ[rawArm i | F] z := by
      exact Finset.sum_congr rfl fun i hi => (htermsz i hi).symm

/-- The original-law integral comparison keeps the exact datewise floor loss. -/
public theorem old_comparator_integral_rounded_le_raw_add_floor
    (control0 : TimeControl p) (t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z, oldComparatorRounded rate rewards C_star C_h t S z ∂sourceInputLaw p) ≤
      (∫ z, oldComparatorRaw rate rewards C_star C_h t S z ∂sourceInputLaw p) +
        ∫ z, oldComparatorFloorLoss rate rewards C_star C_h t S z ∂sourceInputLaw p := by
  let F := sourcePrefixFiltration control0 (t.val + 1)
  have hle := (sourcePrefixFiltration control0).le' (t.val + 1)
  have hrounded := old_comparator_rounded_integrable rate rewards C_star C_h control0 t S
  have hraw := old_comparator_raw_integrable rate rewards C_star C_h control0 t S
  have hfloor := old_comparator_floor_loss_integrable rate rewards C_star C_h control0 t S
  have hcond := old_comparator_cond_exp_rounded_sub_floor_le_raw
    rate rewards C_star C_h control0 t S
  have hleft : Integrable
      (fun z => oldComparatorRounded rate rewards C_star C_h t S z -
        oldComparatorFloorLoss rate rewards C_star C_h t S z) (sourceInputLaw p) :=
    hrounded.sub hfloor
  have hright : Integrable
      (μ[oldComparatorRaw rate rewards C_star C_h t S | F]) μ :=
    integrable_condExp (m := F)
      (f := oldComparatorRaw rate rewards C_star C_h t S)
  have hmono := integral_mono_ae hleft hright hcond
  rw [integral_sub hrounded hfloor] at hmono
  rw [integral_condExp (f := oldComparatorRaw rate rewards C_star C_h t S) hle] at hmono
  linarith

/-- The rounded, raw, and floor-loss OLD comparator calendar sums are all
integrable under the original source law. -/
public theorem old_comparator_calendar_integrable (control0 : TimeControl p)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (fun z => ∑ t : Fin p.T,
      oldComparatorRaw rate rewards C_star C_h t S z) (sourceInputLaw p) ∧
    Integrable (fun z => ∑ t : Fin p.T,
      oldComparatorRounded rate rewards C_star C_h t S z) (sourceInputLaw p) ∧
    Integrable (fun z => ∑ t : Fin p.T,
      oldComparatorFloorLoss rate rewards C_star C_h t S z) (sourceInputLaw p) := by
  refine ⟨integrable_finsetSum Finset.univ (fun t _ =>
      old_comparator_raw_integrable rate rewards C_star C_h control0 t S),
    integrable_finsetSum Finset.univ (fun t _ =>
      old_comparator_rounded_integrable rate rewards C_star C_h control0 t S),
    integrable_finsetSum Finset.univ (fun t _ =>
      old_comparator_floor_loss_integrable rate rewards C_star C_h control0 t S)⟩

/-- The calendar's total explicit floor loss is bounded by the sum of actual
retained OLD event masses, preserving shared event-mass accounting. -/
public theorem old_comparator_calendar_floor_loss_integral_le_gate_mass
    (control0 : TimeControl p) (S : ProductSetLaw.ProductSet p.K p.m) :
    (∑ t : Fin p.T,
      ∫ z, oldComparatorFloorLoss rate rewards C_star C_h t S z ∂sourceInputLaw p) ≤
      (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) *
        ∑ t : Fin p.T,
          (sourceInputLaw p).real
            (ReferenceFirstCollectionOldCalendarExponentialStep.G
              rate rewards C_star C_h t) := by
  calc
    _ ≤ ∑ t : Fin p.T,
        ((p.m : ℝ) / (rate.eta.val * (D p : ℝ)) *
          (sourceInputLaw p).real
            (ReferenceFirstCollectionOldCalendarExponentialStep.G
              rate rewards C_star C_h t)) :=
      Finset.sum_le_sum fun t _ =>
        old_comparator_floor_loss_integral_le_gate_mass
          rate rewards C_star C_h control0 t S
    _ = (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) *
        ∑ t : Fin p.T,
          (sourceInputLaw p).real
            (ReferenceFirstCollectionOldCalendarExponentialStep.G
              rate rewards C_star C_h t) := by rw [Finset.mul_sum]

/-- Summing the original-law datewise comparison retains the explicit
floor-loss calendar sum. -/
public theorem old_comparator_calendar_integral_rounded_le_raw_add_floor
    (control0 : TimeControl p) (S : ProductSetLaw.ProductSet p.K p.m) :
    (∑ t : Fin p.T,
      ∫ z, oldComparatorRounded rate rewards C_star C_h t S z ∂sourceInputLaw p) ≤
      (∑ t : Fin p.T,
        ∫ z, oldComparatorRaw rate rewards C_star C_h t S z ∂sourceInputLaw p) +
      ∑ t : Fin p.T,
        ∫ z, oldComparatorFloorLoss rate rewards C_star C_h t S z ∂sourceInputLaw p := by
  calc
    _ ≤ ∑ t : Fin p.T,
        ((∫ z, oldComparatorRaw rate rewards C_star C_h t S z ∂sourceInputLaw p) +
          ∫ z, oldComparatorFloorLoss rate rewards C_star C_h t S z ∂sourceInputLaw p) :=
      Finset.sum_le_sum fun t _ =>
        old_comparator_integral_rounded_le_raw_add_floor
          rate rewards C_star C_h control0 t S
    _ = _ := Finset.sum_add_distrib

end Bandits.Support.ReferenceFirstCollectionOldOriginalComparatorRounding
