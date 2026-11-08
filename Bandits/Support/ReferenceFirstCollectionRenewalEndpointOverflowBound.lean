/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalEndpointExponentialMoment

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# Actual first-replacement renewal-slice overflow event bound

The event is defined by the original inclusive whole-prefix readouts on the
first-replacement slice. Its tail uses the same unnormalized renewal law,
inherited endpoint moment, and future gate masses as the actual endpoint
telescope.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open scoped Classical MeasureTheory

namespace Bandits.Support.ReferenceFirstCollectionRenewalEndpointOverflowBound

open ReferenceFirstCollectionRenewalEndpointExponentialMoment
open ReferenceFirstCollectionRenewalEndpointTelescope
open ReferenceFirstCollectionRenewalFutureExponentialIncrement
open ReferenceFirstCollectionRenewalAuxiliaryLaw

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

local notation "Z" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.Source
  rate rewards C_star C_h u t
local notation "ν" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
  rate rewards C_star C_h u t
local notation "β" => CanonicalRecordingRates.beta p rate.eta.val
local notation "cap" => (1 / (32 * rate.eta.val))

noncomputable local instance futureDateFintype :
    Fintype (ReferenceFirstCollectionRenewalEndpointExponentialMoment.FutureDate
      (p := p) t) := by
  classical
  letI : Finite (ReferenceFirstCollectionRenewalEndpointExponentialMoment.FutureDate
      (p := p) t) := by
    exact Finite.of_injective
      (fun q : ReferenceFirstCollectionRenewalEndpointExponentialMoment.FutureDate
        (p := p) t => q.1)
      (by intro x y h; exact Subtype.ext h)
  exact Fintype.ofFinite _

/-- The actual inclusive overflow event on the first-replacement renewal
slice, witnessed by a present original whole-prefix readout at a date between
the inherited entry date and the selected inclusive endpoint. -/
def actualSliceOverflowEvent (a : Fin p.K) : Set Z :=
  {z | ∃ n, t.val + 1 ≤ n ∧
    n ≤ ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointIndex
      rate rewards C_star C_h u t z ∧
    ∃ on, actualPrefixReadout rate rewards C_star C_h u t n z = some on ∧
      ((on.1 a).2 : ℝ) /
        ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters
          rate).n : ℝ) > cap}

/-- The inclusive actual overflow event is exactly the endpoint exponential
threshold event. The source endpoint retention theorem supplies the endpoint
presence and retains the detecting update, including an overflow already
present at the inherited entry date. -/
theorem actualSliceOverflow_iff_endpointEnergy (a : Fin p.K) (z : Z) :
    z ∈ actualSliceOverflowEvent rate rewards C_star C_h u t a ↔
      Real.exp (β * cap) <
        ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointEnergy
          rate rewards C_star C_h u t a z := by
  rw [actualSliceOverflowEvent]
  have hthreshold :=
    ReferenceFirstCollectionRenewalEndpointTelescope.actual_endpoint_threshold_iff
      rate rewards C_star C_h u t a z
  have hthreshold' :
      (∃ n, t.val + 1 ≤ n ∧
        n ≤ ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointIndex
          rate rewards C_star C_h u t z ∧
        ∃ on, actualPrefixReadout rate rewards C_star C_h u t n z = some on ∧
          ((on.1 a).2 : ℝ) /
            ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters
              rate).n : ℝ) > cap) ↔
      ∃ on, actualPrefixReadout rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointIndex
          rate rewards C_star C_h u t z) z = some on ∧
        ((on.1 a).2 : ℝ) /
          ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters
            rate).n : ℝ) > cap := by
    simpa [ReferenceFirstCollectionRenewalEndpointTelescope.endpointBegin,
      ReferenceFirstCollectionRenewalFutureSliceEndpoint.beginning,
      ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointIndex] using hthreshold
  change (∃ n, t.val + 1 ≤ n ∧
      n ≤ ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointIndex
        rate rewards C_star C_h u t z ∧
      ∃ on, actualPrefixReadout rate rewards C_star C_h u t n z = some on ∧
        ((on.1 a).2 : ℝ) /
          ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters
            rate).n : ℝ) > cap) ↔
      Real.exp (β * cap) <
        ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointEnergy
          rate rewards C_star C_h u t a z
  rw [hthreshold']
  have hβ : 0 < β := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hn : 0 < (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters
      rate).n := by
    change 0 < rate.n
    exact ActiveFollowerDownAcceptance.rate_n_pos p rate
  have hq : (0 : ℝ) <
      ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters
        rate).n : ℝ) := Nat.cast_pos.mpr hn
  have hscale (x : ℝ) :
      β * x / ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters
        rate).n : ℝ) =
        β * (x / ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters
          rate).n : ℝ)) := by
    field_simp [ne_of_gt hq]
  constructor
  · rintro ⟨on, hon, hover⟩
    have hon' :
        ReferenceFirstCollectionRenewalEndpointTelescope.actualPrefixReadout
          rate rewards C_star C_h u t
          (ReferenceFirstCollectionRenewalEndpointTelescope.endpointEnd
            rate rewards C_star C_h u t z) z = some on := by
      simpa [ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointIndex,
        ReferenceFirstCollectionRenewalEndpointTelescope.endpointEnd] using hon
    have henergy :
        ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointEnergy
            rate rewards C_star C_h u t a z =
          Real.exp (β * (((on.1 a).2 : ℝ) /
            ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters
              rate).n : ℝ))) := by
      simp [ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointEnergy,
        ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointIndex,
        ReferenceFirstCollectionRenewalEndpointTelescope.actualBacklogExpAt,
        ReferenceFirstCollectionRenewalEndpointTelescope.actualReadoutAt,
        ReferenceFirstCollectionRenewalEndpointTelescope.actualPrefixReadout,
        ReferenceFirstCollectionRenewalEndpointTelescope.endpointEnd,
        hon', hscale]
    rw [henergy, Real.exp_lt_exp]
    exact mul_lt_mul_of_pos_left hover hβ
  · intro hover
    have hpresent :
        (actualPrefixReadout rate rewards C_star C_h u t
          (ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointIndex
            rate rewards C_star C_h u t z) z).isSome = true := by
      change (ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointReadout
        rate rewards C_star C_h u t z).isSome = true
      exact ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointReadout_present
        rate rewards C_star C_h u t z
    cases hread : actualPrefixReadout rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointIndex
          rate rewards C_star C_h u t z) z with
    | none => simp [hread] at hpresent
    | some on =>
      have hread' :
          ReferenceFirstCollectionRenewalEndpointTelescope.actualPrefixReadout
            rate rewards C_star C_h u t
            (ReferenceFirstCollectionRenewalEndpointTelescope.endpointEnd
              rate rewards C_star C_h u t z) z = some on := by
        simpa [ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointIndex,
          ReferenceFirstCollectionRenewalEndpointTelescope.endpointEnd] using hread
      have henergy :
          ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointEnergy
              rate rewards C_star C_h u t a z =
            Real.exp (β * (((on.1 a).2 : ℝ) /
              ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters
                rate).n : ℝ))) := by
        simp [ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointEnergy,
          ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointIndex,
          ReferenceFirstCollectionRenewalEndpointTelescope.actualBacklogExpAt,
          ReferenceFirstCollectionRenewalEndpointTelescope.actualReadoutAt,
          ReferenceFirstCollectionRenewalEndpointTelescope.actualPrefixReadout,
          ReferenceFirstCollectionRenewalEndpointTelescope.endpointEnd,
          hread', hscale]
      rw [henergy, Real.exp_lt_exp] at hover
      have hratio := lt_of_mul_lt_mul_left hover (le_of_lt hβ)
      exact ⟨on, rfl, hratio⟩

/-- The literal actual first-slice overflow event is measurable, by its
internal equivalence with the measurable endpoint energy threshold. -/
theorem measurable_actualSliceOverflowEvent (a : Fin p.K)
    (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSet (actualSliceOverflowEvent rate rewards C_star C_h u t a) := by
  have hevent : actualSliceOverflowEvent rate rewards C_star C_h u t a =
      {z : Z | Real.exp (β * cap) <
        ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointEnergy
          rate rewards C_star C_h u t a z} := by
    ext z
    exact actualSliceOverflow_iff_endpointEnergy rate rewards C_star C_h u t a z
  rw [hevent]
  exact measurableSet_lt measurable_const
    (ReferenceFirstCollectionRenewalEndpointExponentialMoment.measurable_endpointEnergy
      rate rewards C_star C_h u t a control0)

/-- Markov's inequality bounds the actual inclusive overflow event by the
inherited entry moment and the sharp sum of actual future-gate masses under the
same finite, possibly zero, unnormalized renewal law. -/
theorem actualSliceOverflow_real_le (a : Fin p.K)
    (control0 : ContinuousLearningRows.TimeControl p) :
    (ν).real (actualSliceOverflowEvent rate rewards C_star C_h u t a) ≤
      Real.exp (-β * cap) *
        ((∫ z, ReferenceFirstCollectionRenewalEndpointExponentialMoment.entryEnergy
            rate rewards C_star C_h u t a z ∂ν) +
          ∑ q : ReferenceFirstCollectionRenewalEndpointExponentialMoment.FutureDate
              (p := p) t,
            (ν).real (Gfuture rate rewards C_star C_h u t q.1 q.2)) := by
  let ε : ℝ := Real.exp (β * cap)
  have hε : 0 < ε := Real.exp_pos _
  have hn : 0 ≤ᵐ[ν]
      (ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointEnergy
        rate rewards C_star C_h u t a) := by
    filter_upwards with z
    exact Real.exp_nonneg _
  have hint :=
    ReferenceFirstCollectionRenewalEndpointExponentialMoment.integrable_endpointEnergy
      rate rewards C_star C_h u t a control0
  have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg hn hint ε
  have hsubset : actualSliceOverflowEvent rate rewards C_star C_h u t a ⊆
      {z : Z | ε ≤
        ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointEnergy
          rate rewards C_star C_h u t a z} := by
    intro z hz
    change ε ≤ _
    have hstrict :=
      (actualSliceOverflow_iff_endpointEnergy rate rewards C_star C_h u t a z).mp hz
    exact hstrict.le
  have hdiv :
      (ν).real {z : Z | ε ≤
        ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointEnergy
          rate rewards C_star C_h u t a z} ≤
        (∫ z, ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointEnergy
          rate rewards C_star C_h u t a z ∂ν) / ε := by
    apply (le_div_iff₀ hε).2
    simpa [mul_comm] using hmarkov
  calc
    (ν).real (actualSliceOverflowEvent rate rewards C_star C_h u t a) ≤
        (ν).real {z : Z | ε ≤
          ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointEnergy
            rate rewards C_star C_h u t a z} :=
      MeasureTheory.measureReal_mono hsubset
    _ ≤ (∫ z, ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointEnergy
        rate rewards C_star C_h u t a z ∂ν) / ε := hdiv
    _ = Real.exp (-β * cap) *
        (∫ z, ReferenceFirstCollectionRenewalEndpointExponentialMoment.endpointEnergy
          rate rewards C_star C_h u t a z ∂ν) := by
      simp [ε, div_eq_mul_inv, Real.exp_neg, mul_comm]
    _ ≤ Real.exp (-β * cap) *
        ((∫ z, ReferenceFirstCollectionRenewalEndpointExponentialMoment.entryEnergy
            rate rewards C_star C_h u t a z ∂ν) +
          ∑ q : ReferenceFirstCollectionRenewalEndpointExponentialMoment.FutureDate
              (p := p) t,
            (ν).real (Gfuture rate rewards C_star C_h u t q.1 q.2)) :=
      mul_le_mul_of_nonneg_left
        (ReferenceFirstCollectionRenewalEndpointExponentialMoment.integral_endpointEnergy_le
          rate rewards C_star C_h u t a control0)
        (Real.exp_nonneg _)

/-- Finite-arm union bound for the actual first-replacement slice overflow
event. Each arm keeps its own inherited entry energy, and every summand uses
the same original renewal law and actual future gates. -/
theorem exists_arm_actualSliceOverflow_real_le
    (control0 : ContinuousLearningRows.TimeControl p) :
    (ν).real {z : Z | ∃ a : Fin p.K,
      z ∈ actualSliceOverflowEvent rate rewards C_star C_h u t a} ≤
      Real.exp (-β * cap) *
        ((∑ a : Fin p.K,
            ∫ z, ReferenceFirstCollectionRenewalEndpointExponentialMoment.entryEnergy
              rate rewards C_star C_h u t a z ∂ν) +
          ∑ _arm : Fin p.K,
            ∑ q : ReferenceFirstCollectionRenewalEndpointExponentialMoment.FutureDate
                (p := p) t,
              (ν).real (Gfuture rate rewards C_star C_h u t q.1 q.2)) := by
  let ε : ℝ := Real.exp (-β * cap)
  calc
    (ν).real {z : Z | ∃ a : Fin p.K,
        z ∈ actualSliceOverflowEvent rate rewards C_star C_h u t a} =
      (ν).real (⋃ a : Fin p.K,
        actualSliceOverflowEvent rate rewards C_star C_h u t a) := by
          congr 1
          ext z
          simp
    _ ≤ ∑ a : Fin p.K,
        (ν).real (actualSliceOverflowEvent rate rewards C_star C_h u t a) :=
      MeasureTheory.measureReal_iUnion_fintype_le _
    _ ≤ ∑ a : Fin p.K,
        ε * ((∫ z,
            ReferenceFirstCollectionRenewalEndpointExponentialMoment.entryEnergy
              rate rewards C_star C_h u t a z ∂ν) +
          ∑ q : ReferenceFirstCollectionRenewalEndpointExponentialMoment.FutureDate
              (p := p) t,
            (ν).real (Gfuture rate rewards C_star C_h u t q.1 q.2)) := by
      apply Finset.sum_le_sum
      intro a ha
      exact actualSliceOverflow_real_le rate rewards C_star C_h u t a control0
    _ = ε *
        ((∑ a : Fin p.K,
            ∫ z, ReferenceFirstCollectionRenewalEndpointExponentialMoment.entryEnergy
              rate rewards C_star C_h u t a z ∂ν) +
            ∑ _arm : Fin p.K,
            ∑ q : ReferenceFirstCollectionRenewalEndpointExponentialMoment.FutureDate
                (p := p) t,
              (ν).real (Gfuture rate rewards C_star C_h u t q.1 q.2)) := by
      calc
        (∑ a : Fin p.K,
            ε * ((∫ z,
                ReferenceFirstCollectionRenewalEndpointExponentialMoment.entryEnergy
                  rate rewards C_star C_h u t a z ∂ν) +
              ∑ q : ReferenceFirstCollectionRenewalEndpointExponentialMoment.FutureDate
                  (p := p) t,
                (ν).real (Gfuture rate rewards C_star C_h u t q.1 q.2))) =
            ε * (∑ a : Fin p.K,
              ((∫ z, ReferenceFirstCollectionRenewalEndpointExponentialMoment.entryEnergy
                  rate rewards C_star C_h u t a z ∂ν) +
                ∑ q : ReferenceFirstCollectionRenewalEndpointExponentialMoment.FutureDate
                    (p := p) t,
                  (ν).real (Gfuture rate rewards C_star C_h u t q.1 q.2))) := by
          rw [Finset.mul_sum]
        _ = ε *
            ((∑ a : Fin p.K,
                ∫ z, ReferenceFirstCollectionRenewalEndpointExponentialMoment.entryEnergy
                  rate rewards C_star C_h u t a z ∂ν) +
              ∑ a : Fin p.K,
                ∑ q : ReferenceFirstCollectionRenewalEndpointExponentialMoment.FutureDate
                    (p := p) t,
                  (ν).real (Gfuture rate rewards C_star C_h u t q.1 q.2)) := by
          rw [Finset.sum_add_distrib]

end Bandits.Support.ReferenceFirstCollectionRenewalEndpointOverflowBound

end
