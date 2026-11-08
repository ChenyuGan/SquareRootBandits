/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalFutureRetainedMoments
public import Bandits.Support.ReferenceFirstCollectionCurrentExponentialIncrement

import Mathlib.Tactic

/-!
# Future-date retained exponential increment on the renewal source

The gate uses the actual enabled future recording parameters and the existing
optional prior readout. The increment is evaluated on the original, unnormalized
renewal source law and preserves absent, disabled, overflow, and zero-arrival
branches.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open scoped Classical MeasureTheory

namespace Bandits.Support.ReferenceFirstCollectionRenewalFutureExponentialIncrement

open ReferenceFirstCollectionRenewalFutureRetainedMoments
open ReferenceFirstCollectionRenewalFutureRecordingLaw
open ReferenceFirstCollectionRenewalFutureControlLaw
open ReferenceFirstCollectionRenewalAuxiliaryLaw
open ReferenceFirstCollectionRenewalFutureFirstReplacementView
open ReferenceSourcePrefixHistoryFiltration

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

local notation "Z" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.Source
  rate rewards C_star C_h u t
local notation "ν" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
  rate rewards C_star C_h u t
local notation "Q" => _root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val

private theorem measurable_option_elim {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (f : α → β) (hf : Measurable f) (b : β) :
    Measurable (fun o : Option α => o.elim b f) := by
  have hsum : Measurable (fun o : Option α => Equiv.optionEquivSumPUnit α o) :=
    comap_measurable _
  convert (hf.sumElim measurable_const).comp hsum using 1
  funext o
  cases o <;> rfl

/-- The actual future retained gate: future parameters are present and enabled,
and the existing optional prior readout is present and has not overflowed. -/
def Gfuture (q : Fin p.T) (hfuture : t.val + 1 < q.val) : Set Z :=
  {z | ∃ xi : Fin p.K → ℝ,
    ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture = some (true, xi) ∧
    ReferenceFirstCollectionRenewalFutureRetainedMoments.priorClear
      rate rewards C_star C_h u t q z = true}

/-- The future-date accepted raw arrival minus the current four-unit service,
only on the actual enabled, prior-clear future gate. -/
def futureIncrement (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) : Z → ℝ :=
  Set.indicator (Gfuture rate rewards C_star C_h u t q hfuture)
    (fun z => ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
      rate rewards C_star C_h u t q hfuture a z - 4)

/-- The exponential of the literal future-date increment. -/
def expFutureIncrement (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) : Z → ℝ :=
  fun z => Real.exp (beta * futureIncrement rate rewards C_star C_h u t q hfuture a z)

/-- The actual future gate is measurable in the future prior field. Its two
components are the public future-parameter projection and the actual optional
prior readout. -/
theorem measurableSet_Gfuture (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSet[futurePriorField rate rewards C_star C_h u t control0 q]
      (Gfuture rate rewards C_star C_h u t q hfuture) := by
  let params := fun z : Z =>
    ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture
  let clear := fun z : Z =>
    ReferenceFirstCollectionRenewalFutureRetainedMoments.priorClear
      rate rewards C_star C_h u t q z
  let enabled := fun z : Z => (params z).elim false Prod.fst
  let gateBit := fun z : Z => enabled z && clear z
  have hparams := ReferenceFirstCollectionRenewalFutureRecordingLaw.measurable_futureParameters
    rate rewards C_star C_h u t control0 q hfuture
  have henabled : Measurable[futurePriorField rate rewards C_star C_h u t control0 q]
      enabled := by
    simpa [enabled, params, Function.comp_def] using
      (measurable_option_elim Prod.fst measurable_fst false).comp hparams
  have hread := ReferenceFirstCollectionRenewalFutureNumericalPrefix.measurable_futurePrefixReadout
    rate rewards C_star C_h u t control0 q.val (by omega)
  have hclear : Measurable[futurePriorField rate rewards C_star C_h u t control0 q]
      clear := by
    change Measurable[futurePriorField rate rewards C_star C_h u t control0 q]
      (ReferenceFirstCollectionRenewalFutureRetainedMoments.priorClear
        rate rewards C_star C_h u t q)
    exact (measurable_of_countable (fun x : Option _ =>
        match x with
        | some (_, (false, _)) => true
        | _ => false)).comp hread
  have hgateBit : Measurable[futurePriorField rate rewards C_star C_h u t control0 q]
      gateBit := by
    simpa [gateBit, Function.comp_def] using
      (measurable_of_countable (fun x : Bool × Bool => x.1 && x.2)).comp
        (henabled.prodMk hclear)
  have hset : MeasurableSet[futurePriorField rate rewards C_star C_h u t control0 q]
      {z : Z | gateBit z = true} := hgateBit (measurableSet_singleton true)
  have heq : Gfuture rate rewards C_star C_h u t q hfuture =
      {z : Z | gateBit z = true} := by
    ext z
    simp only [Gfuture, Set.mem_ofPred_eq, gateBit, enabled, params, clear]
    cases hp : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
        rate rewards C_star C_h u t z q hfuture with
    | none => simp
    | some pair =>
        rcases pair with ⟨on, xi⟩
        cases on <;> simp
  rw [heq]
  exact hset

/-- On the gate, the increment is exactly the accepted raw arrival minus four. -/
theorem futureIncrement_eq_raw_sub_four_of_mem_Gfuture (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z)
    (hz : z ∈ Gfuture rate rewards C_star C_h u t q hfuture) :
    futureIncrement rate rewards C_star C_h u t q hfuture a z =
      ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture a z - 4 := by
  simp [futureIncrement, hz]

/-- Off the gate, the exponential increment's linear term is zero. -/
theorem futureIncrement_eq_zero_of_not_mem_Gfuture (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z)
    (hz : z ∉ Gfuture rate rewards C_star C_h u t q hfuture) :
    futureIncrement rate rewards C_star C_h u t q hfuture a z = 0 := by
  simp [futureIncrement, hz]

/-- The actual future scalar vanishes off the retained gate. This follows from
the existing test-times-amplitude factorization and the actual optional
parameter/prior-clear branches. -/
theorem futureScalar_eq_zero_of_not_mem_Gfuture (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z)
    (hz : z ∉ Gfuture rate rewards C_star C_h u t q hfuture) :
    ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
      rate rewards C_star C_h u t q hfuture a z = 0 := by
  have hamp : ReferenceFirstCollectionRenewalFutureRetainedMoments.futureAmplitude
      rate rewards C_star C_h u t q hfuture a z = 0 := by
    cases hp : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
        rate rewards C_star C_h u t z q hfuture with
    | none => simp [ReferenceFirstCollectionRenewalFutureRetainedMoments.futureAmplitude, hp]
    | some pair =>
        rcases pair with ⟨on, xi⟩
        cases on with
        | false =>
            simp [ReferenceFirstCollectionRenewalFutureRetainedMoments.futureAmplitude, hp]
        | true =>
            cases hc : ReferenceFirstCollectionRenewalFutureRetainedMoments.priorClear
                rate rewards C_star C_h u t q z with
            | false =>
                simp [ReferenceFirstCollectionRenewalFutureRetainedMoments.futureAmplitude,
                  hp, hc]
            | true =>
                exact (False.elim (hz ⟨xi, hp, hc⟩))
  rw [ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_eq_test_mul_amplitude
    rate rewards C_star C_h u t q hfuture a z, hamp]
  simp

/-- An enabled zero raw arrival is retained as the first four-unit service
update, so the exponential increment exponent is `-4`. -/
theorem futureIncrement_eq_neg_four_of_enabled_zero (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z)
    (hz : z ∈ Gfuture rate rewards C_star C_h u t q hfuture)
    (hzero : ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
      rate rewards C_star C_h u t q hfuture a z = 0) :
    futureIncrement rate rewards C_star C_h u t q hfuture a z = -4 := by
  rw [futureIncrement_eq_raw_sub_four_of_mem_Gfuture
    rate rewards C_star C_h u t q hfuture a z hz, hzero]
  ring

/-- The future raw arrival lies between zero and the reciprocal canonical
recording rate. -/
theorem futureScalar_bounds (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (control0 : ContinuousLearningRows.TimeControl p) (a : Fin p.K) (z : Z) :
    0 ≤ ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture a z ∧
      ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture a z ≤ 1 / beta :=
  ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_bounds
    rate rewards C_star C_h u t q hfuture control0 a z

/-- The scaled future raw arrival belongs to the unit interval for the convex
exponential chord. -/
theorem beta_mul_futureScalar_bounds (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) (z : Z) :
    0 ≤ beta * ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture a z ∧
      beta * ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture a z ≤ 1 := by
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hA := futureScalar_bounds rate rewards C_star C_h u t q hfuture control0 a z
  constructor
  · exact mul_nonneg hbeta.le hA.1
  · calc
      beta * ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture a z ≤ beta * (1 / beta) :=
        mul_le_mul_of_nonneg_left hA.2 hbeta.le
      _ = 1 := by field_simp [ne_of_gt hbeta]

/-- The future increment lies between `-4` and the reciprocal canonical rate,
including off-gate points where it is zero. -/
theorem futureIncrement_bounds (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (control0 : ContinuousLearningRows.TimeControl p) (a : Fin p.K) (z : Z) :
    -4 ≤ futureIncrement rate rewards C_star C_h u t q hfuture a z ∧
      futureIncrement rate rewards C_star C_h u t q hfuture a z ≤ 1 / beta := by
  have hA := futureScalar_bounds rate rewards C_star C_h u t q hfuture control0 a z
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  by_cases hz : z ∈ Gfuture rate rewards C_star C_h u t q hfuture
  · rw [futureIncrement_eq_raw_sub_four_of_mem_Gfuture
      rate rewards C_star C_h u t q hfuture a z hz]
    constructor <;> linarith
  · rw [futureIncrement_eq_zero_of_not_mem_Gfuture
      rate rewards C_star C_h u t q hfuture a z hz]
    exact ⟨by norm_num, one_div_nonneg.mpr hbeta.le⟩

private theorem beta_mul_futureIncrement_bounds (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) (z : Z) :
    -4 * beta ≤ beta * futureIncrement rate rewards C_star C_h u t q hfuture a z ∧
      beta * futureIncrement rate rewards C_star C_h u t q hfuture a z ≤ 1 := by
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hx := futureIncrement_bounds rate rewards C_star C_h u t q hfuture control0 a z
  constructor
  · calc
      -4 * beta = beta * (-4) := by ring
      _ ≤ beta * futureIncrement rate rewards C_star C_h u t q hfuture a z :=
        mul_le_mul_of_nonneg_left hx.1 hbeta.le
  · calc
      beta * futureIncrement rate rewards C_star C_h u t q hfuture a z ≤ beta * (1 / beta) :=
        mul_le_mul_of_nonneg_left hx.2 hbeta.le
      _ = 1 := by field_simp [ne_of_gt hbeta]

/-- Deterministic exponential bounds for the actual future increment. -/
theorem expFutureIncrement_bounds (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (control0 : ContinuousLearningRows.TimeControl p) (a : Fin p.K) (z : Z) :
    Real.exp (-4 * beta) ≤ expFutureIncrement rate rewards C_star C_h u t q hfuture a z ∧
      expFutureIncrement rate rewards C_star C_h u t q hfuture a z ≤ Real.exp 1 := by
  have hx := beta_mul_futureIncrement_bounds rate rewards C_star C_h u t q hfuture
    control0 a z
  exact ⟨Real.exp_le_exp_of_le hx.1, Real.exp_le_exp_of_le hx.2⟩

/-- Ambient measurability of the future increment on the original source space. -/
theorem measurable_futureIncrement (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (control0 : ContinuousLearningRows.TimeControl p) (a : Fin p.K) :
    Measurable (futureIncrement rate rewards C_star C_h u t q hfuture a) := by
  have hA := ReferenceFirstCollectionRenewalFutureRetainedMoments.measurable_futureScalar
    rate rewards C_star C_h u t q hfuture control0 a
  have hG := measurableSet_Gfuture rate rewards C_star C_h u t q hfuture control0
  have hle := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  exact (hA.sub_const 4).indicator (hle _ hG)

/-- Ambient integrability of the future increment under the finite original
renewal source law, including a zero-mass source. -/
theorem integrable_futureIncrement (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (control0 : ContinuousLearningRows.TimeControl p) (a : Fin p.K) :
    Integrable (futureIncrement rate rewards C_star C_h u t q hfuture a) ν := by
  have hA := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_integrable
    rate rewards C_star C_h u t q hfuture control0 a
  have hG := measurableSet_Gfuture rate rewards C_star C_h u t q hfuture control0
  have hle := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hsub : Integrable
      (fun z : Z => ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture a z - 4) ν := by
    simpa [Pi.add_apply, sub_eq_add_neg] using hA.add (integrable_const (-4 : ℝ))
  simpa [futureIncrement] using hsub.indicator (hle _ hG)

/-- Ambient measurability of the future-date exponential. -/
theorem measurable_expFutureIncrement (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (control0 : ContinuousLearningRows.TimeControl p) (a : Fin p.K) :
    Measurable (expFutureIncrement rate rewards C_star C_h u t q hfuture a) := by
  have hx := measurable_futureIncrement rate rewards C_star C_h u t q hfuture control0 a
  have hscaled : Measurable (fun z : Z => beta *
      futureIncrement rate rewards C_star C_h u t q hfuture a z) :=
    (measurable_const : Measurable (fun _ : Z => beta)).mul hx
  change Measurable (fun z : Z => Real.exp
    (beta * futureIncrement rate rewards C_star C_h u t q hfuture a z))
  exact hscaled.exp

private theorem integrable_of_norm_le_const {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ} (hf : Measurable f)
    (c : ℝ) (hb : ∀ z, ‖f z‖ ≤ c) : Integrable f μ := by
  have hconst : Integrable (fun _ : X => c) μ := integrable_const c
  refine hconst.mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with z
  simpa using hb z

/-- The bounded future exponential is integrable under the finite, unnormalized
renewal source measure. -/
theorem integrable_expFutureIncrement (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) :
    Integrable (expFutureIncrement rate rewards C_star C_h u t q hfuture a) ν := by
  apply integrable_of_norm_le_const
    (measurable_expFutureIncrement rate rewards C_star C_h u t q hfuture control0 a)
    (Real.exp 1)
  intro z
  have h := expFutureIncrement_bounds rate rewards C_star C_h u t q hfuture control0 a z
  rw [Real.norm_eq_abs, abs_of_nonneg (le_trans (Real.exp_nonneg _) h.1)]
  exact h.2

private theorem condExp_real_const_mul (q : Fin p.T)
    (control0 : ContinuousLearningRows.TimeControl p) (c : ℝ) (f : Z → ℝ) :
    ν[(fun z : Z => c * f z) |
      futurePriorField rate rewards C_star C_h u t control0 q] =ᵐ[ν]
      (fun z => c * ν[f | futurePriorField rate rewards C_star C_h u t control0 q] z) := by
  have hscaled := condExp_smul (μ := ν) c f
    (futurePriorField rate rewards C_star C_h u t control0 q)
  have hfun : (fun z : Z => c * f z) = c • f := by
    funext z
    simp [smul_eq_mul]
  calc
    ν[(fun z : Z => c * f z) | futurePriorField rate rewards C_star C_h u t control0 q] =ᵐ[ν]
        ν[c • f | futurePriorField rate rewards C_star C_h u t control0 q] :=
      condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun hfun z)
    _ =ᵐ[ν] (fun z => c * ν[f |
        futurePriorField rate rewards C_star C_h u t control0 q] z) := by
      filter_upwards [hscaled] with z hz
      simpa only [Pi.smul_apply, smul_eq_mul] using hz

/-- Conditional convex-chord estimate for the actual future raw scalar and
its existing retained first moment. -/
theorem condExp_expFutureScalar_le_chord (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) :
    ν[(fun z : Z => Real.exp (beta *
        ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture a z)) |
      futurePriorField rate rewards C_star C_h u t control0 q] ≤ᵐ[ν]
      (fun z : Z => 1 + (Real.exp 1 - 1) * beta *
        ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
          rate rewards C_star C_h u t q hfuture a z) := by
  let A := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
    rate rewards C_star C_h u t q hfuture a
  let Mone := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
    rate rewards C_star C_h u t q hfuture a
  let scale : ℝ := (Real.exp 1 - 1) * beta
  let f : Z → ℝ := fun z => Real.exp (beta * A z)
  let affine : Z → ℝ := fun z => 1 + scale * A z
  have hAmeas : Measurable[(inferInstance : MeasurableSpace Z)] A :=
    ReferenceFirstCollectionRenewalFutureRetainedMoments.measurable_futureScalar
      rate rewards C_star C_h u t q hfuture control0 a
  have hAint := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_integrable
    rate rewards C_star C_h u t q hfuture control0 a
  have hfmeas : Measurable[(inferInstance : MeasurableSpace Z)] f := by
    have hscaled : Measurable[(inferInstance : MeasurableSpace Z)]
        (fun z : Z => beta * A z) :=
      (measurable_const : Measurable (fun _ : Z => beta)).mul hAmeas
    simpa [f] using hscaled.exp
  have hfint : Integrable f ν := by
    apply integrable_of_norm_le_const hfmeas (Real.exp 1)
    intro z
    have hbound := beta_mul_futureScalar_bounds
      rate rewards C_star C_h u t q hfuture control0 a z
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    change Real.exp (beta * A z) ≤ Real.exp 1
    exact Real.exp_le_exp_of_le hbound.2
  have hscaledInt : Integrable (fun z : Z => scale * A z) ν :=
    by simpa [smul_eq_mul] using hAint.const_mul scale
  have hAffineInt : Integrable affine ν := by
    exact (integrable_const (1 : ℝ)).add (by simpa [affine] using hscaledInt)
  have hpoint : ∀ z : Z, f z ≤ affine z := by
    intro z
    have hbound := beta_mul_futureScalar_bounds
      rate rewards C_star C_h u t q hfuture control0 a z
    have hchord := RecordedRoundMoments.exp_le_unit_chord hbound.1 hbound.2
    calc
      f z ≤ 1 + (Real.exp 1 - 1) * (beta * A z) := by simpa [f] using hchord
      _ = affine z := by dsimp [affine, scale]; ring
  have hmono := condExp_mono
    (m := futurePriorField rate rewards C_star C_h u t control0 q) hfint hAffineInt
    (Filter.Eventually.of_forall hpoint)
  have hsum := condExp_add (integrable_const (1 : ℝ)) hscaledInt
    (futurePriorField rate rewards C_star C_h u t control0 q)
  have hle := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hconst := condExp_const (μ := ν)
    (m := futurePriorField rate rewards C_star C_h u t control0 q)
    (m₀ := (inferInstance : MeasurableSpace Z)) hle (1 : ℝ)
  have hscale := condExp_real_const_mul
    rate rewards C_star C_h u t q control0 scale A
  have hAcond := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_condExp
    rate rewards C_star C_h u t q hfuture control0 a
  have hAffineEq : affine = (fun _ : Z => (1 : ℝ)) +
      (fun z : Z => scale * A z) := by
    funext z
    rfl
  filter_upwards [hmono, hsum, hscale, hAcond] with z hmono_z hsum_z hscale_z hAcond_z
  have hconstant_z := congrFun hconst z
  change ν[f | futurePriorField rate rewards C_star C_h u t control0 q] z ≤
    1 + (Real.exp 1 - 1) * beta * Mone z
  calc
    ν[f | futurePriorField rate rewards C_star C_h u t control0 q] z ≤
        ν[affine | futurePriorField rate rewards C_star C_h u t control0 q] z := hmono_z
    _ = 1 + scale * Mone z := by
      rw [show affine = (fun _ : Z => (1 : ℝ)) +
        (fun z : Z => scale * A z) from hAffineEq]
      rw [hsum_z]
      rw [Pi.add_apply, hconstant_z, hscale_z, hAcond_z]
    _ = 1 + (Real.exp 1 - 1) * beta * Mone z := by dsimp [scale]

private theorem expFutureIncrement_indicator_identity (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z) :
    expFutureIncrement rate rewards C_star C_h u t q hfuture a z =
      Real.exp (-4 * beta) * Set.indicator
        (Gfuture rate rewards C_star C_h u t q hfuture)
        (fun y : Z => Real.exp (beta *
          ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
            rate rewards C_star C_h u t q hfuture a y)) z +
      Set.indicator (Gfuture rate rewards C_star C_h u t q hfuture)ᶜ
        (fun _ : Z => (1 : ℝ)) z := by
  by_cases hz : z ∈ Gfuture rate rewards C_star C_h u t q hfuture
  · have hsplit : beta *
        (ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture a z - 4) =
        (-4 * beta) + beta *
          ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
            rate rewards C_star C_h u t q hfuture a z := by ring
    have hzComp : z ∉ (Gfuture rate rewards C_star C_h u t q hfuture)ᶜ := by
      simpa using hz
    rw [expFutureIncrement,
      futureIncrement_eq_raw_sub_four_of_mem_Gfuture
        rate rewards C_star C_h u t q hfuture a z hz,
      hsplit, Real.exp_add]
    simp [Set.indicator_of_mem hz, Set.indicator_of_notMem hzComp]
  · have hx := futureIncrement_eq_zero_of_not_mem_Gfuture
      rate rewards C_star C_h u t q hfuture a z hz
    rw [expFutureIncrement, hx]
    have hzComp : z ∈ (Gfuture rate rewards C_star C_h u t q hfuture)ᶜ := by
      simpa using hz
    simp [Set.indicator_of_notMem hz, Set.indicator_of_mem hzComp]

/-- The conditional exponential increment is at most one in the actual future
prior field, without any positive-mass, survival, or moment premise. -/
theorem condExp_expFutureIncrement_le_one (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) :
    ν[(expFutureIncrement rate rewards C_star C_h u t q hfuture a) |
      futurePriorField rate rewards C_star C_h u t control0 q] ≤ᵐ[ν]
      (fun _ : Z => 1) := by
  let gate := Gfuture rate rewards C_star C_h u t q hfuture
  let A := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
    rate rewards C_star C_h u t q hfuture a
  let f : Z → ℝ := fun z => Real.exp (beta * A z)
  let fG : Z → ℝ := Set.indicator gate f
  let fGc : Z → ℝ := Set.indicator gateᶜ (fun _ : Z => (1 : ℝ))
  let penalty : ℝ := Real.exp (-4 * beta)
  have hGfield : MeasurableSet[futurePriorField rate rewards C_star C_h u t control0 q] gate :=
    measurableSet_Gfuture rate rewards C_star C_h u t q hfuture control0
  have hle := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hGambient : @MeasurableSet Z (inferInstance : MeasurableSpace Z) gate :=
    hle _ hGfield
  have hAmeas : Measurable[(inferInstance : MeasurableSpace Z)] A :=
    ReferenceFirstCollectionRenewalFutureRetainedMoments.measurable_futureScalar
      rate rewards C_star C_h u t q hfuture control0 a
  have hfmeas : Measurable[(inferInstance : MeasurableSpace Z)] f := by
    have hscaled : Measurable[(inferInstance : MeasurableSpace Z)]
        (fun z : Z => beta * A z) :=
      (measurable_const : Measurable (fun _ : Z => beta)).mul hAmeas
    simpa [f] using hscaled.exp
  have hfint : Integrable f ν := by
    apply integrable_of_norm_le_const hfmeas (Real.exp 1)
    intro z
    have hbound := beta_mul_futureScalar_bounds
      rate rewards C_star C_h u t q hfuture control0 a z
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    change Real.exp (beta * A z) ≤ Real.exp 1
    exact Real.exp_le_exp_of_le hbound.2
  have hfGint : Integrable fG ν := by
    simpa [fG] using hfint.indicator hGambient
  have hfGcint : Integrable fGc ν := by
    simpa [fGc] using (integrable_const (1 : ℝ)).indicator hGambient.compl
  have hscaledInt : Integrable (fun z : Z => penalty * fG z) ν :=
    hfGint.const_mul penalty
  have hZdecomp : expFutureIncrement rate rewards C_star C_h u t q hfuture a =
      fun z : Z => penalty * fG z + fGc z := by
    funext z
    simpa [fG, fGc, penalty, gate] using
      expFutureIncrement_indicator_identity rate rewards C_star C_h u t q hfuture a z
  have hsum := condExp_add hscaledInt hfGcint
    (futurePriorField rate rewards C_star C_h u t control0 q)
  have hscale := condExp_real_const_mul
    rate rewards C_star C_h u t q control0 penalty fG
  have hmask := condExp_indicator (μ := ν) hfint hGfield
  have hmaskComp := condExp_indicator (μ := ν)
    (integrable_const (1 : ℝ)) hGfield.compl
  have hconst := condExp_const (μ := ν)
    (m := futurePriorField rate rewards C_star C_h u t control0 q)
    (m₀ := (inferInstance : MeasurableSpace Z)) hle (1 : ℝ)
  have hCEdecomp :
      ν[(expFutureIncrement rate rewards C_star C_h u t q hfuture a) |
        futurePriorField rate rewards C_star C_h u t control0 q] =ᵐ[ν]
        (fun z : Z => penalty * Set.indicator gate
            (fun y : Z => ν[f | futurePriorField rate rewards C_star C_h u t control0 q] y) z +
          Set.indicator gateᶜ (fun _ : Z => (1 : ℝ)) z) := by
    calc
      ν[(expFutureIncrement rate rewards C_star C_h u t q hfuture a) |
          futurePriorField rate rewards C_star C_h u t control0 q] =ᵐ[ν]
          ν[(fun z : Z => penalty * fG z + fGc z) |
            futurePriorField rate rewards C_star C_h u t control0 q] :=
        condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun hZdecomp z)
      _ =ᵐ[ν] ν[(fun z : Z => penalty * fG z) |
          futurePriorField rate rewards C_star C_h u t control0 q] +
        ν[fGc | futurePriorField rate rewards C_star C_h u t control0 q] := hsum
      _ =ᵐ[ν] (fun z : Z => penalty *
          ν[fG | futurePriorField rate rewards C_star C_h u t control0 q] z +
          ν[fGc | futurePriorField rate rewards C_star C_h u t control0 q] z) := by
        filter_upwards [hscale] with z hz
        simpa only [Pi.add_apply] using
          congrArg (fun x : ℝ => x +
            ν[fGc | futurePriorField rate rewards C_star C_h u t control0 q] z) hz
      _ =ᵐ[ν] (fun z : Z => penalty * Set.indicator gate
          (fun y : Z => ν[f |
            futurePriorField rate rewards C_star C_h u t control0 q] y) z +
            Set.indicator gateᶜ (fun _ : Z => (1 : ℝ)) z) := by
        filter_upwards [hmask, hmaskComp] with z hmask_z hmaskComp_z
        rw [hmask_z, hmaskComp_z, hconst]
  have hchord := condExp_expFutureScalar_le_chord
    rate rewards C_star C_h u t q hfuture control0 a
  have hmoment := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne_le_one
    rate rewards C_star C_h u t q hfuture control0 a
  have hscaleNonneg : 0 ≤ (Real.exp 1 - 1) * beta := by
    have he := Real.exp_one_gt_two
    exact mul_nonneg (by linarith) (CanonicalRecordingRates.beta_pos p rate.eta.property).le
  have hpenaltyPos : 0 < penalty := Real.exp_pos _
  have hscalar := ReferenceFirstCollectionCurrentExponentialIncrement.exp_neg_four_beta_chord_le_one
    rate
  filter_upwards [hCEdecomp, hchord] with z hdecomp hchord_z
  rw [hdecomp]
  by_cases hz : z ∈ gate
  · have hzComp : z ∉ gateᶜ := by simpa using hz
    simp only [Set.indicator_of_mem hz, Set.indicator_of_notMem hzComp, add_zero]
    have hMonele :
        ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
          rate rewards C_star C_h u t q hfuture a z ≤ 1 := hmoment z
    calc
      penalty * ν[f | futurePriorField rate rewards C_star C_h u t control0 q] z ≤
          penalty * (1 + (Real.exp 1 - 1) * beta *
            ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
              rate rewards C_star C_h u t q hfuture a z) :=
        mul_le_mul_of_nonneg_left hchord_z hpenaltyPos.le
      _ ≤ penalty * (1 + (Real.exp 1 - 1) * beta) := by
        apply mul_le_mul_of_nonneg_left _ hpenaltyPos.le
        have hmul := mul_le_mul_of_nonneg_left hMonele hscaleNonneg
        linarith
      _ ≤ 1 := by simpa [penalty] using hscalar
  · have hzComp : z ∈ gateᶜ := by simpa using hz
    simp [Set.indicator_of_notMem hz, Set.indicator_of_mem hzComp]

/-- Every set in the actual future prior field has exponential integral at
most its mass under the original unnormalized renewal source law. -/
theorem setIntegral_expFutureIncrement_le_measure (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) (B : Set Z)
    (hB : MeasurableSet[futurePriorField rate rewards C_star C_h u t control0 q] B) :
    (∫ z in B, expFutureIncrement rate rewards C_star C_h u t q hfuture a z ∂ν) ≤
      Measure.real ν B := by
  have hle := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hZint := integrable_expFutureIncrement
    rate rewards C_star C_h u t q hfuture control0 a
  have hconst : Integrable (fun _ : Z => (1 : ℝ)) ν := integrable_const 1
  calc
    (∫ z in B, expFutureIncrement rate rewards C_star C_h u t q hfuture a z ∂ν) =
        ∫ z in B,
          ν[(expFutureIncrement rate rewards C_star C_h u t q hfuture a) |
            futurePriorField rate rewards C_star C_h u t control0 q] z ∂ν :=
      (setIntegral_condExp hle hZint hB).symm
    _ ≤ ∫ z in B, (1 : ℝ) ∂ν :=
      setIntegral_mono_ae integrable_condExp.integrableOn hconst.integrableOn
        (condExp_expFutureIncrement_le_one
          rate rewards C_star C_h u t q hfuture control0 a)
    _ = Measure.real ν B := by
      rw [setIntegral_const]
      simp only [smul_eq_mul, mul_one]

/-- The unconditional exponential integral is bounded by the original renewal
source mass, not by a normalized probability value. -/
theorem integral_expFutureIncrement_le_mass (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) :
    (∫ z : Z, expFutureIncrement rate rewards C_star C_h u t q hfuture a z ∂ν) ≤
      Measure.real ν Set.univ := by
  rw [← setIntegral_univ]
  exact setIntegral_expFutureIncrement_le_measure
    rate rewards C_star C_h u t q hfuture control0 a Set.univ MeasurableSet.univ

private theorem priorReadout_none_of_prefixInputs_none (q : Fin p.T) (z : Z)
    (hnone : ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
      rate rewards C_star C_h u t q z = none) :
    ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
      rate rewards C_star C_h u t q z = none := by
  unfold ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs at hnone
  change ((ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
      rate rewards C_star C_h u t q.val z).mapM id).map
        (fun xs => ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run Q xs)) = none
  rw [hnone]
  rfl

private theorem priorClear_false_of_prefixInputs_none (q : Fin p.T) (z : Z)
    (hnone : ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
      rate rewards C_star C_h u t q z = none) :
    ReferenceFirstCollectionRenewalFutureRetainedMoments.priorClear
      rate rewards C_star C_h u t q z = false := by
  unfold ReferenceFirstCollectionRenewalFutureRetainedMoments.priorClear
  rw [priorReadout_none_of_prefixInputs_none rate rewards C_star C_h u t q z hnone]

private theorem priorClear_eq_of_prefixInputs (q : Fin p.T) (z : Z)
    (inputs : List (RecordedQueueRun.RoundInput p.K))
    (hinputs : ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
      rate rewards C_star C_h u t q z = some inputs) :
    ReferenceFirstCollectionRenewalFutureRetainedMoments.priorClear
      rate rewards C_star C_h u t q z =
        !((RecordedQueueRun.run Q inputs).overflow) := by
  unfold ReferenceFirstCollectionRenewalFutureRetainedMoments.priorClear
  rw [ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout_eq_of_inputs
    rate rewards C_star C_h u t q z inputs hinputs]
  cases hflag : (RecordedQueueRun.run Q inputs).overflow <;>
    simp [ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout, hflag]

private theorem futureParameters_present_from_cell (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (z : Z)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = some c) :
    ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture = some (c.enabled, c.rate) := by
  have hr := ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_readout
    rate rewards C_star C_h u t z q hfuture
  cases hv : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture with
  | none =>
      rw [hv] at hr
      simp only at hr
      have hbad : (some c : Option (RecordedQueueRun.RoundInput p.K)) = none :=
        hc.symm.trans hr.2
      cases hbad
  | some data =>
      rcases data with ⟨parameters, view, code⟩
      rw [hv] at hr
      obtain ⟨cell, snapshot, valid, hcell, hparameters, hrate, _, _, _⟩ := hr
      have hcell_eq : cell = c := Option.some.inj (hcell.symm.trans hc)
      have hparameters' : parameters = some (c.enabled, c.rate) := by
        rw [← hcell_eq]
        exact hparameters
      simp [ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters,
        hv, hparameters']

private theorem futureParameters_none_of_futureCell_none (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (z : Z)
    (hcell : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = none) :
    ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture = none := by
  cases hv : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture with
  | none => simp [ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters, hv]
  | some data =>
      rcases data with ⟨parameters, view, code⟩
      have hread := ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_readout
        rate rewards C_star C_h u t z q hfuture
      rw [hv] at hread
      obtain ⟨c, snapshot, valid, hreadCell, hparameters, hrate, _, _, _⟩ := hread
      have hbad : (some c : Option (RecordedQueueRun.RoundInput p.K)) = none :=
        hreadCell.symm.trans hcell
      cases hbad

/-- The absent whole optional prefix has zero raw scalar and zero increment. -/
theorem futureIncrement_zero_of_prefix_absent (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z)
    (hnone : ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
      rate rewards C_star C_h u t q z = none) :
    ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture a z = 0 ∧
      futureIncrement rate rewards C_star C_h u t q hfuture a z = 0 := by
  have hA := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_zero_of_prefix_absent
    rate rewards C_star C_h u t q hfuture a z hnone
  have hclear := priorClear_false_of_prefixInputs_none rate rewards C_star C_h u t q z hnone
  have hnot : z ∉ Gfuture rate rewards C_star C_h u t q hfuture := by
    rintro ⟨xi, hparams, hprior⟩
    rw [hclear] at hprior
    cases hprior
  exact ⟨hA.1, futureIncrement_eq_zero_of_not_mem_Gfuture
    rate rewards C_star C_h u t q hfuture a z hnot⟩

/-- An absent first-replacement physical cell keeps its optional marker absent
and contributes zero scalar and increment. -/
theorem futureIncrement_zero_of_slice_absent (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z)
    (hcell : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = none) :
    ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture a z = 0 ∧
      futureIncrement rate rewards C_star C_h u t q hfuture a z = 0 := by
  have hA := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_zero_of_slice_absent
    rate rewards C_star C_h u t q hfuture a z hcell
  have hparams := futureParameters_none_of_futureCell_none
    rate rewards C_star C_h u t q hfuture z hcell
  have hnot : z ∉ Gfuture rate rewards C_star C_h u t q hfuture := by
    rintro ⟨xi, hparams', hprior⟩
    rw [hparams] at hparams'
    cases hparams'
  exact ⟨hA.1, futureIncrement_eq_zero_of_not_mem_Gfuture
    rate rewards C_star C_h u t q hfuture a z hnot⟩

/-- A disabled actual future cell has no enabled parameters and contributes zero
scalar and increment. -/
theorem futureIncrement_zero_of_disabled_cell (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z)
    (inputs : List (RecordedQueueRun.RoundInput p.K))
    (c : RecordedQueueRun.RoundInput p.K)
    (hinputs : ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
      rate rewards C_star C_h u t q z = some inputs)
    (hcell : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = some c)
    (hdisabled : c.enabled = false) :
    ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture a z = 0 ∧
      futureIncrement rate rewards C_star C_h u t q hfuture a z = 0 := by
  have hA := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_zero_of_disabled_cell
    rate rewards C_star C_h u t q hfuture a z inputs c hinputs hcell hdisabled
  have hp := futureParameters_present_from_cell
    rate rewards C_star C_h u t q hfuture z c hcell
  have hp' : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture = some (false, c.rate) := by
    simpa [hdisabled] using hp
  have hnot : z ∉ Gfuture rate rewards C_star C_h u t q hfuture := by
    rintro ⟨xi, hparams, hprior⟩
    have hpair : (true, xi) = (false, c.rate) :=
      Option.some.inj (hparams.symm.trans hp')
    have hbool : (true : Bool) = false := congrArg Prod.fst hpair
    cases hbool
  exact ⟨hA.1, futureIncrement_eq_zero_of_not_mem_Gfuture
    rate rewards C_star C_h u t q hfuture a z hnot⟩

/-- The first update that detects overflow remains in the inherited run, while
the prior-overflow gate forces its future increment to zero. -/
theorem futureIncrement_zero_of_prior_overflow (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z)
    (inputs : List (RecordedQueueRun.RoundInput p.K))
    (hinputs : ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
      rate rewards C_star C_h u t q z = some inputs)
    (hoverflow : (RecordedQueueRun.run Q inputs).overflow = true) :
    ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture a z = 0 ∧
      futureIncrement rate rewards C_star C_h u t q hfuture a z = 0 := by
  have hA := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_zero_of_prior_overflow
    rate rewards C_star C_h u t q hfuture a z inputs hinputs hoverflow
  have hclear := priorClear_eq_of_prefixInputs
    rate rewards C_star C_h u t q z inputs hinputs
  have hclear' : ReferenceFirstCollectionRenewalFutureRetainedMoments.priorClear
      rate rewards C_star C_h u t q z = false := by
    rw [hclear, hoverflow]
    rfl
  have hnot : z ∉ Gfuture rate rewards C_star C_h u t q hfuture := by
    rintro ⟨xi, hparams, hprior⟩
    rw [hclear'] at hprior
    cases hprior
  exact ⟨hA.1, futureIncrement_eq_zero_of_not_mem_Gfuture
    rate rewards C_star C_h u t q hfuture a z hnot⟩

/-- On a present enabled cell with the same inherited prefix still clear, the
increment is the run's actual raw estimate minus four. -/
theorem futureIncrement_present_run (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z)
    (inputs : List (RecordedQueueRun.RoundInput p.K))
    (c : RecordedQueueRun.RoundInput p.K)
    (hinputs : ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
      rate rewards C_star C_h u t q z = some inputs)
    (hcell : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = some c)
    (henabled : c.enabled = true)
    (hnoOverflow : (RecordedQueueRun.run Q inputs).overflow = false) :
    futureIncrement rate rewards C_star C_h u t q hfuture a z =
      RecordedRoundMoments.rawEstimate Q (RecordedQueueRun.run Q inputs) c a - 4 := by
  have hclear := priorClear_eq_of_prefixInputs
    rate rewards C_star C_h u t q z inputs hinputs
  have hclear' : ReferenceFirstCollectionRenewalFutureRetainedMoments.priorClear
      rate rewards C_star C_h u t q z = true := by
    rw [hclear, hnoOverflow]
    rfl
  have hp := futureParameters_present_from_cell
    rate rewards C_star C_h u t q hfuture z c hcell
  have hp' : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture = some (true, c.rate) := by
    simpa [henabled] using hp
  have hgate : z ∈ Gfuture rate rewards C_star C_h u t q hfuture :=
    ⟨c.rate, hp', hclear'⟩
  rw [futureIncrement_eq_raw_sub_four_of_mem_Gfuture
    rate rewards C_star C_h u t q hfuture a z hgate]
  exact congrArg (fun x : ℝ => x - 4)
    (ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_present_run
      rate rewards C_star C_h u t q hfuture a z inputs c hinputs hcell)

/-- On that same optional whole prefix, the increment is the accepted arrival
divided by the queue's actual `n`, then minus four. -/
theorem futureIncrement_present_acceptance (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z)
    (inputs : List (RecordedQueueRun.RoundInput p.K))
    (c : RecordedQueueRun.RoundInput p.K)
    (hinputs : ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
      rate rewards C_star C_h u t q z = some inputs)
    (hcell : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = some c)
    (henabled : c.enabled = true)
    (hnoOverflow : (RecordedQueueRun.run Q inputs).overflow = false) :
    futureIncrement rate rewards C_star C_h u t q hfuture a z =
      ((RecordedQueueRun.acceptedArrival
        (RecordedQueueRun.acceptedRecord Q (RecordedQueueRun.run Q inputs) c a) : ℝ) /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) - 4 := by
  have hraw := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_present_run
    rate rewards C_star C_h u t q hfuture a z inputs c hinputs hcell
  have hrun := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_present_acceptance
    rate rewards C_star C_h u t q hfuture a z inputs c hinputs hcell
  have hrawEq : RecordedRoundMoments.rawEstimate Q (RecordedQueueRun.run Q inputs) c a =
      ((RecordedQueueRun.acceptedArrival
        (RecordedQueueRun.acceptedRecord Q (RecordedQueueRun.run Q inputs) c a) : ℝ) /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) :=
    hraw.symm.trans hrun.1
  rw [futureIncrement_present_run rate rewards C_star C_h u t q hfuture a z
    inputs c hinputs hcell henabled hnoOverflow, hrawEq]

end Bandits.Support.ReferenceFirstCollectionRenewalFutureExponentialIncrement

end
