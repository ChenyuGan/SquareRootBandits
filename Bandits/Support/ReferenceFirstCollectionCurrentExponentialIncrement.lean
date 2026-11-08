/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCurrentRetainedMoments
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Original-law retained first-collection exponential increment

This module proves the exponential increment estimate on the original source
space and source law for either corrected or renewed first invocation of the
actual first collection cell. The retained test uses the complete strict-past
overflow prefix and keeps the current enabled update, including zero-arrival
service and the first update which causes overflow.

Sources: `04_slow_fast_learner.tex:140-188,245-290`,
`05_binary_transport.tex:352-431`, and `06_interruptions.tex:355-426` under
`sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open Bandits.Support.ContinuousLearningRows (TimeControl)
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration (sourcePrefixFiltration)
open Bandits.Support.ReferenceCalendarCollectionCallControlLaw (firstCell)
open Bandits.Support.ReferenceFirstCollectionCurrentRetainedMoments
  (retainedRaw retainedMomentOne)

namespace Bandits.Support.ReferenceFirstCollectionCurrentExponentialIncrement

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)
  (control0 : TimeControl p)
  (u t : Fin p.T)
  (a : Fin p.K)

local notation "S" => SourceInput p
local notation "mu" => sourceInputLaw p
local notation "F" => sourcePrefixFiltration control0 (t.val + 1)
local notation "actualGate" => ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t
local notation "A" => retainedRaw rate rewards C_star C_h u t a
local notation "Mone" => retainedMomentOne rate rewards C_star C_h u t a
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val

/-- The retained increment subtracts service only on the actual retained
first-call gate. In particular, an enabled zero arrival still contributes
`-4`. -/
@[expose] def retainedIncrement : S → ℝ :=
  Set.indicator actualGate (fun z => A z - 4)

/-- The exponential of the literal retained increment under the canonical
recording rate. -/
@[expose] def expRetainedIncrement : S → ℝ :=
  fun z => Real.exp (beta * retainedIncrement rate rewards C_star C_h u t a z)

/-- The canonical exponential rate is positive. -/
theorem beta_pos : 0 < beta :=
  CanonicalRecordingRates.beta_pos p rate.eta.property

/-- The retained increment equals arrival minus four on the actual gate. -/
theorem retainedIncrement_eq_raw_sub_four_of_mem_G (z : S) (hz : z ∈ actualGate) :
    retainedIncrement rate rewards C_star C_h u t a z = A z - 4 := by
  simp [retainedIncrement, hz]

/-- The retained increment is zero off the actual gate. -/
theorem retainedIncrement_eq_zero_of_not_mem_G (z : S) (hz : z ∉ actualGate) :
    retainedIncrement rate rewards C_star C_h u t a z = 0 := by
  simp [retainedIncrement, hz]

/-- Zero accepted arrival on the retained enabled cell still incurs the
current four-unit service update. -/
theorem retainedIncrement_eq_neg_four_of_zero_raw (z : S)
    (hz : z ∈ actualGate) (hzero : A z = 0) :
    retainedIncrement rate rewards C_star C_h u t a z = -4 := by
  rw [retainedIncrement_eq_raw_sub_four_of_mem_G rate rewards C_star C_h u t a z hz, hzero]
  ring

/-- The retained raw arrival lies in the canonical nonnegative interval. -/
theorem retainedRaw_bounds (z : S) :
    0 ≤ A z ∧ A z ≤ 1 / beta :=
  ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_bounds
    rate rewards C_star C_h u t a z

/-- Scaling the retained raw arrival by the canonical rate puts it in the
unit interval used by the convex exponential chord. -/
theorem beta_mul_retainedRaw_bounds (z : S) :
    0 ≤ beta * A z ∧ beta * A z ≤ 1 := by
  have hbeta := beta_pos rate
  have hA := retainedRaw_bounds rate rewards C_star C_h u t a z
  constructor
  · exact mul_nonneg hbeta.le hA.1
  · calc
      beta * A z ≤ beta * (1 / beta) :=
        mul_le_mul_of_nonneg_left hA.2 hbeta.le
      _ = 1 := by field_simp [ne_of_gt hbeta]

/-- A deterministic lower and upper envelope for the retained increment. -/
theorem retainedIncrement_bounds (z : S) :
    -4 ≤ retainedIncrement rate rewards C_star C_h u t a z ∧
      retainedIncrement rate rewards C_star C_h u t a z ≤ 1 / beta := by
  have hA := retainedRaw_bounds rate rewards C_star C_h u t a z
  have hbeta := beta_pos rate
  by_cases hz : z ∈ actualGate
  · rw [retainedIncrement_eq_raw_sub_four_of_mem_G rate rewards C_star C_h u t a z hz]
    constructor <;> linarith
  · rw [retainedIncrement_eq_zero_of_not_mem_G rate rewards C_star C_h u t a z hz]
    exact ⟨by norm_num, one_div_nonneg.mpr hbeta.le⟩

private theorem beta_mul_retainedIncrement_bounds (z : S) :
    -4 * beta ≤ beta * retainedIncrement rate rewards C_star C_h u t a z ∧
      beta * retainedIncrement rate rewards C_star C_h u t a z ≤ 1 := by
  have hbeta := beta_pos rate
  have hx := retainedIncrement_bounds rate rewards C_star C_h u t a z
  constructor
  · calc
      -4 * beta = beta * (-4) := by ring
      _ ≤ beta * retainedIncrement rate rewards C_star C_h u t a z :=
        mul_le_mul_of_nonneg_left hx.1 hbeta.le
  · calc
      beta * retainedIncrement rate rewards C_star C_h u t a z ≤
          beta * (1 / beta) := mul_le_mul_of_nonneg_left hx.2 hbeta.le
      _ = 1 := by field_simp [ne_of_gt hbeta]

/-- Ambient measurability of the retained increment on the original source
space. -/
theorem measurable_retainedIncrement (control0 : TimeControl p) :
    Measurable (retainedIncrement rate rewards C_star C_h u t a) := by
  have hA := ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_measurable
    rate rewards C_star C_h control0 u t a
  have hGfield := ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
    rate rewards C_star C_h control0 u t
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace S) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  exact (hA.sub_const 4).indicator
    (hle _ hGfield)

/-- Ambient integrability of the retained increment under the original source
law, including when the gate is null. -/
theorem integrable_retainedIncrement (control0 : TimeControl p) :
    Integrable (retainedIncrement rate rewards C_star C_h u t a) mu := by
  have hA := ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_integrable
    rate rewards C_star C_h control0 u t a
  have hGfield := ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
    rate rewards C_star C_h control0 u t
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace S) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hsub : Integrable (fun z : S => A z - 4) mu := by
    simpa [Pi.add_apply, sub_eq_add_neg] using
      hA.add (integrable_const (-4 : ℝ))
  simpa [retainedIncrement] using hsub.indicator
    (hle _ hGfield)

/-- The exponential envelope follows from the deterministic increment bounds. -/
theorem expRetainedIncrement_bounds (z : S) :
    Real.exp (-4 * beta) ≤ expRetainedIncrement rate rewards C_star C_h u t a z ∧
      expRetainedIncrement rate rewards C_star C_h u t a z ≤ Real.exp 1 := by
  have hx := beta_mul_retainedIncrement_bounds rate rewards C_star C_h u t a z
  constructor
  · exact Real.exp_le_exp_of_le hx.1
  · exact Real.exp_le_exp_of_le hx.2

/-- Ambient measurability of the literal retained exponential. -/
theorem measurable_expRetainedIncrement (control0 : TimeControl p) :
    Measurable (expRetainedIncrement rate rewards C_star C_h u t a) := by
  have hx := measurable_retainedIncrement rate rewards C_star C_h u t a control0
  have hscaled : Measurable (fun z : S => beta *
      retainedIncrement rate rewards C_star C_h u t a z) :=
    (measurable_const : Measurable (fun _ : S => beta)).mul hx
  change Measurable (fun z : S => Real.exp
    (beta * retainedIncrement rate rewards C_star C_h u t a z))
  exact hscaled.exp

private theorem integrable_of_norm_le_const {f : S → ℝ} (hf : Measurable f)
    (C : ℝ) (hbound : ∀ z, ‖f z‖ ≤ C) : Integrable f mu := by
  have hconst : Integrable (fun _ : S => C) mu := integrable_const C
  refine hconst.mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with z
  simpa using hbound z

/-- Ambient integrability of the retained exponential under the same original
source law. -/
theorem integrable_expRetainedIncrement (control0 : TimeControl p) :
    Integrable (expRetainedIncrement rate rewards C_star C_h u t a) mu := by
  apply integrable_of_norm_le_const
    (measurable_expRetainedIncrement rate rewards C_star C_h u t a control0)
    (Real.exp 1)
  intro z
  have h := expRetainedIncrement_bounds rate rewards C_star C_h u t a z
  rw [Real.norm_eq_abs, abs_of_nonneg (le_trans (Real.exp_nonneg _) h.1)]
  exact h.2

private theorem condExp_real_const_mul (c : ℝ) (f : S → ℝ) :
    mu[(fun z : S => c * f z) | F] =ᵐ[mu]
      (fun z : S => c * mu[f | F] z) := by
  have hscaled := condExp_smul (μ := mu) c f F
  have hfun : (fun z : S => c * f z) = c • f := by
    funext z
    simp [smul_eq_mul]
  calc
    mu[(fun z : S => c * f z) | F] =ᵐ[mu] mu[c • f | F] :=
      condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun hfun z)
    _ =ᵐ[mu] (fun z : S => c * mu[f | F] z) := by
      filter_upwards [hscaled] with z hz
      simpa only [Pi.smul_apply, smul_eq_mul] using hz

/-- The conditional exponential chord estimate for the original retained raw
arrival and its existing first-moment coefficient. -/
theorem condExp_expRetainedRaw_le_chord :
    mu[(fun z : S => Real.exp (beta * A z)) | F] ≤ᵐ[mu]
      (fun z : S => 1 + (Real.exp 1 - 1) * beta * Mone z) := by
  let scale : ℝ := (Real.exp 1 - 1) * beta
  let f : S → ℝ := fun z => Real.exp (beta * A z)
  let affine : S → ℝ := fun z => 1 + scale * A z
  have hAmeas := ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_measurable
    rate rewards C_star C_h control0 u t a
  have hAint := ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_integrable
    rate rewards C_star C_h control0 u t a
  have hfmeas : Measurable f := by
    have hscaled : Measurable (fun z : S => beta * A z) :=
      (measurable_const : Measurable (fun _ : S => beta)).mul hAmeas
    simpa [f] using hscaled.exp
  have hfint : Integrable f mu := by
    apply integrable_of_norm_le_const hfmeas (Real.exp 1)
    intro z
    have hbound := beta_mul_retainedRaw_bounds rate rewards C_star C_h u t a z
    have hExp := Real.exp_nonneg (beta * A z)
    rw [Real.norm_eq_abs, abs_of_nonneg hExp]
    change Real.exp (beta * A z) ≤ Real.exp 1
    exact Real.exp_le_exp_of_le hbound.2
  have hscaledInt : Integrable (fun z : S => scale * A z) mu := by
    simpa [smul_eq_mul] using hAint.const_mul scale
  have hAffineInt : Integrable affine mu := by
    exact (integrable_const (1 : ℝ)).add (by simpa [affine] using hscaledInt)
  have hpoint : ∀ z : S, f z ≤ affine z := by
    intro z
    have hbound := beta_mul_retainedRaw_bounds rate rewards C_star C_h u t a z
    have hchord := RecordedRoundMoments.exp_le_unit_chord hbound.1 hbound.2
    calc
      f z ≤ 1 + (Real.exp 1 - 1) * (beta * A z) := by simpa [f] using hchord
      _ = affine z := by dsimp [affine, scale]; ring
  have hmono := condExp_mono (m := F) hfint hAffineInt
    (Filter.Eventually.of_forall hpoint)
  have hsum := condExp_add (integrable_const (1 : ℝ)) hscaledInt F
  have hle : F ≤ (inferInstance : MeasurableSpace S) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hconst := condExp_const (μ := mu) (m := F)
    (m₀ := (inferInstance : MeasurableSpace S)) hle (1 : ℝ)
  have hscale := condExp_real_const_mul (control0 := control0) (t := t) scale A
  have hAcond := ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_condExp
    rate rewards C_star C_h control0 u t a
  have hAffineEq : affine = (fun _ : S => (1 : ℝ)) + (fun z : S => scale * A z) := by
    funext z
    rfl
  filter_upwards [hmono, hsum, hscale, hAcond] with z hmono_z hsum_z hscale_z hAcond_z
  have hconstant_z := congrFun hconst z
  calc
    mu[f | F] z ≤ mu[affine | F] z := hmono_z
    _ = 1 + scale * Mone z := by
      rw [show affine = (fun _ : S => (1 : ℝ)) + (fun z : S => scale * A z)
        from hAffineEq]
      rw [hsum_z]
      rw [Pi.add_apply, hconstant_z, hscale_z, hAcond_z]
    _ = 1 + (Real.exp 1 - 1) * beta * Mone z := by dsimp [scale]

/-- The exponential service factor dominates the conditional chord at every
positive canonical rate. -/
theorem exp_neg_four_beta_chord_le_one :
    Real.exp (-4 * beta) * (1 + (Real.exp 1 - 1) * beta) ≤ 1 := by
  have hbeta := beta_pos rate
  have hcoef : 0 ≤ (Real.exp 1 - 1) * beta := by
    have he := Real.exp_one_gt_two
    exact mul_nonneg (by linarith) hbeta.le
  have hlinear := Real.add_one_le_exp ((Real.exp 1 - 1) * beta)
  have harg : (Real.exp 1 - 1) * beta - 4 * beta ≤ 0 := by
    have hcoeff : Real.exp 1 - 5 ≤ 0 := by linarith [Real.exp_one_lt_three]
    calc
      (Real.exp 1 - 1) * beta - 4 * beta = (Real.exp 1 - 5) * beta := by ring
      _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcoeff hbeta.le
  calc
    Real.exp (-4 * beta) * (1 + (Real.exp 1 - 1) * beta) ≤
        Real.exp (-4 * beta) * Real.exp ((Real.exp 1 - 1) * beta) :=
      mul_le_mul_of_nonneg_left (by linarith [hlinear]) (Real.exp_nonneg _)
    _ = Real.exp ((Real.exp 1 - 1) * beta - 4 * beta) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp 0 := Real.exp_le_exp_of_le harg
    _ = 1 := Real.exp_zero

private theorem expRetainedIncrement_indicator_identity (z : S) :
    expRetainedIncrement rate rewards C_star C_h u t a z =
      Real.exp (-4 * beta) * Set.indicator actualGate
        (fun y : S => Real.exp (beta * A y)) z +
      Set.indicator actualGateᶜ (fun _ : S => (1 : ℝ)) z := by
  by_cases hz : z ∈ actualGate
  · have hsplit : Real.exp (beta * (A z - 4)) =
        Real.exp (-4 * beta) * Real.exp (beta * A z) := by
      rw [show beta * (A z - 4) = (-4 * beta) + beta * A z by ring,
        Real.exp_add]
    simp [expRetainedIncrement, retainedIncrement, hz, hsplit]
  · simp [expRetainedIncrement, retainedIncrement, hz]

/-- Original-law conditional exponential estimate on the actual retained
first-call gate, without a positivity or survival condition. -/
theorem condExp_expRetainedIncrement_le_one :
    mu[(expRetainedIncrement rate rewards C_star C_h u t a) | F] ≤ᵐ[mu]
      (fun _ : S => 1) := by
  let f : S → ℝ := fun z => Real.exp (beta * A z)
  let fG : S → ℝ := Set.indicator actualGate f
  let fGc : S → ℝ := Set.indicator actualGateᶜ (fun _ : S => (1 : ℝ))
  let penalty : ℝ := Real.exp (-4 * beta)
  have hGfield : MeasurableSet[F] actualGate :=
    ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
      rate rewards C_star C_h control0 u t
  have hle : F ≤ (inferInstance : MeasurableSpace S) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hGambient : MeasurableSet actualGate := hle _ hGfield
  have hfmeas : Measurable f := by
    have hA := ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_measurable
      rate rewards C_star C_h control0 u t a
    have hscaled : Measurable (fun z : S => beta * A z) :=
      (measurable_const : Measurable (fun _ : S => beta)).mul hA
    simpa [f] using hscaled.exp
  have hfint : Integrable f mu := by
    apply integrable_of_norm_le_const hfmeas (Real.exp 1)
    intro z
    have hbound := beta_mul_retainedRaw_bounds rate rewards C_star C_h u t a z
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    change Real.exp (beta * A z) ≤ Real.exp 1
    exact Real.exp_le_exp_of_le hbound.2
  have hfGint : Integrable fG mu := by
    simpa [fG] using hfint.indicator hGambient
  have hfGcint : Integrable fGc mu := by
    simpa [fGc] using (integrable_const (1 : ℝ)).indicator hGambient.compl
  have hscaledInt : Integrable (fun z : S => penalty * fG z) mu :=
    hfGint.const_mul penalty
  have hZdecomp : expRetainedIncrement rate rewards C_star C_h u t a =
      fun z : S => penalty * fG z + fGc z := by
    funext z
    simpa [fG, fGc, penalty] using
      expRetainedIncrement_indicator_identity rate rewards C_star C_h u t a z
  have hsum := condExp_add hscaledInt hfGcint F
  have hscale := condExp_real_const_mul (control0 := control0) (t := t) penalty fG
  have hmask := condExp_indicator (μ := mu) hfint hGfield
  have hmaskComp := condExp_indicator (μ := mu) (integrable_const (1 : ℝ)) hGfield.compl
  have hconst := condExp_const (μ := mu) (m := F)
    (m₀ := (inferInstance : MeasurableSpace S)) hle (1 : ℝ)
  have hCEdecomp :
      mu[(expRetainedIncrement rate rewards C_star C_h u t a) | F] =ᵐ[mu]
        (fun z : S => penalty * Set.indicator actualGate (fun y => mu[f | F] y) z +
          Set.indicator actualGateᶜ (fun _ : S => (1 : ℝ)) z) := by
    calc
      mu[(expRetainedIncrement rate rewards C_star C_h u t a) | F] =ᵐ[mu]
          mu[(fun z : S => penalty * fG z + fGc z) | F] :=
        condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun hZdecomp z)
      _ =ᵐ[mu] mu[(fun z : S => penalty * fG z) | F] + mu[fGc | F] := hsum
      _ =ᵐ[mu] (fun z : S => penalty * mu[fG | F] z + mu[fGc | F] z) := by
        filter_upwards [hscale] with z hz
        simpa only [Pi.add_apply] using
          congrArg (fun x : ℝ => x + mu[fGc | F] z) hz
      _ =ᵐ[mu] (fun z : S => penalty * Set.indicator actualGate
          (fun y : S => mu[f | F] y) z +
            Set.indicator actualGateᶜ (fun _ : S => (1 : ℝ)) z) := by
        filter_upwards [hmask, hmaskComp] with z hmask_z hmaskComp_z
        rw [hmask_z, hmaskComp_z, hconst]
  have hchord := condExp_expRetainedRaw_le_chord
    rate rewards C_star C_h control0 u t a
  have hmoment := ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne_roundedReward_bounds
    rate rewards C_star C_h u t a
  have hscaleNonneg : 0 ≤ (Real.exp 1 - 1) * beta := by
    have he := Real.exp_one_gt_two
    exact mul_nonneg (by linarith) (beta_pos rate).le
  have hpenaltyPos : 0 < penalty := by positivity
  have hscalar := exp_neg_four_beta_chord_le_one rate
  filter_upwards [hCEdecomp, hchord] with z hdecomp hchord_z
  rw [hdecomp]
  by_cases hz : z ∈ actualGate
  · have hzComp : z ∉ actualGateᶜ := by simpa using hz
    simp only [Set.indicator_of_mem hz, Set.indicator_of_notMem hzComp, add_zero]
    have hm := hmoment z
    have hMonele : Mone z ≤ 1 := hm.2.1.trans hm.2.2
    calc
      penalty * mu[f | F] z ≤
          penalty * (1 + (Real.exp 1 - 1) * beta * Mone z) :=
        mul_le_mul_of_nonneg_left hchord_z hpenaltyPos.le
      _ ≤ penalty * (1 + (Real.exp 1 - 1) * beta) := by
        apply mul_le_mul_of_nonneg_left _ hpenaltyPos.le
        have hmul := mul_le_mul_of_nonneg_left hMonele hscaleNonneg
        linarith
      _ ≤ 1 := by simpa [penalty] using hscalar
  · have hzComp : z ∈ actualGateᶜ := by simpa using hz
    simp [Set.indicator_of_notMem hz, Set.indicator_of_mem hzComp]

/-- Every set measurable in the original source-prefix field satisfies the
unconditional integral consequence of the conditional exponential estimate.
-/
theorem setIntegral_expRetainedIncrement_le_measure (B : Set S)
    (hB : MeasurableSet[F] B) :
    (∫ z in B, expRetainedIncrement rate rewards C_star C_h u t a z ∂mu) ≤
      Measure.real mu B := by
  have hle : F ≤ (inferInstance : MeasurableSpace S) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hZint := integrable_expRetainedIncrement
    rate rewards C_star C_h u t a control0
  have hconst : Integrable (fun _ : S => (1 : ℝ)) mu := integrable_const 1
  calc
    (∫ z in B, expRetainedIncrement rate rewards C_star C_h u t a z ∂mu) =
        ∫ z in B,
          mu[(expRetainedIncrement rate rewards C_star C_h u t a) | F] z ∂mu :=
      (setIntegral_condExp hle hZint hB).symm
    _ ≤ ∫ z in B, (1 : ℝ) ∂mu :=
      setIntegral_mono_ae integrable_condExp.integrableOn hconst.integrableOn
        (condExp_expRetainedIncrement_le_one
          rate rewards C_star C_h control0 u t a)
    _ = Measure.real mu B := by
      rw [setIntegral_const]
      simp only [smul_eq_mul, mul_one]

/-- Integrating the original-law exponential estimate over the whole source
space costs exactly its probability mass, which is one. -/
theorem integral_expRetainedIncrement_le_one (control0 : TimeControl p) :
    (∫ z : S, expRetainedIncrement rate rewards C_star C_h u t a z ∂mu) ≤ 1 := by
  rw [← setIntegral_univ]
  calc
    (∫ z in Set.univ,
        expRetainedIncrement rate rewards C_star C_h u t a z ∂mu) ≤
        Measure.real mu Set.univ :=
      setIntegral_expRetainedIncrement_le_measure
        rate rewards C_star C_h control0 u t a Set.univ MeasurableSet.univ
    _ = 1 := by simp [Measure.real]

/-- On the original first-cell event, produce its actual past list and current
enabled cell, retain the all-prefix overflow equivalence and accepted-current
record identity, and identify the normalized recorded increment. -/
theorem firstCell_actual_retainedIncrement (z : S)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (c : RecordedQueueRun.RoundInput p.K),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells?
          rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell
          rate rewards C_star C_h t z = some c ∧
      c.enabled = true ∧
      (z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t ↔
        ∀ h ≤ L.length, ∀ j : Fin p.K,
          32 * (UnstoppedRecordedQueueComparison.unstoppedReplay
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) L h j).2 ≤
              (ReferenceFirstLaunchNumericalCell.queueParameters rate).D) ∧
      ReferenceFirstCollectionCurrentRetainedGate.acceptedCurrent?
          rate rewards C_star C_h t a z =
        some (RecordedQueueRun.acceptedRecord
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.run
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) L) c a) ∧
      A z =
        ((RecordedQueueRun.acceptedArrival
          (RecordedQueueRun.acceptedRecord
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (RecordedQueueRun.run
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) L) c a) : ℝ) /
          ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) ∧
      ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) =
        rate.eta.val * (D p : ℝ) ∧
      (z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t →
        retainedIncrement rate rewards C_star C_h u t a z =
          ((RecordedQueueRun.acceptedArrival
            (RecordedQueueRun.acceptedRecord
              (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (RecordedQueueRun.run
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) L) c a) : ℝ) /
            ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) - 4) ∧
      (z ∉ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t →
        retainedIncrement rate rewards C_star C_h u t a z = 0) := by
  obtain ⟨L, c, hL, hc, henabled, hall, haccepted, hraw, _hsquare⟩ :=
    ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_eq_acceptedArrival_on_firstCell
      rate rewards C_star C_h u t a z hz
  refine ⟨L, c, hL, hc, henabled, hall, haccepted, hraw,
    ?_, ?_, ?_⟩
  · exact (ReferenceFirstLaunchNumericalCell.queueParameters rate).n_eq_eta_mul_D
  · intro hH
    have hG : z ∈ actualGate := ⟨hz, hH⟩
    rw [retainedIncrement_eq_raw_sub_four_of_mem_G rate rewards C_star C_h u t a z hG, hraw]
  · intro hH
    apply retainedIncrement_eq_zero_of_not_mem_G
    intro hG
    exact hH hG.2

end Bandits.Support.ReferenceFirstCollectionCurrentExponentialIncrement

end
