/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCurrentQueueReadout
public import Bandits.Support.ReferenceFirstCollectionCurrentExponentialIncrement

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Original first-call exponential queue step

The exponential queue observations are scalar-localized to the original first
collection-call event. Their one-step conditional estimate is under the
original source law and source-prefix filtration.

Sources: `04_slow_fast_learner.tex:140-188,245-315`,
`05_binary_transport.tex:352-431`, and `06_interruptions.tex:355-426` under
`sources/zip4/manuscript/`.
-/

public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open Bandits.Support.ActualInitializationPhysicalStep (GridRewardTable)
open Bandits.Support.ContinuousLearningRows (TimeControl)
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration (sourcePrefixFiltration)
open Bandits.Support.ReferenceCalendarCollectionCallControlLaw (firstCell)

namespace Bandits.Support.ReferenceFirstCollectionCurrentExponentialQueueStep

local instance sourceInputMeasurableSpace {p : Parameters} :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)
  (control0 : TimeControl p)
  (u t : Fin p.T) (a : Fin p.K)

local notation "S" => SourceInput p
local notation "mu" => sourceInputLaw p
local notation "F" => sourcePrefixFiltration control0 (t.val + 1)
local notation "E" => firstCell rate rewards C_star C_h u t
local notation "G" =>
  ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "q" => ReferenceFirstLaunchNumericalCell.queueParameters rate

/-- The incoming exponential backlog, explicitly zero off the actual first
collection-call event. -/
@[expose] def XMinus (rate0 : ReferenceActivePhysicalStep.RateInput p)
    (rewards0 : GridRewardTable p) (C_star0 C_h0 : ℝ)
    (u0 t0 : Fin p.T) (a0 : Fin p.K) : SourceInput p → ℝ :=
  (firstCell rate0 rewards0 C_star0 C_h0 u0 t0).indicator (fun z => Real.exp
    (CanonicalRecordingRates.beta p rate0.eta.val *
      ReferenceFirstCollectionCurrentQueueReadout.bMinus
        rate0 rewards0 C_star0 C_h0 u0 t0 a0 z))

/-- The post-update exponential backlog, explicitly zero off the same actual
first collection-call event. -/
@[expose] def XPlus (rate0 : ReferenceActivePhysicalStep.RateInput p)
    (rewards0 : GridRewardTable p) (C_star0 C_h0 : ℝ)
    (u0 t0 : Fin p.T) (a0 : Fin p.K) : SourceInput p → ℝ :=
  (firstCell rate0 rewards0 C_star0 C_h0 u0 t0).indicator (fun z => Real.exp
    (CanonicalRecordingRates.beta p rate0.eta.val *
      ReferenceFirstCollectionCurrentQueueReadout.bPlus
        rate0 rewards0 C_star0 C_h0 u0 t0 a0 z))

private theorem exp_reflected_step_le_one_add (b v x : ℝ) :
    Real.exp (b * max (v + x) 0) ≤
      1 + Real.exp (b * v) * Real.exp (b * x) := by
  by_cases h : 0 ≤ v + x
  · rw [max_eq_left h, mul_add, Real.exp_add]
    have hprod : 0 ≤ Real.exp (b * v) * Real.exp (b * x) :=
      mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
    linarith
  · have hle : v + x ≤ 0 := by linarith
    rw [max_eq_right hle]
    simp only [mul_zero, Real.exp_zero]
    have hprod : 0 ≤ Real.exp (b * v) * Real.exp (b * x) :=
      mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
    linarith

/-- The increment definitions agree on the whole source space, including
outside the retained gate. -/
theorem retainedIncrement_eq_currentQueueIncrement (z : S) :
    ReferenceFirstCollectionCurrentExponentialIncrement.retainedIncrement
        rate rewards C_star C_h u t a z =
      ReferenceFirstCollectionCurrentQueueReadout.x
        rate rewards C_star C_h u t a z := by
  by_cases hz : z ∈ G
  · rw [ReferenceFirstCollectionCurrentExponentialIncrement.retainedIncrement_eq_raw_sub_four_of_mem_G
      rate rewards C_star C_h u t a z hz]
    simp [ReferenceFirstCollectionCurrentQueueReadout.x,
      ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw, hz]
  · rw [ReferenceFirstCollectionCurrentExponentialIncrement.retainedIncrement_eq_zero_of_not_mem_G
      rate rewards C_star C_h u t a z hz]
    simp [ReferenceFirstCollectionCurrentQueueReadout.x, hz]

/-- On the actual first-call event, both scalar exponentials use the same
original strict-past list and current cell. -/
theorem firstCell_XMinus_XPlus_actual_readouts (z : S)
    (hz : z ∈ E) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (c : RecordedQueueRun.RoundInput p.K),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells?
          rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell
          rate rewards C_star C_h t z = some c ∧
      XMinus rate rewards C_star C_h u t a z =
        Real.exp (beta * ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog
          rate (some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.run q L))) a) ∧
      XPlus rate rewards C_star C_h u t a z =
        Real.exp (beta * ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog
          rate (some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.step q (RecordedQueueRun.run q L) c))) a) := by
  obtain ⟨L, c, hL, hc, _henabled, hbefore, hafter, _hrest⟩ :=
    ReferenceFirstCollectionCurrentQueueReadout.firstCell_actual_queue_readouts
      rate rewards C_star C_h u t a z hz
  refine ⟨L, c, hL, hc, ?_, ?_⟩
  · rw [XMinus, Set.indicator_of_mem hz]
    rw [ReferenceFirstCollectionCurrentQueueReadout.bMinus,
      Set.indicator_of_mem hz, hbefore]
  · rw [XPlus, Set.indicator_of_mem hz]
    rw [ReferenceFirstCollectionCurrentQueueReadout.bPlus,
      Set.indicator_of_mem hz, hafter]

/-- The incoming exponential observation is measurable in the original
source-prefix field. -/
theorem XMinus_measurable :
    Measurable[F] (XMinus rate rewards C_star C_h u t a) := by
  have hE : MeasurableSet[F] E :=
    ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t
  have hb := ReferenceFirstCollectionCurrentQueueReadout.bMinus_measurable
    rate rewards C_star C_h control0 u t a
  have hscaled : Measurable[F] (fun z : S => beta *
      ReferenceFirstCollectionCurrentQueueReadout.bMinus
        rate rewards C_star C_h u t a z) :=
    (measurable_const : Measurable[F] (fun _ : S => beta)).mul hb
  change Measurable[F] ((E).indicator (fun z => Real.exp
    (beta * ReferenceFirstCollectionCurrentQueueReadout.bMinus
      rate rewards C_star C_h u t a z)))
  exact hscaled.exp.indicator hE

/-- The incoming exponential has a finite global envelope on the full source
space. -/
theorem XMinus_bounds (z : S) :
    0 ≤ XMinus rate rewards C_star C_h u t a z ∧
      XMinus rate rewards C_star C_h u t a z ≤ Real.exp (beta * (2 *
        ReferenceFirstCollectionCurrentQueueReadout.Bcap rate)) := by
  by_cases hz : z ∈ E
  · rw [XMinus, Set.indicator_of_mem hz]
    have hb := ReferenceFirstCollectionCurrentQueueReadout.bMinus_global_bounds
      rate rewards C_star C_h u t a z
    constructor
    · exact Real.exp_nonneg _
    · exact Real.exp_le_exp_of_le (mul_le_mul_of_nonneg_left hb.2
        (ReferenceFirstCollectionCurrentExponentialIncrement.beta_pos rate).le)
  · rw [XMinus, Set.indicator_of_notMem hz]
    constructor
    · norm_num
    · exact Real.exp_nonneg _

/-- The post-update exponential has the same finite global envelope. -/
theorem XPlus_bounds (z : S) :
    0 ≤ XPlus rate rewards C_star C_h u t a z ∧
      XPlus rate rewards C_star C_h u t a z ≤ Real.exp (beta * (2 *
        ReferenceFirstCollectionCurrentQueueReadout.Bcap rate)) := by
  by_cases hz : z ∈ E
  · rw [XPlus, Set.indicator_of_mem hz]
    have hb := ReferenceFirstCollectionCurrentQueueReadout.bPlus_global_bounds
      rate rewards C_star C_h u t a z
    constructor
    · exact Real.exp_nonneg _
    · exact Real.exp_le_exp_of_le (mul_le_mul_of_nonneg_left hb.2
        (ReferenceFirstCollectionCurrentExponentialIncrement.beta_pos rate).le)
  · rw [XPlus, Set.indicator_of_notMem hz]
    constructor
    · norm_num
    · exact Real.exp_nonneg _

private theorem integrable_of_bounded_measurable
    {f : S → ℝ} (hf : Measurable f) (C : ℝ) (_hC : 0 ≤ C)
    (hbound : ∀ z, ‖f z‖ ≤ C) : Integrable f mu := by
  have hconst : Integrable (fun _ : S => C) mu := integrable_const C
  refine hconst.mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with z
  simpa [Real.norm_eq_abs, abs_of_nonneg _hC] using hbound z

section AmbientIntegrability

include control0

/-- The incoming exponential observation is also measurable in the ambient
original source space. -/
theorem XMinus_measurable_ambient :
    Measurable (XMinus rate rewards C_star C_h u t a) := by
  have hle : F ≤ (inferInstance : MeasurableSpace S) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  exact Measurable.mono
    (XMinus_measurable rate rewards C_star C_h control0 u t a) hle le_rfl

/-- The post-update exponential observation is ambient measurable on the
original source space. -/
theorem XPlus_measurable :
    Measurable (XPlus rate rewards C_star C_h u t a) := by
  have hle : F ≤ (inferInstance : MeasurableSpace S) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hEfield : MeasurableSet[F] E :=
    ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t
  have hE : MeasurableSet E := hle _ hEfield
  have hb := ReferenceFirstCollectionCurrentQueueReadout.bPlus_measurable
    rate rewards C_star C_h control0 u t a
  have hscaled : Measurable (fun z : S => beta *
      ReferenceFirstCollectionCurrentQueueReadout.bPlus
        rate rewards C_star C_h u t a z) :=
    (measurable_const : Measurable (fun _ : S => beta)).mul hb
  change Measurable ((E).indicator (fun z => Real.exp
    (beta * ReferenceFirstCollectionCurrentQueueReadout.bPlus
      rate rewards C_star C_h u t a z)))
  exact hscaled.exp.indicator hE

/-- The incoming exponential is integrable under the original source law. -/
theorem XMinus_integrable :
    Integrable (XMinus rate rewards C_star C_h u t a) mu := by
  apply integrable_of_bounded_measurable
    (XMinus_measurable_ambient rate rewards C_star C_h control0 u t a)
    (Real.exp (beta * (2 * ReferenceFirstCollectionCurrentQueueReadout.Bcap rate)))
    (Real.exp_nonneg _)
  intro z
  have h := XMinus_bounds rate rewards C_star C_h u t a z
  rw [Real.norm_of_nonneg h.1]
  exact h.2

/-- The post-update exponential is integrable under the original source law. -/
theorem XPlus_integrable :
    Integrable (XPlus rate rewards C_star C_h u t a) mu := by
  apply integrable_of_bounded_measurable
    (XPlus_measurable rate rewards C_star C_h control0 u t a)
    (Real.exp (beta * (2 * ReferenceFirstCollectionCurrentQueueReadout.Bcap rate)))
    (Real.exp_nonneg _)
  intro z
  have h := XPlus_bounds rate rewards C_star C_h u t a z
  rw [Real.norm_of_nonneg h.1]
  exact h.2

/-- The product needed to pull out the predictable incoming exponential is
integrable on the original source space. -/
theorem XMinus_mul_expRetainedIncrement_integrable :
    Integrable (XMinus rate rewards C_star C_h u t a *
      ReferenceFirstCollectionCurrentExponentialIncrement.expRetainedIncrement
        rate rewards C_star C_h u t a) mu := by
  have hYmeas :=
    ReferenceFirstCollectionCurrentExponentialIncrement.measurable_expRetainedIncrement
      rate rewards C_star C_h u t a control0
  have hmeas : Measurable (XMinus rate rewards C_star C_h u t a *
      ReferenceFirstCollectionCurrentExponentialIncrement.expRetainedIncrement
        rate rewards C_star C_h u t a) :=
    (XMinus_measurable_ambient rate rewards C_star C_h control0 u t a).mul hYmeas
  have hYint :=
    ReferenceFirstCollectionCurrentExponentialIncrement.integrable_expRetainedIncrement
      rate rewards C_star C_h u t a control0
  apply integrable_of_bounded_measurable hmeas
    (Real.exp (beta * (2 * ReferenceFirstCollectionCurrentQueueReadout.Bcap rate)) *
      Real.exp 1)
    (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
  intro z
  change ‖XMinus rate rewards C_star C_h u t a z *
      ReferenceFirstCollectionCurrentExponentialIncrement.expRetainedIncrement
        rate rewards C_star C_h u t a z‖ ≤ _
  have hx := XMinus_bounds rate rewards C_star C_h u t a z
  have hy := ReferenceFirstCollectionCurrentExponentialIncrement.expRetainedIncrement_bounds
    rate rewards C_star C_h u t a z
  have hy_nonneg : 0 ≤
      ReferenceFirstCollectionCurrentExponentialIncrement.expRetainedIncrement
        rate rewards C_star C_h u t a z :=
    le_trans (Real.exp_nonneg _) hy.1
  rw [norm_mul, Real.norm_of_nonneg hx.1, Real.norm_of_nonneg hy_nonneg]
  calc
    XMinus rate rewards C_star C_h u t a z *
        ReferenceFirstCollectionCurrentExponentialIncrement.expRetainedIncrement
          rate rewards C_star C_h u t a z ≤
      Real.exp (beta * (2 * ReferenceFirstCollectionCurrentQueueReadout.Bcap rate)) *
        ReferenceFirstCollectionCurrentExponentialIncrement.expRetainedIncrement
          rate rewards C_star C_h u t a z :=
      mul_le_mul_of_nonneg_right hx.2 hy_nonneg
    _ ≤ Real.exp (beta * (2 * ReferenceFirstCollectionCurrentQueueReadout.Bcap rate)) *
        Real.exp 1 :=
      mul_le_mul_of_nonneg_left hy.2 (Real.exp_nonneg _)

end AmbientIntegrability

/-- On the whole source space, the queue exponential step pays only the
indicator of the current retained gate. -/
theorem XPlus_le_G_indicator_add_product (z : S) :
    XPlus rate rewards C_star C_h u t a z ≤
      (G).indicator (fun _ : S => (1 : ℝ)) z +
        XMinus rate rewards C_star C_h u t a z *
          ReferenceFirstCollectionCurrentExponentialIncrement.expRetainedIncrement
            rate rewards C_star C_h u t a z := by
  by_cases hE : z ∈ E
  · by_cases hG : z ∈ G
    · have htransition :=
        ReferenceFirstCollectionCurrentQueueReadout.bPlus_reflected_transition
          rate rewards C_star C_h u t a z
      have hincrement := retainedIncrement_eq_currentQueueIncrement
        rate rewards C_star C_h u t a z
      simp only [XPlus, XMinus, Set.indicator_of_mem hE,
        Set.indicator_of_mem hG,
        ReferenceFirstCollectionCurrentExponentialIncrement.expRetainedIncrement]
      rw [htransition, ← hincrement]
      exact exp_reflected_step_le_one_add beta
        (ReferenceFirstCollectionCurrentQueueReadout.bMinus
          rate rewards C_star C_h u t a z)
        (ReferenceFirstCollectionCurrentExponentialIncrement.retainedIncrement
          rate rewards C_star C_h u t a z)
    · have htransition :=
        ReferenceFirstCollectionCurrentQueueReadout.bPlus_reflected_transition
          rate rewards C_star C_h u t a z
      have hincrement : ReferenceFirstCollectionCurrentQueueReadout.x
          rate rewards C_star C_h u t a z = 0 := by
        rw [← retainedIncrement_eq_currentQueueIncrement
          rate rewards C_star C_h u t a z]
        exact ReferenceFirstCollectionCurrentExponentialIncrement.retainedIncrement_eq_zero_of_not_mem_G
          rate rewards C_star C_h u t a z hG
      have hb := ReferenceFirstCollectionCurrentQueueReadout.bMinus_global_bounds
        rate rewards C_star C_h u t a z
      have hretainedZero :=
        ReferenceFirstCollectionCurrentExponentialIncrement.retainedIncrement_eq_zero_of_not_mem_G
          rate rewards C_star C_h u t a z hG
      simp only [XPlus, XMinus, Set.indicator_of_mem hE,
        Set.indicator_of_notMem hG,
        ReferenceFirstCollectionCurrentExponentialIncrement.expRetainedIncrement]
      rw [htransition, hincrement, add_zero, max_eq_left hb.1, hretainedZero]
      simp
  · have hG : z ∉ G := by
      rintro ⟨h, _⟩
      exact hE h
    simp [XPlus, XMinus, hE, hG]

/-- The conditional exponential queue step on the original first-call law.
The only gate cost is the current retained-gate indicator. -/
theorem condExp_XPlus_le_XMinus_add_one :
    mu[(XPlus rate rewards C_star C_h u t a) | F] ≤ᵐ[mu]
      (fun z : S => XMinus rate rewards C_star C_h u t a z + 1) := by
  let g : S → ℝ := (G).indicator (fun _ => (1 : ℝ))
  let prod : S → ℝ := XMinus rate rewards C_star C_h u t a *
    ReferenceFirstCollectionCurrentExponentialIncrement.expRetainedIncrement
      rate rewards C_star C_h u t a
  have hle : F ≤ (inferInstance : MeasurableSpace S) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hGfield : MeasurableSet[F] G :=
    ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
      rate rewards C_star C_h control0 u t
  have hGambient : MeasurableSet G := hle _ hGfield
  have hone : Integrable (fun _ : S => (1 : ℝ)) mu := integrable_const 1
  have hGint : Integrable g mu := by
    have h := hone.indicator hGambient
    simpa [g] using h
  have hprodint := XMinus_mul_expRetainedIncrement_integrable
    rate rewards C_star C_h control0 u t a
  have hsumint : Integrable (fun z : S => g z + prod z) mu := by
    exact hGint.add (by simpa [prod] using hprodint)
  have hpoint : ∀ z : S, XPlus rate rewards C_star C_h u t a z ≤
      g z + prod z := by
    intro z
    exact XPlus_le_G_indicator_add_product rate rewards C_star C_h u t a z
  have hmono := condExp_mono (m := F)
    (XPlus_integrable rate rewards C_star C_h control0 u t a) hsumint
    (Filter.Eventually.of_forall hpoint)
  have hsum := condExp_add hGint (by simpa [prod] using hprodint) F
  have hmask := condExp_indicator (μ := mu) (m := F)
    hone hGfield
  have hconst := condExp_const (μ := mu) (m := F)
    (m₀ := (inferInstance : MeasurableSpace S)) hle (1 : ℝ)
  have hGce : mu[g | F] =ᵐ[mu] g := by
    filter_upwards [hmask] with z hmask_z
    rw [hconst] at hmask_z
    simpa [g] using hmask_z
  have hXminusMeas := XMinus_measurable rate rewards C_star C_h control0 u t a
  have hXminusAES : AEStronglyMeasurable[F]
      (XMinus rate rewards C_star C_h u t a) mu := hXminusMeas.aestronglyMeasurable
  have hYint :=
    ReferenceFirstCollectionCurrentExponentialIncrement.integrable_expRetainedIncrement
      rate rewards C_star C_h u t a control0
  have hPull := condExp_mul_of_aestronglyMeasurable_left
    hXminusAES hprodint hYint
  have hPullProd : mu[prod | F] =ᵐ[mu]
      (fun z : S => XMinus rate rewards C_star C_h u t a z *
        mu[ReferenceFirstCollectionCurrentExponentialIncrement.expRetainedIncrement
          rate rewards C_star C_h u t a | F] z) := by
    filter_upwards [hPull] with z hz
    change mu[prod | F] z =
      XMinus rate rewards C_star C_h u t a z *
        mu[ReferenceFirstCollectionCurrentExponentialIncrement.expRetainedIncrement
          rate rewards C_star C_h u t a | F] z at hz
    exact hz
  have hYbound :=
    ReferenceFirstCollectionCurrentExponentialIncrement.condExp_expRetainedIncrement_le_one
      rate rewards C_star C_h control0 u t a
  filter_upwards [hmono, hsum, hGce, hPullProd, hYbound]
    with z hmono_z hsum_z hGce_z hPullProd_z hYbound_z
  have hXnonneg := (XMinus_bounds rate rewards C_star C_h u t a z).1
  have hGle : g z ≤ 1 := by
    by_cases hz : z ∈ G <;> simp [g, hz]
  calc
    mu[(XPlus rate rewards C_star C_h u t a) | F] z ≤
        mu[(fun y : S => g y + prod y) | F] z := hmono_z
    _ = mu[g | F] z + mu[prod | F] z := by
      have hadd : (fun y : S => g y + prod y) = g + prod := by
        funext y
        rfl
      rw [hadd]
      have hprod : prod = XMinus rate rewards C_star C_h u t a *
          ReferenceFirstCollectionCurrentExponentialIncrement.expRetainedIncrement
            rate rewards C_star C_h u t a := rfl
      rw [hprod]
      exact hsum_z
    _ = g z + XMinus rate rewards C_star C_h u t a z *
        mu[ReferenceFirstCollectionCurrentExponentialIncrement.expRetainedIncrement
          rate rewards C_star C_h u t a | F] z := by
      rw [hGce_z, hPullProd_z]
    _ ≤ g z + XMinus rate rewards C_star C_h u t a z := by
      have hmul := mul_le_mul_of_nonneg_left hYbound_z hXnonneg
      have hmul' : XMinus rate rewards C_star C_h u t a z *
          mu[ReferenceFirstCollectionCurrentExponentialIncrement.expRetainedIncrement
            rate rewards C_star C_h u t a | F] z ≤
            XMinus rate rewards C_star C_h u t a z := by simpa using hmul
      linarith [hmul']
    _ ≤ XMinus rate rewards C_star C_h u t a z + 1 := by
      calc
        g z + XMinus rate rewards C_star C_h u t a z ≤
            1 + XMinus rate rewards C_star C_h u t a z :=
          by linarith [hGle]
        _ = XMinus rate rewards C_star C_h u t a z + 1 := by ring

/-- Every original source-prefix measurable set satisfies the conditional
exponential queue-step integral inequality under the same source law. -/
theorem setIntegral_XPlus_le_XMinus_add_measure (B : Set S)
    (hB : MeasurableSet[F] B) :
    (∫ z in B, XPlus rate rewards C_star C_h u t a z ∂mu) ≤
      (∫ z in B, XMinus rate rewards C_star C_h u t a z ∂mu) +
        Measure.real mu B := by
  have hplus := XPlus_integrable rate rewards C_star C_h control0 u t a
  have hminus := XMinus_integrable rate rewards C_star C_h control0 u t a
  have htarget : Integrable (fun z : S => XMinus rate rewards C_star C_h u t a z + 1)
      mu := hminus.add (integrable_const (1 : ℝ))
  have hle : F ≤ (inferInstance : MeasurableSpace S) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  calc
    (∫ z in B, XPlus rate rewards C_star C_h u t a z ∂mu) =
        ∫ z in B,
          mu[(XPlus rate rewards C_star C_h u t a) | F] z ∂mu :=
      (setIntegral_condExp hle hplus hB).symm
    _ ≤ ∫ z in B, (XMinus rate rewards C_star C_h u t a z + 1) ∂mu :=
      setIntegral_mono_ae integrable_condExp.integrableOn htarget.integrableOn
        (condExp_XPlus_le_XMinus_add_one
          rate rewards C_star C_h control0 u t a)
    _ = (∫ z in B, XMinus rate rewards C_star C_h u t a z ∂mu) +
        (∫ z in B, (1 : ℝ) ∂mu) := by
      exact integral_add hminus.integrableOn (integrable_const (1 : ℝ)).integrableOn
    _ = (∫ z in B, XMinus rate rewards C_star C_h u t a z ∂mu) +
        Measure.real mu B := by
      rw [setIntegral_const]
      simp only [smul_eq_mul, mul_one]

/-- The full-space original-law consequence of the first-call exponential
queue step. -/
theorem integral_XPlus_le_integral_XMinus_add_one (control0 : TimeControl p) :
    (∫ z : S, XPlus rate rewards C_star C_h u t a z ∂mu) ≤
      (∫ z : S, XMinus rate rewards C_star C_h u t a z ∂mu) + 1 := by
  rw [← setIntegral_univ]
  calc
    (∫ z in Set.univ, XPlus rate rewards C_star C_h u t a z ∂mu) ≤
        (∫ z in Set.univ, XMinus rate rewards C_star C_h u t a z ∂mu) +
          Measure.real mu Set.univ :=
      setIntegral_XPlus_le_XMinus_add_measure
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (control0 := control0) (u := u) (t := t) (a := a)
        (B := Set.univ) MeasurableSet.univ
    _ = (∫ z : S, XMinus rate rewards C_star C_h u t a z ∂mu) + 1 := by
      simp [Measure.real]

end Bandits.Support.ReferenceFirstCollectionCurrentExponentialQueueStep

end
