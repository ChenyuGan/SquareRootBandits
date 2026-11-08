/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalWholeExponentialQueueStep
public import Bandits.Support.ReferenceFirstCollectionRenewalSourceConditionalExponential

import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Whole-marker exponential step on the original renewal source

The post-update exponential uses the existing complete whole-marker readout.
Its conditional estimate is transferred from the admitted pair law to the
same unnormalized renewal-source law, on the original incoming-readout field.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionRenewalWholeSourceExponentialStep

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev Readout (p : Parameters) :=
  ReferenceFirstCollectionRenewalSourceConditionalExponential.Readout p

variable {p : Parameters}
variable (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

abbrev Source :=
  ReferenceFirstCollectionRenewalSourceExponentialTransport.Source
    rate rewards C_star C_h u t
abbrev Pair :=
  ReferenceFirstCollectionRenewalWholeExponentialQueueStep.Pair
    rate rewards C_star C_h u t

local instance sourceInputMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance renewalBaseMeasurableSpace :
    MeasurableSpace
      (ReferenceFirstCollectionRenewalControlFactor.RenewalBase
        rate rewards C_star C_h u t) := by
  change MeasurableSpace
    (ReferenceFirstCollectionRenewalControlFactor.Source
        rate rewards C_star C_h u t ×
      ReferenceFirstCollectionRenewalControlFactor.AuxiliaryArray p)
  infer_instance

local notation "Z" => Source rate rewards C_star C_h u t
local notation "B" => Pair rate rewards C_star C_h u t
local notation "mu" =>
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
    rate rewards C_star C_h u t
local notation "nu" =>
  ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
    rate rewards C_star C_h u t
local notation "ER" =>
  ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
    rate rewards C_star C_h u t
local notation "F_ER" =>
  ReferenceFirstCollectionRenewalSourceConditionalExponential.F_ER
    rate rewards C_star C_h u t
local notation "XMinus" =>
  ReferenceFirstCollectionRenewalSourceExponentialTransport.sourceXMinus
    rate rewards C_star C_h u t
local notation "sourceIndicator" =>
  ReferenceFirstCollectionRenewalSourceExponentialTransport.sourceIndicator
    rate rewards C_star C_h u t
local notation "noPastOverflow" =>
  ReferenceFirstCollectionRenewalSourceExponentialTransport.noPastOverflow
    rate rewards C_star C_h u t
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val

local instance pairLawIsFinite : IsFiniteMeasure mu :=
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_finite
    rate rewards C_star C_h u t

/-- Exponential of the actual whole-marker post-readout backlog on the
original renewal source. The readout retains registers, overflow, and every
accepted history, and is stepped with the existing whole current cell. -/
def sourceWholeXPlus (j : Fin p.K) (z : Z) : ℝ :=
  Real.exp (beta *
    ((((ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
      rate rewards C_star C_h u t z).1 j).2 : ℝ) / (rate.n : ℝ)))

/-- The literal original-source whole post agrees pointwise with the pair
whole post after projection to the same source coordinate. -/
theorem sourceWholeXPlus_eq_fullXPlus_comp_snd (j : Fin p.K) :
    (fun b : B => sourceWholeXPlus rate rewards C_star C_h u t j b.2) =
      (fun b : B =>
        ReferenceFirstCollectionRenewalWholeExponentialQueueStep.fullXPlus
          rate rewards C_star C_h u t j b) := by
  funext b
  rfl

/-- The whole-source post exponential is ambient Borel measurable. -/
theorem measurable_sourceWholeXPlus (j : Fin p.K) :
    Measurable (sourceWholeXPlus rate rewards C_star C_h u t j) := by
  have hpost : Measurable
      (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
        rate rewards C_star C_h u t) :=
    ReferenceFirstCollectionRenewalSourceCurrentPrefix.measurable_wholePostReadout
      rate rewards C_star C_h u t
  have hvalue : Measurable (fun r : Readout p => ((r.1 j).2 : ℝ)) :=
    (measurable_of_countable fun a : ℕ × ℕ => (a.2 : ℝ)).comp
      ((measurable_pi_apply j).comp measurable_fst)
  change Measurable (fun z : Z => Real.exp (beta *
    ((((ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
      rate rewards C_star C_h u t z).1 j).2 : ℝ) / (rate.n : ℝ))))
  exact Real.measurable_exp.comp
    (measurable_const.mul ((hvalue.comp hpost).div_const (rate.n : ℝ)))

private theorem integral_source_eq_pair (f : Z → ℝ) (hf : Measurable f) :
    (∫ z : Z, f z ∂nu) = ∫ b : B, f b.2 ∂mu := by
  rw [← ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_map_snd
    rate rewards C_star C_h u t]
  rw [integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable]

/-- Integrability of the literal whole post exponential follows by pushing
the existing pair-law L1 result through its exact second-coordinate identity. -/
theorem integrable_sourceWholeXPlus (control0 : TimeControl p) (j : Fin p.K) :
    Integrable (sourceWholeXPlus rate rewards C_star C_h u t j) nu := by
  rw [← ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_map_snd
    rate rewards C_star C_h u t]
  have hcomp : Integrable
      ((sourceWholeXPlus rate rewards C_star C_h u t j) ∘ Prod.snd) mu := by
    change Integrable
      (fun b : B => sourceWholeXPlus rate rewards C_star C_h u t j b.2) mu
    rw [sourceWholeXPlus_eq_fullXPlus_comp_snd rate rewards C_star C_h u t j]
    exact ReferenceFirstCollectionRenewalWholeExponentialQueueStep.integrable_fullXPlus
      rate rewards C_star C_h u t control0 j
  exact (integrable_map_measure
    (measurable_sourceWholeXPlus rate rewards C_star C_h u t j).aestronglyMeasurable
    measurable_snd.aemeasurable).mpr hcomp

/-- The source integral is exactly the integral of the existing whole pair
exponential; the identity is pointwise, not merely almost everywhere. -/
theorem integral_sourceWholeXPlus_eq_integral_fullXPlus
    (j : Fin p.K) :
    (∫ z : Z, sourceWholeXPlus rate rewards C_star C_h u t j z ∂nu) =
      ∫ b : B,
        ReferenceFirstCollectionRenewalWholeExponentialQueueStep.fullXPlus
          rate rewards C_star C_h u t j b ∂mu := by
  calc
    _ = ∫ b : B, sourceWholeXPlus rate rewards C_star C_h u t j b.2 ∂mu :=
      integral_source_eq_pair rate rewards C_star C_h u t
        (sourceWholeXPlus rate rewards C_star C_h u t j)
        (measurable_sourceWholeXPlus rate rewards C_star C_h u t j)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with b
      exact congrFun
        (sourceWholeXPlus_eq_fullXPlus_comp_snd rate rewards C_star C_h u t j) b

private theorem integrable_bounded_readout_mul {f : Z → ℝ}
    (hf : Integrable f nu) (hfm : Measurable f)
    (psi : Readout p → ℝ) (C : ℝ) (_hC : 0 ≤ C)
    (hpsiMeas : Measurable psi) (hpsiBound : ∀ r, |psi r| ≤ C) :
    Integrable (fun z : Z => psi (ER z) * f z) nu := by
  have htest : Measurable (fun z : Z => psi (ER z)) :=
    hpsiMeas.comp
      (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_incomingReadout
        rate rewards C_star C_h u t)
  have hprod := htest.mul hfm
  have hdom : Integrable (fun z : Z => C * ‖f z‖) nu := by
    simpa only [mul_comm] using hf.norm.const_mul C
  refine hdom.mono' hprod.aestronglyMeasurable ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hpsiBound (ER z)) (abs_nonneg (f z))

/-- Every bounded Borel incoming-readout test product with the whole post
exponential is integrable under the same finite, unnormalized source law. -/
theorem integrable_readoutMul_sourceWholeXPlus (control0 : TimeControl p)
    (j : Fin p.K) (psi : Readout p → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hpsiMeas : Measurable psi) (hpsiBound : ∀ r, |psi r| ≤ C) :
    Integrable (fun z : Z => psi (ER z) * sourceWholeXPlus
      rate rewards C_star C_h u t j z) nu := by
  exact integrable_bounded_readout_mul rate rewards C_star C_h u t
    (integrable_sourceWholeXPlus rate rewards C_star C_h u t control0 j)
    (measurable_sourceWholeXPlus rate rewards C_star C_h u t j)
    psi C hC hpsiMeas hpsiBound

/-- The incoming-readout weighted bound on the admitted whole pair law
transfers to the same original source law, keeping its exact event cost. -/
theorem integral_readoutMul_sourceWholeXPlus_le (control0 : TimeControl p)
    (j : Fin p.K) (psi : Readout p → ℝ) (hpsi : Measurable psi)
    (Ctest : ℝ) (hCtest : 0 ≤ Ctest)
    (hpsiBound : ∀ x, 0 ≤ psi x ∧ psi x ≤ Ctest) :
    (∫ z : Z, psi (ER z) * sourceWholeXPlus
        rate rewards C_star C_h u t j z ∂nu) ≤
      (∫ z : Z, psi (ER z) * XMinus j z ∂nu) +
        ∫ z : Z, psi (ER z) * sourceIndicator z ∂nu := by
  have hreadout : Measurable (fun z : Z => psi (ER z)) :=
    hpsi.comp
      (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_incomingReadout
        rate rewards C_star C_h u t)
  have hwholeMeas : Measurable
      (fun z : Z => psi (ER z) * sourceWholeXPlus rate rewards C_star C_h u t j z) :=
    hreadout.mul (measurable_sourceWholeXPlus rate rewards C_star C_h u t j)
  have hminusMeas : Measurable (fun z : Z => psi (ER z) * XMinus j z) :=
    hreadout.mul
      (ReferenceFirstCollectionRenewalSourceExponentialTransport.measurable_sourceXMinus
        rate rewards C_star C_h u t j)
  have hcostMeas : Measurable (fun z : Z => psi (ER z) * sourceIndicator z) :=
    hreadout.mul
      (ReferenceFirstCollectionRenewalSourceExponentialTransport.measurable_sourceIndicator
        rate rewards C_star C_h u t)
  have hwholePair :
      (∫ z : Z, psi (ER z) * sourceWholeXPlus rate rewards C_star C_h u t j z ∂nu) =
        ∫ b : B, psi (ER b.2) *
          ReferenceFirstCollectionRenewalWholeExponentialQueueStep.fullXPlus
            rate rewards C_star C_h u t j b ∂mu := by
    calc
      _ = ∫ b : B, psi (ER b.2) *
          sourceWholeXPlus rate rewards C_star C_h u t j b.2 ∂mu :=
        integral_source_eq_pair rate rewards C_star C_h u t
          (fun z => psi (ER z) * sourceWholeXPlus rate rewards C_star C_h u t j z)
          hwholeMeas
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with b
        rw [congrFun
          (sourceWholeXPlus_eq_fullXPlus_comp_snd rate rewards C_star C_h u t j) b]
  have hminusPair :
      (∫ z : Z, psi (ER z) * XMinus j z ∂nu) =
        ∫ b : B, psi (ER b.2) *
          ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
            rate rewards C_star C_h u t control0 j b ∂mu := by
    calc
      _ = ∫ b : B, psi (ER b.2) * XMinus j b.2 ∂mu :=
        integral_source_eq_pair rate rewards C_star C_h u t
          (fun z => psi (ER z) * XMinus j z) hminusMeas
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with b
        rw [← congrFun
          (ReferenceFirstCollectionRenewalSourceExponentialTransport.sourceXMinus_eq_XMinus_comp_snd
            rate rewards C_star C_h u t control0 j) b]
  have hcostPair :
      (∫ z : Z, psi (ER z) * sourceIndicator z ∂nu) =
        ∫ b : B, psi (ER b.2) *
          ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
            rate rewards C_star C_h u t control0 b ∂mu := by
    calc
      _ = ∫ b : B, psi (ER b.2) * sourceIndicator b.2 ∂mu :=
        integral_source_eq_pair rate rewards C_star C_h u t
          (fun z => psi (ER z) * sourceIndicator z) hcostMeas
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [
          ReferenceFirstCollectionRenewalSourceExponentialTransport.ae_sourceIndicator_eq_indicatorG
            rate rewards C_star C_h u t control0] with b hb
        exact congrArg (fun x : ℝ => psi (ER b.2) * x) hb
  have hpair :=
    ReferenceFirstCollectionRenewalWholeExponentialQueueStep.integral_incomingReadout_mul_fullXPlus_le
      rate rewards C_star C_h u t control0 j psi hpsi Ctest hCtest hpsiBound
  calc
    _ = _ := hwholePair
    _ ≤ _ := hpair
    _ = _ := by rw [← hminusPair, ← hcostPair]

private theorem integral_readoutTest_eq_setIntegral (Dtest : Set (Readout p))
    (H : Set Z) (hpre : ER ⁻¹' Dtest = H) (hH : MeasurableSet H)
    (f : Z → ℝ) :
    (∫ z : Z,
      (Dtest.indicator (fun _ : Readout p => (1 : ℝ))) (ER z) * f z ∂nu) =
      ∫ z in H, f z ∂nu := by
  have hfun :
      (fun z : Z =>
        (Dtest.indicator (fun _ : Readout p => (1 : ℝ))) (ER z) * f z) =
        fun z => Set.indicator H f z := by
    funext z
    by_cases hz : z ∈ H
    · have hz' : z ∈ ER ⁻¹' Dtest := by rw [hpre]; exact hz
      have hd : ER z ∈ Dtest := by
        change z ∈ ER ⁻¹' Dtest at hz'
        exact hz'
      simp [Set.indicator, hz, hd]
    · have hz' : ER z ∉ Dtest := by
        intro hd
        apply hz
        rw [← hpre]
        exact hd
      simp [Set.indicator, hz, hz']
  rw [hfun, integral_indicator hH]

private theorem integral_readoutTest_mul_sourceIndicator_eq_mass
    (Dtest : Set (Readout p)) (hDtest : MeasurableSet Dtest) :
    (∫ z : Z,
      (Dtest.indicator (fun _ : Readout p => (1 : ℝ))) (ER z) *
        sourceIndicator z ∂nu) =
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t).real
        (ER ⁻¹' Dtest ∩ noPastOverflow) := by
  let psi : Readout p → ℝ := Dtest.indicator (fun _ => (1 : ℝ))
  have hset : MeasurableSet (ER ⁻¹' Dtest ∩ noPastOverflow) :=
    (hDtest.preimage
      (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_incomingReadout
        rate rewards C_star C_h u t)).inter
      (ReferenceFirstCollectionRenewalSourceExponentialTransport.measurableSet_noPastOverflow
        rate rewards C_star C_h u t)
  have hpoint :
      (fun z : Z => psi (ER z) * sourceIndicator z) =
        Set.indicator (ER ⁻¹' Dtest ∩ noPastOverflow)
          (fun _ : Z => (1 : ℝ)) := by
    funext z
    by_cases hd : ER z ∈ Dtest <;>
      by_cases ho : z ∈ noPastOverflow <;>
      simp [psi,
        ReferenceFirstCollectionRenewalSourceExponentialTransport.sourceIndicator,
        Set.indicator, Set.mem_inter_iff, Set.mem_preimage, hd, ho]
  calc
    _ = ∫ z : Z,
        Set.indicator (ER ⁻¹' Dtest ∩ noPastOverflow)
          (fun _ : Z => (1 : ℝ)) z ∂nu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => congrFun hpoint z)
    _ = _ := by
      rw [integral_indicator_const (1 : ℝ) hset]
      simp

/-- Every event measurable in the exact incoming-readout field inherits the
localized whole-source exponential estimate and its actual overflow mass. -/
theorem setIntegral_sourceWholeXPlus_le (control0 : TimeControl p)
    (j : Fin p.K) (H : Set Z)
    (hH : MeasurableSet[F_ER] H) :
    (∫ z in H, sourceWholeXPlus rate rewards C_star C_h u t j z ∂nu) ≤
      (∫ z in H, XMinus j z ∂nu) +
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t).real (H ∩ noPastOverflow) := by
  have hHambient : MeasurableSet H :=
    (ReferenceFirstCollectionRenewalSourceConditionalExponential.F_ER_le_ambient
      rate rewards C_star C_h u t) H hH
  obtain ⟨Dtest, hDtest, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hH
  let psi : Readout p → ℝ := Dtest.indicator (fun _ => (1 : ℝ))
  have hpsiMeas : Measurable psi := by
    change Measurable (Dtest.indicator (fun _ : Readout p => (1 : ℝ)))
    exact Measurable.indicator measurable_const hDtest
  have hpsiBound : ∀ x, 0 ≤ psi x ∧ psi x ≤ 1 := by
    intro x
    by_cases hx : x ∈ Dtest <;> simp [psi, hx]
  have hsource := integral_readoutMul_sourceWholeXPlus_le
    rate rewards C_star C_h u t control0 j psi hpsiMeas 1 (by norm_num) hpsiBound
  have hcost := integral_readoutTest_mul_sourceIndicator_eq_mass
    rate rewards C_star C_h u t Dtest hDtest
  have hplus := integral_readoutTest_eq_setIntegral rate rewards C_star C_h u t
    Dtest H hpre hHambient (sourceWholeXPlus rate rewards C_star C_h u t j)
  have hminus := integral_readoutTest_eq_setIntegral rate rewards C_star C_h u t
    Dtest H hpre hHambient (XMinus j)
  rw [hcost] at hsource
  rw [hpre] at hsource
  rw [hplus, hminus] at hsource
  exact hsource

private theorem setIntegral_add_of_integrable {m : MeasurableSpace Z}
    {μ : @Measure Z m} {f g : Z → ℝ} (H : Set Z)
    (hH : MeasurableSet[m] H) (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ z in H, f z + g z ∂μ) =
      (∫ z in H, f z ∂μ) + (∫ z in H, g z ∂μ) := by
  calc
    _ = ∫ z : Z, Set.indicator H (fun z => f z + g z) z ∂μ :=
      (integral_indicator hH).symm
    _ = ∫ z : Z, (Set.indicator H f z + Set.indicator H g z) ∂μ := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ H <;> simp [Set.indicator, hz]
    _ = (∫ z : Z, Set.indicator H f z ∂μ) +
        (∫ z : Z, Set.indicator H g z ∂μ) :=
      integral_add (hf.indicator hH) (hg.indicator hH)
    _ = _ := by rw [integral_indicator hH, integral_indicator hH]

private theorem setIntegral_neg_of_integrable {m : MeasurableSpace Z}
    {μ : @Measure Z m} {g : Z → ℝ} (H : Set Z)
    (hH : MeasurableSet[m] H) :
    (∫ z in H, -g z ∂μ) = -(∫ z in H, g z ∂μ) := by
  calc
    _ = ∫ z : Z, Set.indicator H (fun z => -g z) z ∂μ :=
      (integral_indicator hH).symm
    _ = ∫ z : Z, -(Set.indicator H g z) ∂μ := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ H <;> simp [Set.indicator, hz]
    _ = -(∫ z : Z, Set.indicator H g z ∂μ) := integral_neg _
    _ = _ := by rw [integral_indicator hH]

private theorem setIntegral_sub_of_integrable {m : MeasurableSpace Z}
    {μ : @Measure Z m} {f g : Z → ℝ} (H : Set Z)
    (hH : MeasurableSet[m] H) (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ z in H, f z - g z ∂μ) =
      (∫ z in H, f z ∂μ) - (∫ z in H, g z ∂μ) := by
  calc
    _ = (∫ z in H, f z ∂μ) + (∫ z in H, -g z ∂μ) := by
      rw [show (fun z : Z => f z - g z) = fun z => f z + -g z by
        funext z; exact sub_eq_add_neg _ _]
      exact setIntegral_add_of_integrable rate rewards C_star C_h u t
        H hH hf hg.neg
    _ = _ := by
      rw [setIntegral_neg_of_integrable rate rewards C_star C_h u t H hH]
      exact (sub_eq_add_neg _ _).symm

/-- Conditional expectation of the whole-marker post exponential is bounded
on the original incoming-readout field, under the original unnormalized law. -/
theorem condExp_sourceWholeXPlus_le_sourceXMinus_add_indicator
    (control0 : TimeControl p) (j : Fin p.K) :
    (nu[sourceWholeXPlus rate rewards C_star C_h u t j | F_ER]) ≤ᵐ[nu]
      (fun z : Z => XMinus j z + sourceIndicator z) := by
  let m₀ : MeasurableSpace Z := inferInstance
  let μ₀ : @Measure Z m₀ := nu
  let m : MeasurableSpace Z := F_ER
  have hm : m ≤ m₀ :=
    ReferenceFirstCollectionRenewalSourceConditionalExponential.F_ER_le_ambient
      rate rewards C_star C_h u t
  let μm : @Measure Z m := @Measure.trim Z m m₀ μ₀ hm
  have hfiniteTrim : IsFiniteMeasure μm := by infer_instance
  have _hsigmaFiniteTrim : SigmaFinite μm := by infer_instance
  let ce : Z → ℝ := μ₀[sourceWholeXPlus rate rewards C_star C_h u t j | m]
  let rhs : Z → ℝ := fun z => XMinus j z + sourceIndicator z
  have hplus : Integrable (sourceWholeXPlus rate rewards C_star C_h u t j) μ₀ :=
    integrable_sourceWholeXPlus rate rewards C_star C_h u t control0 j
  have hminus : Integrable (XMinus j) μ₀ :=
    ReferenceFirstCollectionRenewalSourceExponentialTransport.integrable_sourceXMinus
      rate rewards C_star C_h u t control0 j
  have hindicator : Integrable sourceIndicator μ₀ :=
    ReferenceFirstCollectionRenewalSourceConditionalExponential.integrable_sourceIndicator
      rate rewards C_star C_h u t
  have hceSM : StronglyMeasurable[m] ce := by
    dsimp [ce]
    exact stronglyMeasurable_condExp
  have hce : Integrable ce μ₀ := by
    dsimp [ce]
    exact integrable_condExp
  have hceTrim : Integrable ce μm := hce.trim hm hceSM
  have hminusField : Measurable[m] (XMinus j) :=
    ReferenceFirstCollectionRenewalSourceConditionalExponential.measurable_sourceXMinus_F_ER
      rate rewards C_star C_h u t j
  have hindicatorField : Measurable[m] sourceIndicator :=
    ReferenceFirstCollectionRenewalSourceConditionalExponential.measurable_sourceIndicator_F_ER
      rate rewards C_star C_h u t
  have hrhsField : Measurable[m] rhs := hminusField.add hindicatorField
  have hrhsSM : StronglyMeasurable[m] rhs := hrhsField.stronglyMeasurable
  have hrhs : Integrable rhs μ₀ := by
    dsimp [rhs]
    exact hminus.add hindicator
  have hrhsTrim : Integrable rhs μm := hrhs.trim hm hrhsSM
  have hdiffTrim : Integrable (fun z => rhs z - ce z) μm := hrhsTrim.sub hceTrim
  have hnonneg : 0 ≤ᵐ[μm] (fun z => rhs z - ce z) := by
    apply ae_nonneg_of_forall_setIntegral_nonneg hdiffTrim
    intro H hH _hμH
    have hμH : μm H < ⊤ :=
      (measure_mono (Set.subset_univ H)).trans_lt hfiniteTrim.measure_univ_lt_top
    have hceSet :
        (∫ z in H, ce z ∂μ₀) =
          ∫ z in H, sourceWholeXPlus rate rewards C_star C_h u t j z ∂μ₀ :=
      setIntegral_condExp hm hplus hH
    have hlocalized := setIntegral_sourceWholeXPlus_le
      rate rewards C_star C_h u t control0 j H hH
    have hindicatorSet :=
      ReferenceFirstCollectionRenewalSourceConditionalExponential.setIntegral_sourceIndicator_eq_mass
        rate rewards C_star C_h u t H hH
    have hsumSet := setIntegral_add_of_integrable rate rewards C_star C_h u t H
      ((ReferenceFirstCollectionRenewalSourceConditionalExponential.F_ER_le_ambient
        rate rewards C_star C_h u t) H hH) hminus hindicator
    have hceLeRhs :
        (∫ z in H, ce z ∂μ₀) ≤ ∫ z in H, rhs z ∂μ₀ := by
      rw [hceSet]
      dsimp [rhs]
      rw [hsumSet, hindicatorSet]
      exact hlocalized
    have hceTrimSet :
        (∫ z in H, ce z ∂μ₀) = ∫ z in H, ce z ∂μm := by
      simpa [μm] using (setIntegral_trim (μ := μ₀) hm hceSM hH)
    have hrhsTrimSet :
        (∫ z in H, rhs z ∂μ₀) = ∫ z in H, rhs z ∂μm := by
      simpa [μm] using (setIntegral_trim (μ := μ₀) hm hrhsSM hH)
    have hceLeRhsTrim :
        (∫ z in H, ce z ∂μm) ≤ ∫ z in H, rhs z ∂μm := by
      rw [← hceTrimSet, ← hrhsTrimSet]
      exact hceLeRhs
    rw [setIntegral_sub_of_integrable rate rewards C_star C_h u t
      H hH hrhsTrim hceTrim]
    exact sub_nonneg.mpr hceLeRhsTrim
  have hleTrim : ce ≤ᵐ[μm] rhs := by
    filter_upwards [hnonneg] with z hz
    exact sub_nonneg.mp hz
  have hle : ce ≤ᵐ[μ₀] rhs :=
    MeasureTheory.ae_le_of_ae_le_trim (hm := hm) hleTrim
  simpa [ce, μ₀, rhs] using hle

/-- Unweighted whole-source estimate, with the exact no-past-overflow mass
under the possibly-zero renewal-source measure. -/
theorem integral_sourceWholeXPlus_le_integral_sourceXMinus_add_noPastOverflow
    (control0 : TimeControl p) (j : Fin p.K) :
    (∫ z : Z, sourceWholeXPlus rate rewards C_star C_h u t j z ∂nu) ≤
      (∫ z : Z, XMinus j z ∂nu) +
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t).real noPastOverflow := by
  have hweighted := integral_readoutMul_sourceWholeXPlus_le
    rate rewards C_star C_h u t control0 j (fun _ : Readout p => (1 : ℝ))
    measurable_const 1 (by norm_num)
    (by intro x; norm_num)
  have hcost :=
    ReferenceFirstCollectionRenewalSourceExponentialTransport.integral_sourceIndicator_eq_mass
      rate rewards C_star C_h u t
  simp only [one_mul] at hweighted
  rw [hcost] at hweighted
  exact hweighted

end Bandits.Support.ReferenceFirstCollectionRenewalWholeSourceExponentialStep

end
