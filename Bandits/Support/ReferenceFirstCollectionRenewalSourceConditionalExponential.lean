/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalSourceExponentialTransport
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Conditional exponential estimate on the original first-renewal source

This module proves the induced incoming-readout field estimate on the same
unnormalized renewal-source measure as the coordinator transport.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionRenewalSourceConditionalExponential

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters}
variable (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

abbrev Readout (p : Parameters) :=
  ReferenceFirstCollectionRenewalSourceExponentialTransport.Readout p

local notation "Z" =>
  ReferenceFirstCollectionRenewalSourceExponentialTransport.Source
    rate rewards C_star C_h u t
local notation "nu" =>
  ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
    rate rewards C_star C_h u t
local notation "ER" =>
  ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
    rate rewards C_star C_h u t
local notation "XMinus" =>
  ReferenceFirstCollectionRenewalSourceExponentialTransport.sourceXMinus
    rate rewards C_star C_h u t
local notation "XPlus" =>
  ReferenceFirstCollectionRenewalSourceExponentialTransport.sourceXPlus
    rate rewards C_star C_h u t
local notation "sourceIndicator" =>
  ReferenceFirstCollectionRenewalSourceExponentialTransport.sourceIndicator
    rate rewards C_star C_h u t
local notation "noPastOverflow" =>
  ReferenceFirstCollectionRenewalSourceExponentialTransport.noPastOverflow
    rate rewards C_star C_h u t

/-- The literal sigma-algebra induced by the existing complete incoming readout. -/
abbrev F_ER : MeasurableSpace Z :=
  MeasurableSpace.comap ER
    (inferInstance : MeasurableSpace (Readout p))

/-- Every event in the induced readout field is measurable in the source field. -/
theorem F_ER_le_ambient :
    F_ER rate rewards C_star C_h u t ≤ (inferInstance : MeasurableSpace Z) := by
  intro s hs
  obtain ⟨Dtest, hDtest, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hs
  rw [← hpre]
  exact hDtest.preimage
    (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_incomingReadout
      rate rewards C_star C_h u t)

/-- The same incoming exponential is measurable on the induced readout field. -/
theorem measurable_sourceXMinus_F_ER (j : Fin p.K) :
    Measurable[F_ER rate rewards C_star C_h u t] (XMinus j) := by
  have hER : Measurable[F_ER rate rewards C_star C_h u t] ER :=
    comap_measurable ER
  have hvalue : Measurable (fun r : Readout p => ((r.1 j).2 : ℝ)) :=
    (measurable_of_countable fun a : ℕ × ℕ => (a.2 : ℝ)).comp
      ((measurable_pi_apply j).comp measurable_fst)
  change Measurable[F_ER rate rewards C_star C_h u t]
    (fun z : Z => Real.exp
      (CanonicalRecordingRates.beta p rate.eta.val *
        ((((ER z).1 j).2 : ℝ) / (rate.n : ℝ))))
  exact Real.measurable_exp.comp
    (measurable_const.mul ((hvalue.comp hER).div_const (rate.n : ℝ)))

/-- The same overflow indicator is measurable on the induced readout field. -/
theorem measurable_sourceIndicator_F_ER :
    Measurable[F_ER rate rewards C_star C_h u t] sourceIndicator := by
  classical
  have hER : Measurable[F_ER rate rewards C_star C_h u t] ER :=
    comap_measurable ER
  have hflag : Measurable (fun r : Readout p => r.2.1) :=
    measurable_fst.comp measurable_snd
  have hset : MeasurableSet {r : Readout p | r.2.1 = false} :=
    measurableSet_eq_fun hflag measurable_const
  have hOeq : noPastOverflow = ER ⁻¹' {r : Readout p | r.2.1 = false} := by
    ext z
    rfl
  have hO : MeasurableSet[F_ER rate rewards C_star C_h u t] noPastOverflow := by
    rw [hOeq]
    exact hset.preimage hER
  change Measurable[F_ER rate rewards C_star C_h u t]
    (fun z : Z => if z ∈ noPastOverflow then (1 : ℝ) else 0)
  exact Measurable.ite hO measurable_const measurable_const

/-- The literal no-past-overflow event remains measurable on the source. -/
theorem measurableSet_noPastOverflow : MeasurableSet noPastOverflow :=
  ReferenceFirstCollectionRenewalSourceExponentialTransport.measurableSet_noPastOverflow
    rate rewards C_star C_h u t

/-- The source overflow indicator is integrable under the finite, unnormalized law. -/
theorem integrable_sourceIndicator : Integrable sourceIndicator nu := by
  have hconst : Integrable (fun _ : Z => (1 : ℝ)) nu := integrable_const 1
  refine hconst.mono'
    (ReferenceFirstCollectionRenewalSourceExponentialTransport.measurable_sourceIndicator
      rate rewards C_star C_h u t).aestronglyMeasurable ?_
  filter_upwards with z
  by_cases hz : z ∈ noPastOverflow
  · simp [ReferenceFirstCollectionRenewalSourceExponentialTransport.sourceIndicator, hz]
  · simp [ReferenceFirstCollectionRenewalSourceExponentialTransport.sourceIndicator, hz]

private theorem integrable_bounded_readout_mul {f : Z → ℝ} (hf : Integrable f nu)
    (hfm : Measurable f) (psi : Readout p → ℝ) (B : ℝ) (_hB : 0 ≤ B)
    (hpsiMeas : Measurable psi) (hpsiBound : ∀ r, |psi r| ≤ B) :
    Integrable (fun z => psi (ER z) * f z) nu := by
  have htest : Measurable (fun z : Z => psi (ER z)) :=
    hpsiMeas.comp
      (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_incomingReadout
        rate rewards C_star C_h u t)
  have hprod := htest.mul hfm
  have hdom : Integrable (fun z : Z => B * ‖f z‖) nu := by
    simpa only [mul_comm] using hf.norm.const_mul B
  refine hdom.mono' hprod.aestronglyMeasurable ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hpsiBound (ER z)) (abs_nonneg (f z))

/-- Bounded Borel signed tests preserve integrability of the incoming exponential. -/
theorem integrable_readoutMul_sourceXMinus (control0 : TimeControl p) (j : Fin p.K)
    (psi : Readout p → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hpsiMeas : Measurable psi) (hpsiBound : ∀ r, |psi r| ≤ B) :
    Integrable (fun z => psi (ER z) * XMinus j z) nu :=
  integrable_bounded_readout_mul rate rewards C_star C_h u t
    (ReferenceFirstCollectionRenewalSourceExponentialTransport.integrable_sourceXMinus
      rate rewards C_star C_h u t control0 j)
    (ReferenceFirstCollectionRenewalSourceExponentialTransport.measurable_sourceXMinus
      rate rewards C_star C_h u t j)
    psi B hB hpsiMeas hpsiBound

/-- Bounded Borel signed tests preserve integrability of the coordinator exponential. -/
theorem integrable_readoutMul_sourceXPlus (control0 : TimeControl p) (j : Fin p.K)
    (psi : Readout p → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hpsiMeas : Measurable psi) (hpsiBound : ∀ r, |psi r| ≤ B) :
    Integrable (fun z => psi (ER z) * XPlus j z) nu :=
  integrable_bounded_readout_mul rate rewards C_star C_h u t
    (ReferenceFirstCollectionRenewalSourceExponentialTransport.integrable_sourceXPlus
      rate rewards C_star C_h u t control0 j)
    (ReferenceFirstCollectionRenewalSourceExponentialTransport.measurable_sourceXPlus
      rate rewards C_star C_h u t j)
    psi B hB hpsiMeas hpsiBound

/-- Bounded Borel signed tests preserve integrability of the overflow cost. -/
theorem integrable_readoutMul_sourceIndicator (psi : Readout p → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hpsiMeas : Measurable psi)
    (hpsiBound : ∀ r, |psi r| ≤ B) :
    Integrable (fun z => psi (ER z) * sourceIndicator z) nu :=
  integrable_bounded_readout_mul rate rewards C_star C_h u t
    (integrable_sourceIndicator rate rewards C_star C_h u t)
    (ReferenceFirstCollectionRenewalSourceExponentialTransport.measurable_sourceIndicator
      rate rewards C_star C_h u t)
    psi B hB hpsiMeas hpsiBound

private theorem integral_readoutTest_eq_setIntegral (Dtest : Set (Readout p))
    (H : Set Z) (hpre : ER ⁻¹' Dtest = H) (hH : MeasurableSet H) (f : Z → ℝ) :
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
      have hd : ER z ∈ Dtest := by change z ∈ ER ⁻¹' Dtest at hz'; exact hz'
      simp [Set.indicator, hz, hd]
    · have hz' : ER z ∉ Dtest := by
        intro hd
        apply hz
        rw [← hpre]
        exact hd
      simp [Set.indicator, hz, hz']
  rw [hfun, integral_indicator hH]

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
    _ = (∫ z in H, f z ∂μ) + (∫ z in H, g z ∂μ) := by
      rw [integral_indicator hH, integral_indicator hH]

/-- The indicator integral on any readout-field event is its exact no-overflow mass. -/
theorem setIntegral_sourceIndicator_eq_mass (H : Set Z)
    (_hH : MeasurableSet[F_ER rate rewards C_star C_h u t] H) :
    (∫ z in H, sourceIndicator z ∂nu) =
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t).real (H ∩ noPastOverflow) := by
  have hO := measurableSet_noPastOverflow rate rewards C_star C_h u t
  change (∫ z in H,
    Set.indicator noPastOverflow (fun _ : Z => (1 : ℝ)) z ∂nu) = _
  rw [setIntegral_indicator hO]
  simp

/-- Localized original-source coordinator estimate on every induced-field event. -/
theorem setIntegral_sourceXPlus_le (control0 : TimeControl p) (j : Fin p.K)
    (H : Set Z) (hH : MeasurableSet[F_ER rate rewards C_star C_h u t] H) :
    (∫ z in H, XPlus j z ∂nu) ≤
      (∫ z in H, XMinus j z ∂nu) +
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t).real (H ∩ noPastOverflow) := by
  have hHambient : MeasurableSet H :=
    (F_ER_le_ambient rate rewards C_star C_h u t) H hH
  obtain ⟨Dtest, hDtest, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hH
  have hsource :=
    ReferenceFirstCollectionRenewalSourceExponentialTransport.integral_readoutSet_sourceXPlus_le
      rate rewards C_star C_h u t control0 j Dtest hDtest
  have hplus := integral_readoutTest_eq_setIntegral rate rewards C_star C_h u t
    Dtest H hpre hHambient (XPlus j)
  have hminus := integral_readoutTest_eq_setIntegral rate rewards C_star C_h u t
    Dtest H hpre hHambient (XMinus j)
  change _ ≤ _ +
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
      rate rewards C_star C_h u t).real ((ER ⁻¹' Dtest) ∩ noPastOverflow) at hsource
  rw [hpre] at hsource
  rw [hplus, hminus] at hsource
  exact hsource

/-- Set integrals of a difference split over a measurable set. -/
private theorem setIntegral_neg_of_integrable {m : MeasurableSpace Z}
    {μ : @Measure Z m} {g : Z → ℝ} (H : Set Z) (hH : MeasurableSet[m] H) :
    (∫ z in H, -g z ∂μ) = -(∫ z in H, g z ∂μ) := by
  calc
    _ = ∫ z : Z, Set.indicator H (fun z => -g z) z ∂μ :=
      (integral_indicator hH).symm
    _ = ∫ z : Z, -(Set.indicator H g z) ∂μ := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ H <;> simp [Set.indicator, hz]
    _ = -(∫ z : Z, Set.indicator H g z ∂μ) := integral_neg _
    _ = -(∫ z in H, g z ∂μ) := by rw [integral_indicator hH]

private theorem setIntegral_sub_of_integrable {m : MeasurableSpace Z}
    {μ : @Measure Z m} {f g : Z → ℝ} (H : Set Z) (hH : MeasurableSet[m] H)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ z in H, f z - g z ∂μ) =
      (∫ z in H, f z ∂μ) - (∫ z in H, g z ∂μ) := by
  calc
    _ = (∫ z in H, f z ∂μ) + (∫ z in H, -g z ∂μ) := by
      rw [show (fun z : Z => f z - g z) = fun z => f z + -g z by
        funext z; exact sub_eq_add_neg _ _]
      exact setIntegral_add_of_integrable rate rewards C_star C_h u t H hH hf hg.neg
    _ = _ := by
      rw [setIntegral_neg_of_integrable rate rewards C_star C_h u t H hH]
      exact (sub_eq_add_neg _ _).symm

/-- Conditional expectation of the coordinator-post exponential is bounded by
the incoming exponential and the literal overflow cost on the induced field. -/
theorem condExp_sourceXPlus_le_sourceXMinus_add_indicator
    (control0 : TimeControl p) (j : Fin p.K) :
    (nu[XPlus j | F_ER rate rewards C_star C_h u t]) ≤ᵐ[nu]
      (fun z : Z => XMinus j z + sourceIndicator z) := by
  let m₀ : MeasurableSpace Z := inferInstance
  let μ₀ : @Measure Z m₀ := nu
  let m : MeasurableSpace Z := F_ER rate rewards C_star C_h u t
  have hm : m ≤ m₀ := F_ER_le_ambient rate rewards C_star C_h u t
  let μm : @Measure Z m := @Measure.trim Z m m₀ μ₀ hm
  have hfiniteTrim : IsFiniteMeasure μm := by infer_instance
  have _hsigmaFiniteTrim : SigmaFinite μm := by infer_instance
  let ce : Z → ℝ := μ₀[XPlus j | m]
  let rhs : Z → ℝ := fun z => XMinus j z + sourceIndicator z
  have hplus : Integrable (XPlus j) μ₀ :=
    ReferenceFirstCollectionRenewalSourceExponentialTransport.integrable_sourceXPlus
      rate rewards C_star C_h u t control0 j
  have hminus : Integrable (XMinus j) μ₀ :=
    ReferenceFirstCollectionRenewalSourceExponentialTransport.integrable_sourceXMinus
      rate rewards C_star C_h u t control0 j
  have hindicator : Integrable sourceIndicator μ₀ := integrable_sourceIndicator
    rate rewards C_star C_h u t
  have hceSM : StronglyMeasurable[m] ce := by
    dsimp [ce]
    exact stronglyMeasurable_condExp
  have hce : Integrable ce μ₀ := by
    dsimp [ce]
    exact integrable_condExp
  have hceTrim : Integrable ce μm := hce.trim hm hceSM
  have hminusField : Measurable[m] (XMinus j) :=
    measurable_sourceXMinus_F_ER rate rewards C_star C_h u t j
  have hindicatorField : Measurable[m] sourceIndicator :=
    measurable_sourceIndicator_F_ER rate rewards C_star C_h u t
  have hrhsField : Measurable[m] rhs := by
    exact hminusField.add hindicatorField
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
        (∫ z in H, ce z ∂μ₀) = ∫ z in H, XPlus j z ∂μ₀ :=
      setIntegral_condExp hm hplus hH
    have hlocalized := setIntegral_sourceXPlus_le
      rate rewards C_star C_h u t control0 j H hH
    have hindicatorSet := setIntegral_sourceIndicator_eq_mass
      rate rewards C_star C_h u t H hH
    have hsumSet := setIntegral_add_of_integrable rate rewards C_star C_h u t
      H ((F_ER_le_ambient rate rewards C_star C_h u t) H hH) hminus hindicator
    have hceLeRhs :
        (∫ z in H, ce z ∂μ₀) ≤ ∫ z in H, rhs z ∂μ₀ := by
      rw [hceSet]
      dsimp [rhs]
      rw [hsumSet, hindicatorSet]
      exact hlocalized
    have hceTrimSet :
        (∫ z in H, ce z ∂μ₀) = ∫ z in H, ce z ∂μm := by
      simpa [μm] using
        (setIntegral_trim (μ := μ₀) hm hceSM hH)
    have hrhsTrimSet :
        (∫ z in H, rhs z ∂μ₀) = ∫ z in H, rhs z ∂μm := by
      simpa [μm] using
        (setIntegral_trim (μ := μ₀) hm hrhsSM hH)
    have hceLeRhsTrim :
        (∫ z in H, ce z ∂μm) ≤ ∫ z in H, rhs z ∂μm := by
      rw [← hceTrimSet, ← hrhsTrimSet]
      exact hceLeRhs
    rw [setIntegral_sub_of_integrable rate rewards C_star C_h u t H hH
      hrhsTrim hceTrim]
    exact sub_nonneg.mpr hceLeRhsTrim
  have hleTrim : ce ≤ᵐ[μm] rhs := by
    filter_upwards [hnonneg] with z hz
    exact sub_nonneg.mp hz
  have hle : ce ≤ᵐ[μ₀] rhs :=
    MeasureTheory.ae_le_of_ae_le_trim (hm := hm) hleTrim
  simpa [ce, μ₀, rhs] using hle

end Bandits.Support.ReferenceFirstCollectionRenewalSourceConditionalExponential

end
