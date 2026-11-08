/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENS
-/
module

public import Bandits.Support.ReferenceFirstCollectionCurrentQueueEnergy
public import Bandits.Support.ReferenceFirstCollectionCurrentAnchorRateCredit

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Original first collection-call conditional weighted energy drift

This module conditions the actual first-call deterministic energy envelope
under the original source law and source-prefix filtration. It consumes the
retained raw conditional moments and the actual current-call inverse-rate
credit, with the same retained gate on every term.

Sources: `04_slow_fast_learner.tex:140-188,245-322`,
`05_binary_transport.tex:352-431`, and `06_interruptions.tex:355-426`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Bandits.Support.ReferenceFirstCollectionCurrentConditionalWeightedDrift

open ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ActualInitializationPhysicalStep (GridRewardTable)
open ContinuousLearningRows (TimeControl)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefixFiltration)
open ReferenceFirstCollectionCurrentRetainedGate (G)
open ReferenceFirstCollectionCurrentQueueEnergy
open ReferenceFirstCollectionCurrentQueueReadout
  (bMinus bMinus_measurable Bcap bMinus_global_bounds)
open ReferenceFirstCollectionCurrentRetainedMoments
  (retainedRaw retainedRaw_integrable retainedRaw_sq_integrable
    retainedRaw_condExp retainedRaw_sq_condExp retainedMomentOne retainedMomentTwo
    retainedMoment_bounds_on_G)
open ReferenceFirstCollectionCurrentRetainedGate (measurableSet_G)
open ReferenceFirstCollectionCurrentAnchorRateCredit (G_actual_rate_credit)

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)

local instance sourceInputMeasurableSpace : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local notation "μ" => sourceInputLaw p

private theorem integrable_of_bounded_measurable
    {f : SourceInput p → ℝ} (hf : Measurable f) (C : ℝ)
    (_hC : 0 ≤ C) (hbound : ∀ z, ‖f z‖ ≤ C) :
    Integrable f (sourceInputLaw p) := by
  have hconst : Integrable (fun _ : SourceInput p => C) (sourceInputLaw p) :=
    integrable_const C
  refine hconst.mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with z
  simpa [Real.norm_eq_abs, abs_of_nonneg _hC] using hbound z

private theorem reducedTerm_condExp (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    (sourceInputLaw p)[reducedDriftTerm rate rewards C_star C_h u t a | sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[
      sourceInputLaw p] (G rate rewards C_star C_h u t).indicator
        (fun z => thetaMinus rate rewards C_star C_h u t a z *
          ((-15 / 2 : ℝ) * bMinus rate rewards C_star C_h u t a z +
            (2 * bMinus rate rewards C_star C_h u t a z + 1 / 2) *
              retainedMomentOne rate rewards C_star C_h u t a z +
            retainedMomentTwo rate rewards C_star C_h u t a z + 16)) := by
  let g := G rate rewards C_star C_h u t
  let θ := thetaMinus rate rewards C_star C_h u t a
  let b := bMinus rate rewards C_star C_h u t a
  let A := retainedRaw rate rewards C_star C_h u t a
  let A2 := fun z : SourceInput p => (A z) ^ 2
  let B1 := retainedMomentOne rate rewards C_star C_h u t a
  let B2 := retainedMomentTwo rate rewards C_star C_h u t a
  let k0 : SourceInput p → ℝ := g.indicator (fun z =>
    θ z * ((-15 / 2 : ℝ) * b z + 16))
  let k1 : SourceInput p → ℝ := g.indicator (fun z =>
    θ z * (2 * b z + 1 / 2))
  let k2 : SourceInput p → ℝ := g.indicator θ

  have hFle : sourcePrefixFiltration control0 (t.val + 1) ≤ sourceInputMeasurableSpace :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hG : MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)] g := by
    simpa [g] using measurableSet_G
      rate rewards C_star C_h control0 u t
  have hθ : Measurable[sourcePrefixFiltration control0 (t.val + 1)] θ := by
    simpa [θ] using measurable_thetaMinus
      rate rewards C_star C_h control0 u t a
  have hb : Measurable[sourcePrefixFiltration control0 (t.val + 1)] b := by
    simpa [b] using bMinus_measurable
      rate rewards C_star C_h control0 u t a
  have hk0 : Measurable[sourcePrefixFiltration control0 (t.val + 1)] k0 := by
    exact (hθ.mul ((hb.const_mul _).add measurable_const)).indicator hG
  have hk1 : Measurable[sourcePrefixFiltration control0 (t.val + 1)] k1 := by
    exact (hθ.mul ((hb.const_mul _).add measurable_const)).indicator hG
  have hk2 : Measurable[sourcePrefixFiltration control0 (t.val + 1)] k2 := hθ.indicator hG
  have hk0ambient : Measurable[sourceInputMeasurableSpace] k0 :=
    Measurable.mono hk0 hFle le_rfl
  have hk1ambient : Measurable[sourceInputMeasurableSpace] k1 :=
    Measurable.mono hk1 hFle le_rfl
  have hk2ambient : Measurable[sourceInputMeasurableSpace] k2 :=
    Measurable.mono hk2 hFle le_rfl

  have hθb (z : SourceInput p) :
    0 ≤ θ z ∧ θ z ≤ 1 ∧ 0 ≤ b z ∧ b z ≤ 2 * Bcap rate := by
    have hθ' := thetaMinus_bounds rate rewards C_star C_h u t a z
    have hb' := bMinus_global_bounds rate rewards C_star C_h u t a z
    exact ⟨hθ'.1, hθ'.2, hb'.1, hb'.2⟩
  have hBcap : 0 ≤ Bcap rate := by
    unfold Bcap
    exact le_of_lt (one_div_pos.mpr (by positivity [rate.eta.property]))
  have hC0 : 0 ≤ (15 / 2 : ℝ) * (2 * Bcap rate) + 16 := by positivity
  have hC1 : 0 ≤ 2 * (2 * Bcap rate) + 1 / 2 := by positivity
  have hk0bound (z : SourceInput p) :
      ‖k0 z‖ ≤ (15 / 2 : ℝ) * (2 * Bcap rate) + 16 := by
    by_cases hz : z ∈ g
    · simp only [k0, Set.indicator_of_mem hz, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (hθb z).1]
      have hi : |(-15 / 2 : ℝ) * b z + 16| ≤
          (15 / 2 : ℝ) * (2 * Bcap rate) + 16 := by
        rw [abs_le]
        constructor <;> nlinarith [(hθb z).2.2.1, (hθb z).2.2.2, hBcap, hC0]
      calc
        θ z * |(-15 / 2 : ℝ) * b z + 16| ≤
            θ z * ((15 / 2 : ℝ) * (2 * Bcap rate) + 16) :=
              mul_le_mul_of_nonneg_left hi (hθb z).1
        _ ≤ (15 / 2 : ℝ) * (2 * Bcap rate) + 16 := by
              nlinarith [(hθb z).2.1, hC0]
    · simp [k0, Set.indicator_of_notMem hz, hC0]
  have hk1bound (z : SourceInput p) :
      ‖k1 z‖ ≤ 2 * (2 * Bcap rate) + 1 / 2 := by
    by_cases hz : z ∈ g
    · have hfactor : 0 ≤ 2 * b z + 1 / 2 := by nlinarith [(hθb z).2.2.1]
      simp only [k1, Set.indicator_of_mem hz, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (hθb z).1, abs_of_nonneg hfactor]
      calc
        θ z * (2 * b z + 1 / 2) ≤ 1 * (2 * b z + 1 / 2) :=
          mul_le_mul_of_nonneg_right (hθb z).2.1 hfactor
        _ ≤ 2 * (2 * Bcap rate) + 1 / 2 := by
          nlinarith [(hθb z).2.2.2]
    · simpa [k1, Set.indicator_of_notMem hz] using hC1
  have hk2bound (z : SourceInput p) : ‖k2 z‖ ≤ 1 := by
    by_cases hz : z ∈ g
    · simpa [k2, Set.indicator_of_mem hz, Real.norm_eq_abs,
        abs_of_nonneg (hθb z).1] using (hθb z).2.1
    · simp [k2, Set.indicator_of_notMem hz]

  have hk0Int : Integrable k0 (sourceInputLaw p) :=
    integrable_of_bounded_measurable hk0ambient _ hC0 hk0bound
  have hAInt : Integrable A (sourceInputLaw p) :=
    retainedRaw_integrable rate rewards C_star C_h control0 u t a
  have hA2Int : Integrable A2 (sourceInputLaw p) := by
    simpa [A2, A] using
      ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_sq_integrable
      rate rewards C_star C_h control0 u t a
  have hk1AInt : Integrable (fun z => k1 z * A z) (sourceInputLaw p) :=
    hAInt.bdd_mul hk1ambient.stronglyMeasurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hk1bound z)
  have hk2A2Int : Integrable (fun z => k2 z * A2 z) (sourceInputLaw p) :=
    hA2Int.bdd_mul hk2ambient.stronglyMeasurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hk2bound z)

  have hdecomp : ∀ z, reducedDriftTerm rate rewards C_star C_h u t a z =
      k0 z + k1 z * A z + k2 z * A2 z := by
    intro z
    by_cases hz : z ∈ g
    · change z ∈ G rate rewards C_star C_h u t at hz
      simp [g, reducedDriftTerm, k0, k1, k2, A, A2, θ, b,
        Set.indicator_of_mem hz]
      ring_nf
    · change z ∉ G rate rewards C_star C_h u t at hz
      simp [g, reducedDriftTerm, k0, k1, k2, A, A2, θ, b,
        Set.indicator_of_notMem hz]

  have hk0CE : (sourceInputLaw p)[k0 | sourcePrefixFiltration control0 (t.val + 1)] = k0 :=
    condExp_of_stronglyMeasurable hFle hk0.stronglyMeasurable hk0Int
  have hk1pull : (sourceInputLaw p)[fun z => k1 z * A z | sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[
      sourceInputLaw p] fun z => k1 z *
        (sourceInputLaw p)[A | sourcePrefixFiltration control0 (t.val + 1)] z :=
    condExp_mul_of_stronglyMeasurable_left hk1.stronglyMeasurable
      hk1AInt hAInt
  have hk2pull : (sourceInputLaw p)[fun z => k2 z * A2 z | sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[
      sourceInputLaw p] fun z => k2 z *
        (sourceInputLaw p)[A2 | sourcePrefixFiltration control0 (t.val + 1)] z :=
    condExp_mul_of_stronglyMeasurable_left hk2.stronglyMeasurable
      hk2A2Int hA2Int
  have hAcond := retainedRaw_condExp rate rewards C_star C_h control0 u t a
  have hA2cond := retainedRaw_sq_condExp rate rewards C_star C_h control0 u t a
  have hk1CE : (sourceInputLaw p)[fun z => k1 z * A z | sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[
      sourceInputLaw p] fun z => k1 z * B1 z := by
    filter_upwards [hk1pull, hAcond] with z hp hraw
    change (sourceInputLaw p)[fun z => k1 z * A z | sourcePrefixFiltration control0 (t.val + 1)] z = _ at hp
    change (sourceInputLaw p)[A | sourcePrefixFiltration control0 (t.val + 1)] z = B1 z at hraw
    rw [hp, hraw]
  have hk2CE : (sourceInputLaw p)[fun z => k2 z * A2 z | sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[
      sourceInputLaw p] fun z => k2 z * B2 z := by
    filter_upwards [hk2pull, hA2cond] with z hp hraw
    change (sourceInputLaw p)[fun z => k2 z * A2 z | sourcePrefixFiltration control0 (t.val + 1)] z = _ at hp
    change (sourceInputLaw p)[A2 | sourcePrefixFiltration control0 (t.val + 1)] z = B2 z at hraw
    rw [hp, hraw]

  have hCEdecomp : (sourceInputLaw p)[fun z =>
      k0 z + k1 z * A z + k2 z * A2 z | sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[sourceInputLaw p]
      fun z => k0 z + k1 z * B1 z + k2 z * B2 z := by
    have hadd := condExp_add (hk0Int.add hk1AInt) hk2A2Int
      (sourcePrefixFiltration control0 (t.val + 1))
    have hadd01 := condExp_add hk0Int hk1AInt
      (sourcePrefixFiltration control0 (t.val + 1))
    have hinput : (fun z => k0 z + k1 z * A z + k2 z * A2 z) =
        (k0 + (fun z => k1 z * A z)) + (fun z => k2 z * A2 z) := by
      funext z
      rfl
    have hinputCE : (sourceInputLaw p)[fun z =>
        k0 z + k1 z * A z + k2 z * A2 z | sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[
          sourceInputLaw p] (sourceInputLaw p)[
        (k0 + (fun z => k1 z * A z)) + (fun z => k2 z * A2 z) |
          sourcePrefixFiltration control0 (t.val + 1)] := condExp_congr_ae
      (Filter.Eventually.of_forall fun z => congrFun hinput z)
    filter_upwards [hinputCE, hadd, hadd01, hk1CE, hk2CE] with z hin hsum hsum01 h1 h2
    have h0 := congrFun hk0CE z
    rw [hin, hsum]
    simp only [Pi.add_apply]
    rw [hsum01]
    simp only [Pi.add_apply]
    rw [h0, h1, h2]

  have htermCE : (sourceInputLaw p)[reducedDriftTerm
      rate rewards C_star C_h u t a | sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[sourceInputLaw p]
      (G rate rewards C_star C_h u t).indicator (fun z =>
        thetaMinus rate rewards C_star C_h u t a z *
          ((-15 / 2 : ℝ) * bMinus rate rewards C_star C_h u t a z +
            (2 * bMinus rate rewards C_star C_h u t a z + 1 / 2) *
              retainedMomentOne rate rewards C_star C_h u t a z +
            retainedMomentTwo rate rewards C_star C_h u t a z + 16)) := by
    have hcongr : (sourceInputLaw p)[reducedDriftTerm
        rate rewards C_star C_h u t a | sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[
          sourceInputLaw p] (sourceInputLaw p)[fun z =>
        k0 z + k1 z * A z + k2 z * A2 z | sourcePrefixFiltration control0 (t.val + 1)] :=
      condExp_congr_ae
      (Filter.Eventually.of_forall fun z => hdecomp z)
    have hCE := hcongr.trans hCEdecomp
    filter_upwards [hCE] with z hz
    by_cases hg : z ∈ g
    · have hcePoint :
        (sourceInputLaw p)[reducedDriftTerm rate rewards C_star C_h u t a |
          sourcePrefixFiltration control0 (t.val + 1)] z =
          θ z * ((-15 / 2 : ℝ) * b z + 16) +
            θ z * (2 * b z + 1 / 2) * B1 z + θ z * B2 z := by
        simpa [g, k0, k1, k2, A, A2, B1, B2, θ, b,
          Set.indicator_of_mem hg] using hz
      calc
        (sourceInputLaw p)[reducedDriftTerm rate rewards C_star C_h u t a |
            sourcePrefixFiltration control0 (t.val + 1)] z =
            θ z * ((-15 / 2 : ℝ) * b z + 16) +
              θ z * (2 * b z + 1 / 2) * B1 z + θ z * B2 z := hcePoint
        _ = (G rate rewards C_star C_h u t).indicator (fun z =>
              thetaMinus rate rewards C_star C_h u t a z *
                ((-15 / 2 : ℝ) * bMinus rate rewards C_star C_h u t a z +
                  (2 * bMinus rate rewards C_star C_h u t a z + 1 / 2) *
                    retainedMomentOne rate rewards C_star C_h u t a z +
                  retainedMomentTwo rate rewards C_star C_h u t a z + 16)) z := by
          rw [Set.indicator_of_mem hg]
          ring
    · simp [g, k0, k1, k2, B1, B2, θ, b,
        Set.indicator_of_notMem hg] at hz ⊢
      exact hz
  exact htermCE

private theorem reducedEnvelope_condExp (control0 : TimeControl p)
    (u t : Fin p.T) :
    (sourceInputLaw p)[reducedDriftEnvelope rate rewards C_star C_h u t | sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[
      sourceInputLaw p] (G rate rewards C_star C_h u t).indicator
        (fun z => ∑ a : Fin p.K,
          thetaMinus rate rewards C_star C_h u t a z *
            ((-15 / 2 : ℝ) * bMinus rate rewards C_star C_h u t a z +
              (2 * bMinus rate rewards C_star C_h u t a z + 1 / 2) *
                retainedMomentOne rate rewards C_star C_h u t a z +
              retainedMomentTwo rate rewards C_star C_h u t a z + 16)) := by
  have hsum : reducedDriftEnvelope rate rewards C_star C_h u t =
      fun z => ∑ a : Fin p.K,
        reducedDriftTerm rate rewards C_star C_h u t a z := by
    funext z
    exact reducedDriftEnvelope_eq_sum_reducedDriftTerm
      rate rewards C_star C_h u t z
  have hterms : ∀ a ∈ Finset.univ,
      Integrable (reducedDriftTerm rate rewards C_star C_h u t a)
        (sourceInputLaw p) := by
    intro a ha
    exact reducedDriftTerm_integrable rate rewards C_star C_h control0 u t a
  have hce := condExp_finsetSum hterms
    (sourcePrefixFiltration control0 (t.val + 1))
  rw [hsum]
  have hceTerms : (sourceInputLaw p)[fun z =>
      ∑ a : Fin p.K, reducedDriftTerm rate rewards C_star C_h u t a z | sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[
        sourceInputLaw p] fun z => ∑ a : Fin p.K,
          (sourceInputLaw p)[reducedDriftTerm rate rewards C_star C_h u t a | sourcePrefixFiltration control0 (t.val + 1)] z := by
    have hsumFun : (∑ a : Fin p.K, reducedDriftTerm rate rewards C_star C_h u t a) =
        fun z => ∑ a : Fin p.K, reducedDriftTerm rate rewards C_star C_h u t a z := by
      funext z
      simp
    have hsumCE : (∑ a : Fin p.K,
        (sourceInputLaw p)[reducedDriftTerm rate rewards C_star C_h u t a |
          sourcePrefixFiltration control0 (t.val + 1)]) =
        fun z => ∑ a : Fin p.K,
          (sourceInputLaw p)[reducedDriftTerm rate rewards C_star C_h u t a |
            sourcePrefixFiltration control0 (t.val + 1)] z := by
      funext z
      simp
    simpa only [← hsumFun, ← hsumCE] using hce
  have hterm a := reducedTerm_condExp rate rewards C_star C_h control0 u t a
  have hall : ∀ᵐ z ∂sourceInputLaw p, ∀ a : Fin p.K,
      (sourceInputLaw p)[reducedDriftTerm rate rewards C_star C_h u t a | sourcePrefixFiltration control0 (t.val + 1)] z =
        (G rate rewards C_star C_h u t).indicator (fun z =>
          thetaMinus rate rewards C_star C_h u t a z *
            ((-15 / 2 : ℝ) * bMinus rate rewards C_star C_h u t a z +
              (2 * bMinus rate rewards C_star C_h u t a z + 1 / 2) *
                retainedMomentOne rate rewards C_star C_h u t a z +
              retainedMomentTwo rate rewards C_star C_h u t a z + 16)) z := by
    rw [ae_all_iff]
    intro a
    exact hterm a
  filter_upwards [hceTerms, hall] with z hz htermsz
  rw [hz]
  calc
    (∑ a : Fin p.K,
      (sourceInputLaw p)[reducedDriftTerm rate rewards C_star C_h u t a | sourcePrefixFiltration control0 (t.val + 1)] z) =
        ∑ a : Fin p.K, (G rate rewards C_star C_h u t).indicator (fun z =>
          thetaMinus rate rewards C_star C_h u t a z *
            ((-15 / 2 : ℝ) * bMinus rate rewards C_star C_h u t a z +
              (2 * bMinus rate rewards C_star C_h u t a z + 1 / 2) *
                retainedMomentOne rate rewards C_star C_h u t a z +
              retainedMomentTwo rate rewards C_star C_h u t a z + 16)) z := by
      apply Finset.sum_congr rfl
      intro a ha
      exact htermsz a
    _ = (G rate rewards C_star C_h u t).indicator (fun z =>
        ∑ a : Fin p.K,
          thetaMinus rate rewards C_star C_h u t a z *
            ((-15 / 2 : ℝ) * bMinus rate rewards C_star C_h u t a z +
              (2 * bMinus rate rewards C_star C_h u t a z + 1 / 2) *
                retainedMomentOne rate rewards C_star C_h u t a z +
              retainedMomentTwo rate rewards C_star C_h u t a z + 16)) z := by
      by_cases hg : z ∈ G rate rewards C_star C_h u t
      · simp [Set.indicator_of_mem hg]
      · simp [Set.indicator_of_notMem hg]

private theorem momentEnvelope_le_maskedCredit (u t : Fin p.T)
    (z : SourceInput p) :
    (G rate rewards C_star C_h u t).indicator (fun z =>
      ∑ a : Fin p.K,
        thetaMinus rate rewards C_star C_h u t a z *
          ((-15 / 2 : ℝ) * bMinus rate rewards C_star C_h u t a z +
            (2 * bMinus rate rewards C_star C_h u t a z + 1 / 2) *
              retainedMomentOne rate rewards C_star C_h u t a z +
            retainedMomentTwo rate rewards C_star C_h u t a z + 16)) z ≤
    (G rate rewards C_star C_h u t).indicator (fun z =>
      CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ) -
        (11 / 2 : ℝ) * weightedBacklog rate rewards C_star C_h u t z) z := by
  by_cases hz : z ∈ G rate rewards C_star C_h u t
  · obtain ⟨L, r, theta, selected, c, hL, hlen, hactual, ht, hcall,
      hcalendar, hcell, hselected, hanchor, hrate, hband, hcredit⟩ :=
      G_actual_rate_credit rate rewards C_star C_h u t z hz
    obtain ⟨L', c', hL', hcell', henabled, hweightMinus, hweightPlus,
      hthetaMinus, hthetaPlus⟩ :=
      firstCell_actual_score_marginals rate rewards C_star C_h u t z hz.1
    have hLL : L = L' := Option.some.inj (hL.symm.trans hL')
    subst L'
    have hsumTheta : (∑ a : Fin p.K,
        thetaMinus rate rewards C_star C_h u t a z) = (p.m : ℝ) := by
      rw [sum_thetaMinus rate rewards C_star C_h u t z]
      simp [Set.indicator_of_mem hz.1]
    have hthetaNonneg (a : Fin p.K) :
        0 ≤ thetaMinus rate rewards C_star C_h u t a z :=
      (thetaMinus_bounds rate rewards C_star C_h u t a z).1
    have hbBounds (a : Fin p.K) :
        0 ≤ bMinus rate rewards C_star C_h u t a z ∧
          bMinus rate rewards C_star C_h u t a z ≤ 2 * Bcap rate :=
      bMinus_global_bounds rate rewards C_star C_h u t a z
    have hrewardBounds (a : Fin p.K) :
        0 ≤ ((rewards t a).val : ℝ) / (D p : ℝ) ∧
          ((rewards t a).val : ℝ) / (D p : ℝ) ≤ 1 := by
      have hD : 0 < (D p : ℝ) := by exact_mod_cast D_pos p
      constructor
      · positivity
      · have hval : ((rewards t a).val : ℝ) ≤ D p := by
          exact_mod_cast (Fin.is_le (rewards t a))
        exact (div_le_one hD).2 (by exact_mod_cast hval)
    have hMoment a :
        ∃ θ : AssignmentParameterFibreKernel.Theta p,
          ReferenceCalendarLaterSamplerPredictability.calendarParameters
            rate rewards C_star C_h t z = some θ ∧
          retainedMomentOne rate rewards C_star C_h u t a z ≤
            ((rewards t a).val : ℝ) / (D p : ℝ) ∧
          retainedMomentTwo rate rewards C_star C_h u t a z ≤
            (((rewards t a).val : ℝ) / (D p : ℝ)) ^ 2 /
              CanonicalRecordingRates.xi p rate.eta.val θ.2 a := by
      obtain ⟨θ, hθcal, _hlo, _hnonneg, hB1, _hB1le1, _hB2nonneg,
        hB2, _hB2beta⟩ := retainedMoment_bounds_on_G
        rate rewards C_star C_h u t a z hz
      exact ⟨θ, hθcal, hB1, hB2⟩
    have hratePos (a : Fin p.K) : 0 < c.rate a := by
      rw [hrate]
      exact CanonicalRecordingRates.xi_pos p rate.eta.property theta.2 a
    have hsumXi : (∑ a : Fin p.K,
        ProductSetLaw.theta p.m
          (RecordedQueueRun.scoreWeight
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (RecordedQueueRun.run
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) L)) a /
            CanonicalRecordingRates.xi p rate.eta.val theta.2 a) ≤
        CanonicalRecordingRates.R p := by
      simpa [hrate] using hcredit
    have hthetaEq (a : Fin p.K) :
        thetaMinus rate rewards C_star C_h u t a z =
          ProductSetLaw.theta p.m
            (RecordedQueueRun.scoreWeight
              (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (RecordedQueueRun.run
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) L)) a := by
      exact congrFun hthetaMinus a
    have hcalendarRate : ∀ a : Fin p.K,
        c.rate a = CanonicalRecordingRates.xi p rate.eta.val theta.2 a := by
      intro a
      exact congrFun hrate a
    have hterm (a : Fin p.K) :
        thetaMinus rate rewards C_star C_h u t a z *
          ((-15 / 2 : ℝ) * bMinus rate rewards C_star C_h u t a z +
            (2 * bMinus rate rewards C_star C_h u t a z + 1 / 2) *
              retainedMomentOne rate rewards C_star C_h u t a z +
            retainedMomentTwo rate rewards C_star C_h u t a z + 16) ≤
        (-11 / 2 : ℝ) * thetaMinus rate rewards C_star C_h u t a z *
            bMinus rate rewards C_star C_h u t a z +
          thetaMinus rate rewards C_star C_h u t a z /
            CanonicalRecordingRates.xi p rate.eta.val theta.2 a +
          (33 / 2 : ℝ) * thetaMinus rate rewards C_star C_h u t a z := by
      obtain ⟨θ, hθcal, hB1, hB2⟩ := hMoment a
      have hθeq : θ = theta := Option.some.inj (hθcal.symm.trans hcalendar)
      subst θ
      have hrr := hrewardBounds a
      have hxi : 0 < CanonicalRecordingRates.xi p rate.eta.val theta.2 a :=
        CanonicalRecordingRates.xi_pos p rate.eta.property theta.2 a
      have hrrsq : (((rewards t a).val : ℝ) / (D p : ℝ)) ^ 2 ≤ 1 := by
        have hmul := mul_le_mul hrr.2 hrr.2 hrr.1 (by norm_num : (0 : ℝ) ≤ 1)
        nlinarith [hmul]
      have hB2' : retainedMomentTwo rate rewards C_star C_h u t a z ≤
          1 / CanonicalRecordingRates.xi p rate.eta.val theta.2 a := by
        calc
          _ ≤ (((rewards t a).val : ℝ) / (D p : ℝ)) ^ 2 /
              CanonicalRecordingRates.xi p rate.eta.val theta.2 a := hB2
          _ ≤ 1 / CanonicalRecordingRates.xi p rate.eta.val theta.2 a :=
            div_le_div_of_nonneg_right hrrsq hxi.le
      have hcoef : 0 ≤ 2 * bMinus rate rewards C_star C_h u t a z + 1 / 2 := by
        have hb0 := (hbBounds a).1
        nlinarith [hb0]
      have hbody :
          (-15 / 2 : ℝ) * bMinus rate rewards C_star C_h u t a z +
              (2 * bMinus rate rewards C_star C_h u t a z + 1 / 2) *
                retainedMomentOne rate rewards C_star C_h u t a z +
              retainedMomentTwo rate rewards C_star C_h u t a z + 16 ≤
            (-11 / 2 : ℝ) * bMinus rate rewards C_star C_h u t a z +
              1 / CanonicalRecordingRates.xi p rate.eta.val theta.2 a +
              33 / 2 := by
        have hweighted := mul_le_mul_of_nonneg_left hB1 hcoef
        have hbr := mul_le_mul_of_nonneg_left hrr.2
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
            (hbBounds a).1)
        have hhalf : ((rewards t a).val : ℝ) / (D p : ℝ) / 2 ≤ 1 / 2 :=
          div_le_div_of_nonneg_right hrr.2 (by norm_num)
        nlinarith [hweighted, hbr, hhalf, hB2']
      calc
        _ ≤ thetaMinus rate rewards C_star C_h u t a z *
            ((-11 / 2 : ℝ) * bMinus rate rewards C_star C_h u t a z +
              1 / CanonicalRecordingRates.xi p rate.eta.val theta.2 a + 33 / 2) :=
          mul_le_mul_of_nonneg_left hbody (hthetaNonneg a)
        _ = _ := by ring
    have hsumTerms := Finset.sum_le_sum (s := Finset.univ) fun a ha => hterm a
    have hsumRearrange :
        (∑ a : Fin p.K,
          ((-11 / 2 : ℝ) * thetaMinus rate rewards C_star C_h u t a z *
              bMinus rate rewards C_star C_h u t a z +
            thetaMinus rate rewards C_star C_h u t a z /
              CanonicalRecordingRates.xi p rate.eta.val theta.2 a +
            (33 / 2 : ℝ) * thetaMinus rate rewards C_star C_h u t a z)) =
          (-11 / 2 : ℝ) * weightedBacklog rate rewards C_star C_h u t z +
            (∑ a : Fin p.K,
              ProductSetLaw.theta p.m
                (RecordedQueueRun.scoreWeight
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                  (RecordedQueueRun.run
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) L)) a /
                  CanonicalRecordingRates.xi p rate.eta.val theta.2 a) +
            (33 / 2 : ℝ) * (p.m : ℝ) := by
      simp only [Finset.sum_add_distrib]
      have hMarg :
          (∑ a : Fin p.K,
            thetaMinus rate rewards C_star C_h u t a z /
              CanonicalRecordingRates.xi p rate.eta.val theta.2 a) =
            ∑ a : Fin p.K,
              ProductSetLaw.theta p.m
                (RecordedQueueRun.scoreWeight
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                  (RecordedQueueRun.run
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) L)) a /
                CanonicalRecordingRates.xi p rate.eta.val theta.2 a := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hthetaEq a]
      have hbackScaled :
          (∑ a : Fin p.K,
            (-11 / 2 : ℝ) * thetaMinus rate rewards C_star C_h u t a z *
              bMinus rate rewards C_star C_h u t a z) =
            (-11 / 2 : ℝ) * weightedBacklog rate rewards C_star C_h u t z := by
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum]
        rfl
      have hconstant :
          (∑ a : Fin p.K,
            (33 / 2 : ℝ) * thetaMinus rate rewards C_star C_h u t a z) =
            (33 / 2 : ℝ) * (p.m : ℝ) := by
        rw [← Finset.mul_sum, hsumTheta]
      rw [hbackScaled, hMarg, hconstant]
    have hsumFinal :
        (∑ a : Fin p.K,
          ((-11 / 2 : ℝ) * thetaMinus rate rewards C_star C_h u t a z *
              bMinus rate rewards C_star C_h u t a z +
            thetaMinus rate rewards C_star C_h u t a z /
              CanonicalRecordingRates.xi p rate.eta.val theta.2 a +
            (33 / 2 : ℝ) * thetaMinus rate rewards C_star C_h u t a z)) ≤
          CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ) -
            (11 / 2 : ℝ) * weightedBacklog rate rewards C_star C_h u t z := by
      rw [hsumRearrange]
      linarith [hsumXi]
    have hsumPoint :
        (∑ a : Fin p.K,
          thetaMinus rate rewards C_star C_h u t a z *
            ((-15 / 2 : ℝ) * bMinus rate rewards C_star C_h u t a z +
              (2 * bMinus rate rewards C_star C_h u t a z + 1 / 2) *
                retainedMomentOne rate rewards C_star C_h u t a z +
              retainedMomentTwo rate rewards C_star C_h u t a z + 16)) ≤
          CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ) -
            (11 / 2 : ℝ) * weightedBacklog rate rewards C_star C_h u t z :=
      hsumTerms.trans hsumFinal
    simpa [Set.indicator_of_mem hz] using hsumPoint
  · simp [Set.indicator_of_notMem hz]

/-- Conditional energy drift under the original source law and actual
source-prefix history. The retained gate masks the backlog term as well as the
constant credit. -/
public theorem conditional_weighted_drift (control0 : TimeControl p)
    (u t : Fin p.T) :
    (sourceInputLaw p)[(fun z =>
      VPlus rate rewards C_star C_h u t z -
        VMinus rate rewards C_star C_h u t z) |
      sourcePrefixFiltration control0 (t.val + 1)] ≤ᵐ[sourceInputLaw p]
      (G rate rewards C_star C_h u t).indicator (fun z =>
        CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ) -
          (11 / 2 : ℝ) * weightedBacklog rate rewards C_star C_h u t z) := by
  have henergy := energyDifference_integrable rate rewards C_star C_h control0 u t
  have henvelope := reducedDriftEnvelope_integrable rate rewards C_star C_h control0 u t
  have hpoint : ∀ z,
      VPlus rate rewards C_star C_h u t z - VMinus rate rewards C_star C_h u t z ≤
        reducedDriftEnvelope rate rewards C_star C_h u t z :=
    fun z => V_drift_le_reducedDriftEnvelope rate rewards C_star C_h control0 u t z
  have hmono := condExp_mono (m := sourcePrefixFiltration control0 (t.val + 1))
    henergy henvelope (ae_of_all _ hpoint)
  have hred := reducedEnvelope_condExp rate rewards C_star C_h control0 u t
  have hbound := momentEnvelope_le_maskedCredit rate rewards C_star C_h u t
  filter_upwards [hmono, hred] with z hle hce
  rw [hce] at hle
  exact hle.trans (hbound z)

private theorem maskedCredit_integrable
    (rate0 : ReferenceActivePhysicalStep.RateInput p)
    (rewards0 : GridRewardTable p) (Cstar0 Ch0 : ℝ)
    (control0 : TimeControl p)
    (u t : Fin p.T) :
    Integrable ((G rate0 rewards0 Cstar0 Ch0 u t).indicator (fun z =>
      CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ) -
        (11 / 2 : ℝ) * weightedBacklog rate0 rewards0 Cstar0 Ch0 u t z))
      (sourceInputLaw p) := by
  let C := CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)
  have hFle : sourcePrefixFiltration control0 (t.val + 1) ≤ sourceInputMeasurableSpace :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hG : MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)] (G rate0 rewards0 Cstar0 Ch0 u t) :=
    measurableSet_G rate0 rewards0 Cstar0 Ch0 control0 u t
  have hGambient : MeasurableSet (G rate0 rewards0 Cstar0 Ch0 u t) :=
    hFle _ hG
  have hW : Measurable[sourcePrefixFiltration control0 (t.val + 1)] (weightedBacklog rate0 rewards0 Cstar0 Ch0 u t) :=
    measurable_weightedBacklog rate0 rewards0 Cstar0 Ch0 control0 u t
  have hWambient : Measurable (weightedBacklog rate0 rewards0 Cstar0 Ch0 u t) :=
    Measurable.mono hW hFle le_rfl
  have hmeas : Measurable ((G rate0 rewards0 Cstar0 Ch0 u t).indicator
      (fun z => C - (11 / 2 : ℝ) * weightedBacklog rate0 rewards0 Cstar0 Ch0 u t z)) :=
    (measurable_const.sub (hWambient.const_mul _)).indicator hGambient
  have hBcap0 : 0 ≤ Bcap rate0 := by
    unfold Bcap
    exact le_of_lt (one_div_pos.mpr (by positivity [rate0.eta.property]))
  let Cb := |C| + (11 / 2 : ℝ) * (2 * (p.m : ℝ) * Bcap rate0)
  have hCb : 0 ≤ Cb := by dsimp [Cb]; positivity [hBcap0]
  apply integrable_of_bounded_measurable hmeas Cb hCb
  intro z
  by_cases hz : z ∈ G rate0 rewards0 Cstar0 Ch0 u t
  · have hWbounds := weightedBacklog_bounds rate0 rewards0 Cstar0 Ch0 u t z
    rw [Set.indicator_of_mem hz, Real.norm_eq_abs]
    calc
      |C - (11 / 2 : ℝ) * weightedBacklog rate0 rewards0 Cstar0 Ch0 u t z|
          ≤ |C| + |(11 / 2 : ℝ) *
              weightedBacklog rate0 rewards0 Cstar0 Ch0 u t z| := abs_sub _ _
      _ = |C| + (11 / 2 : ℝ) *
            weightedBacklog rate0 rewards0 Cstar0 Ch0 u t z := by
              rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 2),
                abs_of_nonneg hWbounds.1]
      _ ≤ Cb := by
        dsimp [Cb]
        nlinarith [hWbounds.2]
  · simpa [Set.indicator_of_notMem hz, Cb] using hCb

/-- Any source-prefix measurable test set satisfies the drift integral bound.
No positivity assumption on its mass is needed. -/
public theorem sourceSetIntegral_energy_drift (control0 : TimeControl p)
    (u t : Fin p.T) (S : Set (SourceInput p))
    (hS : MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)] S) :
    ∫ z in S, VPlus rate rewards C_star C_h u t z -
        VMinus rate rewards C_star C_h u t z ∂sourceInputLaw p ≤
      ∫ z in S, (G rate rewards C_star C_h u t).indicator (fun z =>
        CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ) -
          (11 / 2 : ℝ) * weightedBacklog rate rewards C_star C_h u t z) z
        ∂sourceInputLaw p := by
  let f := fun z : SourceInput p =>
    VPlus rate rewards C_star C_h u t z - VMinus rate rewards C_star C_h u t z
  let g := fun z : SourceInput p => (G rate rewards C_star C_h u t).indicator (fun z =>
    CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ) -
      (11 / 2 : ℝ) * weightedBacklog rate rewards C_star C_h u t z) z
  have hf : Integrable f (sourceInputLaw p) := by
    simpa [f] using energyDifference_integrable rate rewards C_star C_h control0 u t
  have hg : Integrable g (sourceInputLaw p) := by
    simpa [g] using maskedCredit_integrable rate rewards C_star C_h control0 u t
  have hFle : sourcePrefixFiltration control0 (t.val + 1) ≤ sourceInputMeasurableSpace :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  calc
    ∫ z in S, f z ∂sourceInputLaw p =
        ∫ z in S, (sourceInputLaw p)[f |
          sourcePrefixFiltration control0 (t.val + 1)] z ∂sourceInputLaw p := by
      symm
      exact setIntegral_condExp hFle hf hS
    _ ≤ ∫ z in S, g z ∂sourceInputLaw p :=
      setIntegral_mono_ae integrable_condExp.integrableOn hg.integrableOn
        (by simpa [f, g] using
          conditional_weighted_drift rate rewards C_star C_h control0 u t)

private theorem integral_maskedCredit (control0 : TimeControl p)
    (u t : Fin p.T) :
    ∫ z, (G rate rewards C_star C_h u t).indicator (fun z =>
      CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ) -
        (11 / 2 : ℝ) * weightedBacklog rate rewards C_star C_h u t z) z
      ∂sourceInputLaw p =
    (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (sourceInputLaw p).real (G rate rewards C_star C_h u t) -
      (11 / 2 : ℝ) * ∫ z, (G rate rewards C_star C_h u t).indicator
        (weightedBacklog rate rewards C_star C_h u t) z ∂sourceInputLaw p := by
  let g := G rate rewards C_star C_h u t
  let C := CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)
  have hFle : sourcePrefixFiltration control0 (t.val + 1) ≤ sourceInputMeasurableSpace :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hG : MeasurableSet g :=
    hFle _ (measurableSet_G rate rewards C_star C_h control0 u t)
  have hmask : (fun z => g.indicator (fun z =>
      C - (11 / 2 : ℝ) * weightedBacklog rate rewards C_star C_h u t z) z) =
      fun z => g.indicator (fun _ => C) z -
        (11 / 2 : ℝ) * g.indicator
          (weightedBacklog rate rewards C_star C_h u t) z := by
    funext z
    by_cases hz : z ∈ g
    · simp [Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hz]
  have hWint := weightedBacklog_integrable rate rewards C_star C_h control0 u t
  have hWmask := hWint.indicator hG
  have hCmask : Integrable (g.indicator (fun _ : SourceInput p => C))
      (sourceInputLaw p) := (integrable_const C).indicator hG
  rw [hmask, integral_sub hCmask (hWmask.const_mul (11 / 2 : ℝ))]
  rw [integral_indicator_const C hG, smul_eq_mul, integral_const_mul]
  ring

/-- Whole-space expectation consequence, with the constant term rewritten as
the original source-law mass of the retained gate. -/
public theorem sourceIntegral_energy_drift (control0 : TimeControl p)
    (u t : Fin p.T) :
    ∫ z, VPlus rate rewards C_star C_h u t z -
        VMinus rate rewards C_star C_h u t z ∂sourceInputLaw p ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          (sourceInputLaw p).real (G rate rewards C_star C_h u t) -
        (11 / 2 : ℝ) * ∫ z, (G rate rewards C_star C_h u t).indicator
          (weightedBacklog rate rewards C_star C_h u t) z ∂sourceInputLaw p := by
  have hset := sourceSetIntegral_energy_drift rate rewards C_star C_h control0 u t
    Set.univ MeasurableSet.univ
  have hwhole :
      ∫ z, VPlus rate rewards C_star C_h u t z -
          VMinus rate rewards C_star C_h u t z ∂sourceInputLaw p ≤
        ∫ z, (G rate rewards C_star C_h u t).indicator (fun z =>
          CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ) -
            (11 / 2 : ℝ) * weightedBacklog rate rewards C_star C_h u t z) z
          ∂sourceInputLaw p := by
    simpa only [setIntegral_univ] using hset
  rw [integral_maskedCredit rate rewards C_star C_h control0 u t] at hwhole
  exact hwhole

/-- Equivalent nonnegative weighted-cost form of the same one-call energy
accounting inequality. -/
public theorem sourceIntegral_weighted_cost (control0 : TimeControl p)
    (u t : Fin p.T) :
    ∫ z, VPlus rate rewards C_star C_h u t z -
        VMinus rate rewards C_star C_h u t z ∂sourceInputLaw p +
      (11 / 2 : ℝ) * ∫ z, (G rate rewards C_star C_h u t).indicator
        (weightedBacklog rate rewards C_star C_h u t) z ∂sourceInputLaw p ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (sourceInputLaw p).real (G rate rewards C_star C_h u t) := by
  have h := sourceIntegral_energy_drift rate rewards C_star C_h control0 u t
  linarith

end Bandits.Support.ReferenceFirstCollectionCurrentConditionalWeightedDrift

end
