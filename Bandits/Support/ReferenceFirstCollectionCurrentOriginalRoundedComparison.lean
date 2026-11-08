/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCurrentConditionalWeightedDrift

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Original first collection-call rounded/raw reward comparison

This internal result compares the actual rounded-reward comparator gap on the
first original collection-call cell with the corresponding retained raw
arrival gap. The positive quantization loss remains explicit before using the
fact that at most one tagged first-call cell is present on a source.

Sources: `04_slow_fast_learner.tex:140-188,245-271,323-409`,
`05_binary_transport.tex:352-431`, `06_interruptions.tex:355-426`, and
`08_main_theorem.tex:78-105`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Bandits.Support.ReferenceFirstCollectionCurrentOriginalRoundedComparison

open ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ActualInitializationPhysicalStep (GridRewardTable)
open ContinuousLearningRows (TimeControl)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefixFiltration)
open ReferenceCalendarCollectionCallControlLaw (firstCell)
open ReferenceFirstCollectionCurrentRetainedGate (G measurableSet_G)
open ReferenceFirstCollectionCurrentRetainedMoments
  (retainedRaw retainedRaw_measurable retainedRaw_integrable retainedRaw_condExp
    retainedMomentOne retainedMoment_bounds_on_G)
open ReferenceFirstCollectionCurrentQueueEnergy
  (thetaMinus thetaMinus_bounds measurable_thetaMinus measurable_thetaMinus_ambient
    thetaMinus_mul_retainedRaw_integrable firstCell_actual_score_marginals)
open ReferenceCalendarLaterSamplerPredictability (calendarParameters)

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
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

/-- The original retained raw comparator gap on a fixed actual first-call cell. -/
def rawGap (u t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m)
    (z : SourceInput p) : ℝ :=
  (∑ a ∈ S.1, retainedRaw rate rewards C_star C_h u t a z) -
    ∑ a : Fin p.K,
      thetaMinus rate rewards C_star C_h u t a z *
        retainedRaw rate rewards C_star C_h u t a z

/-- The rounded-reward comparator gap, localized to the actual retained gate. -/
def roundedGap (u t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m)
    (z : SourceInput p) : ℝ :=
  (G rate rewards C_star C_h u t).indicator (fun z =>
    (∑ a ∈ S.1, ((rewards t a).val : ℝ) / (D p : ℝ)) -
      ∑ a : Fin p.K,
        thetaMinus rate rewards C_star C_h u t a z *
          (((rewards t a).val : ℝ) / (D p : ℝ))) z

/-- The explicit, nonnegative rounding loss on the same original gate. -/
def floorLoss (u t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m)
    (z : SourceInput p) : ℝ :=
  (G rate rewards C_star C_h u t).indicator (fun z =>
    match calendarParameters rate rewards C_star C_h t z with
    | none => 0
    | some params =>
        ∑ a ∈ S.1,
          CanonicalRecordingRates.xi p rate.eta.val params.2 a /
            (rate.eta.val * (D p : ℝ))) z

private theorem integrable_of_bounded_measurable
    {f : SourceInput p → ℝ} (hf : Measurable f) (C : ℝ)
    (_hC : 0 ≤ C) (hbound : ∀ z, ‖f z‖ ≤ C) :
    Integrable f (sourceInputLaw p) := by
  have hconst : Integrable (fun _ : SourceInput p => C) (sourceInputLaw p) :=
    integrable_const C
  refine hconst.mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with z
  simpa [Real.norm_eq_abs, abs_of_nonneg _hC] using hbound z

private theorem productSet_card (S : ProductSetLaw.ProductSet p.K p.m) :
    S.1.card = p.m := by
  have hmem := S.2
  simpa [ProductSetLaw.support] using hmem

private theorem reward_bounds (t : Fin p.T) (a : Fin p.K) :
    0 ≤ ((rewards t a).val : ℝ) / (D p : ℝ) ∧
      ((rewards t a).val : ℝ) / (D p : ℝ) ≤ 1 := by
  have hD : 0 < (D p : ℝ) := by
    exact_mod_cast ConstructorDimensions.D_pos p
  have hval : (rewards t a).val ≤ D p :=
    Nat.le_of_lt_succ (rewards t a).isLt
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hD.le
  · apply (div_le_one hD).2
    exact_mod_cast hval

private theorem rawComparator_sum_bounds
    (t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m) :
    0 ≤ (∑ a ∈ S.1, ((rewards t a).val : ℝ) / (D p : ℝ)) ∧
      (∑ a ∈ S.1, ((rewards t a).val : ℝ) / (D p : ℝ)) ≤ (p.m : ℝ) := by
  constructor
  · exact Finset.sum_nonneg fun a ha => (reward_bounds rewards t a).1
  · calc
      (∑ a ∈ S.1, ((rewards t a).val : ℝ) / (D p : ℝ)) ≤
          ∑ a ∈ S.1, (1 : ℝ) :=
        Finset.sum_le_sum fun a ha => (reward_bounds rewards t a).2
      _ = (p.m : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, productSet_card]; simp

private theorem weightedReward_sum_bounds
    (u t : Fin p.T) (z : SourceInput p) :
    0 ≤ (∑ a : Fin p.K,
      thetaMinus rate rewards C_star C_h u t a z *
        (((rewards t a).val : ℝ) / (D p : ℝ))) ∧
      (∑ a : Fin p.K,
        thetaMinus rate rewards C_star C_h u t a z *
          (((rewards t a).val : ℝ) / (D p : ℝ))) ≤ (p.K : ℝ) := by
  constructor
  · exact Finset.sum_nonneg fun a ha =>
      mul_nonneg (thetaMinus_bounds rate rewards C_star C_h u t a z).1
        (reward_bounds rewards t a).1
  · calc
      (∑ a : Fin p.K,
        thetaMinus rate rewards C_star C_h u t a z *
          (((rewards t a).val : ℝ) / (D p : ℝ))) ≤
          ∑ a : Fin p.K, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        have hθ := thetaMinus_bounds rate rewards C_star C_h u t a z
        have hr := reward_bounds rewards t a
        calc
          thetaMinus rate rewards C_star C_h u t a z *
              (((rewards t a).val : ℝ) / (D p : ℝ)) ≤
            1 * (((rewards t a).val : ℝ) / (D p : ℝ)) :=
              mul_le_mul_of_nonneg_right hθ.2 hr.1
          _ ≤ 1 := by simpa using hr.2
      _ = (p.K : ℝ) := by simp

theorem rawGap_measurable (control0 : TimeControl p) (u t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Measurable (rawGap rate rewards C_star C_h u t S) := by
  apply Measurable.sub
  · exact Finset.measurable_fun_sum S.1 fun a ha =>
      retainedRaw_measurable rate rewards C_star C_h control0 u t a
  · exact Finset.measurable_fun_sum Finset.univ fun a ha =>
      (measurable_thetaMinus_ambient rate rewards C_star C_h control0 u t a).mul
        (retainedRaw_measurable rate rewards C_star C_h control0 u t a)

theorem rawGap_integrable (control0 : TimeControl p) (u t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (rawGap rate rewards C_star C_h u t S) (sourceInputLaw p) := by
  have hleft : Integrable (fun z =>
      ∑ a ∈ S.1, retainedRaw rate rewards C_star C_h u t a z) (sourceInputLaw p) :=
    integrable_finsetSum S.1 fun a ha =>
      retainedRaw_integrable rate rewards C_star C_h control0 u t a
  have hright : Integrable (fun z =>
      ∑ a : Fin p.K,
        thetaMinus rate rewards C_star C_h u t a z *
          retainedRaw rate rewards C_star C_h u t a z) (sourceInputLaw p) :=
    integrable_finsetSum Finset.univ fun a ha =>
      thetaMinus_mul_retainedRaw_integrable rate rewards C_star C_h control0 u t a
  change Integrable
    ((fun z => ∑ a ∈ S.1, retainedRaw rate rewards C_star C_h u t a z) -
      fun z => ∑ a : Fin p.K,
        thetaMinus rate rewards C_star C_h u t a z *
          retainedRaw rate rewards C_star C_h u t a z) μ
  exact hleft.sub hright

private theorem xi_anchor_measurable (a : Fin p.K) :
    Measurable (fun v : Fin p.K → ℝ =>
      CanonicalRecordingRates.xi p rate.eta.val v a) := by
  have hprod (S : Finset (Fin p.K)) :
      Measurable (fun v : Fin p.K → ℝ => ProductSetLaw.setWeight v S) := by
    unfold ProductSetLaw.setWeight
    exact Finset.measurable_fun_prod S (fun i _ => measurable_pi_apply i)
  have htotal : Measurable (fun v : Fin p.K → ℝ =>
      FiniteNormalization.totalMass (ProductSetLaw.support p.K p.m)
        (ProductSetLaw.setWeight v)) := by
    unfold FiniteNormalization.totalMass
    exact Finset.measurable_fun_sum _ (fun S _ => hprod S)
  have htheta : Measurable (fun v : Fin p.K → ℝ =>
      ProductSetLaw.theta p.m v a) := by
    unfold ProductSetLaw.theta FiniteNormalization.mass
    apply Finset.measurable_fun_sum
    intro S _
    unfold FiniteNormalization.normalizedWeight
    exact (hprod S).div htotal
  have hf : Measurable (fun v : Fin p.K → ℝ =>
      CanonicalRecordingRates.f p v a) := by
    unfold CanonicalRecordingRates.f
    fun_prop
  exact AssignmentPayloadDerivedMeasurability.measurable_dyadicCeiling.comp
    (measurable_const.max hf)

private theorem measurable_option_elim_local {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) (default : β) :
    Measurable (fun q : Option α => q.elim default f) := by
  have hsum : Measurable (Sum.elim f (fun _ : PUnit => default)) :=
    hf.sumElim measurable_const
  have heq : (fun q : Option α => q.elim default f) =
      (Sum.elim f (fun _ : PUnit => default)) ∘ Equiv.optionEquivSumPUnit α := by
    funext q
    cases q <;> rfl
  rw [heq]
  exact hsum.comp (comap_measurable _)

theorem roundedGap_measurable (control0 : TimeControl p) (u t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (roundedGap rate rewards C_star C_h u t S) := by
  have hG := measurableSet_G rate rewards C_star C_h control0 u t
  have hbase : Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (fun z =>
        (∑ a ∈ S.1, ((rewards t a).val : ℝ) / (D p : ℝ)) -
          ∑ a : Fin p.K,
            thetaMinus rate rewards C_star C_h u t a z *
              (((rewards t a).val : ℝ) / (D p : ℝ))) := by
    apply Measurable.sub
    · exact measurable_const
    · apply Finset.measurable_fun_sum
      intro a ha
      exact (measurable_thetaMinus rate rewards C_star C_h control0 u t a).mul
        measurable_const
  change Measurable[sourcePrefixFiltration control0 (t.val + 1)]
    ((G rate rewards C_star C_h u t).indicator (fun z =>
      (∑ a ∈ S.1, ((rewards t a).val : ℝ) / (D p : ℝ)) -
        ∑ a : Fin p.K,
          thetaMinus rate rewards C_star C_h u t a z *
            (((rewards t a).val : ℝ) / (D p : ℝ))))
  exact hbase.indicator hG

theorem roundedGap_integrable (control0 : TimeControl p) (u t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (roundedGap rate rewards C_star C_h u t S) (sourceInputLaw p) := by
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hmeas := roundedGap_measurable rate rewards C_star C_h control0 u t S
  have hbound (z : SourceInput p) :
      ‖roundedGap rate rewards C_star C_h u t S z‖ ≤
        (p.m : ℝ) + (p.K : ℝ) := by
    by_cases hz : z ∈ G rate rewards C_star C_h u t
    · rw [roundedGap, Set.indicator_of_mem hz, Real.norm_eq_abs]
      have hx := rawComparator_sum_bounds rewards t S
      have hy := weightedReward_sum_bounds rate rewards C_star C_h u t z
      calc
        |(∑ a ∈ S.1, ((rewards t a).val : ℝ) / (D p : ℝ)) -
            ∑ a : Fin p.K,
              thetaMinus rate rewards C_star C_h u t a z *
                (((rewards t a).val : ℝ) / (D p : ℝ))| ≤
            |(∑ a ∈ S.1, ((rewards t a).val : ℝ) / (D p : ℝ))| +
              |∑ a : Fin p.K,
                thetaMinus rate rewards C_star C_h u t a z *
                  (((rewards t a).val : ℝ) / (D p : ℝ))| := abs_sub _ _
        _ ≤ (p.m : ℝ) + (p.K : ℝ) := by
          have hxabs :
              |∑ a ∈ S.1, ((rewards t a).val : ℝ) / (D p : ℝ)| ≤
                (p.m : ℝ) := by
            rw [abs_of_nonneg hx.1]
            exact hx.2
          have hyabs :
              |∑ a : Fin p.K,
                  thetaMinus rate rewards C_star C_h u t a z *
                    (((rewards t a).val : ℝ) / (D p : ℝ))| ≤
                (p.K : ℝ) := by
            rw [abs_of_nonneg hy.1]
            exact hy.2
          exact add_le_add hxabs hyabs
    · simp [roundedGap, Set.indicator_of_notMem hz]
      positivity
  apply integrable_of_bounded_measurable
    (Measurable.mono hmeas hle le_rfl) _ (by positivity) hbound

theorem floorLoss_measurable (control0 : TimeControl p) (u t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (floorLoss rate rewards C_star C_h u t S) := by
  let Theta := AssignmentParameterFibreKernel.Theta p
  have hxiTheta (a : Fin p.K) : Measurable (fun q : Theta =>
      CanonicalRecordingRates.xi p rate.eta.val q.2 a) :=
    (xi_anchor_measurable rate a).comp measurable_snd
  have hsum : Measurable (fun q : Theta =>
      ∑ a ∈ S.1,
        CanonicalRecordingRates.xi p rate.eta.val q.2 a /
          (rate.eta.val * (D p : ℝ))) := by
    apply Finset.measurable_fun_sum S.1
    intro a ha
    exact (hxiTheta a).div_const _
  have hoption : Measurable (fun q : Option Theta =>
      q.elim 0 (fun theta =>
        ∑ a ∈ S.1,
          CanonicalRecordingRates.xi p rate.eta.val theta.2 a /
            (rate.eta.val * (D p : ℝ)))) :=
    measurable_option_elim_local _ hsum 0
  have hparameters := ReferenceCalendarLaterSamplerPredictability.calendarParameters_measurable
    rate rewards C_star C_h control0 t
  have hbase := hoption.comp hparameters
  have hG := measurableSet_G rate rewards C_star C_h control0 u t
  change Measurable[sourcePrefixFiltration control0 (t.val + 1)]
    ((G rate rewards C_star C_h u t).indicator (fun z =>
      match calendarParameters rate rewards C_star C_h t z with
      | none => 0
      | some params =>
          ∑ a ∈ S.1,
            CanonicalRecordingRates.xi p rate.eta.val params.2 a /
              (rate.eta.val * (D p : ℝ))))
  have hmatch : Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (fun z => match calendarParameters rate rewards C_star C_h t z with
        | none => 0
        | some params =>
            ∑ a ∈ S.1,
              CanonicalRecordingRates.xi p rate.eta.val params.2 a /
                (rate.eta.val * (D p : ℝ))) := by
    have heq :
        (fun z => match calendarParameters rate rewards C_star C_h t z with
          | none => 0
          | some params =>
              ∑ a ∈ S.1,
                CanonicalRecordingRates.xi p rate.eta.val params.2 a /
                  (rate.eta.val * (D p : ℝ))) =
        (fun z => (calendarParameters rate rewards C_star C_h t z).elim 0
          (fun params =>
            ∑ a ∈ S.1,
              CanonicalRecordingRates.xi p rate.eta.val params.2 a /
                (rate.eta.val * (D p : ℝ)))) := by
      funext z
      cases calendarParameters rate rewards C_star C_h t z <;> rfl
    rw [heq]
    exact hbase
  exact hmatch.indicator hG

theorem floorLoss_nonneg (u t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m)
    (z : SourceInput p) : 0 ≤ floorLoss rate rewards C_star C_h u t S z := by
  by_cases hz : z ∈ G rate rewards C_star C_h u t
  · obtain ⟨theta, htheta, _hlower, _hone, _hupper, _honeOne,
      _htwoNonneg, _htwo, _htwoBeta⟩ :=
    retainedMoment_bounds_on_G rate rewards C_star C_h u t
      ⟨0, ConstructorDimensions.K_pos p⟩ z hz
    rw [floorLoss, Set.indicator_of_mem hz, htheta]
    apply Finset.sum_nonneg
    intro a ha
    exact div_nonneg
      (le_of_lt (CanonicalRecordingRates.xi_pos p rate.eta.property theta.2 a))
      (le_of_lt (mul_pos rate.eta.property
        (by exact_mod_cast ConstructorDimensions.D_pos p)))
  · simp [floorLoss, Set.indicator_of_notMem hz]

theorem floorLoss_le (u t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m)
    (z : SourceInput p) :
    floorLoss rate rewards C_star C_h u t S z ≤
      (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) := by
  have hden : 0 < rate.eta.val * (D p : ℝ) :=
    mul_pos rate.eta.property (by exact_mod_cast ConstructorDimensions.D_pos p)
  by_cases hz : z ∈ G rate rewards C_star C_h u t
  · obtain ⟨theta, htheta, _hlower, _hone, _hupper, _honeOne,
      _htwoNonneg, _htwo, _htwoBeta⟩ :=
    retainedMoment_bounds_on_G rate rewards C_star C_h u t
      ⟨0, ConstructorDimensions.K_pos p⟩ z hz
    obtain ⟨_n, _r, actualTheta, _selected, _cell, _hn, _ht, _hr, _hrows,
      _hj, _hrewards, hactualTheta, _hselection, _hchosen, _hcell, _hread,
      _hanchor, hpositive⟩ :=
      ReferenceFirstCollectionCurrentRecordedCell.firstCell_selected
        rate rewards C_star C_h u t z hz.1
    have hthetaEq : theta = actualTheta := Option.some.inj (htheta.symm.trans hactualTheta)
    subst theta
    have hxi (a : Fin p.K) :
        CanonicalRecordingRates.xi p rate.eta.val actualTheta.2 a ≤ 1 := by
      have hsmall := CanonicalRecordingRates.xi_le_one_div_16mK
        p rate.eta.property rate.sourceCap actualTheta.2 hpositive a
      have hm : (1 : ℝ) ≤ (p.m : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.m_pos p)
      have hK : (1 : ℝ) ≤ (p.K : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.K_pos p)
      have hden' : (1 : ℝ) ≤ 16 * (p.m : ℝ) * (p.K : ℝ) := by nlinarith
      have hfrac : 1 / (16 * (p.m : ℝ) * (p.K : ℝ)) ≤ 1 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      exact hsmall.trans hfrac
    have hsum :
        (∑ a ∈ S.1, CanonicalRecordingRates.xi p rate.eta.val actualTheta.2 a) ≤
          (p.m : ℝ) := by
      calc
        _ ≤ ∑ a ∈ S.1, (1 : ℝ) :=
          Finset.sum_le_sum fun a ha => hxi a
        _ = (p.m : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, productSet_card]
          simp
    simp only [floorLoss, Set.indicator_of_mem hz, hactualTheta]
    calc
      (∑ a ∈ S.1,
        CanonicalRecordingRates.xi p rate.eta.val actualTheta.2 a /
          (rate.eta.val * (D p : ℝ))) =
          (∑ a ∈ S.1,
            CanonicalRecordingRates.xi p rate.eta.val actualTheta.2 a) /
              (rate.eta.val * (D p : ℝ)) := by
              rw [Finset.sum_div]
      _ ≤ (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) :=
        div_le_div_of_nonneg_right hsum hden.le
  · rw [floorLoss, Set.indicator_of_notMem hz]
    exact div_nonneg (Nat.cast_nonneg _) hden.le

theorem floorLoss_integrable (control0 : TimeControl p) (u t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (floorLoss rate rewards C_star C_h u t S) (sourceInputLaw p) := by
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hmeas := floorLoss_measurable rate rewards C_star C_h control0 u t S
  have hden : 0 < rate.eta.val * (D p : ℝ) :=
    mul_pos rate.eta.property (by exact_mod_cast ConstructorDimensions.D_pos p)
  have hbound (z : SourceInput p) :
      ‖floorLoss rate rewards C_star C_h u t S z‖ ≤
        (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (floorLoss_nonneg rate rewards C_star C_h u t S z)]
    exact floorLoss_le rate rewards C_star C_h u t S z
  apply integrable_of_bounded_measurable
    (Measurable.mono hmeas hle le_rfl) _ (div_nonneg (Nat.cast_nonneg _) hden.le) hbound

private theorem firstCell_pair_unique (u t u' t' : Fin p.T) (z : SourceInput p)
    (h₁ : z ∈ firstCell rate rewards C_star C_h u t)
    (h₂ : z ∈ firstCell rate rewards C_star C_h u' t') : (u, t) = (u', t') := by
  change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) = some (u, t) at h₁
  change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) = some (u', t') at h₂
  exact Option.some.inj (h₁.symm.trans h₂)

theorem sum_floorLoss_le (S : ProductSetLaw.ProductSet p.K p.m)
    (z : SourceInput p) :
    (∑ v ∈ (Finset.univ : Finset (Fin p.T × Fin p.T)),
      floorLoss rate rewards C_star C_h v.1 v.2 S z) ≤
        (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) := by
  classical
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none =>
      have hzero (v : Fin p.T × Fin p.T) :
          floorLoss rate rewards C_star C_h v.1 v.2 S z = 0 := by
        have hnot : z ∉ G rate rewards C_star C_h v.1 v.2 := by
          intro hg
          have hcell := hg.1
          unfold ReferenceCalendarCollectionCallControlLaw.firstCell at hcell
          change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
              rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) =
            some (v.1, v.2) at hcell
          rw [hcall] at hcell
          simp at hcell
        simp [floorLoss, hnot]
      simpa [hzero] using (div_nonneg (Nat.cast_nonneg p.m)
        (mul_pos rate.eta.property (by exact_mod_cast ConstructorDimensions.D_pos p)).le)
  | some c =>
      let q : Fin p.T × Fin p.T := (c.1, c.2.1)
      have hq : z ∈ firstCell rate rewards C_star C_h q.1 q.2 := by
        unfold ReferenceCalendarCollectionCallControlLaw.firstCell
        change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
          rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) =
            some (q.1, q.2)
        rw [hcall]
        simp [q]
      have hunique (v : Fin p.T × Fin p.T)
          (hv : z ∈ G rate rewards C_star C_h v.1 v.2) : v = q := by
        exact firstCell_pair_unique rate rewards C_star C_h v.1 v.2 q.1 q.2 z
          hv.1 hq
      have hsum :
          (∑ v ∈ (Finset.univ : Finset (Fin p.T × Fin p.T)),
            floorLoss rate rewards C_star C_h v.1 v.2 S z) =
          floorLoss rate rewards C_star C_h q.1 q.2 S z := by
        rw [Finset.sum_eq_single q
          (fun v _ hvne => by
            have hnot : z ∉ G rate rewards C_star C_h v.1 v.2 := by
              intro hg
              exact hvne (hunique v hg)
            simp [floorLoss, hnot])
          (by simp)]
      rw [hsum]
      exact floorLoss_le rate rewards C_star C_h q.1 q.2 S z

private theorem rawGap_condExp (control0 : TimeControl p) (u t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    μ[rawGap rate rewards C_star C_h u t S |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[μ]
      (fun z =>
        (∑ a ∈ S.1, retainedMomentOne rate rewards C_star C_h u t a z) -
          ∑ a : Fin p.K,
            thetaMinus rate rewards C_star C_h u t a z *
              retainedMomentOne rate rewards C_star C_h u t a z) := by
  let F := sourcePrefixFiltration control0 (t.val + 1)
  let leftPart := fun z : SourceInput p =>
    ∑ a ∈ S.1, retainedRaw rate rewards C_star C_h u t a z
  let rightPart := fun z : SourceInput p =>
    ∑ a : Fin p.K,
      thetaMinus rate rewards C_star C_h u t a z *
        retainedRaw rate rewards C_star C_h u t a z
  let leftMean := fun z : SourceInput p =>
    ∑ a ∈ S.1, retainedMomentOne rate rewards C_star C_h u t a z
  let rightMean := fun z : SourceInput p =>
    ∑ a : Fin p.K,
      thetaMinus rate rewards C_star C_h u t a z *
        retainedMomentOne rate rewards C_star C_h u t a z
  have hleftInt : Integrable leftPart μ := by
    exact integrable_finsetSum S.1 fun a ha =>
      retainedRaw_integrable rate rewards C_star C_h control0 u t a
  have hrightInt : Integrable rightPart μ := by
    exact integrable_finsetSum Finset.univ fun a ha =>
      thetaMinus_mul_retainedRaw_integrable rate rewards C_star C_h control0 u t a
  have hleftCE : μ[leftPart | F] =ᵐ[μ] leftMean := by
    have hsum := condExp_finsetSum (s := S.1)
      (f := fun a z => retainedRaw rate rewards C_star C_h u t a z)
      (fun a ha => retainedRaw_integrable rate rewards C_star C_h control0 u t a) F
    have harg : leftPart =
        ∑ a ∈ S.1, (fun z => retainedRaw rate rewards C_star C_h u t a z) := by
      funext z
      simp [leftPart, Finset.sum_apply]
    have hsumArg : μ[leftPart | F] =ᵐ[μ]
        μ[∑ a ∈ S.1,
          (fun z => retainedRaw rate rewards C_star C_h u t a z) | F] :=
      condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun harg z)
    have hsum' := hsumArg.trans hsum
    have hterms : ∀ᵐ z ∂μ, ∀ a ∈ S.1,
        μ[retainedRaw rate rewards C_star C_h u t a | F] z =
          retainedMomentOne rate rewards C_star C_h u t a z := by
      apply S.1.eventually_all.mpr
      intro a ha
      exact retainedRaw_condExp rate rewards C_star C_h control0 u t a
    filter_upwards [hsum', hterms] with z hsumz htermsz
    simp only [Finset.sum_apply] at hsumz
    rw [hsumz]
    exact Finset.sum_congr rfl fun a ha => htermsz a ha
  have hrightCE : μ[rightPart | F] =ᵐ[μ] rightMean := by
    have hsum := condExp_finsetSum (s := (Finset.univ : Finset (Fin p.K)))
      (f := fun a z =>
        thetaMinus rate rewards C_star C_h u t a z *
          retainedRaw rate rewards C_star C_h u t a z)
      (fun a ha => thetaMinus_mul_retainedRaw_integrable
        rate rewards C_star C_h control0 u t a) F
    have harg : rightPart =
        ∑ a : Fin p.K, (fun z =>
          thetaMinus rate rewards C_star C_h u t a z *
            retainedRaw rate rewards C_star C_h u t a z) := by
      funext z
      simp [rightPart, Finset.sum_apply]
    have hsumArg : μ[rightPart | F] =ᵐ[μ]
        μ[∑ a : Fin p.K, (fun z =>
          thetaMinus rate rewards C_star C_h u t a z *
            retainedRaw rate rewards C_star C_h u t a z) | F] :=
      condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun harg z)
    have hsum' := hsumArg.trans hsum
    have hterms : ∀ᵐ z ∂μ, ∀ a : Fin p.K,
        μ[(fun z => thetaMinus rate rewards C_star C_h u t a z *
            retainedRaw rate rewards C_star C_h u t a z) | F] z =
          thetaMinus rate rewards C_star C_h u t a z *
            retainedMomentOne rate rewards C_star C_h u t a z := by
      apply Filter.eventually_all.mpr
      intro a
      have hθ : StronglyMeasurable[F]
          (thetaMinus rate rewards C_star C_h u t a) :=
        (measurable_thetaMinus rate rewards C_star C_h control0 u t a).stronglyMeasurable
      have hpull := condExp_mul_of_stronglyMeasurable_left hθ
        (thetaMinus_mul_retainedRaw_integrable rate rewards C_star C_h control0 u t a)
        (retainedRaw_integrable rate rewards C_star C_h control0 u t a)
      have hA := retainedRaw_condExp rate rewards C_star C_h control0 u t a
      filter_upwards [hpull, hA] with x hp hAx
      calc
        μ[(fun z => thetaMinus rate rewards C_star C_h u t a z *
            retainedRaw rate rewards C_star C_h u t a z) | F] x =
            thetaMinus rate rewards C_star C_h u t a x *
              μ[retainedRaw rate rewards C_star C_h u t a | F] x := by
                convert hp using 1
        _ = thetaMinus rate rewards C_star C_h u t a x *
              retainedMomentOne rate rewards C_star C_h u t a x := by
                rw [hAx]
    filter_upwards [hsum', hterms] with z hsumz htermsz
    simp only [Finset.sum_apply] at hsumz
    rw [hsumz]
    exact Finset.sum_congr rfl fun a ha => htermsz a
  have hsub := condExp_sub hleftInt hrightInt F
  have hresult := hsub.trans (hleftCE.sub hrightCE)
  change μ[(leftPart - rightPart) | F] =ᵐ[μ] leftMean - rightMean
  exact hresult

theorem condExp_roundedGap_le_rawGap_add_floorLoss
    (control0 : TimeControl p) (u t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    μ[roundedGap rate rewards C_star C_h u t S |
      sourcePrefixFiltration control0 (t.val + 1)] ≤ᵐ[μ]
        μ[rawGap rate rewards C_star C_h u t S |
          sourcePrefixFiltration control0 (t.val + 1)] +
          floorLoss rate rewards C_star C_h u t S := by
  let F := sourcePrefixFiltration control0 (t.val + 1)
  have hroundedInt := roundedGap_integrable rate rewards C_star C_h control0 u t S
  have hroundedMeas := roundedGap_measurable rate rewards C_star C_h control0 u t S
  have hroundedCE : μ[roundedGap rate rewards C_star C_h u t S | F] =
      roundedGap rate rewards C_star C_h u t S :=
    condExp_of_stronglyMeasurable
      ((sourcePrefixFiltration control0).le' (t.val + 1))
      hroundedMeas.stronglyMeasurable hroundedInt
  have hrawCE := rawGap_condExp rate rewards C_star C_h control0 u t S
  have hpoint (z : SourceInput p) :
      roundedGap rate rewards C_star C_h u t S z ≤
        (∑ a ∈ S.1, retainedMomentOne rate rewards C_star C_h u t a z) -
          ∑ a : Fin p.K,
            thetaMinus rate rewards C_star C_h u t a z *
              retainedMomentOne rate rewards C_star C_h u t a z +
          floorLoss rate rewards C_star C_h u t S z := by
    by_cases hz : z ∈ G rate rewards C_star C_h u t
    · obtain ⟨theta, htheta, _hlower0, _hone0, _hupper0, _honeOne0,
        _htwoNonneg0, _htwo0, _htwoBeta0⟩ :=
        retainedMoment_bounds_on_G rate rewards C_star C_h u t
          ⟨0, ConstructorDimensions.K_pos p⟩ z hz
      have hmean (a : Fin p.K) :
          retainedMomentOne rate rewards C_star C_h u t a z ≤
            ((rewards t a).val : ℝ) / (D p : ℝ) ∧
          ((rewards t a).val : ℝ) / (D p : ℝ) -
              CanonicalRecordingRates.xi p rate.eta.val theta.2 a /
                (rate.eta.val * (D p : ℝ)) ≤
            retainedMomentOne rate rewards C_star C_h u t a z := by
        obtain ⟨theta', htheta', hlower, _hnonneg, _hupper, _hone, _htwoNonneg,
          _htwo, _htwoBeta⟩ :=
          retainedMoment_bounds_on_G rate rewards C_star C_h u t a z hz
        have hthetaEq : theta' = theta := Option.some.inj (htheta'.symm.trans htheta)
        subst theta'
        exact ⟨_hupper, hlower⟩
      have hlossArm (a : Fin p.K) :
          ((rewards t a).val : ℝ) / (D p : ℝ) -
            retainedMomentOne rate rewards C_star C_h u t a z ≤
          CanonicalRecordingRates.xi p rate.eta.val theta.2 a /
            (rate.eta.val * (D p : ℝ)) := by
        linarith [(hmean a).2]
      have hloss : floorLoss rate rewards C_star C_h u t S z =
          (∑ a ∈ S.1,
            CanonicalRecordingRates.xi p rate.eta.val theta.2 a /
              (rate.eta.val * (D p : ℝ))) := by
        simp [floorLoss, hz, htheta]
      rw [roundedGap, Set.indicator_of_mem hz, hloss]
      have hcompLower :
          (∑ a ∈ S.1, ((rewards t a).val : ℝ) / (D p : ℝ)) -
            (∑ a ∈ S.1, retainedMomentOne rate rewards C_star C_h u t a z) ≤
          ∑ a ∈ S.1,
            CanonicalRecordingRates.xi p rate.eta.val theta.2 a /
              (rate.eta.val * (D p : ℝ)) := by
        calc
          _ = ∑ a ∈ S.1,
              (((rewards t a).val : ℝ) / (D p : ℝ) -
                retainedMomentOne rate rewards C_star C_h u t a z) := by
                  rw [Finset.sum_sub_distrib]
          _ ≤ ∑ a ∈ S.1,
              (CanonicalRecordingRates.xi p rate.eta.val theta.2 a /
                (rate.eta.val * (D p : ℝ))) :=
                Finset.sum_le_sum fun a ha => hlossArm a
      have hweightedNonneg : 0 ≤
          ∑ a : Fin p.K,
            thetaMinus rate rewards C_star C_h u t a z *
              (((rewards t a).val : ℝ) / (D p : ℝ) -
                retainedMomentOne rate rewards C_star C_h u t a z) := by
        apply Finset.sum_nonneg
        intro a ha
        exact mul_nonneg (thetaMinus_bounds rate rewards C_star C_h u t a z).1
          (sub_nonneg.mpr (hmean a).1)
      have halgebra :
          (∑ a ∈ S.1, ((rewards t a).val : ℝ) / (D p : ℝ)) -
              ∑ a : Fin p.K,
                thetaMinus rate rewards C_star C_h u t a z *
                  (((rewards t a).val : ℝ) / (D p : ℝ)) ≤
            (∑ a ∈ S.1, retainedMomentOne rate rewards C_star C_h u t a z) -
              ∑ a : Fin p.K,
                thetaMinus rate rewards C_star C_h u t a z *
                  retainedMomentOne rate rewards C_star C_h u t a z +
              ∑ a ∈ S.1,
                CanonicalRecordingRates.xi p rate.eta.val theta.2 a /
                  (rate.eta.val * (D p : ℝ)) := by
        have hweightedId :
            (∑ a : Fin p.K,
                thetaMinus rate rewards C_star C_h u t a z *
                  (((rewards t a).val : ℝ) / (D p : ℝ))) -
              ∑ a : Fin p.K,
                thetaMinus rate rewards C_star C_h u t a z *
                  retainedMomentOne rate rewards C_star C_h u t a z =
            ∑ a : Fin p.K,
              thetaMinus rate rewards C_star C_h u t a z *
                (((rewards t a).val : ℝ) / (D p : ℝ) -
                  retainedMomentOne rate rewards C_star C_h u t a z) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro a ha
          ring
        linarith [hcompLower, hweightedNonneg, hweightedId]
      exact halgebra
    · have hmeanZero (a : Fin p.K) :
          retainedMomentOne rate rewards C_star C_h u t a z = 0 := by
        by_cases hE : z ∈ firstCell rate rewards C_star C_h u t
        · have hH : z ∉ ReferenceFirstCollectionCurrentRetainedGate.H
              rate rewards C_star C_h t := by
            intro hH
            exact hz ⟨hE, hH⟩
          simp [ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne, hH]
        · simp [ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne,
            ReferenceFirstCollectionCurrentRawMoments.currentMomentOne, hE]
      have hroundZero : roundedGap rate rewards C_star C_h u t S z = 0 := by
        simp [roundedGap, Set.indicator_of_notMem hz]
      have hfloorZero : floorLoss rate rewards C_star C_h u t S z = 0 := by
        simp [floorLoss, Set.indicator_of_notMem hz]
      rw [hroundZero, hfloorZero]
      simp_rw [hmeanZero]
      simp
  filter_upwards [hrawCE] with z hright
  change μ[roundedGap rate rewards C_star C_h u t S | F] z ≤
    μ[rawGap rate rewards C_star C_h u t S | F] z +
      floorLoss rate rewards C_star C_h u t S z
  rw [congrFun hroundedCE z, hright]
  exact hpoint z

theorem integral_roundedGap_le_rawGap_add_floorLoss
    (control0 : TimeControl p) (u t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z, roundedGap rate rewards C_star C_h u t S z ∂μ) ≤
      (∫ z, rawGap rate rewards C_star C_h u t S z ∂μ) +
        ∫ z, floorLoss rate rewards C_star C_h u t S z ∂μ := by
  let F := sourcePrefixFiltration control0 (t.val + 1)
  have hle := (sourcePrefixFiltration control0).le' (t.val + 1)
  have hrounded := roundedGap_integrable rate rewards C_star C_h control0 u t S
  have hraw := rawGap_integrable rate rewards C_star C_h control0 u t S
  have hfloor := floorLoss_integrable rate rewards C_star C_h control0 u t S
  have hcond := condExp_roundedGap_le_rawGap_add_floorLoss
    rate rewards C_star C_h control0 u t S
  have hleftInt : Integrable
      (μ[roundedGap rate rewards C_star C_h u t S | F]) μ := integrable_condExp
  have hrightInt : Integrable
      ((μ[rawGap rate rewards C_star C_h u t S | F]) +
        floorLoss rate rewards C_star C_h u t S) μ :=
    (integrable_condExp (f := rawGap rate rewards C_star C_h u t S)).add hfloor
  have hcond' : μ[roundedGap rate rewards C_star C_h u t S | F] ≤ᵐ[μ]
      (fun z => μ[rawGap rate rewards C_star C_h u t S | F] z +
        floorLoss rate rewards C_star C_h u t S z) := by
    filter_upwards [hcond] with z hz
    exact hz
  calc
    (∫ z, roundedGap rate rewards C_star C_h u t S z ∂μ) =
        ∫ z, μ[roundedGap rate rewards C_star C_h u t S | F] z ∂μ :=
      (integral_condExp (f := roundedGap rate rewards C_star C_h u t S) hle).symm
    _ ≤ ∫ z, μ[rawGap rate rewards C_star C_h u t S | F] z +
          floorLoss rate rewards C_star C_h u t S z ∂μ :=
      integral_mono_ae hleftInt hrightInt (by simpa [F] using hcond')
    _ = (∫ z, μ[rawGap rate rewards C_star C_h u t S | F] z ∂μ) +
          ∫ z, floorLoss rate rewards C_star C_h u t S z ∂μ :=
      integral_add (integrable_condExp (f := rawGap rate rewards C_star C_h u t S)) hfloor
    _ = (∫ z, rawGap rate rewards C_star C_h u t S z ∂μ) +
          ∫ z, floorLoss rate rewards C_star C_h u t S z ∂μ := by
      rw [integral_condExp hle]

theorem sum_floorLoss_integrable (control0 : TimeControl p)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (fun z =>
      ∑ v ∈ (Finset.univ : Finset (Fin p.T × Fin p.T)),
        floorLoss rate rewards C_star C_h v.1 v.2 S z) (sourceInputLaw p) :=
  integrable_finsetSum Finset.univ fun v _hv =>
    floorLoss_integrable rate rewards C_star C_h control0 v.1 v.2 S

theorem integral_sum_floorLoss_le (control0 : TimeControl p)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z, ∑ v ∈ (Finset.univ : Finset (Fin p.T × Fin p.T)),
      floorLoss rate rewards C_star C_h v.1 v.2 S z ∂μ) ≤
        (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) := by
  let pairs : Finset (Fin p.T × Fin p.T) := Finset.univ
  let total : SourceInput p → ℝ := fun z =>
    ∑ v ∈ pairs, floorLoss rate rewards C_star C_h v.1 v.2 S z
  have htotalInt : Integrable total μ := by
    exact integrable_finsetSum pairs fun v hv =>
      floorLoss_integrable rate rewards C_star C_h control0 v.1 v.2 S
  have hbound : ∀ z, total z ≤
      (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) := by
    intro z
    simpa [total, pairs] using sum_floorLoss_le rate rewards C_star C_h S z
  have hconstInt : Integrable (fun _ : SourceInput p =>
      (p.m : ℝ) / (rate.eta.val * (D p : ℝ))) μ := integrable_const _
  have hmono := integral_mono_ae htotalInt hconstInt
    (Filter.Eventually.of_forall hbound)
  calc
    (∫ z, ∑ v ∈ (Finset.univ : Finset (Fin p.T × Fin p.T)),
      floorLoss rate rewards C_star C_h v.1 v.2 S z ∂μ) ≤
        ∫ _ : SourceInput p,
          (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) ∂μ := by
      simpa [total, pairs] using hmono
    _ = (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) := by
      simp [integral_const, Measure.real, measure_univ]

theorem sum_integral_roundedGap_le
    (control0 : TimeControl p) (S : ProductSetLaw.ProductSet p.K p.m) :
    (∑ v ∈ (Finset.univ : Finset (Fin p.T × Fin p.T)),
      ∫ z, roundedGap rate rewards C_star C_h v.1 v.2 S z ∂μ) ≤
      (∑ v ∈ (Finset.univ : Finset (Fin p.T × Fin p.T)),
        ∫ z, rawGap rate rewards C_star C_h v.1 v.2 S z ∂μ) +
      (∑ v ∈ (Finset.univ : Finset (Fin p.T × Fin p.T)),
        ∫ z, floorLoss rate rewards C_star C_h v.1 v.2 S z ∂μ) := by
  calc
    _ ≤ ∑ v ∈ (Finset.univ : Finset (Fin p.T × Fin p.T)),
        ((∫ z, rawGap rate rewards C_star C_h v.1 v.2 S z ∂μ) +
          ∫ z, floorLoss rate rewards C_star C_h v.1 v.2 S z ∂μ) := by
      apply Finset.sum_le_sum
      intro v hv
      exact integral_roundedGap_le_rawGap_add_floorLoss
        rate rewards C_star C_h control0 v.1 v.2 S
    _ = _ := by rw [Finset.sum_add_distrib]

theorem sum_integral_roundedGap_le_rawGap_add_quantization_bound
    (control0 : TimeControl p) (S : ProductSetLaw.ProductSet p.K p.m) :
    (∑ v ∈ (Finset.univ : Finset (Fin p.T × Fin p.T)),
      ∫ z, roundedGap rate rewards C_star C_h v.1 v.2 S z ∂μ) ≤
      (∑ v ∈ (Finset.univ : Finset (Fin p.T × Fin p.T)),
        ∫ z, rawGap rate rewards C_star C_h v.1 v.2 S z ∂μ) +
        (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) := by
  have hsum := sum_integral_roundedGap_le rate rewards C_star C_h control0 S
  have hfloor := integral_sum_floorLoss_le rate rewards C_star C_h control0 S
  have hfloorEq :
      (∑ v ∈ (Finset.univ : Finset (Fin p.T × Fin p.T)),
        ∫ z, floorLoss rate rewards C_star C_h v.1 v.2 S z ∂μ) =
      ∫ z, ∑ v ∈ (Finset.univ : Finset (Fin p.T × Fin p.T)),
        floorLoss rate rewards C_star C_h v.1 v.2 S z ∂μ := by
    symm
    exact integral_finsetSum Finset.univ fun v hv =>
      floorLoss_integrable rate rewards C_star C_h control0 v.1 v.2 S
  rw [hfloorEq] at hsum
  linarith

end Bandits.Support.ReferenceFirstCollectionCurrentOriginalRoundedComparison

end
