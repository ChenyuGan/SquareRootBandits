/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalInstallationHandoverChoiceFrame
public import Bandits.Support.ReferenceOriginalInstallationHandoverWordSlice

import Mathlib.Tactic

/-!
# Fresh service on one actual original installation

This module studies one fixed calendar installation and its actual pending
followers on the original physical run. The birth date, current choice,
physical observations, and analytic first-bad mask all use the same source.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceFirstLiveHandoverBoundaryFactorization
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open scoped Classical ENNReal

namespace Bandits.Support.ReferenceOriginalInstallationHandoverFreshService

open ReferenceOriginalFixedInstallationHandoverSupport
open ReferenceFirstLiveHandoverBoundaryFactorization
open ReferenceFirstLiveHandoverConfirmationService

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : TimeControl p)

local notation "Source" => ReferenceOriginalFixedInstallationHandoverSupport.SourceInput p
local notation "μ" => sourceInputLaw p
local notation "F" => sourcePrefixFiltration control0

/-- The pre-acceptance physical observation, masked by the actual fixed-date
pending task and its ordinary CHOICE status. -/
public def X_before (ell t : Fin p.T) (i : Fin (p.m - 1))
    (z : Source) : ℝ :=
  (if before rate rewards C_star C_h ell t i z then (1 : ℝ) else 0) *
    (if V_before rate rewards C_star C_h i t z then (1 : ℝ) else 0)

/-- The accepted-word physical observation, masked by the actual fixed-date
pending task and its ordinary CHOICE status. -/
public def X_after (ell t : Fin p.T) (i : Fin (p.m - 1))
    (z : Source) : ℝ :=
  (if after rate rewards C_star C_h ell t i z then (1 : ℝ) else 0) *
    (if V_after rate rewards C_star C_h i t z then (1 : ℝ) else 0)

/-- The instantaneous service coefficient uses every positive arm in the
whole reward row. -/
public def serviceCoefficient (t : Fin p.T) : ℝ :=
  ((Finset.univ.filter fun a : Fin p.K => 0 < (rewards t a).val).card : ℝ) /
    (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ))

/-- The actual BEFORE and AFTER masks are disjoint because they use the two
distinct ordinary CHOICE status codes. -/
public theorem stages_disjoint (ell t : Fin p.T) (i : Fin (p.m - 1))
    (z : Source) :
    ¬ (before rate rewards C_star C_h ell t i z ∧
      after rate rewards C_star C_h ell t i z) := by
  rintro ⟨⟨_, hb⟩, ⟨_, ha⟩⟩
  exact (by decide : (some (0 : Fin 3) : Option (Fin 3)) ≠ some 1) (hb.symm.trans ha)

include control0 in
/-- The two fixed-installation service indicators are integrable on the full
original source law, including absent and exceptional physical branches. -/
theorem integrable_service_indicators (ell t : Fin p.T) (i : Fin (p.m - 1)) :
    Integrable (X_before rate rewards C_star C_h ell t i) μ ∧
      Integrable (X_after rate rewards C_star C_h ell t i) μ := by
  classical
  let Hb : Set Source := {z | before rate rewards C_star C_h ell t i z}
  let Ha : Set Source := {z | after rate rewards C_star C_h ell t i z}
  have hHbF : MeasurableSet[F (t.val + 1)] Hb := by
    exact (stages_measurableSet rate rewards C_star C_h control0 ell t i).1
  have hHaF : MeasurableSet[F (t.val + 1)] Ha := by
    exact (stages_measurableSet rate rewards C_star C_h control0 ell t i).2
  have hHb : MeasurableSet Hb :=
    (sourcePrefixFiltration control0).le (t.val + 1) Hb hHbF
  have hHa : MeasurableSet Ha :=
    (sourcePrefixFiltration control0).le (t.val + 1) Ha hHaF
  have hVb : MeasurableSet {z : Source | V_before rate rewards C_star C_h i t z} :=
    measurableSet_V_before rate rewards C_star C_h i t
  have hVa : MeasurableSet {z : Source | V_after rate rewards C_star C_h i t z} :=
    measurableSet_V_after rate rewards C_star C_h i t
  constructor
  · have hi := ((integrable_const (1 : ℝ) : Integrable (fun _ : Source => (1 : ℝ)) μ)
      ).indicator (hHb.inter hVb)
    convert hi using 1
    funext z
    by_cases hs : z ∈ Hb
    · have hs' : before rate rewards C_star C_h ell t i z := by simpa [Hb] using hs
      by_cases hv : V_before rate rewards C_star C_h i t z <;>
      simp [X_before, Hb, hs, hs', hv]
    · have hs' : ¬ before rate rewards C_star C_h ell t i z := by simpa [Hb] using hs
      by_cases hv : V_before rate rewards C_star C_h i t z <;>
      simp [X_before, Hb, hs, hs', hv]
  · have hi := ((integrable_const (1 : ℝ) : Integrable (fun _ : Source => (1 : ℝ)) μ)
      ).indicator (hHa.inter hVa)
    convert hi using 1
    funext z
    by_cases hs : z ∈ Ha
    · have hs' : after rate rewards C_star C_h ell t i z := by simpa [Ha] using hs
      by_cases hv : V_after rate rewards C_star C_h i t z <;>
      simp [X_after, Ha, hs, hs', hv]
    · have hs' : ¬ after rate rewards C_star C_h ell t i z := by simpa [Ha] using hs
      by_cases hv : V_after rate rewards C_star C_h i t z <;>
      simp [X_after, Ha, hs, hs', hv]

/-- The fixed-installation BEFORE mask is measurable by round end. -/
public theorem X_before_roundEnd_stronglyMeasurable (ell t : Fin p.T)
    (i : Fin (p.m - 1)) :
    StronglyMeasurable[F (t.val + 2)] (X_before rate rewards C_star C_h ell t i) := by
  have hstageSet := (stages_measurableSet rate rewards C_star C_h control0 ell t i).1
  have hstageSet' : MeasurableSet[F (t.val + 2)]
      {z : Source | before rate rewards C_star C_h ell t i z} := by
    exact (sourcePrefixFiltration control0).mono (by omega) _ hstageSet
  have hstage : StronglyMeasurable[F (t.val + 2)]
      (fun z : Source => if before rate rewards C_star C_h ell t i z then (1 : ℝ) else 0) := by
    change StronglyMeasurable[F (t.val + 2)]
      ({z | before rate rewards C_star C_h ell t i z}.indicator fun _ => (1 : ℝ))
    exact stronglyMeasurable_const.indicator hstageSet'
  have hobs := V_before_roundEnd_stronglyMeasurable rate rewards C_star C_h control0 i t
  change StronglyMeasurable[F (t.val + 2)]
    ((fun z => if before rate rewards C_star C_h ell t i z then (1 : ℝ) else 0) *
      (fun z => if V_before rate rewards C_star C_h i t z then (1 : ℝ) else 0))
  exact hstage.mul hobs

/-- The fixed-installation AFTER mask is measurable by round end. -/
public theorem X_after_roundEnd_stronglyMeasurable (ell t : Fin p.T)
    (i : Fin (p.m - 1)) :
    StronglyMeasurable[F (t.val + 2)] (X_after rate rewards C_star C_h ell t i) := by
  have hstageSet := (stages_measurableSet rate rewards C_star C_h control0 ell t i).2
  have hstageSet' : MeasurableSet[F (t.val + 2)]
      {z : Source | after rate rewards C_star C_h ell t i z} := by
    exact (sourcePrefixFiltration control0).mono (by omega) _ hstageSet
  have hstage : StronglyMeasurable[F (t.val + 2)]
      (fun z : Source => if after rate rewards C_star C_h ell t i z then (1 : ℝ) else 0) := by
    change StronglyMeasurable[F (t.val + 2)]
      ({z | after rate rewards C_star C_h ell t i z}.indicator fun _ => (1 : ℝ))
    exact stronglyMeasurable_const.indicator hstageSet'
  have hobs := V_after_roundEnd_stronglyMeasurable rate rewards C_star C_h control0 i t
  change StronglyMeasurable[F (t.val + 2)]
    ((fun z => if after rate rewards C_star C_h ell t i z then (1 : ℝ) else 0) *
      (fun z => if V_after rate rewards C_star C_h i t z then (1 : ℝ) else 0))
  exact hstage.mul hobs

/-- The combined masked service is zero or one on every original source.
This pointwise fact includes null, absent, and failure cases. -/
public theorem service_zero_or_one (ell t : Fin p.T) (i : Fin (p.m - 1))
    (z : Source) :
    X_before rate rewards C_star C_h ell t i z +
        X_after rate rewards C_star C_h ell t i z = 0 ∨
      X_before rate rewards C_star C_h ell t i z +
        X_after rate rewards C_star C_h ell t i z = 1 := by
  classical
  by_cases hb : before rate rewards C_star C_h ell t i z
  · have ha : ¬ after rate rewards C_star C_h ell t i z := by
      intro ha
      exact stages_disjoint rate rewards C_star C_h ell t i z ⟨hb, ha⟩
    by_cases hv : V_before rate rewards C_star C_h i t z <;>
      simp [X_before, X_after, hb, ha, hv]
  · by_cases ha : after rate rewards C_star C_h ell t i z
    · by_cases hv : V_after rate rewards C_star C_h i t z <;>
        simp [X_before, X_after, hb, ha, hv]
    · simp [X_before, X_after, hb, ha]

/-- The combined fixed-installation observation is measurable by round end. -/
public theorem combined_roundEnd_stronglyMeasurable (ell t : Fin p.T)
    (i : Fin (p.m - 1)) :
    StronglyMeasurable[F (t.val + 2)]
      (fun z => X_before rate rewards C_star C_h ell t i z +
        X_after rate rewards C_star C_h ell t i z) := by
  exact (X_before_roundEnd_stronglyMeasurable rate rewards C_star C_h control0 ell t i).add
    (X_after_roundEnd_stronglyMeasurable rate rewards C_star C_h control0 ell t i)

/-- Pull the fixed-installation BEFORE mask through the actual physical event
conditional law. The remaining integral is over the full current control. -/
private theorem before_condExp_whole_control_integral (ell t : Fin p.T) (i : Fin (p.m - 1)) :
    μ[(X_before rate rewards C_star C_h ell t i) | F (t.val + 1)] =ᵐ[μ]
      fun z => (if before rate rewards C_star C_h ell t i z then (1 : ℝ) else 0) *
        ∫ control,
          (if V_before rate rewards C_star C_h i t
            (replaceSourceControl p t (sourcePrefix control0 t.val z) control)
           then (1 : ℝ) else 0) ∂timeControlLaw p := by
  classical
  let Hs : Set Source := {z | before rate rewards C_star C_h ell t i z}
  let g : Source → ℝ := fun z => if z ∈ Hs then 1 else 0
  let f : Source → ℝ := fun z => if V_before rate rewards C_star C_h i t z then 1 else 0
  have hHs : MeasurableSet[F (t.val + 1)] Hs := by
    exact (stages_measurableSet rate rewards C_star C_h control0 ell t i).1
  have hg : StronglyMeasurable[F (t.val + 1)] g := by
    change StronglyMeasurable[F (t.val + 1)] (Hs.indicator fun _ => (1 : ℝ))
    exact stronglyMeasurable_const.indicator hHs
  have hf : StronglyMeasurable[F (t.val + 2)] f := by
    exact V_before_roundEnd_stronglyMeasurable rate rewards C_star C_h control0 i t
  have hfield : F (t.val + 1) ≤ F (t.val + 2) :=
    (sourcePrefixFiltration control0).mono (by omega)
  have hambient : F (t.val + 2) ≤ (inferInstance : MeasurableSpace Source) := by
    simpa using (sourcePrefixFiltration control0).le (t.val + 2)
  have hgA : StronglyMeasurable g := by
    exact (hg.mono hfield).mono hambient
  have hfA : StronglyMeasurable f := hf.mono hambient
  have hgfA : StronglyMeasurable (fun z => g z * f z) := hgA.mul hfA
  have hnormf : ∀ z, ‖f z‖ ≤ (1 : ℝ) := by
    intro z
    by_cases hv : V_before rate rewards C_star C_h i t z <;> simp [f, hv]
  have hnormgf : ∀ z, ‖g z * f z‖ ≤ (1 : ℝ) := by
    intro z
    by_cases hs : z ∈ Hs <;>
      by_cases hv : V_before rate rewards C_star C_h i t z <;>
      simp [g, f, hs, hv]
  have hfInt : Integrable f μ := by
    refine (integrable_const (1 : ℝ)).mono' hfA.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall hnormf
  have hgfInt : Integrable (fun z => g z * f z) μ := by
    refine (integrable_const (1 : ℝ)).mono' hgfA.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall hnormgf
  have hpull := condExp_mul_of_stronglyMeasurable_left hg hgfInt hfInt
  have hraw := V_before_condExp rate rewards C_star C_h control0 i t
  filter_upwards [hpull, hraw] with z hpull hz
  calc
    μ[(fun z => g z * f z) | F (t.val + 1)] z =
        g z * μ[f | F (t.val + 1)] z := hpull
    _ = g z * ∫ control,
          (if V_before rate rewards C_star C_h i t
            (replaceSourceControl p t (sourcePrefix control0 t.val z) control)
           then (1 : ℝ) else 0) ∂timeControlLaw p := by rw [hz]

/-- Pull the fixed-installation AFTER mask through the actual physical event
conditional law. The remaining integral is over the full current control. -/
private theorem after_condExp_whole_control_integral (ell t : Fin p.T) (i : Fin (p.m - 1)) :
    μ[(X_after rate rewards C_star C_h ell t i) | F (t.val + 1)] =ᵐ[μ]
      fun z => (if after rate rewards C_star C_h ell t i z then (1 : ℝ) else 0) *
        ∫ control,
          (if V_after rate rewards C_star C_h i t
            (replaceSourceControl p t (sourcePrefix control0 t.val z) control)
           then (1 : ℝ) else 0) ∂timeControlLaw p := by
  classical
  let Hs : Set Source := {z | after rate rewards C_star C_h ell t i z}
  let g : Source → ℝ := fun z => if z ∈ Hs then 1 else 0
  let f : Source → ℝ := fun z => if V_after rate rewards C_star C_h i t z then 1 else 0
  have hHs : MeasurableSet[F (t.val + 1)] Hs := by
    exact (stages_measurableSet rate rewards C_star C_h control0 ell t i).2
  have hg : StronglyMeasurable[F (t.val + 1)] g := by
    change StronglyMeasurable[F (t.val + 1)] (Hs.indicator fun _ => (1 : ℝ))
    exact stronglyMeasurable_const.indicator hHs
  have hf : StronglyMeasurable[F (t.val + 2)] f := by
    exact V_after_roundEnd_stronglyMeasurable rate rewards C_star C_h control0 i t
  have hfield : F (t.val + 1) ≤ F (t.val + 2) :=
    (sourcePrefixFiltration control0).mono (by omega)
  have hambient : F (t.val + 2) ≤ (inferInstance : MeasurableSpace Source) := by
    simpa using (sourcePrefixFiltration control0).le (t.val + 2)
  have hgA : StronglyMeasurable g := by
    exact (hg.mono hfield).mono hambient
  have hfA : StronglyMeasurable f := hf.mono hambient
  have hgfA : StronglyMeasurable (fun z => g z * f z) := hgA.mul hfA
  have hnormf : ∀ z, ‖f z‖ ≤ (1 : ℝ) := by
    intro z
    by_cases hv : V_after rate rewards C_star C_h i t z <;> simp [f, hv]
  have hnormgf : ∀ z, ‖g z * f z‖ ≤ (1 : ℝ) := by
    intro z
    by_cases hs : z ∈ Hs <;>
      by_cases hv : V_after rate rewards C_star C_h i t z <;>
      simp [g, f, hs, hv]
  have hfInt : Integrable f μ := by
    refine (integrable_const (1 : ℝ)).mono' hfA.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall hnormf
  have hgfInt : Integrable (fun z => g z * f z) μ := by
    refine (integrable_const (1 : ℝ)).mono' hgfA.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall hnormgf
  have hpull := condExp_mul_of_stronglyMeasurable_left hg hgfInt hfInt
  have hraw := V_after_condExp rate rewards C_star C_h control0 i t
  filter_upwards [hpull, hraw] with z hpull hz
  calc
    μ[(fun z => g z * f z) | F (t.val + 1)] z =
        g z * μ[f | F (t.val + 1)] z := hpull
    _ = g z * ∫ control,
          (if V_after rate rewards C_star C_h i t
            (replaceSourceControl p t (sourcePrefix control0 t.val z) control)
           then (1 : ℝ) else 0) ∂timeControlLaw p := by rw [hz]

private def serviceStage (accepted : Bool) (ell t : Fin p.T)
    (i : Fin (p.m - 1)) (z : Source) : Prop :=
  if accepted then after rate rewards C_star C_h ell t i z
  else before rate rewards C_star C_h ell t i z

private def serviceTest (accepted : Bool) (i : Fin (p.m - 1))
    (t : Fin p.T) (z : Source) : Prop :=
  if accepted then V_after rate rewards C_star C_h i t z
  else V_before rate rewards C_star C_h i t z

private theorem actual_record_replaced_current (t : Fin p.T) (z : Source)
    (u : TimeControl p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h t (replaceSourceControl p t z u) = some r) :
    r.input.row.2 t = u := by
  obtain ⟨hrows, hselected, htime, _hrewards⟩ :=
    ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
      rate rewards C_star C_h t (replaceSourceControl p t z u) r hr
  simp only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hselected,
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ActualInitializationPhysicalStep.selectedRowIndex,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex, Function.update_self]

private theorem affine_bit_integral (i : Fin (p.m - 1))
    (word : AffineChannelLaw.Word (B p)) (bit : AffineChannelLaw.Bit) :
    (∫ a : AffineSamples p,
      (if AffineChannelLaw.affineHash
          (a (0, show Fin (d p) from i)) word = bit then (1 : ℝ) else 0)
        ∂affineSamplesLaw p) = 1 / 2 := by
  let channel : Channel p := (0, show Fin (d p) from i)
  let A : Set (AffineChannelLaw.Sample (B p)) :=
    {sample | AffineChannelLaw.affineHash sample word = bit}
  have hA : MeasurableSet A := MeasurableSet.of_discrete
  have hpre : MeasurableSet {a : AffineSamples p |
      AffineChannelLaw.affineHash (a channel) word = bit} :=
    hA.preimage (measurable_pi_apply channel)
  have hmass : (affineSamplesLaw p)
      {a : AffineSamples p | AffineChannelLaw.affineHash (a channel) word = bit} =
      (1 : ℝ≥0∞) / 2 := by
    change (affineSamplesLaw p) ((fun a : AffineSamples p => a channel) ⁻¹' A) = _
    rw [← Measure.map_apply (measurable_pi_apply channel) hA]
    have hmap := (measurePreserving_eval
      (fun _ : Channel p => (AffineChannelLaw.jointLaw (B p)).toMeasure) channel).map_eq
    change (Measure.map _ (Measure.pi _)) A = _
    rw [hmap, ← AffineChannelLaw.eventProbability_eq_measure,
      AffineChannelLaw.affineHash_probability]
  have hint : (∫ a : AffineSamples p,
      {a | AffineChannelLaw.affineHash (a channel) word = bit}.indicator
        (fun _ => (1 : ℝ)) a ∂affineSamplesLaw p) =
      (affineSamplesLaw p).real {a | AffineChannelLaw.affineHash (a channel) word = bit} :=
    integral_indicator_one hpre
  have hint' : (∫ a : AffineSamples p,
      (if AffineChannelLaw.affineHash (a channel) word = bit then (1 : ℝ) else 0)
        ∂affineSamplesLaw p) =
      (affineSamplesLaw p).real {a | AffineChannelLaw.affineHash (a channel) word = bit} := by
    simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply] using hint
  rw [hint', Measure.real, hmass]
  norm_num

private theorem integrable_service_replacement (accepted : Bool)
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source) :
    Integrable (fun u : TimeControl p =>
      if serviceTest rate rewards C_star C_h accepted i t
          (replaceSourceControl p t z u) then (1 : ℝ) else 0) (timeControlLaw p) := by
  have hV : MeasurableSet {y : Source | serviceTest rate rewards C_star C_h accepted i t y} := by
    cases accepted with
    | false =>
        simpa only [serviceTest, Bool.false_eq_true, ite_false] using
          measurableSet_V_before rate rewards C_star C_h i t
    | true =>
        simpa only [serviceTest, ite_true] using
          measurableSet_V_after rate rewards C_star C_h i t
  have hset : MeasurableSet {u : TimeControl p |
      serviceTest rate rewards C_star C_h accepted i t (replaceSourceControl p t z u)} :=
    hV.preimage ((ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl
      p t).comp (measurable_const.prodMk measurable_id))
  exact (integrable_const (1 : ℝ)).indicator hset

include control0 in
private theorem actual_affine_first_integral (accepted : Bool) (ell t : Fin p.T)
    (i : Fin (p.m - 1)) (z : Source)
    (hz : serviceStage rate rewards C_star C_h accepted ell t i z)
    (x : Slice p) :
    (∫ a : AffineSamples p,
      (if serviceTest rate rewards C_star C_h accepted i t
          (replaceSourceControl p t z (x, a)) then (1 : ℝ) else 0)
        ∂affineSamplesLaw p) =
      (if PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
        0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val
       then (1 : ℝ) else 0) * (1 / 2) := by
  classical
  have hraw : rawPending rate rewards C_star C_h ell t i z := by
    cases accepted with
    | false =>
        have hb : before rate rewards C_star C_h ell t i z := by
          simpa only [serviceStage, Bool.false_eq_true, ite_false] using hz
        exact hb.1.2
    | true =>
        have ha : after rate rewards C_star C_h ell t i z := by
          simpa only [serviceStage, ite_true] using hz
        exact ha.1.2
  have hstage : serviceStage rate rewards C_star C_h accepted ell t i
      (replaceSourceControl p t z (x, control0.2)) := by
    cases accepted with
    | false =>
        have hb := (ReferenceOriginalFixedInstallationHandoverSupport.stages_replaceSourceControl
          rate rewards C_star C_h control0 ell t i z (x, control0.2)).1.mp
            (by simpa only [serviceStage, Bool.false_eq_true, ite_false] using hz)
        simpa only [serviceStage, Bool.false_eq_true, ite_false] using hb
    | true =>
        have ha := (ReferenceOriginalFixedInstallationHandoverSupport.stages_replaceSourceControl
          rate rewards C_star C_h control0 ell t i z (x, control0.2)).2.mp
            (by simpa only [serviceStage, ite_true] using hz)
        simpa only [serviceStage, ite_true] using ha
  obtain ⟨r0, selected0, hr0, hsel0, _hi0⟩ :=
    ReferenceOriginalInstallationHandoverWordSlice.replacement_actual_selected_witness
      rate rewards C_star C_h control0 ell t i z hraw (x, control0.2)
  let word := CoordinatorLocalArmChoice.storedDownFlatWord selected0.view.payload i
  have heq (a : AffineSamples p) :
      (if serviceTest rate rewards C_star C_h accepted i t
          (replaceSourceControl p t z (x, a)) then (1 : ℝ) else 0) =
      (if PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
        0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val
       then (if AffineChannelLaw.affineHash
          (a (0, show Fin (d p) from i)) word =
          (if accepted then (0 : AffineChannelLaw.Bit) else 1) then 1 else 0)
       else 0) := by
    have hstageA : serviceStage rate rewards C_star C_h accepted ell t i
        (replaceSourceControl p t z (x, a)) := by
      cases accepted with
      | false =>
          have hb := (ReferenceOriginalFixedInstallationHandoverSupport.stages_replaceSourceControl
            rate rewards C_star C_h control0 ell t i z (x, a)).1.mp
              (by simpa only [serviceStage, Bool.false_eq_true, ite_false] using hz)
          simpa only [serviceStage, Bool.false_eq_true, ite_false] using hb
      | true =>
          have ha := (ReferenceOriginalFixedInstallationHandoverSupport.stages_replaceSourceControl
            rate rewards C_star C_h control0 ell t i z (x, a)).2.mp
              (by simpa only [serviceStage, ite_true] using hz)
          simpa only [serviceStage, ite_true] using ha
    have hphysical : ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord
        (p := p) (rate := rate)) (selected : ReferenceActivePhysicalStep.Selection r.input),
        actualRecord rate rewards C_star C_h t (replaceSourceControl p t z (x, a)) = some r ∧
        r.output.preparation.coordinator.selection = some selected ∧
        (serviceTest rate rewards C_star C_h accepted i t
          (replaceSourceControl p t z (x, a)) ↔
          PublicDiscreteDraws.slotDraw (r.input.row.2 t).1 = PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (r.input.row.2 t).1 = i ∧
          CoordinatorLocalArmChoice.currentDownHash selected.view.payload
            (r.input.row.2 t) i = (if accepted then (0 : AffineChannelLaw.Bit) else 1) ∧
          0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
            (r.input.row.2 t).1).val
              (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val) := by
      cases accepted with
      | false =>
          obtain ⟨r, selected, hr, hsel, hgeometry⟩ :=
            ReferenceOriginalInstallationHandoverChoiceFrame.before_physical_service
              rate rewards C_star C_h ell t i (replaceSourceControl p t z (x, a))
              (by simpa only [serviceStage, Bool.false_eq_true, ite_false] using hstageA)
          refine ⟨r, selected, hr, hsel, ?_⟩
          simpa only [serviceTest, Bool.false_eq_true, ite_false,
            Bool.false_eq_true, ite_false] using hgeometry
      | true =>
          obtain ⟨r, selected, hr, hsel, hgeometry⟩ :=
            ReferenceOriginalInstallationHandoverChoiceFrame.after_physical_service
              rate rewards C_star C_h ell t i (replaceSourceControl p t z (x, a))
              (by simpa only [serviceStage, ite_true] using hstageA)
          refine ⟨r, selected, hr, hsel, ?_⟩
          simpa only [serviceTest, ite_true, ite_true] using hgeometry
    obtain ⟨r, selected, hr, hsel, hgeometry⟩ := hphysical
    have hpayload := ReferenceOriginalInstallationHandoverWordSlice.replacement_payload_eq_of_same_slice
      rate rewards C_star C_h control0 ell t i z hraw (x, a) (x, control0.2) rfl
      r r0 selected selected0 hr hr0 hsel hsel0
    have hcurrent := actual_record_replaced_current rate rewards C_star C_h t z
      (x, a) r hr
    have hgeometry' := hgeometry
    rw [hcurrent, hpayload.1] at hgeometry'
    simp only [CoordinatorLocalArmChoice.currentDownHash,
      CoordinatorLocalArmChoice.downChannel] at hgeometry'
    rw [hgeometry']
    simp only [word]
    have hpartition :
        (PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
          AffineChannelLaw.affineHash (a (0, i)) word =
            (if accepted then (0 : AffineChannelLaw.Bit) else 1) ∧
          0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val) ↔
        ((PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
          0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val) ∧
          AffineChannelLaw.affineHash (a (0, i)) word =
            (if accepted then (0 : AffineChannelLaw.Bit) else 1)) := by
      constructor
      · rintro ⟨hdown, hdraw, hbit, hpositive⟩
        exact ⟨⟨hdown, hdraw, hpositive⟩, hbit⟩
      · rintro ⟨⟨hdown, hdraw, hpositive⟩, hbit⟩
        exact ⟨hdown, hdraw, hbit, hpositive⟩
    calc
      _ = (if (PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
          0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val) ∧
          AffineChannelLaw.affineHash (a (0, i)) word =
            (if accepted then (0 : AffineChannelLaw.Bit) else 1)
         then (1 : ℝ) else 0) := by
        congr 1
        exact propext hpartition
      _ = if PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
          0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val then
          (if AffineChannelLaw.affineHash (a (0, i)) word =
            (if accepted then (0 : AffineChannelLaw.Bit) else 1) then 1 else 0)
        else 0 := by
          let scalar : Prop := PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
              PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
              0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
                (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val
          let bit : Prop := AffineChannelLaw.affineHash (a (0, i)) word =
            (if accepted then (0 : AffineChannelLaw.Bit) else 1)
          change (if scalar ∧ bit then (1 : ℝ) else 0) =
            if scalar then (if bit then 1 else 0) else 0
          by_cases hscalar : scalar
          · by_cases hbit : bit
            · rw [ite_eq_left ⟨hscalar, hbit⟩, ite_eq_left hscalar, ite_eq_left hbit]
            · have hleft : ¬ (scalar ∧ bit) := fun h => hbit h.2
              rw [ite_eq_right hleft, ite_eq_left hscalar, ite_eq_right hbit]
          · have hleft : ¬ (scalar ∧ bit) := fun h => hscalar h.1
            rw [ite_eq_right hleft, ite_eq_right hscalar]
  simp_rw [heq]
  by_cases hscalar : PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
      0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val
  · simp_rw [ite_eq_left hscalar]
    simpa only [one_mul] using
      (affine_bit_integral (p := p) i word
        (if accepted then (0 : AffineChannelLaw.Bit) else 1))
  · simp_rw [ite_eq_right hscalar]
    simp only [integral_zero, zero_mul]

include control0 in
private theorem actual_replacement_integral (accepted : Bool) (ell t : Fin p.T)
    (i : Fin (p.m - 1)) (z : Source)
    (hz : serviceStage rate rewards C_star C_h accepted ell t i z) :
    (∫ u : TimeControl p,
      (if serviceTest rate rewards C_star C_h accepted i t
          (replaceSourceControl p t z u) then (1 : ℝ) else 0)
        ∂timeControlLaw p) = serviceCoefficient rewards t := by
  let A : Set (Slice p) := {x |
    PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
      0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val}
  have hA : MeasurableSet A := by
    exact ((PublicDiscreteDraws.measurable_slotDraw (m := p.m) (K := p.K))
      (measurableSet_singleton _)).inter
      (((PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K)
        (measurableSet_singleton _)).inter
        ((MeasurableSet.of_discrete : MeasurableSet
          {tuple : OrderedTupleSampler.Tuple p.m p.K |
            0 < (rewards t (tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val}).preimage
          (OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K)))
  have hpositive (a : Fin p.K) :
      0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t a) ↔
        0 < (rewards t a).val := by
    change 0 < ((rewards t a).val : ℝ) / (D p : ℝ) ↔ _
    have hD : (0 : ℝ) < (D p : ℝ) := by exact_mod_cast D_pos p
    rw [div_pos_iff_of_pos_right hD]
    exact_mod_cast Iff.rfl
  let roundedRow : ActiveRoundActions.RewardRow p.K :=
    ⟨fun a => RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t a),
      fun a => RealRewardGridCount.realRewardGridValue_mem_Icc
        (D p) (D_pos p) (rewards t a)⟩
  let serviceSlice : Set (Slice p) :=
    {x | PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
      0 < roundedRow.val ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))}
  have hservice : serviceSlice = A := by
    ext x
    simp only [serviceSlice, A, Set.mem_ofPred_eq, roundedRow, hpositive]
  have hbase : (ContinuousControlSlice.sliceLaw p.m p.K) serviceSlice *
      ((1 : ℝ≥0∞) / 2) = ENNReal.ofReal
        (((DownServiceProbability.positiveArms roundedRow).card : ℝ) /
          (8 * (ContinuousLearningRows.d p : ℝ) * (p.K : ℝ))) :=
    positive_receiver_slice_half_probability rewards t i
  have hmass : (ContinuousControlSlice.sliceLaw p.m p.K) A * ((1 : ℝ≥0∞) / 2) =
      ENNReal.ofReal (serviceCoefficient rewards t) := by
    rw [← hservice, hbase, positiveArms_card_eq_original_grid_count rewards t]
    simp only [serviceCoefficient, ContinuousLearningRows.d]
  have hnonneg : 0 ≤ serviceCoefficient rewards t := by
    unfold serviceCoefficient
    positivity
  have hreal : ((ContinuousControlSlice.sliceLaw p.m p.K) A).toReal * ((1 : ℝ) / 2) =
      serviceCoefficient rewards t := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hnonneg] using
      congrArg ENNReal.toReal hmass
  rw [timeControlLaw, integral_prod _
    (integrable_service_replacement rate rewards C_star C_h accepted i t z)]
  simp_rw [actual_affine_first_integral rate rewards C_star C_h control0 accepted ell t i z hz]
  have hindicator : (fun x : Slice p =>
      if PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
        0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val then (1 : ℝ) else 0) =
      A.indicator 1 := by
    funext x
    simp only [A, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
  rw [integral_mul_const, hindicator, integral_indicator_one hA, Measure.real]
  exact hreal

public theorem before_condExp_integral (ell t : Fin p.T) (i : Fin (p.m - 1)) :
    μ[(X_before rate rewards C_star C_h ell t i) | F (t.val + 1)] =ᵐ[μ]
      fun z => serviceCoefficient rewards t *
        (if before rate rewards C_star C_h ell t i z then (1 : ℝ) else 0) := by
  filter_upwards [before_condExp_whole_control_integral rate rewards C_star C_h control0 ell t i]
    with z hz
  rw [hz]
  by_cases hstage : before rate rewards C_star C_h ell t i z
  · have hpref := (ReferenceOriginalFixedInstallationHandoverSupport.stages_factor
      rate rewards C_star C_h control0 ell t i z).1.mp hstage
    have hint := actual_replacement_integral rate rewards C_star C_h control0
      false ell t i (sourcePrefix control0 t.val z) hpref
    have hint' : (∫ control : TimeControl p,
        (if V_before rate rewards C_star C_h i t
          (replaceSourceControl p t (sourcePrefix control0 t.val z) control)
         then (1 : ℝ) else 0) ∂timeControlLaw p) = serviceCoefficient rewards t := by
      simpa only [serviceTest, Bool.false_eq_true, ite_false] using hint
    simp only [hstage, ite_true]
    rw [hint']
    ring
  · simp only [hstage, ite_false, zero_mul, mul_zero]

public theorem after_condExp_integral (ell t : Fin p.T) (i : Fin (p.m - 1)) :
    μ[(X_after rate rewards C_star C_h ell t i) | F (t.val + 1)] =ᵐ[μ]
      fun z => serviceCoefficient rewards t *
        (if after rate rewards C_star C_h ell t i z then (1 : ℝ) else 0) := by
  filter_upwards [after_condExp_whole_control_integral rate rewards C_star C_h control0 ell t i]
    with z hz
  rw [hz]
  by_cases hstage : after rate rewards C_star C_h ell t i z
  · have hpref := (ReferenceOriginalFixedInstallationHandoverSupport.stages_factor
      rate rewards C_star C_h control0 ell t i z).2.mp hstage
    have hint := actual_replacement_integral rate rewards C_star C_h control0
      true ell t i (sourcePrefix control0 t.val z) hpref
    have hint' : (∫ control : TimeControl p,
        (if V_after rate rewards C_star C_h i t
          (replaceSourceControl p t (sourcePrefix control0 t.val z) control)
         then (1 : ℝ) else 0) ∂timeControlLaw p) = serviceCoefficient rewards t := by
      simpa only [serviceTest, ite_true] using hint
    simp only [hstage, ite_true]
    rw [hint']
    ring
  · simp only [hstage, ite_false, zero_mul, mul_zero]

public theorem combined_condExp_integral (ell t : Fin p.T) (i : Fin (p.m - 1)) :
    μ[(fun z => X_before rate rewards C_star C_h ell t i z +
      X_after rate rewards C_star C_h ell t i z) | F (t.val + 1)] =ᵐ[μ]
      fun z => serviceCoefficient rewards t *
        (if pending rate rewards C_star C_h ell t i z then (1 : ℝ) else 0) := by
  obtain ⟨hbInt, haInt⟩ :=
    integrable_service_indicators rate rewards C_star C_h control0 ell t i
  have hbLaw := before_condExp_integral rate rewards C_star C_h control0 ell t i
  have haLaw := after_condExp_integral rate rewards C_star C_h control0 ell t i
  have hadd := condExp_add hbInt haInt (F (t.val + 1))
  filter_upwards [hadd, hbLaw, haLaw] with z hz hb ha
  change μ[(fun z => X_before rate rewards C_star C_h ell t i z +
      X_after rate rewards C_star C_h ell t i z) | F (t.val + 1)] z =
    μ[(X_before rate rewards C_star C_h ell t i) | F (t.val + 1)] z +
      μ[(X_after rate rewards C_star C_h ell t i) | F (t.val + 1)] z at hz
  rw [hz, hb, ha]
  have hpartition := ReferenceOriginalInstallationHandoverChoiceFrame.pending_stage_indicator_sum
    rate rewards C_star C_h ell t i z
  rw [hpartition]
  ring

end Bandits.Support.ReferenceOriginalInstallationHandoverFreshService

end
