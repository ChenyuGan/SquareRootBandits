/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionPrecallCalendarIncrementIdentity
public import Bandits.Support.ReferenceFirstCollectionCurrentConditionalWeightedDrift
public import Bandits.Support.ReferenceFirstCollectionOldPrefixOriginRateCredit

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Original pre-call OLD conditional weighted-energy drift

The scalar readouts below use the original optional pre-call cell prefix and
its zero-initialized recorded queue run. An absent prefix contributes zero.
This file is an internal OLD-date component; it does not close a manuscript
statement or assemble the later calendar telescope.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionOldConditionalWeightedEnergyDrift

open ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ActualInitializationPhysicalStep (GridRewardTable)
open ContinuousLearningRows (TimeControl)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefixFiltration)
open ReferenceFirstCollectionOldCalendarExponentialStep (E G)

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)
  (control0 : TimeControl p) (t : Fin p.T)

local notation "S" => SourceInput p
local notation "μ" => sourceInputLaw p
local notation "q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "F" => sourcePrefixFiltration control0 (t.val + 1)

local instance sourceInputMeasurableSpace : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Option α) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

/-! The Option-valued source prefix remains the literal calendar object. -/

/-- The original weighted-square potential of the actual pre-call prefix. -/
public def oldPotential (n : ℕ) (z : S) : ℝ :=
  match ReferenceFirstCollectionPrecallCalendarSupport.precallCells?
      rate rewards C_star C_h n z with
  | none => 0
  | some L =>
      RecordedWeightedDrift.weightedSquarePotential p.m q
        (RecordedQueueRun.run q L)

/-- The original weighted backlog of the actual pre-call prefix. -/
public def oldBacklog (n : ℕ) (z : S) : ℝ :=
  match ReferenceFirstCollectionPrecallCalendarSupport.precallCells?
      rate rewards C_star C_h n z with
  | none => 0
  | some L =>
      RecordedWeightedDrift.weightedBacklog p.m q
        (RecordedQueueRun.run q L)

/-- The retained OLD per-date potential increment on the source gate. -/
public def dOld (z : S) : ℝ :=
  (ReferenceFirstCollectionOldCalendarExponentialStep.G
    rate rewards C_star C_h t).indicator (fun z =>
    oldPotential rate rewards C_star C_h (t.val + 1) z -
      oldPotential rate rewards C_star C_h t.val z) z

/-- The OLD weighted-backlog cost on the same source gate. -/
public def costOld (z : S) : ℝ :=
  (ReferenceFirstCollectionOldCalendarExponentialStep.G
    rate rewards C_star C_h t).indicator (fun z =>
    oldBacklog rate rewards C_star C_h t.val z) z

private theorem integrable_of_bounded_measurable
    {f : S → ℝ} (hf : Measurable f) (C : ℝ)
    (_hC : 0 ≤ C) (hbound : ∀ z, ‖f z‖ ≤ C) : Integrable f μ := by
  have hconst : Integrable (fun _ : S => C) μ := integrable_const C
  refine hconst.mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with z
  simpa [Real.norm_eq_abs, abs_of_nonneg _hC] using hbound z

private theorem measurable_rateValue (a : Fin p.K) :
    Measurable (fun o : Option (Fin p.K → ℝ) =>
      (o.getD (fun _ => 0)) a) := by
  let e := Equiv.optionEquivSumPUnit (Fin p.K → ℝ)
  have he : Measurable e := comap_measurable _
  have hs : Measurable (Sum.elim (fun w : Fin p.K → ℝ => w a)
      (fun _ : PUnit => (0 : ℝ))) :=
    (measurable_pi_apply a).sumElim measurable_const
  have h := hs.comp he
  convert h using 1
  funext o
  dsimp only [Function.comp_apply]
  cases o <;> rfl

private theorem measurableSet_option_some {α : Type*} [MeasurableSpace α]
    (s : Set α) (hs : MeasurableSet s) :
    MeasurableSet (some '' s : Set (Option α)) := by
  change MeasurableSet[(inferInstance : MeasurableSpace (α ⊕ PUnit)).comap
    (Equiv.optionEquivSumPUnit α)]
    (some '' s)
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨Sum.inl '' s, measurableSet_inl_image.mpr hs, ?_⟩
  ext x
  cases x <;> simp

/-- The actual old marker's retained first and second conditional moments.
The rate and floor amplitude remain read from the same optional incoming
payload; the gate keeps absent, present-bottom, and disabled cases distinct. -/
public theorem old_retainedRaw_sq_condExp (a : Fin p.K) :
    (μ[(ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t).indicator
          (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
            rate rewards C_star C_h t a) |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[μ]
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t).indicator (fun z =>
            (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
              rate rewards C_star C_h t z).getD (fun _ => 0) a *
              (ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
                rate rewards C_star C_h t a z).getD 0)) ∧
    (μ[(fun z => ((ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t).indicator
          (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
            rate rewards C_star C_h t a) z) ^ 2) |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[μ]
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t).indicator (fun z =>
            (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
              rate rewards C_star C_h t z).getD (fun _ => 0) a *
              ((ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
                rate rewards C_star C_h t a z).getD 0) ^ 2)) ∧
    (∀ z, 0 ≤ (ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t).indicator (fun z =>
          (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
            rate rewards C_star C_h t z).getD (fun _ => 0) a *
            (ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
              rate rewards C_star C_h t a z).getD 0) z ∧
      (ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t).indicator (fun z =>
          (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
            rate rewards C_star C_h t z).getD (fun _ => 0) a *
            (ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
              rate rewards C_star C_h t a z).getD 0) z ≤
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t).indicator (fun _ => (1 : ℝ)) z) ∧
    (∀ z, 0 ≤ (ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t).indicator (fun z =>
          (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
            rate rewards C_star C_h t z).getD (fun _ => 0) a *
            ((ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
              rate rewards C_star C_h t a z).getD 0) ^ 2) z ∧
      (ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t).indicator (fun z =>
          (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
            rate rewards C_star C_h t z).getD (fun _ => 0) a *
            ((ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
              rate rewards C_star C_h t a z).getD 0) ^ 2) z ≤
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t).indicator (fun z =>
            1 / ((ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
              rate rewards C_star C_h t z).getD (fun _ => 0) a)) z) ∧
    Integrable ((ReferenceFirstCollectionOldCalendarExponentialStep.G
      rate rewards C_star C_h t).indicator
        (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
          rate rewards C_star C_h t a)) μ ∧
    Integrable (fun z => ((ReferenceFirstCollectionOldCalendarExponentialStep.G
      rate rewards C_star C_h t).indicator
        (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
          rate rewards C_star C_h t a) z) ^ 2) μ := by
  let g := ReferenceFirstCollectionOldCalendarExponentialStep.G
    rate rewards C_star C_h t
  let e := ReferenceFirstCollectionOldCalendarExponentialStep.E
    rate rewards C_star C_h t
  let raw : S → ℝ := g.indicator
    (ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h t a)
  let test : S → ℝ := fun z => if
    ReferenceFirstCollectionOldRecorderFoundation.oldMarker?
      rate rewards C_star C_h t z = some (some a) then 1 else 0
  let amp : S → ℝ := fun z =>
    (ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
      rate rewards C_star C_h t a z).getD 0
  let xi : S → ℝ := fun z =>
    (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
      rate rewards C_star C_h t z).getD (fun _ => 0) a
  let mark := g.indicator test
  let first := g.indicator (fun z => xi z * amp z)
  let second := g.indicator (fun z => xi z * amp z ^ 2)
  let inverse := g.indicator (fun z => 1 / xi z)
  have hFle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace S) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hgF : MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)] g := by
    simpa [g] using
      ReferenceFirstCollectionOldCalendarExponentialStep.measurableSet_G
        rate rewards C_star C_h control0 t
  have heF : MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)] e := by
    simpa [e] using
      ReferenceFirstCollectionOldCalendarExponentialStep.measurableSet_E
        rate rewards C_star C_h control0 t
  have hgAmb : MeasurableSet g := hFle _ hgF
  have heAmb : MeasurableSet e := hFle _ heF
  have hinner : @MeasurableSet (Option (Fin p.K))
      (PrivateRoundFreshness.optionArmMeasurableSpace p)
      ({some a} : Set (Option (Fin p.K))) := by
    change MeasurableSet[⊤] _
    simp
  have htarget : MeasurableSet
      ({some (some a)} : Set (Option (Option (Fin p.K)))) := by
    have hset : ({some (some a)} : Set (Option (Option (Fin p.K)))) =
        some '' ({some a} : Set (Option (Fin p.K))) := by
      ext x
      simp
    rw [hset]
    exact measurableSet_option_some _ hinner
  have htestSet : MeasurableSet {z : S |
      ReferenceFirstCollectionOldRecorderFoundation.oldMarker?
        rate rewards C_star C_h t z = some (some a)} :=
    htarget.preimage
      (ReferenceFirstCollectionOldRecorderFoundation.oldMarker_measurable
        rate rewards C_star C_h t)
  have htestM : Measurable test := by
    simpa [test] using
      (Measurable.ite htestSet measurable_const measurable_const)
  have hrawM : Measurable raw := by
    simpa [raw, g] using
      (ReferenceFirstCollectionOldRecorderFoundation.oldRaw_measurable
        rate rewards C_star C_h t a).indicator hgAmb
  have hrawBound : ∀ z, ‖raw z‖ ≤
      1 / CanonicalRecordingRates.beta p rate.eta.val := by
    intro z
    by_cases hz : z ∈ g
    · simp only [raw, Set.indicator_of_mem hz, Real.norm_eq_abs,
        abs_of_nonneg (ReferenceFirstCollectionOldRecorderFoundation.oldRaw_bounds
          rate rewards C_star C_h t a z).1]
      exact (ReferenceFirstCollectionOldRecorderFoundation.oldRaw_bounds
        rate rewards C_star C_h t a z).2
    · simp [raw, Set.indicator_of_notMem hz]
      positivity [CanonicalRecordingRates.beta_pos p rate.eta.property]
  have hbeta : 0 ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val :=
    (div_nonneg zero_le_one
      (CanonicalRecordingRates.beta_pos p rate.eta.property).le)
  have hrawInt : Integrable raw μ :=
    integrable_of_bounded_measurable hrawM _ hbeta hrawBound
  have hrawSqM : Measurable (fun z => raw z ^ 2) := hrawM.pow_const 2
  have hrawSqBound : ∀ z, ‖raw z ^ 2‖ ≤
      (1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2 := by
    intro z
    rw [norm_pow]
    exact (sq_le_sq₀ (norm_nonneg _) hbeta).2 (hrawBound z)
  have hrawSqInt : Integrable (fun z => raw z ^ 2) μ :=
    integrable_of_bounded_measurable hrawSqM _ (sq_nonneg _) hrawSqBound
  have hmarkM : Measurable mark := htestM.indicator hgAmb
  have hmarkBound (z : S) : ‖mark z‖ ≤ 1 := by
    by_cases hz : z ∈ g
    · by_cases ht : ReferenceFirstCollectionOldRecorderFoundation.oldMarker?
          rate rewards C_star C_h t z = some (some a)
      · simp [mark, Set.indicator_of_mem hz, test, ht]
      · simp [mark, Set.indicator_of_mem hz, test, ht]
    · simp [mark, Set.indicator_of_notMem hz]
  have hmarkInt : Integrable mark μ :=
    integrable_of_bounded_measurable hmarkM 1 (by norm_num) hmarkBound
  have hampF : Measurable[sourcePrefixFiltration control0 (t.val + 1)] amp := by
    simpa [amp] using
      ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitudeValue_measurable
        rate rewards C_star C_h control0 t a
  have hampSqF : Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (fun z => amp z ^ 2) := hampF.pow_const 2
  have hxiF : Measurable[sourcePrefixFiltration control0 (t.val + 1)] xi := by
    have h := (measurable_rateValue (p := p) a).comp
        (ReferenceFirstCollectionOldRecorderFoundation.incomingRates_measurable
          rate rewards C_star C_h control0 t)
    convert h using 1
    funext z
    rfl
  have htestEInt : Integrable (e.indicator test) μ := by
    have hM : Measurable (e.indicator test) := htestM.indicator heAmb
    have hB (z : S) : ‖e.indicator test z‖ ≤ 1 := by
      by_cases hz : z ∈ e
      · by_cases hm : ReferenceFirstCollectionOldRecorderFoundation.oldMarker?
            rate rewards C_star C_h t z = some (some a)
        · simp [Set.indicator_of_mem hz, test, hm]
        · simp [Set.indicator_of_mem hz, test, hm]
      · simp [Set.indicator_of_notMem hz]
    exact integrable_of_bounded_measurable hM 1 (by norm_num) hB
  have hmask : mark = g.indicator (e.indicator test) := by
    funext z
    by_cases hz : z ∈ g
    · have hzE : z ∈ e := by simpa [e] using hz.1.1
      simp [mark, Set.indicator_of_mem hz, Set.indicator_of_mem hzE]
    · simp [mark, Set.indicator_of_notMem hz]
  have hmarkCE :
      (μ[mark | sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[μ]
        g.indicator xi) := by
    have hceG := condExp_indicator htestEInt hgF
    have hEarm :=
      ReferenceFirstCollectionOldSelectorRecordingLaw.oldMarker_arm_condExp
        rate rewards C_star C_h control0 t a
    have hEarm' : μ[e.indicator test |
        sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[μ]
        e.indicator (fun z =>
          if ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled?
              rate rewards C_star C_h t z = some true then xi z else 0) := by
      simpa [e, ReferenceFirstCollectionOldCalendarExponentialStep.E, test, xi] using hEarm
    filter_upwards [hceG, hEarm'] with z hceGz hEarmz
    calc
      μ[mark | sourcePrefixFiltration control0 (t.val + 1)] z =
          μ[g.indicator (e.indicator test) |
            sourcePrefixFiltration control0 (t.val + 1)] z := by
              rw [hmask]
      _ = g.indicator
          (μ[e.indicator test | sourcePrefixFiltration control0 (t.val + 1)]) z :=
            hceGz
      _ = (g.indicator xi) z := by
        by_cases hz : z ∈ g
        · have hzE : z ∈ e := by simpa [e] using hz.1.1
          have hzEnabled : ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled?
              rate rewards C_star C_h t z = some true := by
            have hgate := hz
            simp only [g, ReferenceFirstCollectionOldCalendarExponentialStep.G,
              Set.mem_inter_iff, Set.mem_ofPred_eq] at hgate
            rcases hgate with ⟨_, hEnabled⟩
            exact hEnabled
          simp only [Set.indicator_of_mem hz]
          rw [hEarmz]
          simp [Set.indicator_of_mem hzE, hzEnabled, xi]
        · simp [Set.indicator_of_notMem hz]
  have hrawTest : ∀ z, raw z = amp z * mark z := by
    intro z
    by_cases hz : z ∈ g
    · have hzOld : z ∈ ReferenceFirstCollectionOldRecorderFoundation.oldSelector
          rate rewards C_star C_h t := by
        simpa [ReferenceFirstCollectionOldCalendarExponentialStep.E] using hz.1.1
      have hfact := ReferenceFirstCollectionOldRecorderFoundation.oldRaw_eq_test_mul_amplitude
        rate rewards C_star C_h t a z hzOld
      have hrawEq : raw z =
          ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h t a z := by
        simp [raw, Set.indicator_of_mem hz]
      have hmarkEq : mark z = test z := by simp [mark, Set.indicator_of_mem hz]
      rw [hrawEq, hmarkEq, hfact]
      simp [test, amp]
    · simp [raw, mark, Set.indicator_of_notMem hz]
  have hrawSqTest : ∀ z, raw z ^ 2 = amp z ^ 2 * mark z := by
    intro z
    rw [hrawTest z]
    by_cases hz : z ∈ g
    · simp only [mark, Set.indicator_of_mem hz, test]
      split_ifs <;> ring
    · simp [mark, Set.indicator_of_notMem hz]
  have hampMulInt : Integrable (fun z => amp z * mark z) μ :=
    hrawInt.congr (Filter.Eventually.of_forall hrawTest)
  have hampSqMulInt : Integrable (fun z => amp z ^ 2 * mark z) μ :=
    hrawSqInt.congr (Filter.Eventually.of_forall hrawSqTest)
  have hceRawMul := condExp_mul_of_stronglyMeasurable_left
    hampF.stronglyMeasurable hampMulInt hmarkInt
  have hceSqMul := condExp_mul_of_stronglyMeasurable_left
    hampSqF.stronglyMeasurable hampSqMulInt hmarkInt
  have hceRawMul' : μ[(fun z => amp z * mark z) |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[μ]
        (fun z => amp z * μ[mark | sourcePrefixFiltration control0 (t.val + 1)] z) := by
    have hfun : (fun z => amp z * mark z) =ᵐ[μ] (amp * mark) := by
      filter_upwards [] with z
      rfl
    calc
      _ =ᵐ[μ] μ[amp * mark | sourcePrefixFiltration control0 (t.val + 1)] :=
        condExp_congr_ae hfun
      _ =ᵐ[μ] amp * μ[mark | sourcePrefixFiltration control0 (t.val + 1)] := hceRawMul
      _ =ᵐ[μ] (fun z => amp z * μ[mark | sourcePrefixFiltration control0 (t.val + 1)] z) := by
        filter_upwards [] with z
        rfl
  have hceSqMul' : μ[(fun z => amp z ^ 2 * mark z) |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[μ]
        (fun z => amp z ^ 2 * μ[mark | sourcePrefixFiltration control0 (t.val + 1)] z) := by
    have hfun : (fun z => amp z ^ 2 * mark z) =ᵐ[μ]
        ((fun z => amp z ^ 2) * mark) := by
      filter_upwards [] with z
      rfl
    calc
      _ =ᵐ[μ] μ[(fun z => amp z ^ 2) * mark |
          sourcePrefixFiltration control0 (t.val + 1)] := condExp_congr_ae hfun
      _ =ᵐ[μ] (fun z => amp z ^ 2) * μ[mark |
          sourcePrefixFiltration control0 (t.val + 1)] := hceSqMul
      _ =ᵐ[μ] (fun z => amp z ^ 2 * μ[mark |
          sourcePrefixFiltration control0 (t.val + 1)] z) := by
        filter_upwards [] with z
        rfl
  have hfirstCE : μ[raw | sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[μ] first := by
    have hrawEqAE : raw =ᵐ[μ] (fun z => amp z * mark z) :=
      Filter.Eventually.of_forall hrawTest
    have hcongr : μ[raw | sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[μ]
        μ[(fun z => amp z * mark z) | sourcePrefixFiltration control0 (t.val + 1)] :=
      condExp_congr_ae hrawEqAE
    filter_upwards [hcongr, hceRawMul', hmarkCE] with z h1 h2 h3
    rw [h1, h2, h3]
    by_cases hz : z ∈ g <;> simp [first, Set.indicator, hz, mul_comm]
  have hsecondCE :
      μ[(fun z => raw z ^ 2) | sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[μ] second := by
    have hrawSqEqAE : (fun z => raw z ^ 2) =ᵐ[μ]
        (fun z => amp z ^ 2 * mark z) := by
      filter_upwards [] with z
      exact hrawSqTest z
    have hcongr : μ[(fun z => raw z ^ 2) | sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[μ]
        μ[(fun z => amp z ^ 2 * mark z) | sourcePrefixFiltration control0 (t.val + 1)] :=
      condExp_congr_ae hrawSqEqAE
    filter_upwards [hcongr, hceSqMul', hmarkCE] with z h1 h2 h3
    rw [h1, h2, h3]
    by_cases hz : z ∈ g <;> simp [second, Set.indicator, hz, mul_comm]
  have hfirstBounds : ∀ z, 0 ≤ first z ∧
      first z ≤ g.indicator (fun _ => (1 : ℝ)) z := by
    intro z
    by_cases hz : z ∈ g
    · have hzE : z ∈ ReferenceFirstCollectionOldRecorderFoundation.oldSelector
          rate rewards C_star C_h t := by
        simpa [ReferenceFirstCollectionOldCalendarExponentialStep.E] using hz.1.1
      obtain ⟨payload, hp, hnonneg, hmean, hreward⟩ :=
        ReferenceFirstCollectionOldRecorderFoundation.oldCell_firstMean_le_reward
          rate rewards C_star C_h t a z hzE
      have hxi : xi z = payload.rate a := by
        simp [xi,
          ReferenceFirstCollectionOldRecorderFoundation.incomingRates?, hp]
      have hamp : amp z =
          (ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
            rate rewards C_star C_h t a z).getD 0 := by
        rfl
      simp only [first, Set.indicator_of_mem hz]
      rw [hxi, hamp]
      exact ⟨hnonneg, hmean.trans hreward⟩
    · simp [first, Set.indicator_of_notMem hz]
  have hsecondBounds : ∀ z, 0 ≤ second z ∧
      second z ≤ inverse z := by
    intro z
    by_cases hz : z ∈ g
    · have hzE : z ∈ ReferenceFirstCollectionOldRecorderFoundation.oldSelector
          rate rewards C_star C_h t := by
        simpa [ReferenceFirstCollectionOldCalendarExponentialStep.E] using hz.1.1
      obtain ⟨payload, hp, hnonneg, hmean, hreward⟩ :=
        ReferenceFirstCollectionOldRecorderFoundation.oldCell_firstMean_le_reward
          rate rewards C_star C_h t a z hzE
      have hxi : xi z = payload.rate a := by
        simp [xi,
          ReferenceFirstCollectionOldRecorderFoundation.incomingRates?, hp]
      have hamp : amp z =
          (ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
            rate rewards C_star C_h t a z).getD 0 := rfl
      have hxiPos : 0 < xi z := by
        rw [hxi]
        exact (CanonicalRecordingRates.beta_pos p rate.eta.property).trans_le
          (AssignmentStartPayload.Input.beta_le_rate payload a)
      have hxiAmpNonneg : 0 ≤ xi z * amp z := by
        rw [hxi, hamp]
        exact hnonneg
      have hampNonneg : 0 ≤ amp z :=
        (mul_nonneg_iff_of_pos_left hxiPos).mp hxiAmpNonneg
      have hxiAmp : xi z * amp z ≤ 1 := by
        rw [hxi, hamp]
        exact hmean.trans hreward
      have hampInv : amp z ≤ 1 / xi z := (le_div_iff₀ hxiPos).2
        (by nlinarith only [hxiAmp])
      have hproduct : 0 ≤ xi z * amp z ^ 2 :=
        mul_nonneg hxiPos.le (sq_nonneg _)
      have hbound : xi z * amp z ^ 2 ≤ 1 / xi z := by
        calc
          xi z * amp z ^ 2 = amp z * (xi z * amp z) := by ring
          _ ≤ amp z * 1 := mul_le_mul_of_nonneg_left hxiAmp hampNonneg
          _ ≤ 1 / xi z := by simpa using hampInv
      simp only [second, inverse, Set.indicator_of_mem hz]
      exact ⟨hproduct, hbound⟩
    · simp [second, inverse, Set.indicator_of_notMem hz]
  refine ⟨?_, ?_, ?_, ?_, hrawInt, hrawSqInt⟩
  · simpa [raw, first, g, amp, xi] using hfirstCE
  · simpa [raw, second, g, amp, xi] using hsecondCE
  · intro z
    simpa [first, g] using hfirstBounds z
  · intro z
    simpa [second, inverse, g] using hsecondBounds z

/-- On the old selector outside the retained gate, the whole numerical score
and queue state is preserved. The proof uses the actual appended old cell;
queue preservation alone would not establish preservation of score weights. -/
private theorem oldPotential_preserve_on_E_outside_G (z : S)
    (hzE : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.E
      rate rewards C_star C_h t)
    (hzG : z ∉ ReferenceFirstCollectionOldCalendarExponentialStep.G
      rate rewards C_star C_h t) :
    oldPotential rate rewards C_star C_h (t.val + 1) z =
      oldPotential rate rewards C_star C_h t.val z := by
  obtain ⟨L, c, hL, hc, hnext, hrun⟩ :=
    ReferenceFirstCollectionOldCalendarExponentialStep.actual_old_calendar_append
      rate rewards C_star C_h t z hzE
  have hprefix :
      ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
        rate rewards C_star C_h t z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run q L)) := by
    have hread := ReferenceFirstCollectionOldCalendarExponentialStep.precallReadout_eq_prefixReadout_on_E
      rate rewards C_star C_h t z hzE
    have hread' : ReferenceFirstCollectionPrecallCalendarSupport.precallReadout?
        rate rewards C_star C_h t.val z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run q L)) := by
      simp [ReferenceFirstCollectionPrecallCalendarSupport.precallReadout?, hL]
    exact hread.symm.trans hread'
  have hstop : c.enabled = false ∨ (RecordedQueueRun.run q L).overflow = true := by
    by_cases hH : z ∈ ReferenceFirstCollectionCurrentRetainedGate.H
        rate rewards C_star C_h t
    · have hnotEnabled :
          ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled?
            rate rewards C_star C_h t z ≠ some true := by
        intro he
        exact hzG ⟨⟨hzE, hH⟩, he⟩
      have hinc := ReferenceFirstCollectionOldRecorderFoundation.oldCell_enabled_eq_incoming
        rate rewards C_star C_h t z c hc
      have hnot : c.enabled ≠ true := by
        intro he
        apply hnotEnabled
        simpa [he] using hinc
      cases he : c.enabled with
      | false => exact Or.inl rfl
      | true => exact False.elim (hnot he)
    · have hnotFalse :
          (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.run q L)).2.1 ≠ false := by
        intro hfalse
        apply hH
        exact ⟨_, hprefix, hfalse⟩
      have hoverflow : (RecordedQueueRun.run q L).overflow = true := by
        cases he : (RecordedQueueRun.run q L).overflow with
        | false =>
            exact False.elim (hnotFalse (by
              simp [he,
                ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout]))
        | true => exact rfl
      exact Or.inr hoverflow
  have hpot :=
    RecordedWeightedDrift.weightedSquarePotential_step_eq_of_disabled_or_overflowed
      p.m q (RecordedQueueRun.run q L) c hstop
  calc
    oldPotential rate rewards C_star C_h (t.val + 1) z =
        RecordedWeightedDrift.weightedSquarePotential p.m q
          (RecordedQueueRun.run q (L ++ [c])) := by
            simp [oldPotential, hnext]
    _ = RecordedWeightedDrift.weightedSquarePotential p.m q
          (RecordedQueueRun.step q (RecordedQueueRun.run q L) c) :=
            congrArg (RecordedWeightedDrift.weightedSquarePotential p.m q) hrun
    _ = RecordedWeightedDrift.weightedSquarePotential p.m q
          (RecordedQueueRun.run q L) := hpot
    _ = oldPotential rate rewards C_star C_h t.val z := by
          simp [oldPotential, hL]

/-- The localized OLD potential increment vanishes on the part of the actual
OLD selector excluded by the retained gate, including disabled cells and
already-overflowed prefixes. -/
public theorem old_increment_eq_E_increment :
    (ReferenceFirstCollectionOldCalendarExponentialStep.G
      rate rewards C_star C_h t).indicator (fun z =>
      oldPotential rate rewards C_star C_h (t.val + 1) z -
        oldPotential rate rewards C_star C_h t.val z) =
    (ReferenceFirstCollectionOldCalendarExponentialStep.E
      rate rewards C_star C_h t).indicator (fun z =>
      oldPotential rate rewards C_star C_h (t.val + 1) z -
        oldPotential rate rewards C_star C_h t.val z) := by
  funext z
  by_cases hzE : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.E
      rate rewards C_star C_h t
  · by_cases hzG : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t
    · simp [Set.indicator_of_mem hzG, Set.indicator_of_mem hzE]
    · have hzero := oldPotential_preserve_on_E_outside_G
        rate rewards C_star C_h t z hzE hzG
      simp [Set.indicator_of_notMem hzG, Set.indicator_of_mem hzE, hzero]
  · have hzG : z ∉ ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t := by
      intro h
      exact hzE h.1.1
    simp [Set.indicator_of_notMem hzE, Set.indicator_of_notMem hzG]

open ReferenceFirstCollectionCurrentQueueReadout
  (QueueReadout QueueArrivals before? normalizedReadoutBacklog optionalReadoutUpdate)
open ReferenceFirstCollectionCurrentQueueEnergy
  (weightVectorOfReadout thetaOfOptionalWeights)
open ReferenceFirstCollectionRenewalIncomingQueueMeasurability (stateReadout)
open ReferenceFirstCollectionPrecallCalendarSupport (precallCells? precallBacklog)
open ReferenceFirstCollectionOldRecorderFoundation (oldCell? oldRaw oldCoordinates?)

local instance readoutOptionMeasurableSpace : MeasurableSpace (Option (QueueReadout p.K)) :=
  ReferenceInitializationMeasurability.optionCountableMeasurableSpace _

private instance sumSingleton {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) where
  measurableSet_singleton x := by
    cases x with
    | inl a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inl_image
    | inr a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inr_image

private instance optionSingleton {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] : MeasurableSingletonClass (Option α) where
  measurableSet_singleton x := by
    have h := (comap_measurable (Equiv.optionEquivSumPUnit α))
      (MeasurableSet.singleton (Equiv.optionEquivSumPUnit α x))
    convert h using 1
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage,
      (Equiv.optionEquivSumPUnit α).injective.eq_iff]

/-- The original OLD cell applied to the existing optional incoming readout.
Both absent observations remain absent. -/
def oldAfter? (z : S) : Option (QueueReadout p.K) :=
  optionalReadoutUpdate rate (before? rate rewards C_star C_h t z)
    ((oldCoordinates? rate rewards C_star C_h t z).map
      (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate))

/-- Incoming marginal, localized only to the actual OLD selector. -/
def incomingTheta (a : Fin p.K) (z : S) : ℝ :=
  (E rate rewards C_star C_h t).indicator (fun z =>
    thetaOfOptionalWeights
      ((before? rate rewards C_star C_h t z).map weightVectorOfReadout) a) z

/-- Incoming normalized queue on the same actual OLD selector. -/
def incomingBacklog (a : Fin p.K) (z : S) : ℝ :=
  (E rate rewards C_star C_h t).indicator (fun z =>
    normalizedReadoutBacklog rate (before? rate rewards C_star C_h t z) a) z

/-- Scalar potential projection; absence contributes zero without a state. -/
def readoutPotential (o : Option (QueueReadout p.K)) : ℝ :=
  ∑ a : Fin p.K, thetaOfOptionalWeights (o.map weightVectorOfReadout) a *
    normalizedReadoutBacklog rate o a ^ 2

private theorem readoutPotential_state (state : RecordedQueueRun.RunState p.K) :
    readoutPotential rate (some (stateReadout state)) =
      RecordedWeightedDrift.weightedSquarePotential p.m q state := rfl

private theorem before_on_E (z : S) (hz : z ∈ E rate rewards C_star C_h t)
    (L : List (RecordedQueueRun.RoundInput p.K))
    (hL : precallCells? rate rewards C_star C_h t.val z = some L) :
    before? rate rewards C_star C_h t z = some (stateReadout (RecordedQueueRun.run q L)) := by
  have h := ReferenceFirstCollectionOldCalendarExponentialStep.precallReadout_eq_prefixReadout_on_E
    rate rewards C_star C_h t z hz
  exact h.symm.trans (by
    simp only [ReferenceFirstCollectionPrecallCalendarSupport.precallReadout?, hL, Option.map_some])

private theorem after_on_E (z : S) (hz : z ∈ E rate rewards C_star C_h t)
    (L : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K)
    (hL : precallCells? rate rewards C_star C_h t.val z = some L)
    (hc : oldCell? rate rewards C_star C_h t z = some c) :
    oldAfter? rate rewards C_star C_h t z =
      some (stateReadout (RecordedQueueRun.step q (RecordedQueueRun.run q L) c)) := by
  rw [oldAfter?, before_on_E rate rewards C_star C_h t z hz L hL]
  simp only [oldCoordinates?, hc, Option.map_some,
    ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical_numericalCoordinates,
    optionalReadoutUpdate, Option.bind_some, Option.map_some]
  rfl

private theorem oldAfter_measurable (control0 : TimeControl p) : Measurable (oldAfter? rate rewards C_star C_h t) := by
  have harr : Measurable (fun z => (oldCoordinates? rate rewards C_star C_h t z).map
      (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)) :=
    ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
      (fun v => ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate v.1)
      ((ReferenceLaterCollectionSourceReadoutMeasurability.measurable_arrivalsFromNumerical rate).comp
        measurable_fst) _
      (ReferenceFirstCollectionOldRecorderFoundation.oldCoordinates_measurable rate rewards C_star C_h t)
  have hu : Measurable (fun v : Option (QueueReadout p.K) × Option (QueueArrivals p.K) =>
      optionalReadoutUpdate rate v.1 v.2) := measurable_of_countable _
  exact hu.comp ((ReferenceFirstCollectionCurrentQueueReadout.before?_measurable_ambient
    rate rewards C_star C_h control0 t).prodMk harr)

private theorem incoming_measurable (a : Fin p.K) :
    Measurable[F] (incomingTheta rate rewards C_star C_h t a) ∧
    Measurable[F] (incomingBacklog rate rewards C_star C_h t a) := by
  have hT : Measurable (fun o : Option (QueueReadout p.K) =>
      thetaOfOptionalWeights (o.map weightVectorOfReadout) a) := measurable_of_countable _
  have hB : Measurable (fun o : Option (QueueReadout p.K) =>
      normalizedReadoutBacklog rate o a) := measurable_of_countable _
  have hread := ReferenceFirstCollectionCurrentQueueReadout.before?_measurable
    rate rewards C_star C_h control0 t
  have hE := ReferenceFirstCollectionOldCalendarExponentialStep.measurableSet_E
    rate rewards C_star C_h control0 t
  exact ⟨(hT.comp hread).indicator hE, (hB.comp hread).indicator hE⟩

private theorem incoming_on_E (a : Fin p.K) (z : S)
    (hz : z ∈ E rate rewards C_star C_h t)
    (L : List (RecordedQueueRun.RoundInput p.K))
    (hL : precallCells? rate rewards C_star C_h t.val z = some L) :
    incomingTheta rate rewards C_star C_h t a z =
      ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L)) a ∧
    incomingBacklog rate rewards C_star C_h t a z =
      StoppedQueueBound.normalizedBacklog q (RecordedQueueRun.run q L) a := by
  simp only [incomingTheta, incomingBacklog, Set.indicator_of_mem hz,
    before_on_E rate rewards C_star C_h t z hz L hL]
  exact ⟨rfl, rfl⟩

private theorem incoming_bounds (a : Fin p.K) (z : S) :
    0 ≤ incomingTheta rate rewards C_star C_h t a z ∧
    incomingTheta rate rewards C_star C_h t a z ≤ 1 ∧
    0 ≤ incomingBacklog rate rewards C_star C_h t a z ∧
    incomingBacklog rate rewards C_star C_h t a z ≤ 2 * (1 / (32 * rate.eta.val)) := by
  by_cases hz : z ∈ E rate rewards C_star C_h t
  · obtain ⟨L, c, hL, _, _, _⟩ :=
      ReferenceFirstCollectionOldCalendarExponentialStep.actual_old_calendar_append
        rate rewards C_star C_h t z hz
    rw [(incoming_on_E rate rewards C_star C_h t a z hz L hL).1,
      (incoming_on_E rate rewards C_star C_h t a z hz L hL).2]
    have hb := ReferenceFirstCollectionOldCalendarExponentialStep.precallBacklog_bounds
      rate rewards C_star C_h a t.val (Nat.le_of_lt t.isLt) z
    simp only [precallBacklog, hL] at hb
    exact ⟨(RecordedMarginalGrowth.state_theta_pos q _ a (m_pos p) p.m_lt_K).le,
      (ProductSetLaw.theta_lt_one _ a (m_pos p) p.m_lt_K
        (RecordedMarginalGrowth.state_scoreWeight_pos q _)).le, hb⟩
  · simp only [incomingTheta, incomingBacklog, Set.indicator_of_notMem hz]
    exact ⟨le_rfl, zero_le_one, le_rfl, by positivity [rate.eta.property]⟩

/-- Global bounds for the literal optional potential and backlog. -/
theorem old_readout_bounds (n : ℕ) (hn : n ≤ p.T) (z : S) :
    0 ≤ oldPotential rate rewards C_star C_h n z ∧
    oldPotential rate rewards C_star C_h n z ≤
      (p.K : ℝ) * (2 * (1 / (32 * rate.eta.val))) ^ 2 ∧
    0 ≤ oldBacklog rate rewards C_star C_h n z ∧
    oldBacklog rate rewards C_star C_h n z ≤
      (p.K : ℝ) * (2 * (1 / (32 * rate.eta.val))) := by
  cases hL : precallCells? rate rewards C_star C_h n z with
  | none =>
    simp only [oldPotential, oldBacklog, hL, le_refl, true_and]
    constructor <;> positivity [rate.eta.property]
  | some L =>
    have hθ (a : Fin p.K) :
        0 ≤ ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L)) a ∧
        ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L)) a ≤ 1 :=
      ⟨(RecordedMarginalGrowth.state_theta_pos q _ a (m_pos p) p.m_lt_K).le,
        (ProductSetLaw.theta_lt_one _ a (m_pos p) p.m_lt_K
          (RecordedMarginalGrowth.state_scoreWeight_pos q _)).le⟩
    have hb (a : Fin p.K) :=
      ReferenceFirstCollectionOldCalendarExponentialStep.precallBacklog_bounds
        rate rewards C_star C_h a n hn z
    simp only [precallBacklog, hL] at hb
    simp only [oldPotential, oldBacklog, hL, RecordedWeightedDrift.weightedSquarePotential,
      RecordedWeightedDrift.weightedBacklog]
    refine ⟨Finset.sum_nonneg (fun a _ => mul_nonneg (hθ a).1 (sq_nonneg _)), ?_,
      Finset.sum_nonneg (fun a _ => mul_nonneg (hθ a).1 (hb a).1), ?_⟩
    · calc
        _ ≤ ∑ _a : Fin p.K, (2 * (1 / (32 * rate.eta.val))) ^ 2 := by
          apply Finset.sum_le_sum
          intro a _
          exact (mul_le_of_le_one_left (sq_nonneg _) (hθ a).2).trans
            ((sq_le_sq₀ (hb a).1 (by positivity [rate.eta.property])).2 (hb a).2)
        _ = _ := by simp
    · calc
        _ ≤ ∑ _a : Fin p.K, 2 * (1 / (32 * rate.eta.val)) := by
          exact Finset.sum_le_sum fun a _ =>
            (mul_le_of_le_one_left (hb a).1 (hθ a).2).trans (hb a).2
        _ = _ := by simp

/-- Both actual OLD potentials are ambient measurable after localization to E. -/
theorem old_potential_measurable (control0 : TimeControl p) :
    Measurable ((E rate rewards C_star C_h t).indicator
      (oldPotential rate rewards C_star C_h t.val)) ∧
    Measurable ((E rate rewards C_star C_h t).indicator
      (oldPotential rate rewards C_star C_h (t.val + 1))) := by
  have hproject : Measurable (readoutPotential (p := p) rate) := measurable_of_countable _
  have hE : MeasurableSet (E rate rewards C_star C_h t) :=
    (sourcePrefixFiltration control0).le' (t.val + 1) _
      (ReferenceFirstCollectionOldCalendarExponentialStep.measurableSet_E
        rate rewards C_star C_h control0 t)
  have hbefore := (hproject.comp
    (ReferenceFirstCollectionCurrentQueueReadout.before?_measurable_ambient
      rate rewards C_star C_h control0 t)).indicator hE
  have hafter := (hproject.comp (oldAfter_measurable rate rewards C_star C_h t control0)).indicator hE
  have heq : ∀ z ∈ E rate rewards C_star C_h t,
      oldPotential rate rewards C_star C_h t.val z =
        readoutPotential rate (before? rate rewards C_star C_h t z) ∧
      oldPotential rate rewards C_star C_h (t.val + 1) z =
        readoutPotential rate (oldAfter? rate rewards C_star C_h t z) := by
    intro z hz
    obtain ⟨L, c, hL, hc, hnext, hrun⟩ :=
      ReferenceFirstCollectionOldCalendarExponentialStep.actual_old_calendar_append
        rate rewards C_star C_h t z hz
    rw [before_on_E rate rewards C_star C_h t z hz L hL,
      after_on_E rate rewards C_star C_h t z hz L c hL hc,
      readoutPotential_state, readoutPotential_state]
    simp only [oldPotential, hL, hnext, hrun, and_self]
  constructor
  · convert hbefore using 1
    exact Set.indicator_congr fun z hz => (heq z hz).1
  · convert hafter using 1
    exact Set.indicator_congr fun z hz => (heq z hz).2

/-- The deterministic reduced envelope uses the literal retained OLD raw arrival. -/
def reducedTerm (a : Fin p.K) (z : S) : ℝ :=
  (G rate rewards C_star C_h t).indicator (fun z =>
    incomingTheta rate rewards C_star C_h t a z *
      ((-15 / 2 : ℝ) * incomingBacklog rate rewards C_star C_h t a z +
        (2 * incomingBacklog rate rewards C_star C_h t a z + 1 / 2) *
          (G rate rewards C_star C_h t).indicator (oldRaw rate rewards C_star C_h t a) z +
        ((G rate rewards C_star C_h t).indicator (oldRaw rate rewards C_star C_h t a) z) ^ 2 + 16)) z

private theorem deterministic_drift (z : S) :
    dOld rate rewards C_star C_h t z ≤
      ∑ a : Fin p.K, reducedTerm rate rewards C_star C_h t a z := by
  by_cases hz : z ∈ G rate rewards C_star C_h t
  · obtain ⟨L, c, payload, r, hL, hc, _hp, _hrate, hnext, _hlen,
      _hsigma, _hanchor, _hspan, _hband, _hcredit, _hr, _htime, henabled, _hdate⟩ :=
      ReferenceFirstCollectionOldPrefixOriginRateCredit.old_prefix_score_and_rate_credit
        rate rewards C_star C_h t z hz
    have hrun : RecordedQueueRun.run q (L ++ [c]) =
        RecordedQueueRun.step q (RecordedQueueRun.run q L) c := by
      simp only [RecordedQueueRun.run, RecordedEpisodeStability.execute_append,
        RecordedQueueRun.execute]
    have hθ (a : Fin p.K) := (incoming_on_E rate rewards C_star C_h t a z hz.1.1 L hL).1
    have hb (a : Fin p.K) := (incoming_on_E rate rewards C_star C_h t a z hz.1.1 L hL).2
    have hraw (a : Fin p.K) : oldRaw rate rewards C_star C_h t a z =
        RecordedRoundMoments.normalizedQuantizedArrival q c a := by
      simp only [oldRaw, hc]
    have hrec (a : Fin p.K) :
        StoppedQueueBound.normalizedBacklog q (RecordedQueueRun.step q (RecordedQueueRun.run q L) c) a =
        QueueSquareDrift.queueNext (incomingBacklog rate rewards C_star C_h t a z)
          (oldRaw rate rewards C_star C_h t a z) := by
      have h := ReferenceFirstCollectionOldCalendarExponentialStep.precallBacklog_step_on_G
        rate rewards C_star C_h t a z hz
      simpa only [precallBacklog, hL, hnext, hrun, hb a, QueueSquareDrift.queueNext,
        max_comm] using h
    have hpoint (a : Fin p.K) :
        ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight q
            (RecordedQueueRun.step q (RecordedQueueRun.run q L) c)) a *
          StoppedQueueBound.normalizedBacklog q
            (RecordedQueueRun.step q (RecordedQueueRun.run q L) c) a ^ 2 -
        ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L)) a *
          StoppedQueueBound.normalizedBacklog q (RecordedQueueRun.run q L) a ^ 2 ≤
        reducedTerm rate rewards C_star C_h t a z := by
      let b := incomingBacklog rate rewards C_star C_h t a z
      let A := oldRaw rate rewards C_star C_h t a z
      have hA := (ReferenceFirstCollectionOldRecorderFoundation.oldRaw_bounds
        rate rewards C_star C_h t a z).1
      have hb0 := (incoming_bounds rate rewards C_star C_h t a z).2.2.1
      have hcap := (ReferenceFirstCollectionOldCalendarExponentialStep.precallBacklog_bounds
        rate rewards C_star C_h a (t.val + 1) (Nat.succ_le_of_lt t.isLt) z).2
      simp only [precallBacklog, hnext, hrun, hrec a] at hcap
      have hs := QueueSquareDrift.queueNext_sq_sub_le b A hb0 hA
      have hp := QueueSquareDrift.queueNext_sq_le_cap_mul b A
        (1 / (32 * rate.eta.val)) hb0 hA (by positivity [rate.eta.property]) hcap
      have heta : (q).eta ≤ 1 / 64 :=
        RecordedWeightedDrift.eta_le_one_div_sixtyFour p q rate.sourceCap
      have hg := RecordedMarginalGrowth.step_theta_growth q (RecordedQueueRun.run q L) c a
        p.two_le_m p.m_lt_K heta
      have hθ0 := (incoming_bounds rate rewards C_star C_h t a z).1
      have hθ0' : 0 ≤ ProductSetLaw.theta p.m
          (RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L)) a := by
        rw [← hθ a]; exact hθ0
      have hw := QueueSquareDrift.weighted_square_step _ _ (q).eta
        (QueueSquareDrift.queueNext b A) b hθ0' (q).eta_pos.le (hg.1.trans hg.2)
      rw [← hθ a] at hw
      rw [← hθ a, ← hb a, hrec a]
      simp only [reducedTerm, Set.indicator_of_mem hz]
      apply hw.trans
      apply mul_le_mul_of_nonneg_left _ hθ0
      have hscale := mul_le_mul_of_nonneg_left hp
        (show 0 ≤ 8 * rate.eta.val by positivity [rate.eta.property])
      have hcoef := RecordedWeightedDrift.sixteen_eta_mul_backlogCap q
      change 16 * rate.eta.val * (1 / (32 * rate.eta.val)) = (1 / 2 : ℝ) at hcoef
      have hscale' : 8 * rate.eta.val * QueueSquareDrift.queueNext b A ^ 2 ≤
          (1 / 2 : ℝ) * (b + A) := by
        calc
          _ ≤ 8 * rate.eta.val * (2 * (1 / (32 * rate.eta.val)) * (b + A)) := hscale
          _ = (16 * rate.eta.val * (1 / (32 * rate.eta.val))) * (b + A) := by ring
          _ = _ := by rw [hcoef]
      change QueueSquareDrift.queueNext b A ^ 2 - b ^ 2 +
        8 * rate.eta.val * QueueSquareDrift.queueNext b A ^ 2 ≤
        (-15 / 2 : ℝ) * b + (2 * b + 1 / 2) * A + A ^ 2 + 16
      linarith only [hs, hscale']
    simp only [dOld, Set.indicator_of_mem hz, oldPotential, hL, hnext, hrun,
      RecordedWeightedDrift.weightedSquarePotential, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun a _ => hpoint a
  · simp only [dOld, reducedTerm, Set.indicator_of_notMem hz, Finset.sum_const_zero, le_refl]

/-- Measurability and integrability of the actual retained increment and cost. -/
theorem old_readouts_regular :
    Measurable (dOld rate rewards C_star C_h t) ∧
    Integrable (dOld rate rewards C_star C_h t) μ ∧
    Measurable[F] (costOld rate rewards C_star C_h t) ∧
    Integrable (costOld rate rewards C_star C_h t) μ := by
  have hFle := (sourcePrefixFiltration control0).le' (t.val + 1)
  have hG := ReferenceFirstCollectionOldCalendarExponentialStep.measurableSet_G
    rate rewards C_star C_h control0 t
  have hGamb : MeasurableSet (G rate rewards C_star C_h t) := hFle _ hG
  have hp := old_potential_measurable rate rewards C_star C_h t control0
  have hdEq : dOld rate rewards C_star C_h t =
      (G rate rewards C_star C_h t).indicator (fun z =>
        (E rate rewards C_star C_h t).indicator
          (oldPotential rate rewards C_star C_h (t.val + 1)) z -
        (E rate rewards C_star C_h t).indicator
          (oldPotential rate rewards C_star C_h t.val) z) := by
    funext z
    by_cases hz : z ∈ G rate rewards C_star C_h t
    · simp only [dOld, Set.indicator_of_mem hz, Set.indicator_of_mem hz.1.1]
    · simp only [dOld, Set.indicator_of_notMem hz]
  have hdM : Measurable (dOld rate rewards C_star C_h t) := by
    rw [hdEq]
    exact (hp.2.sub hp.1).indicator hGamb
  have hcEq : costOld rate rewards C_star C_h t = fun z =>
      (G rate rewards C_star C_h t).indicator (fun z =>
        ∑ a : Fin p.K, incomingTheta rate rewards C_star C_h t a z *
          incomingBacklog rate rewards C_star C_h t a z) z := by
    funext z
    by_cases hz : z ∈ G rate rewards C_star C_h t
    · obtain ⟨L, c, hL, _, _, _⟩ :=
        ReferenceFirstCollectionOldCalendarExponentialStep.actual_old_calendar_append
          rate rewards C_star C_h t z hz.1.1
      simp only [costOld, Set.indicator_of_mem hz, oldBacklog, hL,
        RecordedWeightedDrift.weightedBacklog]
      exact Finset.sum_congr rfl fun a _ => by
        rw [(incoming_on_E rate rewards C_star C_h t a z hz.1.1 L hL).1,
          (incoming_on_E rate rewards C_star C_h t a z hz.1.1 L hL).2]
    · simp only [costOld, Set.indicator_of_notMem hz]
  have hcM : Measurable[F] (costOld rate rewards C_star C_h t) := by
    rw [hcEq]
    apply Measurable.indicator _ hG
    exact Finset.measurable_fun_sum _ fun a _ =>
      (incoming_measurable rate rewards C_star C_h control0 t a).1.mul
        (incoming_measurable rate rewards C_star C_h control0 t a).2
  have hdInt : Integrable (dOld rate rewards C_star C_h t) μ := by
    apply integrable_of_bounded_measurable hdM
      (2 * ((p.K : ℝ) * (2 * (1 / (32 * rate.eta.val))) ^ 2)) (by positivity)
    intro z
    by_cases hz : z ∈ G rate rewards C_star C_h t
    · rw [dOld, Set.indicator_of_mem hz, Real.norm_eq_abs, abs_le]
      have h0 := old_readout_bounds rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt) z
      have h1 := old_readout_bounds rate rewards C_star C_h (t.val + 1) (Nat.succ_le_of_lt t.isLt) z
      constructor <;> linarith only [h0.1, h0.2.1, h1.1, h1.2.1]
    · simp only [dOld, Set.indicator_of_notMem hz, norm_zero]
      positivity
  have hcInt : Integrable (costOld rate rewards C_star C_h t) μ := by
    apply integrable_of_bounded_measurable (Measurable.mono hcM hFle le_rfl)
      ((p.K : ℝ) * (2 * (1 / (32 * rate.eta.val)))) (by positivity [rate.eta.property])
    intro z
    by_cases hz : z ∈ G rate rewards C_star C_h t
    · have hb := (old_readout_bounds rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt) z).2.2
      simpa only [costOld, Set.indicator_of_mem hz, Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2
    · simp only [costOld, Set.indicator_of_notMem hz, norm_zero]
      positivity [rate.eta.property]
  exact ⟨hdM, hdInt, hcM, hcInt⟩

/-- The retained conditional first raw moment, with the original optional payload. -/
def momentOne (a : Fin p.K) (z : S) : ℝ :=
  (G rate rewards C_star C_h t).indicator (fun z =>
    (ReferenceFirstCollectionOldRecorderFoundation.incomingRates? rate rewards C_star C_h t z).getD
      (fun _ => 0) a *
    (ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude? rate rewards C_star C_h t a z).getD 0) z

/-- The retained conditional second raw moment on the same source law. -/
def momentTwo (a : Fin p.K) (z : S) : ℝ :=
  (G rate rewards C_star C_h t).indicator (fun z =>
    (ReferenceFirstCollectionOldRecorderFoundation.incomingRates? rate rewards C_star C_h t z).getD
      (fun _ => 0) a *
    ((ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude? rate rewards C_star C_h t a z).getD 0) ^ 2) z

private theorem reducedTerm_condExp (a : Fin p.K) :
    Integrable (reducedTerm rate rewards C_star C_h t a) μ ∧
    μ[reducedTerm rate rewards C_star C_h t a | F] =ᵐ[μ]
      (G rate rewards C_star C_h t).indicator (fun z =>
        incomingTheta rate rewards C_star C_h t a z *
          ((-15 / 2 : ℝ) * incomingBacklog rate rewards C_star C_h t a z +
            (2 * incomingBacklog rate rewards C_star C_h t a z + 1 / 2) *
              momentOne rate rewards C_star C_h t a z +
            momentTwo rate rewards C_star C_h t a z + 16)) := by
  let g := G rate rewards C_star C_h t
  let θ := incomingTheta rate rewards C_star C_h t a
  let b := incomingBacklog rate rewards C_star C_h t a
  let A := g.indicator (oldRaw rate rewards C_star C_h t a)
  let A2 := fun z => (A z) ^ 2
  let k0 := g.indicator (fun z => θ z * ((-15 / 2 : ℝ) * b z + 16))
  let k1 := g.indicator (fun z => θ z * (2 * b z + 1 / 2))
  let k2 := g.indicator θ
  let M := 2 * (1 / (32 * rate.eta.val))
  have hM : 0 ≤ M := by dsimp [M]; positivity [rate.eta.property]
  have hFle := (sourcePrefixFiltration control0).le' (t.val + 1)
  have hg := ReferenceFirstCollectionOldCalendarExponentialStep.measurableSet_G
    rate rewards C_star C_h control0 t
  have hθ := (incoming_measurable rate rewards C_star C_h control0 t a).1
  have hb := (incoming_measurable rate rewards C_star C_h control0 t a).2
  have hk0 : Measurable[F] k0 := (hθ.mul ((hb.const_mul _).add_const _)).indicator hg
  have hk1 : Measurable[F] k1 := (hθ.mul ((hb.const_mul _).add_const _)).indicator hg
  have hk2 : Measurable[F] k2 := hθ.indicator hg
  have hbounds z : 0 ≤ θ z ∧ θ z ≤ 1 ∧ 0 ≤ b z ∧ b z ≤ M :=
    incoming_bounds rate rewards C_star C_h t a z
  have hk0B z : ‖k0 z‖ ≤ (15 / 2 : ℝ) * M + 16 := by
    by_cases hz : z ∈ g
    · simp only [k0, Set.indicator_of_mem hz, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (hbounds z).1]
      have hi : |(-15 / 2 : ℝ) * b z + 16| ≤ (15 / 2 : ℝ) * M + 16 := by
        rw [abs_le]
        constructor <;> linarith only [(hbounds z).2.2.1, (hbounds z).2.2.2, hM]
      exact (mul_le_mul_of_nonneg_left hi (hbounds z).1).trans
        (mul_le_of_le_one_left (by positivity) (hbounds z).2.1)
    · simp only [k0, Set.indicator_of_notMem hz, norm_zero]
      positivity
  have hk1B z : ‖k1 z‖ ≤ 2 * M + 1 / 2 := by
    by_cases hz : z ∈ g
    · have hf : 0 ≤ 2 * b z + 1 / 2 := by linarith only [(hbounds z).2.2.1]
      simp only [k1, Set.indicator_of_mem hz, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (hbounds z).1, abs_of_nonneg hf]
      exact (mul_le_of_le_one_left hf (hbounds z).2.1).trans
        (by linarith only [(hbounds z).2.2.2])
    · simp only [k1, Set.indicator_of_notMem hz, norm_zero]
      positivity
  have hk2B z : ‖k2 z‖ ≤ 1 := by
    by_cases hz : z ∈ g
    · simpa only [k2, Set.indicator_of_mem hz, Real.norm_eq_abs,
        abs_of_nonneg (hbounds z).1] using (hbounds z).2.1
    · simp only [k2, Set.indicator_of_notMem hz, norm_zero, zero_le_one]
  have hi0 := integrable_of_bounded_measurable (Measurable.mono hk0 hFle le_rfl)
    _ (by positivity : 0 ≤ (15 / 2 : ℝ) * M + 16) hk0B
  have hm := old_retainedRaw_sq_condExp rate rewards C_star C_h control0 t a
  have hiA : Integrable A μ := hm.2.2.2.2.1
  have hiA2 : Integrable A2 μ := hm.2.2.2.2.2
  have hi1 : Integrable (fun z => k1 z * A z) μ :=
    hiA.bdd_mul (Measurable.mono hk1 hFle le_rfl).aestronglyMeasurable
      (ae_of_all _ hk1B)
  have hi2 : Integrable (fun z => k2 z * A2 z) μ :=
    hiA2.bdd_mul (Measurable.mono hk2 hFle le_rfl).aestronglyMeasurable
      (ae_of_all _ hk2B)
  have hdecomp : reducedTerm rate rewards C_star C_h t a =
      (k0 + (fun z => k1 z * A z)) + (fun z => k2 z * A2 z) := by
    funext z
    by_cases hz : z ∈ g <;>
      simp [reducedTerm, k0, k1, k2, A, A2, θ, b, g, Set.indicator, hz]; ring
  have hc0 : μ[k0 | F] = k0 :=
    condExp_of_stronglyMeasurable hFle hk0.stronglyMeasurable hi0
  have hc1 := condExp_mul_of_stronglyMeasurable_left hk1.stronglyMeasurable hi1 hiA
  have hc2 := condExp_mul_of_stronglyMeasurable_left hk2.stronglyMeasurable hi2 hiA2
  have hcAdd := condExp_add (hi0.add hi1) hi2 F
  have hcAdd01 := condExp_add hi0 hi1 F
  refine ⟨by rw [hdecomp]; exact (hi0.add hi1).add hi2, ?_⟩
  rw [hdecomp]
  filter_upwards [hcAdd, hcAdd01, hc1, hc2, hm.1, hm.2.1] with z hsum hsum01 h1 h2 hA hA2
  rw [hsum]
  simp only [Pi.add_apply]
  rw [hsum01]
  simp only [Pi.add_apply]
  change μ[(fun z => k1 z * A z) | F] z = k1 z * μ[A | F] z at h1
  change μ[(fun z => k2 z * A2 z) | F] z = k2 z * μ[A2 | F] z at h2
  rw [congrFun hc0 z, h1, h2]
  change μ[A | F] z = momentOne rate rewards C_star C_h t a z at hA
  change μ[A2 | F] z = momentTwo rate rewards C_star C_h t a z at hA2
  rw [hA, hA2]
  by_cases hz : z ∈ g <;> simp [k0, k1, k2, θ, b, g, Set.indicator, hz]; ring

include control0 in
private theorem moment_bound_on_G (z : S) (hz : z ∈ G rate rewards C_star C_h t) :
    (∑ a : Fin p.K, incomingTheta rate rewards C_star C_h t a z *
      ((-15 / 2 : ℝ) * incomingBacklog rate rewards C_star C_h t a z +
        (2 * incomingBacklog rate rewards C_star C_h t a z + 1 / 2) *
          momentOne rate rewards C_star C_h t a z +
        momentTwo rate rewards C_star C_h t a z + 16)) ≤
      CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ) -
        (11 / 2 : ℝ) * oldBacklog rate rewards C_star C_h t.val z := by
  obtain ⟨L, c, payload, r, hL, _hc, hp, hrate, _hnext, _hlen,
    _hsigma, _hanchor, _hspan, _hband, hcredit, _hr, _htime, _henabled, _hdate⟩ :=
    ReferenceFirstCollectionOldPrefixOriginRateCredit.old_prefix_score_and_rate_credit
      rate rewards C_star C_h t z hz
  have hθ (a : Fin p.K) := (incoming_on_E rate rewards C_star C_h t a z hz.1.1 L hL).1
  have hb (a : Fin p.K) := (incoming_on_E rate rewards C_star C_h t a z hz.1.1 L hL).2
  have hsumθ : (∑ a : Fin p.K, incomingTheta rate rewards C_star C_h t a z) = (p.m : ℝ) := by
    simp_rw [hθ]
    exact RecordedMarginalGrowth.state_sum_theta_eq_m q _ (m_pos p) p.m_lt_K
  have hsumB : (∑ a : Fin p.K, incomingTheta rate rewards C_star C_h t a z *
      incomingBacklog rate rewards C_star C_h t a z) =
      oldBacklog rate rewards C_star C_h t.val z := by
    simp only [oldBacklog, hL, RecordedWeightedDrift.weightedBacklog]
    exact Finset.sum_congr rfl fun a _ => by rw [hθ a, hb a]
  have hterms (a : Fin p.K) :
      incomingTheta rate rewards C_star C_h t a z *
        ((-15 / 2 : ℝ) * incomingBacklog rate rewards C_star C_h t a z +
          (2 * incomingBacklog rate rewards C_star C_h t a z + 1 / 2) *
            momentOne rate rewards C_star C_h t a z +
          momentTwo rate rewards C_star C_h t a z + 16) ≤
      incomingTheta rate rewards C_star C_h t a z *
        ((-11 / 2 : ℝ) * incomingBacklog rate rewards C_star C_h t a z + 1 / c.rate a + 33 / 2) := by
    have hm := old_retainedRaw_sq_condExp rate rewards C_star C_h control0 t a
    have hfirst : momentOne rate rewards C_star C_h t a z ≤ 1 := by
      simpa only [momentOne, Set.indicator_of_mem hz] using (hm.2.2.1 z).2
    have hsecond : momentTwo rate rewards C_star C_h t a z ≤ 1 / c.rate a := by
      have h := (hm.2.2.2.1 z).2
      simpa only [momentTwo, Set.indicator_of_mem hz,
        ReferenceFirstCollectionOldRecorderFoundation.incomingRates?, hp,
        Option.map_some, Option.getD_some, ← hrate] using h
    have hb0 := (incoming_bounds rate rewards C_star C_h t a z).2.2.1
    have hmean := mul_le_mul_of_nonneg_left hfirst
      (show 0 ≤ 2 * incomingBacklog rate rewards C_star C_h t a z + 1 / 2 by linarith)
    apply mul_le_mul_of_nonneg_left _ (incoming_bounds rate rewards C_star C_h t a z).1
    linarith only [hmean, hsecond]
  calc
    _ ≤ ∑ a : Fin p.K, incomingTheta rate rewards C_star C_h t a z *
        ((-11 / 2 : ℝ) * incomingBacklog rate rewards C_star C_h t a z + 1 / c.rate a + 33 / 2) :=
      Finset.sum_le_sum fun a _ => hterms a
    _ = (-11 / 2 : ℝ) * oldBacklog rate rewards C_star C_h t.val z +
        (∑ a : Fin p.K, incomingTheta rate rewards C_star C_h t a z / c.rate a) +
        (33 / 2 : ℝ) * (p.m : ℝ) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have hleft : (∑ a : Fin p.K, incomingTheta rate rewards C_star C_h t a z *
          ((-11 / 2 : ℝ) * incomingBacklog rate rewards C_star C_h t a z)) =
          (-11 / 2 : ℝ) * oldBacklog rate rewards C_star C_h t.val z := by
        rw [← hsumB, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
      rw [hleft, ← Finset.sum_mul, hsumθ]
      simp only [mul_one_div]
      ring
    _ ≤ _ := by simp_rw [hθ]; linarith only [hcredit]

/-- Unconditional per-date OLD conditional weighted-energy drift. The only
inputs are the original data, control and date; origin and credit are produced
inside the proof. The first overflow-detecting update is retained. -/
theorem conditional_weighted_drift :
    μ[dOld rate rewards C_star C_h t | F] ≤ᵐ[μ]
      (G rate rewards C_star C_h t).indicator (fun z =>
        CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ) -
          (11 / 2 : ℝ) * oldBacklog rate rewards C_star C_h t.val z) := by
  have hterms a := reducedTerm_condExp rate rewards C_star C_h control0 t a
  have hsumInt : Integrable (fun z => ∑ a : Fin p.K,
      reducedTerm rate rewards C_star C_h t a z) μ :=
    integrable_finsetSum _ fun a _ => (hterms a).1
  have hmono := condExp_mono (m := F)
    (old_readouts_regular rate rewards C_star C_h control0 t).2.1 hsumInt
    (ae_of_all _ (deterministic_drift rate rewards C_star C_h t))
  have hsum := condExp_finsetSum (fun a (_ : a ∈ (Finset.univ : Finset (Fin p.K))) =>
    (hterms a).1) F
  have hsum' : μ[(fun z => ∑ a : Fin p.K, reducedTerm rate rewards C_star C_h t a z) | F] =ᵐ[μ]
      (fun z => ∑ a : Fin p.K, μ[reducedTerm rate rewards C_star C_h t a | F] z) := by
    simpa only [Finset.sum_fn] using hsum
  have hall : ∀ᵐ z ∂μ, ∀ a : Fin p.K,
      μ[reducedTerm rate rewards C_star C_h t a | F] z =
        (G rate rewards C_star C_h t).indicator (fun z =>
          incomingTheta rate rewards C_star C_h t a z *
            ((-15 / 2 : ℝ) * incomingBacklog rate rewards C_star C_h t a z +
              (2 * incomingBacklog rate rewards C_star C_h t a z + 1 / 2) *
                momentOne rate rewards C_star C_h t a z +
              momentTwo rate rewards C_star C_h t a z + 16)) z := by
    rw [ae_all_iff]
    exact fun a => (hterms a).2
  filter_upwards [hmono, hsum', hall] with z hle hce heq
  rw [hce] at hle
  simp_rw [heq] at hle
  by_cases hz : z ∈ G rate rewards C_star C_h t
  · simp only [Set.indicator_of_mem hz] at hle ⊢
    exact hle.trans (moment_bound_on_G rate rewards C_star C_h control0 t z hz)
  · simpa only [Set.indicator_of_notMem hz, Finset.sum_const_zero] using hle

include control0 in
/-- Integrated OLD weighted cost at the original date, with the exact mass
of G. This is a one-date consequence, with no calendar telescope. -/
theorem sourceIntegral_weighted_cost :
    (∫ z, dOld rate rewards C_star C_h t z ∂μ) +
      (11 / 2 : ℝ) * (∫ z, costOld rate rewards C_star C_h t z ∂μ) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (μ).real (G rate rewards C_star C_h t) := by
  let g := G rate rewards C_star C_h t
  let C := CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)
  have hreg := old_readouts_regular rate rewards C_star C_h control0 t
  have hg : MeasurableSet g := (sourcePrefixFiltration control0).le' (t.val + 1) _
    (ReferenceFirstCollectionOldCalendarExponentialStep.measurableSet_G
      rate rewards C_star C_h control0 t)
  have hcInt : Integrable (g.indicator (fun _ : S => C)) μ :=
    (integrable_const C).indicator hg
  have hboundInt : Integrable (fun z => g.indicator (fun _ : S => C) z -
      (11 / 2 : ℝ) * costOld rate rewards C_star C_h t z) μ :=
    hcInt.sub (hreg.2.2.2.const_mul _)
  have hmask : g.indicator (fun z => C - (11 / 2 : ℝ) *
      oldBacklog rate rewards C_star C_h t.val z) =
      fun z => g.indicator (fun _ : S => C) z - (11 / 2 : ℝ) * costOld rate rewards C_star C_h t z := by
    funext z
    by_cases hz : z ∈ g <;> simp [costOld, g, Set.indicator, hz]
  have hle := integral_mono_ae (integrable_condExp (f := dOld rate rewards C_star C_h t))
    hboundInt (by
      rw [← hmask]
      exact conditional_weighted_drift rate rewards C_star C_h control0 t)
  rw [integral_condExp ((sourcePrefixFiltration control0).le' (t.val + 1)),
    integral_sub hcInt (hreg.2.2.2.const_mul _), integral_const_mul,
    integral_indicator_const C hg, smul_eq_mul] at hle
  dsimp only [C] at hle
  linarith only [hle]

private instance listSingleton {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] : MeasurableSingletonClass (List α) where
  measurableSet_singleton L := by
    have hinj : Function.Injective
        (ReferenceActiveHorizonMeasurability.listObservationCoordinates (α := α)) := by
      intro A B h
      apply List.ext_getElem (congrArg Prod.fst h)
      intro k hk hk'
      have he := congrFun (congrArg Prod.snd h) k
      simpa only [ReferenceActiveHorizonMeasurability.listObservationCoordinates,
        ReferenceActiveHorizonMeasurability.listObservationAt,
        List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk', Sum.inr.injEq] using he
    have hh := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
      (MeasurableSet.singleton (ReferenceActiveHorizonMeasurability.listObservationCoordinates L))
    convert hh using 1
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, hinj.eq_iff]

private theorem firstCallBoundary_measurable :
    Measurable (ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary rate rewards C_star C_h) := by
  let A := Fin p.T × (Fin p.T × ReferenceFirstCollectionSamplerCall.Theta p)
  have hv : Measurable (fun c : A => c.2.1.val) :=
    (measurable_of_countable (fun t : Fin p.T => t.val)).comp
      (measurable_fst.comp measurable_snd)
  have h : Measurable (fun z : S => Sum.elim (fun c : A => c.2.1.val)
      (fun _ : PUnit => p.T) (Equiv.optionEquivSumPUnit A
        (ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h z))) :=
    (hv.sumElim (measurable_const (a := p.T))).comp
    ((comap_measurable (Equiv.optionEquivSumPUnit A)).comp
      (ReferenceFirstCollectionSamplerCall.measurable_firstCollectionCall rate rewards C_star C_h))
  convert h using 1
  funext z
  unfold ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary
  cases ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h z <;> rfl

private theorem cell0_arrival_projection
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r).map
        (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate) =
      ((ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r).map
        (Sum.map (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)
          (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate))).map
        (Sum.elim id id) := by
  have hp := ReferenceCompleteNumericalBranchObservation.branch_readout_projections rate 0 r
  have hl := congrArg Prod.fst hp
  have hr := congrArg Prod.snd hp
  change ReferenceCompleteNumericalBranchObservation.leftProjection _ =
    (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).map
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates at hl
  change ReferenceCompleteNumericalBranchObservation.rightProjection _ =
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).map
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates at hr
  have he : (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r).map
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates =
      (ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r).map (Sum.elim id id) := by
    rw [ReferenceFirstCollectionCurrentRetainedGate.cell0, Option.map_or, ← hl, ← hr]
    cases h : ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r with
    | none => rfl
    | some value => cases value <;> rfl
  have he' := congrArg (Option.map
    (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)) he
  simp only [Option.map_map, Function.comp_def,
    ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical_numericalCoordinates] at he'
  rw [he']
  cases ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r with
  | none => rfl
  | some value => cases value <;> rfl

private theorem arrivalSlots_measurable (n : ℕ) (hn : n ≤ p.T) :
    Measurable (fun z : S =>
      (ReferenceFirstCollectionPrecallCalendarSupport.precallSlots rate rewards C_star C_h n z).map
        (Option.map (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate))) := by
  let cut := ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary rate rewards C_star C_h n
  let start := fun z : S => ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hcut : Measurable cut := measurable_const.min (firstCallBoundary_measurable rate rewards C_star C_h)
  have hstart : Measurable start :=
    ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart rate rewards C_star C_h
  have hproj := (ReferenceCompleteNumericalBranchObservation.measurable_branchArrivalProjection
    rate rewards C_star C_h).comp ((measurable_const (a := (0 : ℕ))).prodMk measurable_id)
  have hf : Measurable (fun v : ℕ × (ℕ × List
      (ReferenceCompleteNumericalBranchObservation.BranchArrivalEntry rate)) =>
      (v.2.2.take (v.1 - v.2.1)).map (fun e => e.2.map (Sum.elim id id))) :=
    measurable_of_countable _
  convert hf.comp (hcut.prodMk (hstart.prodMk hproj)) using 1
  funext z
  simp only [Function.comp_apply, ReferenceFirstCollectionPrecallCalendarSupport.precallSlots,
    ReferenceCompleteNumericalBranchObservation.branchArrivalProjection,
    ReferenceCompleteNumericalBranchObservation.branchCalendar, List.map_take, List.map_map,
    Function.comp_def]
  have htake : cut z - start z ≤
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    exact Nat.sub_le_sub_right
      ((ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary_le rate rewards C_star C_h n z).trans hn) _
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take]
    exact (Nat.min_eq_left htake).symm
  · intro k hk hk'
    have hkR : k < (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length := by
      have hkcut : k < cut z - start z := by simpa only [List.length_map, List.length_range] using hk
      omega
    simp only [List.getElem_map, List.getElem_range, List.getElem_take,
      List.getElem?_eq_getElem hkR, Option.bind_some]
    exact cell0_arrival_projection rate _

private theorem mapM_map {A B : Type*} (xs : List (Option A)) (f : A → B) :
    (xs.mapM id).map (List.map f) = (xs.map (Option.map f)).mapM id := by
  induction xs with
  | nil => rfl
  | cons c xs ih =>
    cases c with
    | none => simp [List.mapM_cons]
    | some c =>
      cases hx : xs.mapM id <;> simp [List.mapM_cons, ← ih, hx]

private theorem readout_fold (L : List (RecordedQueueRun.RoundInput p.K))
    (state : RecordedQueueRun.RunState p.K) :
    (L.map (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate)).foldl
        (ReferenceFirstCollectionCurrentQueueReadout.readoutUpdate rate) (stateReadout state) =
      stateReadout (RecordedQueueRun.execute q L state) := by
  induction L generalizing state with
  | nil => rfl
  | cons c L ih =>
    simp only [List.map_cons, List.foldl_cons, RecordedQueueRun.execute]
    exact ih (RecordedQueueRun.step q state c)

/-- The entire original optional prefix observation is Borel, including the
terminal/no-call and failed-first-invocation boundaries. -/
theorem precallReadout_measurable (n : ℕ) (hn : n ≤ p.T) :
    Measurable (ReferenceFirstCollectionPrecallCalendarSupport.precallReadout? rate rewards C_star C_h n) := by
  classical
  let cut := ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary rate rewards C_star C_h n
  have hcut : Measurable cut := measurable_const.min (firstCallBoundary_measurable rate rewards C_star C_h)
  have hlaunch : MeasurableSet {z : S | ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h (cut z) z} :=
    (ReferenceCorrectedLaunchMeasurability.measurableSet_generated_crossing rate rewards C_star C_h).inter
      (measurableSet_le (ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
        rate rewards C_star C_h) hcut)
  let slots := fun z : S =>
    (ReferenceFirstCollectionPrecallCalendarSupport.precallSlots rate rewards C_star C_h n z).map
      (Option.map (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate))
  have hslots : Measurable slots := arrivalSlots_measurable rate rewards C_star C_h n hn
  have hsome := LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ hslots
  have hcode : Measurable (fun z : S => if
      ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h (cut z) z then
        some (slots z) else (none : Option (List (Option (QueueArrivals p.K))))) :=
    Measurable.ite hlaunch hsome measurable_const
  have hf : Measurable (fun o : Option (List (Option (QueueArrivals p.K))) =>
      o.bind (fun slots => (slots.mapM id).map (fun arrivals => arrivals.foldl
        (ReferenceFirstCollectionCurrentQueueReadout.readoutUpdate rate)
        (stateReadout (RecordedQueueRun.initialState p.K))))) := measurable_of_countable _
  convert hf.comp hcode using 1
  funext z
  dsimp only [Function.comp_apply]
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h (cut z) z
  · simp only [hz, ite_true, Option.bind_some, slots,
      ReferenceFirstCollectionPrecallCalendarSupport.precallReadout?, precallCells?]
    rw [ite_eq_left hz, ← mapM_map]
    cases hL : (ReferenceFirstCollectionPrecallCalendarSupport.precallSlots rate rewards C_star C_h n z).mapM id with
    | none => rfl
    | some L => exact congrArg some (readout_fold rate L (RecordedQueueRun.initialState p.K)).symm
  · simp only [hz, ite_false, Option.bind_none,
      ReferenceFirstCollectionPrecallCalendarSupport.precallReadout?, precallCells?]
    rw [ite_eq_right hz]
    rfl

/-- Whole-carrier measurability and integrability of both literal scalar
readouts. The optional carrier is preserved by `precallReadout_measurable`. -/
theorem old_scalar_readouts_regular (n : ℕ) (hn : n ≤ p.T) :
    Measurable (oldPotential rate rewards C_star C_h n) ∧
    Integrable (oldPotential rate rewards C_star C_h n) μ ∧
    Measurable (oldBacklog rate rewards C_star C_h n) ∧
    Integrable (oldBacklog rate rewards C_star C_h n) μ := by
  have hread := precallReadout_measurable rate rewards C_star C_h n hn
  have hp : Measurable (oldPotential rate rewards C_star C_h n) := by
    have hf : Measurable (readoutPotential (p := p) rate) := measurable_of_countable _
    convert hf.comp hread using 1
    funext z
    dsimp only [Function.comp_apply]
    cases hL : precallCells? rate rewards C_star C_h n z with
    | none => simp only [oldPotential, ReferenceFirstCollectionPrecallCalendarSupport.precallReadout?,
        hL, Option.map_none, readoutPotential, thetaOfOptionalWeights, normalizedReadoutBacklog,
        Option.elim_none, zero_mul, Finset.sum_const_zero]
    | some L => simp only [oldPotential, ReferenceFirstCollectionPrecallCalendarSupport.precallReadout?,
        hL, Option.map_some, readoutPotential_state]
  have hb : Measurable (oldBacklog rate rewards C_star C_h n) := by
    have hf : Measurable (fun o : Option (QueueReadout p.K) =>
        ∑ a : Fin p.K, thetaOfOptionalWeights (o.map weightVectorOfReadout) a *
          normalizedReadoutBacklog rate o a) := measurable_of_countable _
    convert hf.comp hread using 1
    funext z
    dsimp only [Function.comp_apply]
    cases hL : precallCells? rate rewards C_star C_h n z with
    | none => simp only [oldBacklog, ReferenceFirstCollectionPrecallCalendarSupport.precallReadout?,
        hL, Option.map_none, thetaOfOptionalWeights, normalizedReadoutBacklog,
        Option.elim_none, zero_mul, Finset.sum_const_zero]
    | some L =>
      simp only [oldBacklog, ReferenceFirstCollectionPrecallCalendarSupport.precallReadout?, hL, Option.map_some]
      rfl
  have hiP : Integrable (oldPotential rate rewards C_star C_h n) μ := by
    apply integrable_of_bounded_measurable hp _ (by positivity : 0 ≤
      (p.K : ℝ) * (2 * (1 / (32 * rate.eta.val))) ^ 2)
    intro z
    have h := old_readout_bounds rate rewards C_star C_h n hn z
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2.1
  have hiB : Integrable (oldBacklog rate rewards C_star C_h n) μ := by
    apply integrable_of_bounded_measurable hb _ (by positivity [rate.eta.property] : 0 ≤
      (p.K : ℝ) * (2 * (1 / (32 * rate.eta.val))))
    intro z
    have h := (old_readout_bounds rate rewards C_star C_h n hn z).2.2
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
  exact ⟨hp, hiP, hb, hiB⟩

end Bandits.Support.ReferenceFirstCollectionOldConditionalWeightedEnergyDrift
