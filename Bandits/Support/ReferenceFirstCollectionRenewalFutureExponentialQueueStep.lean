/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalFutureQueueReadout
public import Bandits.Support.ReferenceFirstCollectionRenewalFutureExponentialIncrement

import Mathlib.Tactic

/-!
# One future-date exponential queue step on the renewal source

The localized readouts and future increment use the existing whole prefix,
actual future cell, original renewal source measure, and prior field.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open scoped Classical MeasureTheory

namespace Bandits.Support.ReferenceFirstCollectionRenewalFutureExponentialQueueStep

open ReferenceFirstCollectionRenewalFutureRetainedMoments
open ReferenceFirstCollectionRenewalFutureRecordingLaw
open ReferenceFirstCollectionRenewalFutureControlLaw
open ReferenceFirstCollectionRenewalFutureFirstReplacementView
open ReferenceFirstCollectionRenewalAuxiliaryLaw
open ReferenceFirstCollectionRenewalIncomingQueueMeasurability
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
local notation "β" => CanonicalRecordingRates.beta p rate.eta.val
local notation "Bcap" => 1 / (32 * rate.eta.val)

private theorem measurable_option_isSome {X α : Type*} (mX : MeasurableSpace X)
    [MeasurableSpace α] (f : X → Option α)
    (hf : @Measurable X (Option α) mX inferInstance f) :
    @Measurable X Bool mX inferInstance (fun x => (f x).isSome) := by
  let code := Equiv.optionEquivSumPUnit α
  have hcode : @Measurable X (Sum α PUnit) mX inferInstance
      (fun x => code (f x)) := (comap_measurable code).comp hf
  have htag : Measurable (Sum.elim (fun _ : α => true) (fun _ : PUnit => false)) :=
    measurable_const.sumElim measurable_const
  have heq : (fun x => (f x).isSome) =
      fun x => Sum.elim (fun _ : α => true) (fun _ : PUnit => false) (code (f x)) := by
    funext x
    cases f x <;> simp [code, Equiv.optionEquivSumPUnit_none,
      Equiv.optionEquivSumPUnit_some]
  rw [heq]
  exact htag.comp hcode

private theorem integrable_of_measurable_norm_le_const {X : Type*}
    [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (c : ℝ)
    (hb : ∀ x, ‖f x‖ ≤ c) : Integrable f μ :=
  (integrable_const c).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)

/-- The predictable support on which both actual optional readouts exist. -/
def futureQueueSupport (q : Fin p.T) (hfuture : t.val + 1 < q.val) : Set Z :=
  {z | (futureParameters rate rewards C_star C_h u t z q hfuture).isSome = true ∧
    (priorReadout rate rewards C_star C_h u t q z).isSome = true}

/-- The prior exponential readout, zero away from the common actual support. -/
def futureQueueExpBefore (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) : Z → ℝ :=
  (futureQueueSupport rate rewards C_star C_h u t q hfuture).indicator
    (fun z => Real.exp (β * ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogBefore
      rate rewards C_star C_h u t q hfuture a z))

/-- The successor exponential readout, localized to that same prior support. -/
def futureQueueExpAfter (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) : Z → ℝ :=
  (futureQueueSupport rate rewards C_star C_h u t q hfuture).indicator
    (fun z => Real.exp (β * ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogAfter
      rate rewards C_star C_h u t q hfuture a z))

/-- The support is measurable in the exact future prior field by measuring the
actual option tags; no discrete measurable structure is put on rate values. -/
theorem measurableSet_futureQueueSupport (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSet[_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q] (futureQueueSupport rate rewards C_star C_h u t q hfuture) := by
  let params := fun z : Z => futureParameters rate rewards C_star C_h u t z q hfuture
  let prior := fun z : Z => priorReadout rate rewards C_star C_h u t q z
  let gateBit := fun z : Z => (params z).isSome && (prior z).isSome
  have hparams := measurable_futureParameters rate rewards C_star C_h u t control0 q hfuture
  have hprior : Measurable[_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q] prior := by
    change Measurable[_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q]
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
        rate rewards C_star C_h u t q.val)
    exact ReferenceFirstCollectionRenewalFutureNumericalPrefix.measurable_futurePrefixReadout
      rate rewards C_star C_h u t control0 q.val (by omega)
  have hparamsSome : Measurable[_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q] (fun z : Z => (params z).isSome) :=
    measurable_option_isSome (_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q) _ hparams
  have hpriorSome : Measurable[_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q] (fun z : Z => (prior z).isSome) :=
    (measurable_of_countable (fun o : Option _ => o.isSome)).comp hprior
  have hgate : Measurable[_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q] gateBit := by
    exact (measurable_of_countable (fun b : Bool × Bool => b.1 && b.2)).comp
      (hparamsSome.prodMk hpriorSome)
  have hset : MeasurableSet[_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q] {z : Z | gateBit z = true} :=
    hgate (measurableSet_singleton true)
  have heq : futureQueueSupport rate rewards C_star C_h u t q hfuture =
      {z : Z | gateBit z = true} := by
    ext z
    simp [futureQueueSupport, gateBit, params, prior, Bool.and_eq_true]
  rw [heq]
  exact hset

theorem measurableSet_futureQueueSupport_ambient (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSet (futureQueueSupport rate rewards C_star C_h u t q hfuture) := by
  have hfield := futurePriorField_le rate rewards C_star C_h u t control0 q (by omega)
  exact hfield _ (measurableSet_futureQueueSupport rate rewards C_star C_h u t q hfuture control0)

/-- The actual enabled, prior-clear gate is contained in the common support. -/
theorem Gfuture_subset_futureQueueSupport (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) :
    ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t q hfuture ⊆
      futureQueueSupport rate rewards C_star C_h u t q hfuture := by
  intro z hz
  rcases hz with ⟨xi, hparams, hclear⟩
  constructor
  · rw [hparams]
    rfl
  · cases hread : priorReadout rate rewards C_star C_h u t q z with
    | none => simp [priorClear, hread] at hclear
    | some _ => simp

theorem measurable_futureQueueExpBefore (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) :
    Measurable[_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q] (futureQueueExpBefore rate rewards C_star C_h u t q hfuture a) := by
  have hbefore := ReferenceFirstCollectionRenewalFutureQueueReadout.measurable_futureBacklogBefore
    rate rewards C_star C_h u t control0 q hfuture a
  have hexp : Measurable[_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q] (fun z : Z => Real.exp (β *
      ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogBefore
        rate rewards C_star C_h u t q hfuture a z)) := by
    have hscaled : Measurable[_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q] (fun z : Z => β *
        ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogBefore
          rate rewards C_star C_h u t q hfuture a z) :=
      (measurable_const : Measurable[_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q] (fun _ : Z => β)).mul hbefore
    exact hscaled.exp
  change Measurable[_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q] ((futureQueueSupport rate rewards C_star C_h u t q hfuture).indicator _)
  exact hexp.indicator (measurableSet_futureQueueSupport rate rewards C_star C_h u t q hfuture control0)

theorem measurable_futureQueueExpBefore_ambient (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) :
    Measurable (futureQueueExpBefore rate rewards C_star C_h u t q hfuture a) := by
  have hbefore := ReferenceFirstCollectionRenewalFutureQueueReadout.measurable_futureBacklogBefore_ambient
    rate rewards C_star C_h u t control0 q hfuture a
  have hexp : Measurable (fun z : Z => Real.exp (β *
      ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogBefore
        rate rewards C_star C_h u t q hfuture a z)) := by
    have hscaled : Measurable (fun z : Z => β *
        ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogBefore
          rate rewards C_star C_h u t q hfuture a z) :=
      (measurable_const : Measurable (fun _ : Z => β)).mul hbefore
    exact hscaled.exp
  exact hexp.indicator (measurableSet_futureQueueSupport_ambient
    rate rewards C_star C_h u t q hfuture control0)

theorem measurable_futureQueueExpAfter (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) :
    Measurable (futureQueueExpAfter rate rewards C_star C_h u t q hfuture a) := by
  have hafter := ReferenceFirstCollectionRenewalFutureQueueReadout.measurable_futureBacklogAfter
    rate rewards C_star C_h u t control0 q hfuture a
  have hexp : Measurable (fun z : Z => Real.exp (β *
      ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogAfter
        rate rewards C_star C_h u t q hfuture a z)) := by
    have hscaled : Measurable (fun z : Z => β *
        ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogAfter
          rate rewards C_star C_h u t q hfuture a z) :=
      (measurable_const : Measurable (fun _ : Z => β)).mul hafter
    exact hscaled.exp
  exact hexp.indicator (measurableSet_futureQueueSupport_ambient
    rate rewards C_star C_h u t q hfuture control0)

theorem futureQueueExpBefore_nonneg_le (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z) :
    0 ≤ futureQueueExpBefore rate rewards C_star C_h u t q hfuture a z ∧
      futureQueueExpBefore rate rewards C_star C_h u t q hfuture a z ≤
        Real.exp (2 * β * Bcap) := by
  by_cases hz : z ∈ futureQueueSupport rate rewards C_star C_h u t q hfuture
  · have hb := ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogs_bounds
      rate rewards C_star C_h u t q hfuture a z
    have hβ := CanonicalRecordingRates.beta_pos p rate.eta.property
    have hbound : β * ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogBefore
        rate rewards C_star C_h u t q hfuture a z ≤ 2 * β * Bcap := by
      calc
        _ ≤ β * (2 * Bcap) := mul_le_mul_of_nonneg_left hb.1.2 hβ.le
        _ = 2 * β * Bcap := by ring
    rw [futureQueueExpBefore, Set.indicator_of_mem hz]
    exact ⟨Real.exp_nonneg _, Real.exp_le_exp_of_le hbound⟩
  · rw [futureQueueExpBefore, Set.indicator_of_notMem hz]
    exact ⟨by norm_num, le_of_lt (Real.exp_pos _)⟩

theorem futureQueueExpAfter_nonneg_le (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z) :
    0 ≤ futureQueueExpAfter rate rewards C_star C_h u t q hfuture a z ∧
      futureQueueExpAfter rate rewards C_star C_h u t q hfuture a z ≤
        Real.exp (2 * β * Bcap) := by
  by_cases hz : z ∈ futureQueueSupport rate rewards C_star C_h u t q hfuture
  · have hb := ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogs_bounds
      rate rewards C_star C_h u t q hfuture a z
    have hβ := CanonicalRecordingRates.beta_pos p rate.eta.property
    have hbound : β * ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogAfter
        rate rewards C_star C_h u t q hfuture a z ≤ 2 * β * Bcap := by
      calc
        _ ≤ β * (2 * Bcap) := mul_le_mul_of_nonneg_left hb.2.2 hβ.le
        _ = 2 * β * Bcap := by ring
    rw [futureQueueExpAfter, Set.indicator_of_mem hz]
    exact ⟨Real.exp_nonneg _, Real.exp_le_exp_of_le hbound⟩
  · rw [futureQueueExpAfter, Set.indicator_of_notMem hz]
    exact ⟨by norm_num, le_of_lt (Real.exp_pos _)⟩

theorem futureQueueExpBefore_zero_of_not_mem_support (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z)
    (hz : z ∉ futureQueueSupport rate rewards C_star C_h u t q hfuture) :
    futureQueueExpBefore rate rewards C_star C_h u t q hfuture a z = 0 := by
  simp [futureQueueExpBefore, hz]

theorem futureQueueExpAfter_zero_of_not_mem_support (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z)
    (hz : z ∉ futureQueueSupport rate rewards C_star C_h u t q hfuture) :
    futureQueueExpAfter rate rewards C_star C_h u t q hfuture a z = 0 := by
  simp [futureQueueExpAfter, hz]

theorem futureQueueExp_present_run (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z)
    (hz : z ∈ futureQueueSupport rate rewards C_star C_h u t q hfuture) :
    ∃ inputs : List (RecordedQueueRun.RoundInput p.K),
    ∃ c : RecordedQueueRun.RoundInput p.K,
      prefixInputs rate rewards C_star C_h u t q z = some inputs ∧
      futureCell rate rewards C_star C_h u t z q hfuture = some c ∧
      ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogBefore
        rate rewards C_star C_h u t q hfuture a z =
          StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q inputs) a ∧
      ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogAfter
        rate rewards C_star C_h u t q hfuture a z =
          StoppedQueueBound.normalizedBacklog Q
            (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c) a ∧
      futureQueueExpBefore rate rewards C_star C_h u t q hfuture a z =
        Real.exp (β * StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q inputs) a) ∧
      futureQueueExpAfter rate rewards C_star C_h u t q hfuture a z =
        Real.exp (β * StoppedQueueBound.normalizedBacklog Q
          (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c) a) := by
  obtain ⟨inputs, c, hinputs, hcell, _, _, hbefore, hafter⟩ :=
    ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogs_present
      rate rewards C_star C_h u t q hfuture a z hz
  refine ⟨inputs, c, hinputs, hcell, hbefore, hafter, ?_, ?_⟩
  · rw [futureQueueExpBefore, Set.indicator_of_mem hz, hbefore]
  · rw [futureQueueExpAfter, Set.indicator_of_mem hz, hafter]

private theorem futureParameters_eq_of_futureCell (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (z : Z) (c : RecordedQueueRun.RoundInput p.K)
    (hc : futureCell rate rewards C_star C_h u t z q hfuture = some c) :
    futureParameters rate rewards C_star C_h u t z q hfuture = some (c.enabled, c.rate) := by
  have hread := firstReplacement_future_readout rate rewards C_star C_h u t z q hfuture
  cases hv : futureRecordingView rate rewards C_star C_h u t z q hfuture with
  | none =>
      rw [hv] at hread
      simp only at hread
      have hbad : (some c : Option (RecordedQueueRun.RoundInput p.K)) = none :=
        hc.symm.trans hread.2
      cases hbad
  | some data =>
      rcases data with ⟨parameters, view, code⟩
      rw [hv] at hread
      obtain ⟨cell, snapshot, valid, hcell, hparameters, hrate, _, _, _⟩ := hread
      have hcellEq : cell = c := Option.some.inj (hcell.symm.trans hc)
      rw [← hcellEq]
      simpa [futureParameters, hv] using hparameters

private theorem exp_mul_max_zero_le (b y : ℝ) :
    Real.exp (b * max y 0) ≤ Real.exp (b * y) + 1 := by
  by_cases hy : y ≤ 0
  · rw [max_eq_right hy]
    have he := Real.exp_nonneg (b * y)
    simp only [mul_zero, Real.exp_zero]
    linarith
  · have hy' : 0 ≤ y := le_of_lt (lt_of_not_ge hy)
    rw [max_eq_left hy']
    linarith

/-- Whole-space one-step domination, including enabled zero-arrival service
and inactive disabled or prior-overflow preservation. -/
theorem futureQueueExpAfter_le_before_mul_expFutureIncrement_add_G (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z) :
    futureQueueExpAfter rate rewards C_star C_h u t q hfuture a z ≤
      futureQueueExpBefore rate rewards C_star C_h u t q hfuture a z *
        ReferenceFirstCollectionRenewalFutureExponentialIncrement.expFutureIncrement
          rate rewards C_star C_h u t q hfuture a z +
      Set.indicator
        (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
          rate rewards C_star C_h u t q hfuture)
        (fun _ : Z => (1 : ℝ)) z := by
  let gate := ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture
  by_cases hs : z ∈ futureQueueSupport rate rewards C_star C_h u t q hfuture
  · obtain ⟨inputs, c, hinputs, hcell, hQbefore, hQafter, hYbefore, hYafter⟩ :=
      futureQueueExp_present_run rate rewards C_star C_h u t q hfuture a z hs
    have hpriorReadout := ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout_eq_of_inputs
      rate rewards C_star C_h u t q z inputs hinputs
    by_cases hg : z ∈ gate
    · have hgateMem : z ∈ gate := hg
      rcases hg with ⟨xi, hparams, hclear⟩
      have hparamsCell := futureParameters_eq_of_futureCell
        rate rewards C_star C_h u t q hfuture z c hcell
      have hpair : (true, xi) = (c.enabled, c.rate) :=
        Option.some.inj (hparams.symm.trans hparamsCell)
      have henabled : c.enabled = true := by
        have h := congrArg Prod.fst hpair
        simpa using h.symm
      have hnoOverflow : (RecordedQueueRun.run Q inputs).overflow = false := by
        have hclearMatch := hclear
        unfold priorClear at hclearMatch
        rw [hpriorReadout] at hclearMatch
        cases ho : (RecordedQueueRun.run Q inputs).overflow with
        | false => rfl
        | true =>
            have hfalse : False := by
              simp [stateReadout, ho] at hclearMatch
            exact hfalse.elim
      have hreflect := ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogAfter_reflected_of_retained
        rate rewards C_star C_h u t q hfuture a z inputs c hinputs hcell hclear henabled
      have hraw := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_present_run
        rate rewards C_star C_h u t q hfuture a z inputs c hinputs hcell
      have hxrun := ReferenceFirstCollectionRenewalFutureExponentialIncrement.futureIncrement_present_run
        rate rewards C_star C_h u t q hfuture a z inputs c hinputs hcell henabled hnoOverflow
      have hx : ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture a z - 4 =
        ReferenceFirstCollectionRenewalFutureExponentialIncrement.futureIncrement
          rate rewards C_star C_h u t q hfuture a z := by
        rw [hraw]
        exact hxrun.symm
      have hZexp : ReferenceFirstCollectionRenewalFutureExponentialIncrement.expFutureIncrement
          rate rewards C_star C_h u t q hfuture a z =
        Real.exp (β * (ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture a z - 4)) := by
        by_cases hrawZero : RecordedRoundMoments.rawEstimate Q
            (RecordedQueueRun.run Q inputs) c a = 0
        · have hscalarZero := hraw.trans hrawZero
          have hxzero :=
            ReferenceFirstCollectionRenewalFutureExponentialIncrement.futureIncrement_eq_neg_four_of_enabled_zero
              rate rewards C_star C_h u t q hfuture a z hgateMem hscalarZero
          change Real.exp (β *
            ReferenceFirstCollectionRenewalFutureExponentialIncrement.futureIncrement
              rate rewards C_star C_h u t q hfuture a z) = _
          rw [hxzero, hscalarZero]
          congr 1
          ring
        · change Real.exp (β *
            ReferenceFirstCollectionRenewalFutureExponentialIncrement.futureIncrement
              rate rewards C_star C_h u t q hfuture a z) = _
          rw [← hx]
      let b := StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q inputs) a
      let x := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture a z - 4
      have hdecomp : Real.exp (β * (b + x)) = Real.exp (β * b) * Real.exp (β * x) := by
        rw [show β * (b + x) = β * b + β * x by ring]
        exact Real.exp_add _ _
      have hpoint := exp_mul_max_zero_le β (b + x)
      have hafterBacklog :
          ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogAfter
            rate rewards C_star C_h u t q hfuture a z = max (b + x) 0 := by
        by_cases hrawZero : RecordedRoundMoments.rawEstimate Q
            (RecordedQueueRun.run Q inputs) c a = 0
        · have hscalarZero := hraw.trans hrawZero
          have hdrain :=
            ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogAfter_eq_drain_of_retained_zero
              rate rewards C_star C_h u t q hfuture a z inputs c hinputs hcell hclear henabled
              hrawZero
          rw [hdrain, hQbefore]
          apply congrArg (fun y : ℝ => max y 0)
          dsimp [b, x]
          rw [hscalarZero]
          ring
        · rw [hreflect, hQbefore]
          apply congrArg (fun y : ℝ => max y 0)
          dsimp [b, x]
          ring
      calc
        futureQueueExpAfter rate rewards C_star C_h u t q hfuture a z =
            Real.exp (β * StoppedQueueBound.normalizedBacklog Q
              (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c) a) := hYafter
        _ = Real.exp (β * max (b + x) 0) := by
          have hstep : StoppedQueueBound.normalizedBacklog Q
              (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c) a = max (b + x) 0 := by
            calc
              _ = ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogAfter
                  rate rewards C_star C_h u t q hfuture a z := hQafter.symm
              _ = _ := hafterBacklog
          rw [hstep]
        _ ≤ Real.exp (β * (b + x)) + 1 := hpoint
        _ = futureQueueExpBefore rate rewards C_star C_h u t q hfuture a z *
              ReferenceFirstCollectionRenewalFutureExponentialIncrement.expFutureIncrement
                rate rewards C_star C_h u t q hfuture a z +
              Set.indicator gate (fun _ : Z => (1 : ℝ)) z := by
          rw [hYbefore, hZexp]
          simp only [Set.indicator_of_mem hgateMem]
          simpa [b, x] using congrArg (fun y : ℝ => y + 1) hdecomp
    · have hinactive : c.enabled = false ∨ (RecordedQueueRun.run Q inputs).overflow = true := by
        by_cases henabled : c.enabled = true
        · by_cases hoverflow : (RecordedQueueRun.run Q inputs).overflow = true
          · exact Or.inr hoverflow
          · have hnoOverflow : (RecordedQueueRun.run Q inputs).overflow = false :=
              Bool.eq_false_iff.mpr hoverflow
            have hpriorClear : priorClear rate rewards C_star C_h u t q z = true := by
              unfold priorClear
              rw [hpriorReadout]
              simp [stateReadout, hnoOverflow]
            have hp := futureParameters_eq_of_futureCell
              rate rewards C_star C_h u t q hfuture z c hcell
            have hparamsEnabled : futureParameters rate rewards C_star C_h u t z q hfuture =
                some (true, c.rate) := by
              simpa [henabled] using hp
            have hmem : z ∈ gate := ⟨c.rate, hparamsEnabled, hpriorClear⟩
            exact False.elim (hg hmem)
        · left
          exact Bool.eq_false_iff.mpr henabled
      have hinactiveQueue := ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogAfter_eq_before_of_inactive
        rate rewards C_star C_h u t q hfuture a z inputs c hinputs hcell hinactive
      have hBackEq : StoppedQueueBound.normalizedBacklog Q
          (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c) a =
        StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q inputs) a := by
        calc
          _ = ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogAfter
              rate rewards C_star C_h u t q hfuture a z := hQafter.symm
          _ = ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogBefore
              rate rewards C_star C_h u t q hfuture a z := hinactiveQueue
          _ = _ := hQbefore
      have hxzero := ReferenceFirstCollectionRenewalFutureExponentialIncrement.futureIncrement_eq_zero_of_not_mem_Gfuture
        rate rewards C_star C_h u t q hfuture a z hg
      have hZone : ReferenceFirstCollectionRenewalFutureExponentialIncrement.expFutureIncrement
          rate rewards C_star C_h u t q hfuture a z = 1 := by
        simp [ReferenceFirstCollectionRenewalFutureExponentialIncrement.expFutureIncrement, hxzero]
      rw [hYafter, hYbefore, hBackEq, hZone, Set.indicator_of_notMem hg]
      simp
  · have hnotGate : z ∉ gate := by
      intro hz
      exact hs (Gfuture_subset_futureQueueSupport rate rewards C_star C_h u t q hfuture hz)
    rw [futureQueueExpAfter_zero_of_not_mem_support rate rewards C_star C_h u t q hfuture a z hs,
      futureQueueExpBefore_zero_of_not_mem_support rate rewards C_star C_h u t q hfuture a z hs,
      Set.indicator_of_notMem hnotGate]
    simp

theorem integrable_futureQueueExpBefore (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) :
    Integrable (futureQueueExpBefore rate rewards C_star C_h u t q hfuture a) ν := by
  apply integrable_of_measurable_norm_le_const
    (futureQueueExpBefore rate rewards C_star C_h u t q hfuture a)
    (measurable_futureQueueExpBefore_ambient rate rewards C_star C_h u t q hfuture control0 a)
    (Real.exp (2 * β * Bcap))
  intro z
  have h := futureQueueExpBefore_nonneg_le rate rewards C_star C_h u t q hfuture a z
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2

theorem integrable_futureQueueExpAfter (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) :
    Integrable (futureQueueExpAfter rate rewards C_star C_h u t q hfuture a) ν := by
  apply integrable_of_measurable_norm_le_const
    (futureQueueExpAfter rate rewards C_star C_h u t q hfuture a)
    (measurable_futureQueueExpAfter rate rewards C_star C_h u t q hfuture control0 a)
    (Real.exp (2 * β * Bcap))
  intro z
  have h := futureQueueExpAfter_nonneg_le rate rewards C_star C_h u t q hfuture a z
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2

private theorem integrable_futureGateIndicator (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (Set.indicator
      (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t q hfuture)
      (fun _ : Z => (1 : ℝ))) ν := by
  have hfield := futurePriorField_le rate rewards C_star C_h u t control0 q (by omega)
  have hgate := ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurableSet_Gfuture
    rate rewards C_star C_h u t q hfuture control0
  simpa using (integrable_const (1 : ℝ)).indicator (hfield _ hgate)

theorem integrable_futureQueueExpBefore_mul_expFutureIncrement (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) :
    Integrable
      (fun z : Z => futureQueueExpBefore rate rewards C_star C_h u t q hfuture a z *
        ReferenceFirstCollectionRenewalFutureExponentialIncrement.expFutureIncrement
          rate rewards C_star C_h u t q hfuture a z) ν := by
  have hbeforeMeas := measurable_futureQueueExpBefore_ambient
    rate rewards C_star C_h u t q hfuture control0 a
  have hexpMeas := ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurable_expFutureIncrement
    rate rewards C_star C_h u t q hfuture control0 a
  have hmeas : Measurable (fun z : Z =>
      futureQueueExpBefore rate rewards C_star C_h u t q hfuture a z *
        ReferenceFirstCollectionRenewalFutureExponentialIncrement.expFutureIncrement
          rate rewards C_star C_h u t q hfuture a z) := hbeforeMeas.mul hexpMeas
  apply integrable_of_measurable_norm_le_const _ hmeas
    (Real.exp (2 * β * Bcap) * Real.exp 1)
  intro z
  have hy := futureQueueExpBefore_nonneg_le rate rewards C_star C_h u t q hfuture a z
  have hx := ReferenceFirstCollectionRenewalFutureExponentialIncrement.expFutureIncrement_bounds
    rate rewards C_star C_h u t q hfuture control0 a z
  have hprodNonneg : 0 ≤ futureQueueExpBefore rate rewards C_star C_h u t q hfuture a z *
      ReferenceFirstCollectionRenewalFutureExponentialIncrement.expFutureIncrement
        rate rewards C_star C_h u t q hfuture a z :=
    mul_nonneg hy.1 (le_trans (Real.exp_nonneg _) hx.1)
  have hprodBound : futureQueueExpBefore rate rewards C_star C_h u t q hfuture a z *
      ReferenceFirstCollectionRenewalFutureExponentialIncrement.expFutureIncrement
        rate rewards C_star C_h u t q hfuture a z ≤ Real.exp (2 * β * Bcap) * Real.exp 1 := by
    calc
      _ ≤ Real.exp (2 * β * Bcap) *
          ReferenceFirstCollectionRenewalFutureExponentialIncrement.expFutureIncrement
            rate rewards C_star C_h u t q hfuture a z :=
        mul_le_mul_of_nonneg_right hy.2 (le_trans (Real.exp_nonneg _) hx.1)
      _ ≤ Real.exp (2 * β * Bcap) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left hx.2 (Real.exp_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hprodNonneg]
  exact hprodBound

/-- Conditional one-step inequality on the exact original future prior field. -/
theorem condExp_futureQueueExpAfter_le_before_add_G (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) :
    ν[(futureQueueExpAfter rate rewards C_star C_h u t q hfuture a) | _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q] ≤ᵐ[ν]
      (fun z : Z => futureQueueExpBefore rate rewards C_star C_h u t q hfuture a z +
        Set.indicator
          (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
            rate rewards C_star C_h u t q hfuture)
          (fun _ : Z => (1 : ℝ)) z) := by
  let yBefore := futureQueueExpBefore rate rewards C_star C_h u t q hfuture a
  let yAfter := futureQueueExpAfter rate rewards C_star C_h u t q hfuture a
  let zExp := ReferenceFirstCollectionRenewalFutureExponentialIncrement.expFutureIncrement
    rate rewards C_star C_h u t q hfuture a
  let gate := ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture
  let gateIndicator := Set.indicator gate (fun _ : Z => (1 : ℝ))
  have hfield := futurePriorField_le rate rewards C_star C_h u t control0 q (by omega)
  have hYBeforeInt := integrable_futureQueueExpBefore rate rewards C_star C_h u t q hfuture control0 a
  have hYAfterInt := integrable_futureQueueExpAfter rate rewards C_star C_h u t q hfuture control0 a
  have hZExpInt := ReferenceFirstCollectionRenewalFutureExponentialIncrement.integrable_expFutureIncrement
    rate rewards C_star C_h u t q hfuture control0 a
  have hProductInt := integrable_futureQueueExpBefore_mul_expFutureIncrement
    rate rewards C_star C_h u t q hfuture control0 a
  have hGateInt := integrable_futureGateIndicator rate rewards C_star C_h u t q hfuture control0
  have hRhsInt : Integrable (fun z : Z => yBefore z * zExp z + gateIndicator z) ν := by
    exact hProductInt.add hGateInt
  have hpoint := futureQueueExpAfter_le_before_mul_expFutureIncrement_add_G
    rate rewards C_star C_h u t q hfuture a
  have hmono := condExp_mono (m := _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q) hYAfterInt hRhsInt
    (Filter.Eventually.of_forall fun z => hpoint z)
  have hsum := condExp_add hProductInt hGateInt
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q)
  have hYBeforeMeas := measurable_futureQueueExpBefore rate rewards C_star C_h u t q hfuture control0 a
  have hYBeforeStrong : StronglyMeasurable[_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q] yBefore := by
    exact hYBeforeMeas.stronglyMeasurable
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (m := _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q) hYBeforeStrong hProductInt hZExpInt
  have hgateField := ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurableSet_Gfuture
    rate rewards C_star C_h u t q hfuture control0
  have hgateCond := condExp_indicator (μ := ν) (integrable_const (1 : ℝ)) hgateField
  have hconst := condExp_const (μ := ν) (m := _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q)
    (m₀ := (inferInstance : MeasurableSpace Z)) hfield (1 : ℝ)
  have hgateId : ν[gateIndicator | _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q] =ᵐ[ν] gateIndicator := by
    calc
      ν[gateIndicator | _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q] =ᵐ[ν]
          gate.indicator (fun z : Z => ν[(fun _ : Z => (1 : ℝ)) | _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q] z) := hgateCond
      _ =ᵐ[ν] gateIndicator := by
        filter_upwards [] with z
        change gate.indicator
            (fun z : Z => ν[(fun _ : Z => (1 : ℝ)) |
              _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
                rate rewards C_star C_h u t control0 q] z) z =
          gate.indicator (fun _ : Z => (1 : ℝ)) z
        by_cases hz : z ∈ gate
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
          exact congrFun hconst z
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
  have hconditional :=
    ReferenceFirstCollectionRenewalFutureExponentialIncrement.condExp_expFutureIncrement_le_one
      rate rewards C_star C_h u t q hfuture control0 a
  have hsumFunction : (fun y : Z => yBefore y * zExp y + gateIndicator y) =
      (fun y : Z => yBefore y * zExp y) + gateIndicator := by
    funext y
    rfl
  have hsumFunctionCE :
      ν[(fun y : Z => yBefore y * zExp y + gateIndicator y) |
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
          rate rewards C_star C_h u t control0 q] =ᵐ[ν]
        ν[(fun y : Z => yBefore y * zExp y) + gateIndicator |
          _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
            rate rewards C_star C_h u t control0 q] := condExp_congr_ae
    (Filter.Eventually.of_forall fun y => congrFun hsumFunction y)
  have hproductFunction : (fun y : Z => yBefore y * zExp y) = yBefore * zExp := by
    funext y
    rfl
  have hproductFunctionCE :
      ν[(fun y : Z => yBefore y * zExp y) |
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
          rate rewards C_star C_h u t control0 q] =ᵐ[ν]
        ν[yBefore * zExp |
          _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
            rate rewards C_star C_h u t control0 q] := condExp_congr_ae
    (Filter.Eventually.of_forall fun y => congrFun hproductFunction y)
  filter_upwards [hmono, hsum, hpull, hsumFunctionCE, hproductFunctionCE,
      hgateId, hconditional] with z hmonoZ hsumZ hpullZ hsumFunctionZ
        hproductFunctionZ hgateZ hconditionalZ
  have hyNonneg := (futureQueueExpBefore_nonneg_le rate rewards C_star C_h u t q hfuture a z).1
  have hsumAt :
      ν[(fun y : Z => yBefore y * zExp y + gateIndicator y) |
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
          rate rewards C_star C_h u t control0 q] z =
        ν[(fun y : Z => yBefore y * zExp y) |
          _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
            rate rewards C_star C_h u t control0 q] z +
        ν[gateIndicator |
          _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
            rate rewards C_star C_h u t control0 q] z := by
    exact hsumFunctionZ.trans hsumZ
  have hpullAt :
      ν[(fun y : Z => yBefore y * zExp y) |
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
          rate rewards C_star C_h u t control0 q] z =
        yBefore z * ν[zExp |
          _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
            rate rewards C_star C_h u t control0 q] z := by
    exact hproductFunctionZ.trans hpullZ
  have hgateAt :
      ν[gateIndicator |
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
          rate rewards C_star C_h u t control0 q] z = gateIndicator z := by
    simpa [gateIndicator] using hgateZ
  calc
    ν[yAfter | _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q] z ≤ ν[(fun y : Z => yBefore y * zExp y + gateIndicator y) | _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q] z := hmonoZ
    _ = yBefore z * ν[zExp | _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q] z + gateIndicator z := by
      rw [hsumAt, hpullAt, hgateAt]
    _ ≤ yBefore z + gateIndicator z := by
      have hmul := mul_le_mul_of_nonneg_left hconditionalZ hyNonneg
      simpa using add_le_add_right hmul (gateIndicator z)

/-- Every future-prior-field measurable set obeys the unnormalized restricted
integral inequality, with the exact intersection of the set and the gate. -/
theorem setIntegral_futureQueueExpAfter_le (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) (B : Set Z)
    (hB : MeasurableSet[_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q] B) :
    ∫ z in B, futureQueueExpAfter rate rewards C_star C_h u t q hfuture a z ∂ν ≤
      ∫ z in B, futureQueueExpBefore rate rewards C_star C_h u t q hfuture a z ∂ν +
        (renewalSourceLaw rate rewards C_star C_h u t).real (B ∩ ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
          rate rewards C_star C_h u t q hfuture) := by
  let yBefore := futureQueueExpBefore rate rewards C_star C_h u t q hfuture a
  let yAfter := futureQueueExpAfter rate rewards C_star C_h u t q hfuture a
  let gate := ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture
  let gateIndicator := Set.indicator gate (fun _ : Z => (1 : ℝ))
  have hfield := futurePriorField_le rate rewards C_star C_h u t control0 q (by omega)
  have hYBeforeInt := integrable_futureQueueExpBefore rate rewards C_star C_h u t q hfuture control0 a
  have hYAfterInt := integrable_futureQueueExpAfter rate rewards C_star C_h u t q hfuture control0 a
  have hGateInt := integrable_futureGateIndicator rate rewards C_star C_h u t q hfuture control0
  have hRhsInt : Integrable (fun z : Z => yBefore z + gateIndicator z) ν := by
    exact hYBeforeInt.add hGateInt
  have hconditional := condExp_futureQueueExpAfter_le_before_add_G
    rate rewards C_star C_h u t q hfuture control0 a
  have hCondInt : Integrable
      (ν[yAfter |
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
          rate rewards C_star C_h u t control0 q]) ν :=
    integrable_condExp
  have hCondOn : IntegrableOn
      (ν[yAfter |
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
          rate rewards C_star C_h u t control0 q]) B ν := hCondInt.integrableOn
  have hRhsOn : IntegrableOn (fun z : Z => yBefore z + gateIndicator z) B ν :=
    hRhsInt.integrableOn
  have hmono : ∫ z in B,
        ν[yAfter |
          _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
            rate rewards C_star C_h u t control0 q] z ∂ν ≤
      ∫ z in B, (yBefore z + gateIndicator z) ∂ν :=
    setIntegral_mono_ae (s := B) hCondOn hRhsOn hconditional
  have hleft := setIntegral_condExp hfield hYAfterInt hB
  have hBambient : MeasurableSet B := hfield _ hB
  have hGateField := ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurableSet_Gfuture
    rate rewards C_star C_h u t q hfuture control0
  have hGateAmbient : MeasurableSet gate := hfield _ hGateField
  have hright : ∫ z in B, (yBefore z + gateIndicator z) ∂ν =
      ∫ z in B, yBefore z ∂ν +
        (renewalSourceLaw rate rewards C_star C_h u t).real (B ∩ gate) := by
    rw [integral_add hYBeforeInt.integrableOn hGateInt.integrableOn]
    have hgateIntegral : ∫ z in B, gateIndicator z ∂ν =
        (renewalSourceLaw rate rewards C_star C_h u t).real (B ∩ gate) := by
      rw [show gateIndicator = gate.indicator (fun _ : Z => (1 : ℝ)) by rfl,
        setIntegral_indicator hGateAmbient]
      simp
    rw [hgateIntegral]
  calc
    ∫ z in B, yAfter z ∂ν = ∫ z in B, ν[yAfter | _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField rate rewards C_star C_h u t control0 q] z ∂ν := hleft.symm
    _ ≤ ∫ z in B, (yBefore z + gateIndicator z) ∂ν := hmono
    _ = ∫ z in B, yBefore z ∂ν +
        (renewalSourceLaw rate rewards C_star C_h u t).real (B ∩ gate) := hright

theorem integral_futureQueueExpAfter_le (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) :
    ∫ z, futureQueueExpAfter rate rewards C_star C_h u t q hfuture a z ∂ν ≤
      ∫ z, futureQueueExpBefore rate rewards C_star C_h u t q hfuture a z ∂ν +
        (renewalSourceLaw rate rewards C_star C_h u t).real (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
          rate rewards C_star C_h u t q hfuture) := by
  have h := setIntegral_futureQueueExpAfter_le rate rewards C_star C_h u t q hfuture
    control0 a Set.univ MeasurableSet.univ
  simpa using h

end Bandits.Support.ReferenceFirstCollectionRenewalFutureExponentialQueueStep

end
