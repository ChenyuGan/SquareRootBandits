/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalEndpointTelescope
public import Bandits.Support.ReferenceFirstCollectionRenewalFutureExponentialQueueStep

import Mathlib.Tactic

/-!
# Actual-source renewal endpoint exponential moment

This module integrates the original inclusive endpoint telescope on the same
finite, unnormalized renewal source. The inherited entry energy is retained.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open scoped Classical MeasureTheory

namespace Bandits.Support.ReferenceFirstCollectionRenewalEndpointExponentialMoment

open ReferenceFirstCollectionRenewalEndpointTelescope
open ReferenceFirstCollectionRenewalFutureExponentialQueueStep
open ReferenceFirstCollectionRenewalFutureSliceEndpoint
open ReferenceFirstCollectionRenewalFutureNumericalPrefix
open ReferenceFirstCollectionRenewalFutureQueueReadout
open ReferenceFirstCollectionRenewalFutureFirstReplacementView
open ReferenceFirstCollectionRenewalFutureExponentialIncrement
open ReferenceFirstCollectionRenewalNextPhysicalPrefix
open ReferenceFirstCollectionRenewalAuxiliaryLaw
open ReferenceInspectedPastRoundObservations
open ReferenceCoordinatorRecorderCallTrace
open ReferenceActiveHorizonMeasurability

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

local notation "Z" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.Source
  rate rewards C_star C_h u t
local notation "ν" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
  rate rewards C_star C_h u t
local notation "b" => t.val + 1
local notation "Q" => _root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "β" => CanonicalRecordingRates.beta p rate.eta.val

/-- The actual finite calendar dates strictly after the inherited entry
boundary. -/
def FutureDate := {q : Fin p.T // t.val + 1 < q.val}

noncomputable local instance futureDateFintype : Fintype (FutureDate (p := p) t) := by
  classical
  letI : Finite (FutureDate (p := p) t) := by
    exact Finite.of_injective
      (fun q : FutureDate (p := p) t => q.1)
      (by intro x y h; exact Subtype.ext h)
  exact Fintype.ofFinite _

noncomputable local instance endpointSupportDateFintype (z : Z) :
    Fintype (ReferenceFirstCollectionRenewalEndpointTelescope.EndpointSupportDate
      rate rewards C_star C_h u t z) := by
  classical
  letI : Finite (ReferenceFirstCollectionRenewalEndpointTelescope.EndpointSupportDate
      rate rewards C_star C_h u t z) := by
    exact Finite.of_injective
      (fun d => d.1)
      (by intro x y h; exact Subtype.ext h)
  exact Fintype.ofFinite _

/-- The inclusive endpoint is the actual first-slice endpoint of the source
run, including its selected detecting cutoff update. -/
def endpointIndex (z : Z) : ℕ :=
  ReferenceFirstCollectionRenewalEndpointTelescope.endpointEnd
    rate rewards C_star C_h u t z

/-- The actual inherited entry date absorbs the immediate successor date. -/
def entryIndex (z : Z) : ℕ := min (b + 1) (endpointIndex rate rewards C_star C_h u t z)

/-- The full actual exponential at the inclusive endpoint of the original
whole-prefix numerical run. -/
def endpointEnergy (a : Fin p.K) (z : Z) : ℝ :=
  ReferenceFirstCollectionRenewalEndpointTelescope.actualBacklogExpAt
    rate rewards C_star C_h u t z a
    ⟨endpointIndex rate rewards C_star C_h u t z,
      ⟨by
        have hb := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds
          rate rewards C_star C_h u t z
        change ReferenceFirstCollectionRenewalFutureSliceEndpoint.beginning t ≤
          ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex
            rate rewards C_star C_h u t z
        exact hb.1.trans hb.2.1,
        le_rfl⟩⟩

/-- The entry exponential is read at the actual whole-prefix date
`min (b + 1) k`; it is inherited from the original queue run. -/
def entryEnergy (a : Fin p.K) (z : Z) : ℝ :=
  ReferenceFirstCollectionRenewalEndpointTelescope.actualBacklogExpAt
    rate rewards C_star C_h u t z a
    ⟨entryIndex rate rewards C_star C_h u t z,
      ⟨by
        have hb := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds
          rate rewards C_star C_h u t z
        change ReferenceFirstCollectionRenewalFutureSliceEndpoint.beginning t ≤
          min (b + 1) (ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex
            rate rewards C_star C_h u t z)
        exact Nat.le_min.mpr ⟨by
          change t.val + 1 ≤ (t.val + 1) + 1
          omega,
          hb.1.trans hb.2.1⟩,
        min_le_right _ _⟩⟩

/-- A total finite index for the action after `t`, clamped only to make the
measurable readout total when `t` is the final action date. -/
def immediateObservationIndex : Fin p.T :=
  ⟨min (t.val + 1) (p.T - 1), by
    have hT := p.one_le_T
    omega⟩

/-- The original next record's selected dispatcher tag, read through the
accepted measurable whole-round code. It is false when no action follows the
renewal call. -/
def immediateSelected (z : Z) : Bool :=
  decide (t.val + 1 < p.T) &&
    (((ReferenceInspectedPastRoundObservations.pastRoundObservations
      rate rewards C_star C_h p.T le_rfl z.val
      (immediateObservationIndex (p := p) t)).elim false fun code =>
        (ReferenceCoordinatorRecorderCallTrace.cell code).isSome))

private theorem measurable_option_isSome {X α : Type*} [MeasurableSpace X]
    [MeasurableSpace α] (f : X → Option α) (hf : Measurable f) :
    Measurable (fun x => (f x).isSome) := by
  let code := Equiv.optionEquivSumPUnit α
  have hcode : Measurable (fun x => code (f x)) := (comap_measurable code).comp hf
  have htag : Measurable (Sum.elim (fun _ : α => true) (fun _ : PUnit => false)) :=
    measurable_const.sumElim measurable_const
  have heq : (fun x => (f x).isSome) =
      fun x => Sum.elim (fun _ : α => true) (fun _ : PUnit => false) (code (f x)) := by
    funext x
    cases f x <;> simp [code, Equiv.optionEquivSumPUnit_none,
      Equiv.optionEquivSumPUnit_some]
  rw [heq]
  exact htag.comp hcode

private theorem measurable_option_elim {X A B : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [MeasurableSpace B] (f : A → B) (hf : Measurable f)
    (defaultValue : B) : Measurable (fun o : Option A => o.elim defaultValue f) := by
  have hsum : Measurable (fun o : Option A => Equiv.optionEquivSumPUnit A o) :=
    comap_measurable _
  convert (hf.sumElim measurable_const).comp hsum using 1
  funext o
  cases o <;> rfl

private theorem measurable_selectedCode :
    Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) =>
        (ReferenceCoordinatorRecorderCallTrace.cell code).isSome) := by
  exact measurable_option_isSome _
    (ReferenceCoordinatorRecorderCallTrace.measurable_cell (p := p) (rate := rate))

/-- The actual first following selected dispatcher event is ambient Borel. -/
theorem measurable_immediateSelected : Measurable (immediateSelected rate rewards C_star C_h u t) := by
  have hobs : Measurable (fun z : Z =>
      ReferenceInspectedPastRoundObservations.pastRoundObservations
        rate rewards C_star C_h p.T le_rfl z.val
        (immediateObservationIndex (p := p) t)) :=
    (((measurable_pi_iff.mp
      (ReferenceInspectedPastRoundObservations.measurable_pastRoundObservations
        rate rewards C_star C_h p.T le_rfl))
        (immediateObservationIndex (p := p) t)).comp measurable_subtype_coe)
  have htag : Measurable (fun z : Z =>
      ((ReferenceInspectedPastRoundObservations.pastRoundObservations
        rate rewards C_star C_h p.T le_rfl z.val
        (immediateObservationIndex (p := p) t)).elim false fun code =>
          (ReferenceCoordinatorRecorderCallTrace.cell code).isSome)) :=
    (measurable_option_elim (X := Z)
      (A := ReferenceActiveHorizonMeasurability.RoundRecordCode
        (p := p) (rate := rate)) (B := Bool)
      (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
        (p := p) (rate := rate) =>
          (ReferenceCoordinatorRecorderCallTrace.cell code).isSome)
      (measurable_selectedCode (p := p) rate) false).comp hobs
  have hand : Measurable (fun z : Z =>
      decide (t.val + 1 < p.T) &&
        ((ReferenceInspectedPastRoundObservations.pastRoundObservations
          rate rewards C_star C_h p.T le_rfl z.val
          (immediateObservationIndex (p := p) t)).elim false fun code =>
            (ReferenceCoordinatorRecorderCallTrace.cell code).isSome)) :=
    (measurable_of_countable (fun v : Bool × Bool => v.1 && v.2)).comp
      (measurable_const.prodMk htag)
  change Measurable (fun z : Z => decide (t.val + 1 < p.T) &&
    ((ReferenceInspectedPastRoundObservations.pastRoundObservations
      rate rewards C_star C_h p.T le_rfl z.val
      (immediateObservationIndex (p := p) t)).elim false fun code =>
        (ReferenceCoordinatorRecorderCallTrace.cell code).isSome))
  exact hand

/-- On the original source, the common support used by the one-date
exponential terms is exactly the actual strict-prefix support of the
inclusive endpoint telescope. -/
theorem futureQueueSupport_iff_before_endpoint (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (z : Z) :
    z ∈ ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueSupport
      rate rewards C_star C_h u t q hfuture ↔
      q.val < endpointIndex rate rewards C_star C_h u t z := by
  change ReferenceFirstCollectionRenewalFutureSliceEndpoint.supportTest
      rate rewards C_star C_h u t q hfuture z ↔
    q.val < ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex
      rate rewards C_star C_h u t z
  exact ReferenceFirstCollectionRenewalFutureSliceEndpoint.supportTest_iff_before_endpoint
    rate rewards C_star C_h u t z q hfuture

/-- On an actual supported first-slice date, the endpoint's full original
prefix increment is the difference of the two exponential readouts localized
to the same actual future support. -/
theorem endpointSupportIncrement_eq_futureQueueExpDiff (a : Fin p.K) (z : Z)
    (d : ReferenceFirstCollectionRenewalEndpointTelescope.EndpointSupportDate
      rate rewards C_star C_h u t z) :
    ReferenceFirstCollectionRenewalEndpointTelescope.endpointSupportIncrement
        rate rewards C_star C_h u t z a d =
      ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueExpAfter
          rate rewards C_star C_h u t d.1 (Classical.choose d.2) a z -
        ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueExpBefore
          rate rewards C_star C_h u t d.1 (Classical.choose d.2) a z := by
  let hfuture := Classical.choose d.2
  let hsupport := Classical.choose_spec d.2
  have hmem : z ∈ ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueSupport
      rate rewards C_star C_h u t d.1 hfuture := by
    change ReferenceFirstCollectionRenewalFutureSliceEndpoint.supportTest
      rate rewards C_star C_h u t d.1 hfuture z
    exact hsupport
  obtain ⟨inputs, cell, hinputs, hcellView, hcell, hreadBefore, hreadAfter,
      hreadAfterStep, hinc, hreadEq, hrunEq⟩ :=
    ReferenceFirstCollectionRenewalEndpointTelescope.endpointSupportIncrement_actual_append
      rate rewards C_star C_h u t a z d
  obtain ⟨inputs', cell', hinputs', hcell', hbefore, hafter,
      hexpBefore, hexpAfter⟩ :=
    ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueExp_present_run
      rate rewards C_star C_h u t d.1 hfuture a z hmem
  have hinputsEq : inputs = inputs' := by
    apply Option.some.inj
    rw [← hinputs]
    simpa [ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells,
      ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs] using hinputs'
  have hcellEq : cell = cell' := Option.some.inj (hcellView.symm.trans hcell')
  subst inputs'
  subst cell'
  rw [hexpAfter, hexpBefore]
  rw [hinc, hrunEq]
  simp only [StoppedQueueBound.normalizedBacklog,
    ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout]
  have hnNat : (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters
      rate).n ≠ 0 := by
    change rate.n ≠ 0
    exact (ActiveFollowerDownAcceptance.rate_n_pos p rate).ne'
  have hn : (((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters
      rate).n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hnNat
  field_simp [hn]

/-- The inherited entry date is one of the two actual dates `b` and `b+1`;
the endpoint bounds ensure this even for empty or terminal slices. -/
theorem entryIndex_eq_beginning_or_successor (z : Z) :
    entryIndex rate rewards C_star C_h u t z = t.val + 1 ∨
    entryIndex rate rewards C_star C_h u t z = t.val + 2 := by
  have hb := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds
    rate rewards C_star C_h u t z
  have hbk := hb.1.trans hb.2.1
  change t.val + 1 ≤ ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex
    rate rewards C_star C_h u t z at hbk
  change min (t.val + 2)
      (ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex
        rate rewards C_star C_h u t z) = t.val + 1 ∨
    min (t.val + 2)
      (ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex
        rate rewards C_star C_h u t z) = t.val + 2
  by_cases hk : ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex
      rate rewards C_star C_h u t z ≤ t.val + 1
  · have heq := Nat.le_antisymm hk hbk
    rw [heq]
    simp
  · have hk' : t.val + 2 ≤
      ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex
        rate rewards C_star C_h u t z := by omega
    rw [Nat.min_eq_left hk']
    simp

/-- Rewriting the actual endpoint identity with the inherited entry energy
keeps the complete finite support sum and its source witnesses. -/
theorem endpointEnergy_eq_entryEnergy_add_supportSum (a : Fin p.K) (z : Z) :
    endpointEnergy rate rewards C_star C_h u t a z =
      entryEnergy rate rewards C_star C_h u t a z +
        ∑ d : ReferenceFirstCollectionRenewalEndpointTelescope.EndpointSupportDate
          rate rewards C_star C_h u t z,
          ReferenceFirstCollectionRenewalEndpointTelescope.endpointSupportIncrement
            rate rewards C_star C_h u t z a d := by
  simpa [endpointEnergy, entryEnergy, endpointIndex, entryIndex,
    ReferenceFirstCollectionRenewalEndpointTelescope.endpointBegin,
    ReferenceFirstCollectionRenewalEndpointTelescope.endpointEnd,
    ReferenceFirstCollectionRenewalEndpointTelescope.endpointTelescopeStart,
    ReferenceFirstCollectionRenewalFutureSliceEndpoint.beginning] using
    (ReferenceFirstCollectionRenewalEndpointTelescope.actual_endpoint_exp_telescope
      rate rewards C_star C_h u t a z)

/-- Reindex every actual supported whole-prefix increment onto the fixed
finite calendar dates `q` with `b < q.val`. Dates outside the same actual
support contribute the two masked zeros. -/
theorem endpointSupportSum_eq_futureQueueExpDiffSum (a : Fin p.K) (z : Z) :
    (∑ d : ReferenceFirstCollectionRenewalEndpointTelescope.EndpointSupportDate
        rate rewards C_star C_h u t z,
      ReferenceFirstCollectionRenewalEndpointTelescope.endpointSupportIncrement
        rate rewards C_star C_h u t z a d) =
      ∑ q : (FutureDate (p := p) t), (
        ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueExpAfter
            rate rewards C_star C_h u t q.1 q.2 a z -
          ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueExpBefore
            rate rewards C_star C_h u t q.1 q.2 a z) := by
  classical
  let supports := fun q : FutureDate (p := p) t =>
    z ∈ ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueSupport
      rate rewards C_star C_h u t q.1 q.2
  let increment := fun q : FutureDate (p := p) t =>
    ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueExpAfter
        rate rewards C_star C_h u t q.1 q.2 a z -
      ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueExpBefore
        rate rewards C_star C_h u t q.1 q.2 a z
  have hzero (q : FutureDate (p := p) t) (hq : ¬ supports q) : increment q = 0 := by
    have hnot : z ∉ ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueSupport
        rate rewards C_star C_h u t q.1 q.2 := hq
    simp [increment,
      ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueExpAfter_zero_of_not_mem_support
        rate rewards C_star C_h u t q.1 q.2 a z hnot,
      ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueExpBefore_zero_of_not_mem_support
        rate rewards C_star C_h u t q.1 q.2 a z hnot]
  have hsumFilter :
      (∑ q : FutureDate (p := p) t, increment q) =
        ∑ q ∈ Finset.univ.filter supports, increment q := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hs : supports q
    · rw [ite_eq_left hs]
    · rw [ite_eq_right hs, hzero q hs]
  have hbij :
      (∑ q ∈ Finset.univ.filter supports, increment q) =
        ∑ d : ReferenceFirstCollectionRenewalEndpointTelescope.EndpointSupportDate
          rate rewards C_star C_h u t z,
          ReferenceFirstCollectionRenewalEndpointTelescope.endpointSupportIncrement
            rate rewards C_star C_h u t z a d := by
    apply Finset.sum_bij (s := Finset.univ.filter supports) (t := Finset.univ)
      (fun q hq =>
        ⟨q.1, ⟨q.2, by
          have hs : supports q := (Finset.mem_filter.mp hq).2
          change z ∈ ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueSupport
            rate rewards C_star C_h u t q.1 q.2 at hs
          change ReferenceFirstCollectionRenewalFutureSliceEndpoint.supportTest
            rate rewards C_star C_h u t q.1 q.2 z
          exact hs⟩⟩)
    · intro q hq
      exact Finset.mem_univ _
    · intro q hq q' hq' heq
      have hFin : q.1 = q'.1 :=
        congrArg (fun d : ReferenceFirstCollectionRenewalEndpointTelescope.EndpointSupportDate
          rate rewards C_star C_h u t z => d.1) heq
      apply Subtype.ext
      exact hFin
    · intro d hd
      rcases d with ⟨q, ⟨hfuture, hsupport⟩⟩
      let q' : FutureDate (p := p) t := ⟨q, hfuture⟩
      have hmem : supports q' := by
        change z ∈ ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueSupport
          rate rewards C_star C_h u t q hfuture
        change ReferenceFirstCollectionRenewalFutureSliceEndpoint.supportTest
          rate rewards C_star C_h u t q hfuture z at hsupport
        exact hsupport
      refine ⟨q', Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · simpa [supports] using hmem
      · apply Subtype.ext
        rfl
    · intro q hq
      have hs : supports q := (Finset.mem_filter.mp hq).2
      let d : ReferenceFirstCollectionRenewalEndpointTelescope.EndpointSupportDate
          rate rewards C_star C_h u t z :=
        ⟨q.1, ⟨q.2, by
          change z ∈ ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueSupport
            rate rewards C_star C_h u t q.1 q.2 at hs
          exact hs⟩⟩
      simpa [increment, d] using
        (endpointSupportIncrement_eq_futureQueueExpDiff rate rewards C_star C_h u t a z d).symm
  rw [hsumFilter, hbij]

/-- The full inclusive endpoint is the inherited entry energy plus the sum
over the fixed finite type of actual future dates, with each masked increment
kept on its original one-date support. -/
theorem endpointEnergy_eq_entryEnergy_add_futureSum (a : Fin p.K) (z : Z) :
    endpointEnergy rate rewards C_star C_h u t a z =
      entryEnergy rate rewards C_star C_h u t a z +
        ∑ q : (FutureDate (p := p) t), (
          ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueExpAfter
              rate rewards C_star C_h u t q.1 q.2 a z -
            ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueExpBefore
              rate rewards C_star C_h u t q.1 q.2 a z) := by
  rw [endpointEnergy_eq_entryEnergy_add_supportSum]
  rw [endpointSupportSum_eq_futureQueueExpDiffSum]

/-- The finite sum of actual masked increments is integrable under the same
finite unnormalized renewal source. -/
theorem integrable_futureQueueExpDiffSum (a : Fin p.K)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (fun z : Z =>
      ∑ q : FutureDate (p := p) t, (
        ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueExpAfter
            rate rewards C_star C_h u t q.1 q.2 a z -
          ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueExpBefore
            rate rewards C_star C_h u t q.1 q.2 a z)) ν := by
  classical
  apply integrable_finsetSum Finset.univ
  intro q hq
  exact
    (ReferenceFirstCollectionRenewalFutureExponentialQueueStep.integrable_futureQueueExpAfter
      rate rewards C_star C_h u t q.1 q.2 control0 a).sub
    (ReferenceFirstCollectionRenewalFutureExponentialQueueStep.integrable_futureQueueExpBefore
      rate rewards C_star C_h u t q.1 q.2 control0 a)

/-- The integrated fixed-date increment sum is bounded by the sharp sum of
the original unnormalized future-gate masses. -/
theorem integral_futureQueueExpDiffSum_le (a : Fin p.K)
    (control0 : ContinuousLearningRows.TimeControl p) :
    ∫ z, (∑ q : FutureDate (p := p) t, (
      ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueExpAfter
          rate rewards C_star C_h u t q.1 q.2 a z -
        ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueExpBefore
          rate rewards C_star C_h u t q.1 q.2 a z)) ∂ν ≤
      ∑ q : FutureDate (p := p) t,
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t).real
          (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
          rate rewards C_star C_h u t q.1 q.2) := by
  classical
  rw [integral_finsetSum Finset.univ (fun q hq =>
    (ReferenceFirstCollectionRenewalFutureExponentialQueueStep.integrable_futureQueueExpAfter
      rate rewards C_star C_h u t q.1 q.2 control0 a).sub
    (ReferenceFirstCollectionRenewalFutureExponentialQueueStep.integrable_futureQueueExpBefore
      rate rewards C_star C_h u t q.1 q.2 control0 a))]
  apply Finset.sum_le_sum
  intro q hq
  rw [integral_sub
    (ReferenceFirstCollectionRenewalFutureExponentialQueueStep.integrable_futureQueueExpAfter
      rate rewards C_star C_h u t q.1 q.2 control0 a)
    (ReferenceFirstCollectionRenewalFutureExponentialQueueStep.integrable_futureQueueExpBefore
      rate rewards C_star C_h u t q.1 q.2 control0 a)]
  have h := ReferenceFirstCollectionRenewalFutureExponentialQueueStep.integral_futureQueueExpAfter_le
    rate rewards C_star C_h u t q.1 q.2 control0 a
  linarith

private theorem next_source_lookup (z : Z) (hq : b < p.T) :
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
      rate rewards C_star C_h u t z)[b -
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
          rate rewards C_star C_h u t z]? =
      some (nextRecord rate rewards C_star C_h u t z hq) := by
  have hs := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart_le_call
    rate rewards C_star C_h u t z
  have heq := ReferenceFirstCollectionRenewalIncomingQueuePrefix.start_eq_physicalStart
    rate rewards C_star C_h u t z
  have hi : b - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
      rate rewards C_star C_h u t z =
      t.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z + 1 := by
    change t.val + 1 - ReferenceCompletePhysicalHistory.physicalStart
      rate z.val rewards C_star C_h = _
    rw [← heq]
    change ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
      rate rewards C_star C_h u t z ≤ t.val at hs
    omega
  rw [hi]
  exact nextRecord_lookup rate rewards C_star C_h u t z hq

private theorem calendarCells_immediate_append (z : Z) (hq : b < p.T) :
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
        rate rewards C_star C_h u t (b + 1) z =
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
        rate rewards C_star C_h u t b z ++
      [ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate
        (nextRecord rate rewards C_star C_h u t z hq)] := by
  have hs := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart_le_call
    rate rewards C_star C_h u t z
  have hi : b + 1 - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
      rate rewards C_star C_h u t z =
      (b - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
        rate rewards C_star C_h u t z) + 1 := by omega
  rw [ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells,
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells,
    hi, List.take_add_one, next_source_lookup rate rewards C_star C_h u t z hq,
    List.map_append]
  rfl

private theorem continuing_tail_next (z : Z) (hq : b < p.T) :
    ∃ tail, (ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingRecords
      rate rewards C_star C_h u t z) =
      ((nextRecord rate rewards C_star C_h u t z hq) :: tail).takeWhile
        ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen := by
  have hl := nextRecord_lookup rate rewards C_star C_h u t z hq
  obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp hl
  refine ⟨(ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords
    rate rewards C_star C_h u t z).drop
      (t.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z + 1 + 1), ?_⟩
  change ((ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords
    rate rewards C_star C_h u t z).drop
      (t.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z + 1)).takeWhile _ = _
  rw [List.drop_eq_getElem_cons hi, hv]

/-- The next optional whole-prefix readout is present exactly when the
inclusive endpoint passes the inherited boundary. This checks the actual
immediate dispatcher, including its failed and exceptional branches. -/
theorem immediate_prefix_present_iff (z : Z) (hq : b < p.T) :
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
      rate rewards C_star C_h u t (b + 1) z).isSome = true ↔
      b < endpointIndex rate rewards C_star C_h u t z := by
  have happ := calendarCells_immediate_append rate rewards C_star C_h u t z hq
  have hcurrent := ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells_current_mapM
    rate rewards C_star C_h u t z
  have hread := nextDate_readouts rate rewards C_star C_h u t z hq
  obtain ⟨tail, htail⟩ := continuing_tail_next rate rewards C_star C_h u t z hq
  have hlength : ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingLength
      rate rewards C_star C_h u t z =
      (((nextRecord rate rewards C_star C_h u t z hq) :: tail).takeWhile
        ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen).length := by
    change (ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingRecords
      rate rewards C_star C_h u t z).length = _
    rw [htail]
  have hfirst (hz : ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingLength
      rate rewards C_star C_h u t z = 0) :
      ReferenceFirstCollectionRenewalFutureSliceEndpoint.firstNoncontinuingRecord
        rate rewards C_star C_h u t z =
        some (nextRecord rate rewards C_star C_h u t z hq) := by
    unfold ReferenceFirstCollectionRenewalFutureSliceEndpoint.firstNoncontinuingRecord
    rw [hz, Nat.add_zero]
    have hl := nextRecord_lookup rate rewards C_star C_h u t z hq
    exact hl
  have hpresence :
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
        rate rewards C_star C_h u t (b + 1) z).isSome =
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate
        (nextRecord rate rewards C_star C_h u t z hq)).isSome := by
    unfold ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
    rw [happ, ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout_append,
      hcurrent]
    cases ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate
      (nextRecord rate rewards C_star C_h u t z hq) <;> rfl
  rw [hpresence]
  dsimp only at hread
  cases hc : (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator
    <;> simp only [hc] at hread hlength
  all_goals try
    have hz : ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingLength
        rate rewards C_star C_h u t z = 0 := by
      simpa [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hc] using hlength
    have hd : ReferenceFirstCollectionRenewalFutureSliceEndpoint.cutoffEndpointDelta
        rate rewards C_star C_h u t z = 0 := by
      simp [ReferenceFirstCollectionRenewalFutureSliceEndpoint.cutoffEndpointDelta, hfirst hz, hc]
    simp [ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell,
      hread.2.1, hread.2.2.2, endpointIndex,
      ReferenceFirstCollectionRenewalEndpointTelescope.endpointEnd,
      ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex,
      ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingEnd,
      ReferenceFirstCollectionRenewalFutureSliceEndpoint.beginning, hz, hd]
  rename_i outcome
  cases outcome <;> simp only at hread hlength
  all_goals try
    have hz : ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingLength
        rate rewards C_star C_h u t z = 0 := by
      simpa [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hc] using hlength
    have hd : ReferenceFirstCollectionRenewalFutureSliceEndpoint.cutoffEndpointDelta
        rate rewards C_star C_h u t z = 0 := by
      simp [ReferenceFirstCollectionRenewalFutureSliceEndpoint.cutoffEndpointDelta, hfirst hz, hc]
    simp [ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell,
      hread.2.1, hread.2.2.2, endpointIndex,
      ReferenceFirstCollectionRenewalEndpointTelescope.endpointEnd,
      ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex,
      ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingEnd,
      ReferenceFirstCollectionRenewalFutureSliceEndpoint.beginning, hz, hd]
  · obtain ⟨c, _, hC, _, hL⟩ := hread
    have hz : ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingLength
        rate rewards C_star C_h u t z = 0 := by
      simpa [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hc] using hlength
    have hd : ReferenceFirstCollectionRenewalFutureSliceEndpoint.cutoffEndpointDelta
        rate rewards C_star C_h u t z = 1 := by
      simp [ReferenceFirstCollectionRenewalFutureSliceEndpoint.cutoffEndpointDelta, hfirst hz, hc]
    simp [ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell, hL, hC,
      endpointIndex, ReferenceFirstCollectionRenewalEndpointTelescope.endpointEnd,
      ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex,
      ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingEnd,
      ReferenceFirstCollectionRenewalFutureSliceEndpoint.beginning, hz, hd]
  · obtain ⟨c, _, hL, _, hC⟩ := hread
    have hpos : 0 < ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingLength
        rate rewards C_star C_h u t z := by
      simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hc] at hlength
      omega
    have hk : b < endpointIndex rate rewards C_star C_h u t z := by
      change t.val + 1 < t.val + 1 +
        ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingLength
          rate rewards C_star C_h u t z + _
      omega
    simp [ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell, hL, hC, hk]

/-- The actual entry readout selects the present immediate successor, and
otherwise retains the present inherited prefix. No queue value is supplied
for an absent readout. -/
theorem entry_prefix_eq_option_or (z : Z) (hq : b < p.T) :
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
        rate rewards C_star C_h u t (entryIndex rate rewards C_star C_h u t z) z =
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
        rate rewards C_star C_h u t (b + 1) z).or
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
        rate rewards C_star C_h u t b z) := by
  have hiff := immediate_prefix_present_iff rate rewards C_star C_h u t z hq
  have hb := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds
    rate rewards C_star C_h u t z
  have hbk : b ≤ endpointIndex rate rewards C_star C_h u t z := hb.1.trans hb.2.1
  cases ho : ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
      rate rewards C_star C_h u t (b + 1) z with
  | none =>
      have hnot : ¬ b < endpointIndex rate rewards C_star C_h u t z := by
        intro h
        have := hiff.mpr h
        simp [ho] at this
      have he : endpointIndex rate rewards C_star C_h u t z = b := by omega
      simp [entryIndex, he]
  | some r =>
      have hk := hiff.mp (by simp [ho])
      have hj : entryIndex rate rewards C_star C_h u t z = b + 1 := by
        unfold entryIndex
        exact min_eq_left (by omega)
      simp [hj, ho]

private theorem entry_prefix_present (z : Z) :
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
      rate rewards C_star C_h u t (entryIndex rate rewards C_star C_h u t z) z).isSome = true := by
  apply ReferenceFirstCollectionRenewalFutureSliceEndpoint.futurePrefixReadout_present_through_endpoint
  · have hb := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds
      rate rewards C_star C_h u t z
    change b ≤ min (b + 1) (endpointIndex rate rewards C_star C_h u t z)
    exact Nat.le_min.mpr ⟨by omega, hb.1.trans hb.2.1⟩
  · exact min_le_right _ _

private theorem measurable_entry_prefix
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (fun z : Z =>
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
        rate rewards C_star C_h u t (entryIndex rate rewards C_star C_h u t z) z) := by
  have hbase := ReferenceFirstCollectionRenewalFutureNumericalPrefix.measurable_futurePrefixReadout_ambient
    rate rewards C_star C_h u t control0 b (by omega)
  by_cases hq : b < p.T
  · have hnext := ReferenceFirstCollectionRenewalFutureNumericalPrefix.measurable_futurePrefixReadout_ambient
      rate rewards C_star C_h u t control0 (b + 1) (by omega)
    have hm := (measurable_of_countable (fun v :
        Option ((Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ)))) ×
        Option ((Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ)))) =>
        v.1.or v.2)).comp (hnext.prodMk hbase)
    convert hm using 1
    funext z
    exact entry_prefix_eq_option_or rate rewards C_star C_h u t z hq
  · convert hbase using 1
    funext z
    have hb := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds
      rate rewards C_star C_h u t z
    have hk : endpointIndex rate rewards C_star C_h u t z = b := by
      have hbk : b ≤ endpointIndex rate rewards C_star C_h u t z := hb.1.trans hb.2.1
      have hkT : endpointIndex rate rewards C_star C_h u t z ≤ p.T := hb.2.2
      omega
    have hj : entryIndex rate rewards C_star C_h u t z = b := by simp [entryIndex, hk]
    rw [hj]

private instance listMeasurableSingleton {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] : MeasurableSingletonClass (List A) where
  measurableSet_singleton l := by
    let : MeasurableSingletonClass (Unit ⊕ A) := ⟨fun x => by
      cases x with
      | inl a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inl_image
      | inr a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inr_image⟩
    have hinj : Function.Injective (listObservationCoordinates (α := A)) := by
      intro xs ys h
      apply List.ext_getElem (congrArg Prod.fst h)
      intro i hi hj
      have he := congrFun (congrArg Prod.snd h) i
      simpa only [listObservationCoordinates, listObservationAt,
        List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Sum.inr.injEq] using he
    have hh := measurable_listObservationCoordinates
      (MeasurableSet.singleton (listObservationCoordinates l))
    convert hh using 1
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, hinj.eq_iff]

private theorem measurable_present_get {X R : Type*} [MeasurableSpace X]
    [MeasurableSpace R] [Countable R] [MeasurableSingletonClass R]
    (f : X → Option R) (hf : Measurable f) (hp : ∀ x, (f x).isSome = true) :
    Measurable (fun x => (f x).get (hp x)) := by
  have hs : Measurable (fun x => (⟨f x, hp x⟩ : {o : Option R // o.isSome = true})) :=
    hf.subtype_mk
  exact (measurable_of_countable (fun o : {o : Option R // o.isSome = true} =>
    o.val.get o.property)).comp hs

/-- Ambient measurability of the inherited actual entry energy, obtained from
the two fixed original-prefix observations and their genuine presence tag. -/
theorem measurable_entryEnergy (a : Fin p.K)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (entryEnergy rate rewards C_star C_h u t a) := by
  have hm := measurable_present_get _
    (measurable_entry_prefix rate rewards C_star C_h u t control0)
    (entry_prefix_present rate rewards C_star C_h u t)
  have he := (measurable_of_countable (fun r :
      (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))) =>
        Real.exp (β * ((r.1 a).2 : ℝ) / ((Q).n : ℝ)))).comp hm
  exact he

private theorem mem_of_mapM_id_some {A : Type*} (cells : List (Option A))
    (inputs : List A) (hmap : cells.mapM id = some inputs) (x : A)
    (hx : x ∈ inputs) : ∃ o, o ∈ cells ∧ o = some x := by
  induction cells generalizing inputs with
  | nil =>
      have hnil : inputs = [] := Option.some.inj (by simpa using hmap)
      subst inputs
      simp at hx
  | cons cell cells ih =>
      cases cell with
      | none => simp [List.mapM_cons] at hmap
      | some y =>
          simp only [List.mapM_cons] at hmap
          cases htail : cells.mapM id with
          | none => simp [htail] at hmap
          | some tail =>
              simp [htail] at hmap
              have hmem : x = y ∨ x ∈ tail := List.mem_cons.mp (by simpa [hmap] using hx)
              rcases hmem with hxy | htailmem
              · subst x
                exact ⟨some y, by simp, rfl⟩
              · obtain ⟨o, ho, hox⟩ := ih tail htail htailmem
                exact ⟨o, by simp [ho], hox⟩

private theorem actual_prefix_rates (n : ℕ) (z : Z)
    (inputs : List (RecordedQueueRun.RoundInput p.K))
    (hi : ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
        rate rewards C_star C_h u t n z) = some inputs) :
    ∀ c ∈ inputs, ∀ a, 32 * rate.eta.val ≤ c.rate a := by
  intro c hc a
  obtain ⟨o, ho, he⟩ := mem_of_mapM_id_some _ inputs hi c hc
  obtain ⟨r, _, hr⟩ := List.mem_map.mp ho
  have hcell : ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate r = some c :=
    hr.trans he
  exact (ReferenceFirstCollectionRenewalFutureQueueReadout.calendarCell_present_rate_bounds
    rate r c hcell).2 a

/-- Every actual endpoint-date energy has a uniform bound from its same
whole numerical prefix. This includes terminal prefix `T` without creating
an action at `T`. -/
theorem actualBacklogExpAt_le (a : Fin p.K) (z : Z)
    (n : ReferenceFirstCollectionRenewalEndpointTelescope.EndpointDate
      rate rewards C_star C_h u t z) :
    ReferenceFirstCollectionRenewalEndpointTelescope.actualBacklogExpAt
      rate rewards C_star C_h u t z a n ≤
      Real.exp (β * (2 * (1 / (32 * rate.eta.val)))) := by
  have hp := ReferenceFirstCollectionRenewalFutureSliceEndpoint.futurePrefixReadout_present_through_endpoint
    rate rewards C_star C_h u t z n.val n.property.1 n.property.2
  cases hi : ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
        rate rewards C_star C_h u t n.val z) with
  | none =>
      simp [ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout,
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout, hi] at hp
  | some inputs =>
      have hrun := StoppedQueueBound.run_prefix_normalized_backlog_le_twice_threshold
        Q inputs (actual_prefix_rates rate rewards C_star C_h u t n.val z inputs hi)
        inputs.length a
      have hbound : StoppedQueueBound.normalizedBacklog Q
          (RecordedQueueRun.run Q inputs) a ≤ 2 * (1 / (32 * rate.eta.val)) := by
        simpa only [List.take_length, ReferenceFirstLaunchNumericalCell.queueParameters] using hrun
      have hread : ReferenceFirstCollectionRenewalEndpointTelescope.actualReadoutAt
          rate rewards C_star C_h u t z n =
          ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.run Q inputs) := by
        simp [ReferenceFirstCollectionRenewalEndpointTelescope.actualReadoutAt,
          ReferenceFirstCollectionRenewalEndpointTelescope.actualPrefixReadout,
          ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout,
          ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout, hi]
      unfold ReferenceFirstCollectionRenewalEndpointTelescope.actualBacklogExpAt
      rw [hread]
      apply Real.exp_le_exp_of_le
      have hh := mul_le_mul_of_nonneg_left hbound
        (CanonicalRecordingRates.beta_pos p rate.eta.property).le
      simpa only [StoppedQueueBound.normalizedBacklog,
        ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout,
        mul_div_assoc] using hh

/-- The original finite unnormalized renewal law integrates the actual
inherited entry energy; no incoming moment premise is required. -/
theorem integrable_entryEnergy (a : Fin p.K)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (entryEnergy rate rewards C_star C_h u t a) ν := by
  apply (integrable_const (Real.exp (β * (2 * (1 / (32 * rate.eta.val)))))).mono'
    (measurable_entryEnergy rate rewards C_star C_h u t a control0).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  have hn : 0 ≤ entryEnergy rate rewards C_star C_h u t a z := Real.exp_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact actualBacklogExpAt_le rate rewards C_star C_h u t a z _

/-- The fixed finite increment sum is ambient measurable on the original
source, with the original common support for each pair of terms. -/
theorem measurable_futureQueueExpDiffSum (a : Fin p.K)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (fun z : Z => ∑ q : FutureDate (p := p) t,
      (ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueExpAfter
        rate rewards C_star C_h u t q.1 q.2 a z -
      ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueExpBefore
        rate rewards C_star C_h u t q.1 q.2 a z)) := by
  apply Finset.measurable_sum
  intro q hq
  exact (ReferenceFirstCollectionRenewalFutureExponentialQueueStep.measurable_futureQueueExpAfter
    rate rewards C_star C_h u t q.1 q.2 control0 a).sub
    (ReferenceFirstCollectionRenewalFutureExponentialQueueStep.measurable_futureQueueExpBefore_ambient
      rate rewards C_star C_h u t q.1 q.2 control0 a)

/-- Endpoint measurability follows from the exact telescope, keeping the
full exiting endpoint energy. -/
theorem measurable_endpointEnergy (a : Fin p.K)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (endpointEnergy rate rewards C_star C_h u t a) := by
  have heq : endpointEnergy rate rewards C_star C_h u t a =
      fun z : Z => entryEnergy rate rewards C_star C_h u t a z +
        ∑ q : FutureDate (p := p) t,
          (ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueExpAfter
            rate rewards C_star C_h u t q.1 q.2 a z -
          ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueExpBefore
            rate rewards C_star C_h u t q.1 q.2 a z) := by
    funext z
    exact endpointEnergy_eq_entryEnergy_add_futureSum rate rewards C_star C_h u t a z
  rw [heq]
  exact (measurable_entryEnergy rate rewards C_star C_h u t a control0).add
    (measurable_futureQueueExpDiffSum rate rewards C_star C_h u t a control0)

/-- Integrability of the actual inclusive endpoint under the same original
possibly-zero finite renewal measure. -/
theorem integrable_endpointEnergy (a : Fin p.K)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (endpointEnergy rate rewards C_star C_h u t a) ν := by
  have hi := (integrable_entryEnergy rate rewards C_star C_h u t a control0).add
    (integrable_futureQueueExpDiffSum rate rewards C_star C_h u t a control0)
  apply hi.congr
  exact Filter.Eventually.of_forall fun z =>
    (endpointEnergy_eq_entryEnergy_add_futureSum rate rewards C_star C_h u t a z).symm

/-- The finite unnormalized renewal endpoint exponential moment, with the
inherited entry energy and the sharp sum of actual future-gate masses. -/
theorem integral_endpointEnergy_le (a : Fin p.K)
    (control0 : ContinuousLearningRows.TimeControl p) :
    ∫ z, endpointEnergy rate rewards C_star C_h u t a z ∂ν ≤
      (∫ z, entryEnergy rate rewards C_star C_h u t a z ∂ν) +
      ∑ q : FutureDate (p := p) t,
        (ν).real (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
          rate rewards C_star C_h u t q.1 q.2) := by
  have heq : endpointEnergy rate rewards C_star C_h u t a =
      fun z : Z => entryEnergy rate rewards C_star C_h u t a z +
        ∑ q : FutureDate (p := p) t,
          (ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueExpAfter
            rate rewards C_star C_h u t q.1 q.2 a z -
          ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueExpBefore
            rate rewards C_star C_h u t q.1 q.2 a z) := by
    funext z
    exact endpointEnergy_eq_entryEnergy_add_futureSum rate rewards C_star C_h u t a z
  rw [heq, integral_add
    (integrable_entryEnergy rate rewards C_star C_h u t a control0)
    (integrable_futureQueueExpDiffSum rate rewards C_star C_h u t a control0)]
  exact add_le_add le_rfl
    (integral_futureQueueExpDiffSum_le rate rewards C_star C_h u t a control0)

end Bandits.Support.ReferenceFirstCollectionRenewalEndpointExponentialMoment

end
