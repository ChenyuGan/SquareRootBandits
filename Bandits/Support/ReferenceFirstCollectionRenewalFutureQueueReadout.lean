/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalFutureRetainedMoments

import Mathlib.Tactic

/-!
# Localized future queue readouts on the renewal source

This module observes the existing optional whole-prefix run immediately before
one actual future cell and immediately after that same cell. Both scalar
observations use the same predictable support and the original renewal source.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open scoped Classical MeasureTheory

namespace Bandits.Support.ReferenceFirstCollectionRenewalFutureQueueReadout

open ReferenceFirstCollectionRenewalFutureRetainedMoments
open ReferenceFirstCollectionRenewalFutureNumericalPrefix
open ReferenceFirstCollectionRenewalFutureRecordingLaw
open ReferenceFirstCollectionRenewalFutureFirstReplacementView
open ReferenceFirstCollectionRenewalFutureControlLaw
open ReferenceFirstCollectionRenewalAuxiliaryLaw
open ReferenceFirstCollectionRenewalIncomingQueueMeasurability
open ReferenceSourcePrefixHistoryFiltration

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)
  (control0 : ContinuousLearningRows.TimeControl p)
  (q : Fin p.T) (hfuture : t.val + 1 < q.val) (a : Fin p.K)

local notation "Z" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.Source
  rate rewards C_star C_h u t
local notation "ν" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
  rate rewards C_star C_h u t
local notation "Q" => _root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "Fq" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
  rate rewards C_star C_h u t control0 q
local notation "before?" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
  rate rewards C_star C_h u t q
local notation "after?" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
  rate rewards C_star C_h u t (q.val + 1)
local notation "S" => Set.ofPred (fun z : Z =>
  Option.isSome (ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture) = true ∧
    Option.isSome (ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
      rate rewards C_star C_h u t q z) = true)
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

/-- Integer queue backlog divided by the canonical queue denominator; absence
has scalar projection zero. -/
private def optionalBacklog (rate : ReferenceActivePhysicalStep.RateInput p)
    (a : Fin p.K) (o : Option
    ((Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))))) : ℝ :=
  match o with
  | none => 0
  | some r => ((r.1 a).2 : ℝ) /
      ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)

include q hfuture a in
/-- The future-date backlog immediately before the actual cell, localized to
the predictable support of present future parameters and present prior run. -/
def futureBacklogBefore (z : Z) : ℝ :=
  if z ∈ S then
    match before? z with
    | none => 0
    | some r => ((r.1 a).2 : ℝ) / ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)
  else 0

include q hfuture a in
/-- The same future-date backlog immediately after the actual cell, localized
to the same prior-date support. -/
def futureBacklogAfter (z : Z) : ℝ :=
  if z ∈ S then
    match after? z with
    | none => 0
    | some r => ((r.1 a).2 : ℝ) / ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)
  else 0

private theorem measurable_optionalBacklog :
    Measurable (optionalBacklog rate a) := by
  exact measurable_of_countable _

/-- The optional prior run is measurable in the exact future prior field. -/
theorem measurable_futureBacklogBefore :
    Measurable[Fq] (futureBacklogBefore rate rewards C_star C_h u t q hfuture a) := by
  have hparams := ReferenceFirstCollectionRenewalFutureRecordingLaw.measurable_futureParameters
    rate rewards C_star C_h u t control0 q hfuture
  have hbefore : Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q] (before?) := by
    change Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q]
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
        rate rewards C_star C_h u t q.val)
    exact ReferenceFirstCollectionRenewalFutureNumericalPrefix.measurable_futurePrefixReadout
      rate rewards C_star C_h u t control0 q.val (by omega)
  have hparamsSome : Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q] (fun z : Z =>
      (ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
        rate rewards C_star C_h u t z q hfuture).isSome) :=
    measurable_option_isSome
      (ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q) _ hparams
  have hbeforeSome : Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q] (fun z : Z => (before? z).isSome) :=
    (measurable_of_countable (fun o : Option
      ((Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ)))) => o.isSome)).comp hbefore
  let params := fun z : Z => ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
    rate rewards C_star C_h u t z q hfuture
  let gateBit := fun z : Z => (params z).isSome && (before? z).isSome
  have hgate : Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q] gateBit :=
    (measurable_of_countable (fun b : Bool × Bool => b.1 && b.2)).comp
      (hparamsSome.prodMk hbeforeSome)
  have hS : MeasurableSet[Fq] S := by
    have hset : MeasurableSet[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q] {z : Z | gateBit z = true} :=
      hgate (measurableSet_singleton true)
    have heq : S = {z : Z | gateBit z = true} := by
      ext z
      change ((params z).isSome = true ∧ (before? z).isSome = true) ↔
        gateBit z = true
      simp [gateBit, Bool.and_eq_true]
    rw [heq]
    exact hset
  have hproj : Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q]
      (fun z : Z => optionalBacklog rate a (before? z)) :=
    (measurable_optionalBacklog rate a).comp hbefore
  change Measurable[Fq] (fun z : Z => if z ∈ S then
    optionalBacklog rate a (before? z) else 0)
  exact Measurable.ite hS hproj measurable_const

include control0 in
/-- The successor readout is measurable in the original ambient source. -/
theorem measurable_futureBacklogAfter :
    Measurable (futureBacklogAfter rate rewards C_star C_h u t q hfuture a) := by
  have hparams := ReferenceFirstCollectionRenewalFutureRecordingLaw.measurable_futureParameters
    rate rewards C_star C_h u t control0 q hfuture
  have hbefore : Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q] (before?) := by
    change Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q]
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
        rate rewards C_star C_h u t q.val)
    exact ReferenceFirstCollectionRenewalFutureNumericalPrefix.measurable_futurePrefixReadout
      rate rewards C_star C_h u t control0 q.val (by omega)
  have hparamsSome : Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q] (fun z : Z =>
      (ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
        rate rewards C_star C_h u t z q hfuture).isSome) :=
    measurable_option_isSome
      (ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q) _ hparams
  have hbeforeSome : Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q] (fun z : Z => (before? z).isSome) :=
    (measurable_of_countable (fun o : Option
      ((Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ)))) => o.isSome)).comp hbefore
  let params := fun z : Z => ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
    rate rewards C_star C_h u t z q hfuture
  let gateBit := fun z : Z => (params z).isSome && (before? z).isSome
  have hgate : Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q] gateBit :=
    (measurable_of_countable (fun b : Bool × Bool => b.1 && b.2)).comp
      (hparamsSome.prodMk hbeforeSome)
  have hS : MeasurableSet[Fq] S := by
    have hset : MeasurableSet[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q] {z : Z | gateBit z = true} :=
      hgate (measurableSet_singleton true)
    have heq : S = {z : Z | gateBit z = true} := by
      ext z
      change ((params z).isSome = true ∧ (before? z).isSome = true) ↔
        gateBit z = true
      simp [gateBit, Bool.and_eq_true]
    rw [heq]
    exact hset
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hSambient : MeasurableSet S := hfield _ hS
  have hafter : Measurable (after?) :=
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.measurable_futurePrefixReadout_ambient
      rate rewards C_star C_h u t control0 (q.val + 1) (by omega)
  have hproj : Measurable (fun z : Z => optionalBacklog rate a (after? z)) :=
    (measurable_optionalBacklog rate a).comp hafter
  change Measurable (fun z : Z => if z ∈ S then
    optionalBacklog rate a (after? z) else 0)
  exact Measurable.ite hSambient hproj measurable_const

include control0 in
/-- The prior scalar is also measurable in the original ambient source. -/
theorem measurable_futureBacklogBefore_ambient :
    Measurable (futureBacklogBefore rate rewards C_star C_h u t q hfuture a) := by
  have hm := measurable_futureBacklogBefore rate rewards C_star C_h u t control0 q hfuture a
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  exact hm.mono hfield le_rfl

include control0 in
/-- The prior observation is strongly measurable under the original,
unnormalized renewal law. -/
theorem aestronglyMeasurable_futureBacklogBefore :
    AEStronglyMeasurable
      (futureBacklogBefore rate rewards C_star C_h u t q hfuture a) ν := by
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  exact (measurable_futureBacklogBefore rate rewards C_star C_h u t control0 q hfuture a)
    |>.mono hfield le_rfl |>.aestronglyMeasurable

/-- The actual live or collection readout exposes the payload's canonical
rate, including disabled collection cells. -/
theorem calendarCell_present_rate_bounds
    (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate r = some c) :
    (∀ i, CanonicalRecordingRates.beta p rate.eta.val ≤ c.rate i) ∧
      (∀ i, 32 * rate.eta.val ≤ c.rate i) := by
  classical
  cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r with
  | some live =>
      have hlive : live = c := by
        have h := hc
        simp [ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell, hl] at h
        exact h
      subst c
      obtain ⟨_, selected, _, _, hrate, _⟩ :=
        ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical 0 r live hl
      constructor
      · intro i
        rw [hrate]
        exact selected.view.payload.beta_le_rate i
      · intro i
        rw [hrate, selected.view.payload.rate_eq_canonical]
        exact CanonicalRecordingRates.thirtyTwo_mul_eta_le_xi p rate.eta.property
          selected.view.payload.anchor i
  | none =>
      have hcollection :
          ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c := by
        simpa [ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell, hl] using hc
      rcases ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call
          0 r c hcollection with
        ⟨payload, ledger, started, weights, out, hcall, hdiag, hrun, henabled,
          henabled', hrate, hreward, hrecord, hgate, harr⟩
      constructor
      · intro i
        rw [hrate]
        exact payload.beta_le_rate i
      · intro i
        rw [hrate, payload.rate_eq_canonical]
        exact CanonicalRecordingRates.thirtyTwo_mul_eta_le_xi p rate.eta.property
          payload.anchor i

private theorem mem_of_mapM_id_some {α : Type*} (cells : List (Option α))
    (inputs : List α) (hmap : cells.mapM id = some inputs) (x : α)
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
              have hmem0 : x ∈ y :: tail := by simpa [hmap] using hx
              have hmem : x = y ∨ x ∈ tail := List.mem_cons.mp hmem0
              rcases hmem with hxy | htailmem
              · subst x
                exact ⟨some y, by simp, rfl⟩
              · obtain ⟨o, ho, hox⟩ := ih tail htail htailmem
                exact ⟨o, by simp [ho], hox⟩

/-- Every present literal numerical calendar cell has the actual canonical
rate lower bounds. -/
theorem calendarCells_present_rates
    (z : Z)
    (inputs : List (RecordedQueueRun.RoundInput p.K))
    (hinputs : ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
      rate rewards C_star C_h u t q z = some inputs)
    (c : RecordedQueueRun.RoundInput p.K) (hc : c ∈ inputs) :
    (∀ i, CanonicalRecordingRates.beta p rate.eta.val ≤ c.rate i) ∧
      (∀ i, 32 * rate.eta.val ≤ c.rate i) := by
  have hmap : (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
      rate rewards C_star C_h u t q.val z).mapM id = some inputs := by
    simpa [ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs,
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells] using hinputs
  obtain ⟨cell, hcell, hsome⟩ := mem_of_mapM_id_some
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
      rate rewards C_star C_h u t q.val z) inputs hmap c hc
  obtain ⟨r, _, hrecord⟩ := List.mem_map.mp hcell
  have hopt : ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate r = some c := by
    simpa [hsome] using hrecord
  exact calendarCell_present_rate_bounds rate r c hopt

/-- Every member of the same full optional prefix carries the source-derived
rate lower bounds needed by the stopped queue theorem. -/
theorem prefixInputs_present_rates (z : Z) (inputs : List (RecordedQueueRun.RoundInput p.K))
    (hinputs : ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
      rate rewards C_star C_h u t q z = some inputs) :
    ∀ c ∈ inputs,
      (∀ i, CanonicalRecordingRates.beta p rate.eta.val ≤ c.rate i) ∧
        (∀ i, 32 * rate.eta.val ≤ c.rate i) := by
  intro c hc
  exact calendarCells_present_rates rate rewards C_star C_h u t q z inputs hinputs c hc

private theorem futureParameters_present_of_futureCell
    (z : Z) (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = some c) :
    ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture = some (c.enabled, c.rate) := by
  have hread := ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_readout
    rate rewards C_star C_h u t z q hfuture
  cases hv : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture with
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
      have hcell_eq : cell = c := Option.some.inj (hcell.symm.trans hc)
      rw [← hcell_eq]
      simpa [ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters, hv] using
        hparameters

private theorem futureCell_present_of_parameters
    (z : Z) (hparams : (ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture).isSome = true) :
    ∃ c : RecordedQueueRun.RoundInput p.K,
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
        rate rewards C_star C_h u t z q hfuture = some c ∧
      ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
        rate rewards C_star C_h u t z q hfuture = some (c.enabled, c.rate) := by
  cases hv : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture with
  | none =>
      simp [ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters, hv] at hparams
  | some data =>
      rcases data with ⟨parameters, view, code⟩
      have hread := ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_readout
        rate rewards C_star C_h u t z q hfuture
      rw [hv] at hread
      obtain ⟨c, snapshot, valid, hcell, hparameters, hrate, _, _, _⟩ := hread
      refine ⟨c, hcell, ?_⟩
      simpa [ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters, hv] using
        hparameters

private theorem priorReadout_none_of_prefixInputs_none (z : Z)
    (hinputs : ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
      rate rewards C_star C_h u t q z = none) :
    ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
      rate rewards C_star C_h u t q z = none := by
  change ((ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
      rate rewards C_star C_h u t q.val z).mapM id).map
        (fun inputs => ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run Q inputs)) = none
  have hmap : (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
      rate rewards C_star C_h u t q.val z).mapM id = none := by
    simpa [ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs] using hinputs
  rw [hmap]
  rfl

private theorem priorClear_eq_of_prefixInputs_some (z : Z)
    (inputs : List (RecordedQueueRun.RoundInput p.K))
    (hinputs : ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
      rate rewards C_star C_h u t q z = some inputs) :
    ReferenceFirstCollectionRenewalFutureRetainedMoments.priorClear
      rate rewards C_star C_h u t q z =
        !(RecordedQueueRun.run Q inputs).overflow := by
  unfold ReferenceFirstCollectionRenewalFutureRetainedMoments.priorClear
  rw [ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout_eq_of_inputs
    rate rewards C_star C_h u t q z inputs hinputs]
  cases hflag : (RecordedQueueRun.run Q inputs).overflow <;>
    simp [ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout, hflag]

/-- On the literal predictable support, both optional readouts are the same
existing run and its actual one-cell successor. -/
theorem futureBacklogs_present (z : Z) (hz : z ∈ S) :
    ∃ inputs : List (RecordedQueueRun.RoundInput p.K),
    ∃ c : RecordedQueueRun.RoundInput p.K,
      ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
        rate rewards C_star C_h u t q z = some inputs ∧
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
        rate rewards C_star C_h u t z q hfuture = some c ∧
      (before? z = some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.run Q inputs))) ∧
      (after? z = some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c))) ∧
      futureBacklogBefore rate rewards C_star C_h u t q hfuture a z =
        StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q inputs) a ∧
      futureBacklogAfter rate rewards C_star C_h u t q hfuture a z =
        StoppedQueueBound.normalizedBacklog
          Q (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c) a := by
  obtain ⟨c, hc, hparams⟩ := futureCell_present_of_parameters
    rate rewards C_star C_h u t q hfuture z hz.1
  cases hinputs : ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
      rate rewards C_star C_h u t q z with
  | none =>
      have hnone := priorReadout_none_of_prefixInputs_none rate rewards C_star C_h u t q z hinputs
      have hbefore : (before? z).isSome = true := hz.2
      rw [hnone] at hbefore
      simp at hbefore
  | some inputs =>
      have hbefore := ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout_eq_of_inputs
        rate rewards C_star C_h u t q z inputs hinputs
      have haccept := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_present_acceptance
        rate rewards C_star C_h u t q hfuture a z inputs c hinputs hc
      have hafter := haccept.2.1
      have hsupport : z ∈ S := by
        refine ⟨?_, ?_⟩
        · rw [hparams]
          rfl
        · rw [hbefore]
          rfl
      have hscalarBefore :
          futureBacklogBefore rate rewards C_star C_h u t q hfuture a z =
            StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q inputs) a := by
        unfold futureBacklogBefore
        rw [ite_eq_left hsupport, hbefore]
        rfl
      have hscalarAfter :
          futureBacklogAfter rate rewards C_star C_h u t q hfuture a z =
            StoppedQueueBound.normalizedBacklog
              Q (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c) a := by
        unfold futureBacklogAfter
        rw [ite_eq_left hsupport, hafter]
        rfl
      exact ⟨inputs, c, rfl, hc, hbefore, hafter, hscalarBefore, hscalarAfter⟩

/-- Every actual present first-replacement cell inherits the live/collection
payload rate bounds from its original unmasked source record. -/
theorem futureCell_present_rate_bounds (z : Z) (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = some c) :
    (∀ i, CanonicalRecordingRates.beta p rate.eta.val ≤ c.rate i) ∧
      (∀ i, 32 * rate.eta.val ≤ c.rate i) := by
  have hcell := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureSliceCell_eq_unmasked
    rate rewards C_star C_h u t q hfuture z c hc
  exact calendarCell_present_rate_bounds rate
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureRecord
      rate rewards C_star C_h u t q z) c hcell

private theorem normalizedBacklog_nonneg (state : RecordedQueueRun.RunState p.K) :
    0 ≤ StoppedQueueBound.normalizedBacklog Q state a := by
  change 0 ≤ ((state.registers a).2 : ℝ) / ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Both localized readouts remain within the actual reachable two-threshold
bound on the whole original launch prefix. -/
theorem futureBacklogs_bounds (z : Z) :
    futureBacklogBefore rate rewards C_star C_h u t q hfuture a z ∈
      Set.Icc (0 : ℝ) (2 * Bcap) ∧
    futureBacklogAfter rate rewards C_star C_h u t q hfuture a z ∈
      Set.Icc (0 : ℝ) (2 * Bcap) := by
  have hBcap : 0 ≤ Bcap := by
    have heta : 0 < rate.eta.val := rate.eta.property
    exact div_nonneg (by norm_num) (le_of_lt (mul_pos (by norm_num) heta))
  by_cases hz : z ∈ S
  · obtain ⟨inputs, c, hinputs, hc, hbefore, hafter, hscalarBefore, hscalarAfter⟩ :=
      futureBacklogs_present rate rewards C_star C_h u t q hfuture a z hz
    have hprefixRates := prefixInputs_present_rates rate rewards C_star C_h u t q z inputs hinputs
    have hbeforeBound := StoppedQueueBound.run_prefix_normalized_backlog_le_twice_threshold
      Q inputs (by
        intro round hround i
        exact (hprefixRates round hround).2 i) inputs.length a
    have hcellRates := futureCell_present_rate_bounds rate rewards C_star C_h u t q hfuture z c hc
    have happendedRates : ∀ round ∈ inputs ++ [c], ∀ i, 32 * rate.eta.val ≤ round.rate i := by
      intro round hround i
      rcases List.mem_append.mp hround with hmem | hmem
      · exact (hprefixRates round hmem).2 i
      · simp only [List.mem_singleton] at hmem
        subst round
        exact hcellRates.2 i
    have hafterBound := StoppedQueueBound.run_prefix_normalized_backlog_le_twice_threshold
      Q (inputs ++ [c]) happendedRates (inputs ++ [c]).length a
    have hrun := ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one
      rate inputs c
    constructor
    · constructor
      · rw [hscalarBefore]
        exact normalizedBacklog_nonneg rate a (RecordedQueueRun.run Q inputs)
      · have hbeforeRun : StoppedQueueBound.normalizedBacklog Q
            (RecordedQueueRun.run Q inputs) a ≤ 2 *
              (1 / (32 * (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta)) := by
          simpa [List.take_length] using hbeforeBound
        rw [hscalarBefore]
        simpa [ReferenceFirstLaunchNumericalCell.queueParameters] using hbeforeRun
    · constructor
      · rw [hscalarAfter, ← hrun]
        exact normalizedBacklog_nonneg rate a (RecordedQueueRun.run Q (inputs ++ [c]))
      · have hafterRun : StoppedQueueBound.normalizedBacklog Q
            (RecordedQueueRun.run Q (inputs ++ [c])) a ≤ 2 *
              (1 / (32 * (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta)) := by
          simpa only [List.take_length] using hafterBound
        rw [hscalarAfter, ← hrun]
        simpa [ReferenceFirstLaunchNumericalCell.queueParameters] using hafterRun
  · constructor
    · simp only [futureBacklogBefore, ite_eq_right hz]
      constructor
      · rfl
      · change 0 ≤ 2 * Bcap
        nlinarith [hBcap]
    · simp only [futureBacklogAfter, ite_eq_right hz]
      constructor
      · rfl
      · change 0 ≤ 2 * Bcap
        nlinarith [hBcap]

/-- Before a prior-clear update the normalized backlog is bounded by the
source threshold, including the first update that later causes overflow. -/
theorem futureBacklogBefore_le_threshold_of_priorClear (z : Z)
    (hclear : ReferenceFirstCollectionRenewalFutureRetainedMoments.priorClear
      rate rewards C_star C_h u t q z = true) :
    futureBacklogBefore rate rewards C_star C_h u t q hfuture a z ≤ Bcap := by
  have hBcap : 0 ≤ Bcap := by
    have heta : 0 < rate.eta.val := rate.eta.property
    exact div_nonneg (by norm_num) (le_of_lt (mul_pos (by norm_num) heta))
  by_cases hz : z ∈ S
  · obtain ⟨inputs, c, hinputs, hc, hbefore, hafter, hscalarBefore, hscalarAfter⟩ :=
      futureBacklogs_present rate rewards C_star C_h u t q hfuture a z hz
    have hoverflow : (RecordedQueueRun.run Q inputs).overflow = false := by
      have hclear' := priorClear_eq_of_prefixInputs_some rate rewards C_star C_h u t q z inputs hinputs
      rw [hclear'] at hclear
      cases ho : (RecordedQueueRun.run Q inputs).overflow <;> simp [ho] at hclear ⊢
    have hoverflowPrefix :
        (RecordedQueueRun.run Q (inputs.take inputs.length)).overflow = false := by
      simpa [List.take_length] using hoverflow
    have hbound := StoppedQueueBound.run_prefix_normalized_backlog_le_threshold_of_overflow_false
      Q inputs inputs.length a hoverflowPrefix
    have hboundRun : StoppedQueueBound.normalizedBacklog Q
        (RecordedQueueRun.run Q inputs) a ≤ 1 / (32 * rate.eta.val) := by
      simpa [List.take_length, ReferenceFirstLaunchNumericalCell.queueParameters] using hbound
    rw [hscalarBefore]
    exact hboundRun
  · simp only [futureBacklogBefore, ite_eq_right hz]
    change 0 ≤ Bcap
    exact hBcap

/-- The present enabled, prior-clear update obeys the reflected normalized
queue equation on the same observed run states. -/
theorem futureBacklogAfter_reflected_of_retained
    (z : Z) (inputs : List (RecordedQueueRun.RoundInput p.K))
    (c : RecordedQueueRun.RoundInput p.K)
    (hinputs : ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
      rate rewards C_star C_h u t q z = some inputs)
    (hc : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = some c)
    (hclear : ReferenceFirstCollectionRenewalFutureRetainedMoments.priorClear
      rate rewards C_star C_h u t q z = true)
    (henabled : c.enabled = true) :
    futureBacklogAfter rate rewards C_star C_h u t q hfuture a z =
      max (futureBacklogBefore rate rewards C_star C_h u t q hfuture a z +
        ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture a z - 4) 0 := by
  have hbefore := ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout_eq_of_inputs
    rate rewards C_star C_h u t q z inputs hinputs
  have hparams := futureParameters_present_of_futureCell rate rewards C_star C_h u t
    q hfuture z c hc
  have hz : z ∈ S := by
    refine ⟨?_, ?_⟩
    · rw [hparams]
      rfl
    · rw [hbefore]
      rfl
  obtain ⟨inputs', c', hinputs', hc', hbefore', hafter', hscalarBefore, hscalarAfter⟩ :=
    futureBacklogs_present rate rewards C_star C_h u t q hfuture a z hz
  have hinputsEq : inputs' = inputs := Option.some.inj (hinputs'.symm.trans hinputs)
  have hcEq : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst inputs'
  subst c'
  have hfalse : (RecordedQueueRun.run Q inputs).overflow = false := by
    have hclear' := priorClear_eq_of_prefixInputs_some rate rewards C_star C_h u t q z inputs hinputs
    rw [hclear'] at hclear
    cases ho : (RecordedQueueRun.run Q inputs).overflow <;> simp [ho] at hclear ⊢
  have hraw := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_present_run
    rate rewards C_star C_h u t q hfuture a z inputs c hinputs hc
  have hstep := CanonicalQueueProcess.normalizedBacklog_step_of_retained
    Q (RecordedQueueRun.run Q inputs) c a hfalse henabled
  calc
    futureBacklogAfter rate rewards C_star C_h u t q hfuture a z =
        StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.step Q
          (RecordedQueueRun.run Q inputs) c) a := hscalarAfter
    _ = max (StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q inputs) a +
        RecordedRoundMoments.rawEstimate Q (RecordedQueueRun.run Q inputs) c a - 4) 0 := hstep
    _ = max (futureBacklogBefore rate rewards C_star C_h u t q hfuture a z +
        ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture a z - 4) 0 := by
      rw [← hscalarBefore, ← hraw]

/-- Enabled zero-arrival service subtracts four before reflection. -/
theorem futureBacklogAfter_eq_drain_of_retained_zero
    (z : Z) (inputs : List (RecordedQueueRun.RoundInput p.K))
    (c : RecordedQueueRun.RoundInput p.K)
    (hinputs : ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
      rate rewards C_star C_h u t q z = some inputs)
    (hc : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = some c)
    (hclear : ReferenceFirstCollectionRenewalFutureRetainedMoments.priorClear
      rate rewards C_star C_h u t q z = true)
    (henabled : c.enabled = true)
    (hzero : RecordedRoundMoments.rawEstimate Q (RecordedQueueRun.run Q inputs) c a = 0) :
    futureBacklogAfter rate rewards C_star C_h u t q hfuture a z =
      max (futureBacklogBefore rate rewards C_star C_h u t q hfuture a z - 4) 0 := by
  have hraw := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_present_run
    rate rewards C_star C_h u t q hfuture a z inputs c hinputs hc
  have hscalar : ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
      rate rewards C_star C_h u t q hfuture a z = 0 := hraw.trans hzero
  rw [futureBacklogAfter_reflected_of_retained rate rewards C_star C_h u t q
    hfuture a z inputs c hinputs hc hclear henabled, hscalar]
  ring_nf

/-- On an actual present disabled or prior-overflow cell, the localized
normalized backlog is preserved by the canonical inactive transition. -/
theorem futureBacklogAfter_eq_before_of_inactive
    (z : Z) (inputs : List (RecordedQueueRun.RoundInput p.K))
    (c : RecordedQueueRun.RoundInput p.K)
    (hinputs : ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
      rate rewards C_star C_h u t q z = some inputs)
    (hc : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = some c)
    (hinactive : c.enabled = false ∨ (RecordedQueueRun.run Q inputs).overflow = true) :
    futureBacklogAfter rate rewards C_star C_h u t q hfuture a z =
      futureBacklogBefore rate rewards C_star C_h u t q hfuture a z := by
  have hbefore := ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout_eq_of_inputs
    rate rewards C_star C_h u t q z inputs hinputs
  have hparams := futureParameters_present_of_futureCell rate rewards C_star C_h u t
    q hfuture z c hc
  have hz : z ∈ S := by
    refine ⟨?_, ?_⟩
    · rw [hparams]
      rfl
    · rw [hbefore]
      rfl
  obtain ⟨inputs', c', hinputs', hc', hbefore', hafter', hscalarBefore, hscalarAfter⟩ :=
    futureBacklogs_present rate rewards C_star C_h u t q hfuture a z hz
  have hinputsEq : inputs' = inputs := Option.some.inj (hinputs'.symm.trans hinputs)
  have hcEq : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst inputs'
  subst c'
  calc
    futureBacklogAfter rate rewards C_star C_h u t q hfuture a z =
        StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.step Q
          (RecordedQueueRun.run Q inputs) c) a := hscalarAfter
    _ = StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q inputs) a :=
      (CanonicalQueueProcess.normalizedBacklog_step_of_inactive
        Q (RecordedQueueRun.run Q inputs) c a hinactive)
    _ = futureBacklogBefore rate rewards C_star C_h u t q hfuture a z :=
      hscalarBefore.symm

/-- The same disabled or prior-overflow step appends its actual no-op record
to the original per-arm history. -/
theorem futureBacklogAfter_inactive_appends_noop
    (z : Z) (inputs : List (RecordedQueueRun.RoundInput p.K))
    (c : RecordedQueueRun.RoundInput p.K)
    (hinputs : ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
      rate rewards C_star C_h u t q z = some inputs)
    (hc : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = some c)
    (hinactive : c.enabled = false ∨ (RecordedQueueRun.run Q inputs).overflow = true) :
    (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c).records a =
      (RecordedQueueRun.run Q inputs).records a ++ [(false, 0)] := by
  have haccept := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_present_acceptance
    rate rewards C_star C_h u t q hfuture a z inputs c hinputs hc
  rw [haccept.2.2]
  rcases hinactive with henabled | hoverflow
  · simp [RecordedQueueRun.acceptedRecord, henabled]
  · simp [RecordedQueueRun.acceptedRecord, hoverflow]

/-- Both localized observations vanish off their literal common support. The
underlying optional readouts remain unchanged and may still be absent. -/
theorem futureBacklogs_zero_off_presence (z : Z) (hz : z ∉ S) :
    futureBacklogBefore rate rewards C_star C_h u t q hfuture a z = 0 ∧
    futureBacklogAfter rate rewards C_star C_h u t q hfuture a z = 0 := by
  constructor
  · unfold futureBacklogBefore
    rw [ite_eq_right hz]
  · unfold futureBacklogAfter
    rw [ite_eq_right hz]

include control0 in
/-- The bounded prior scalar is integrable under the original finite renewal
measure, without normalizing it or assuming positive mass. -/
theorem integrable_futureBacklogBefore :
    Integrable (futureBacklogBefore rate rewards C_star C_h u t q hfuture a) ν := by
  have hm := measurable_futureBacklogBefore_ambient
    rate rewards C_star C_h u t control0 q hfuture a
  have hbound := futureBacklogs_bounds rate rewards C_star C_h u t q hfuture a
  have hBcap : 0 ≤ Bcap := by
    have heta : 0 < rate.eta.val := rate.eta.property
    exact div_nonneg (by norm_num) (le_of_lt (mul_pos (by norm_num) heta))
  apply integrable_of_measurable_norm_le_const _ hm (2 * Bcap)
  intro z
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by nlinarith [(hbound z).1.1, hBcap], (hbound z).1.2⟩

include control0 in
/-- The bounded successor scalar is integrable under the original finite
renewal measure, without normalizing it or assuming positive mass. -/
theorem integrable_futureBacklogAfter :
    Integrable (futureBacklogAfter rate rewards C_star C_h u t q hfuture a) ν := by
  have hm := measurable_futureBacklogAfter rate rewards C_star C_h u t control0 q hfuture a
  have hbound := futureBacklogs_bounds rate rewards C_star C_h u t q hfuture a
  have hBcap : 0 ≤ Bcap := by
    have heta : 0 < rate.eta.val := rate.eta.property
    exact div_nonneg (by norm_num) (le_of_lt (mul_pos (by norm_num) heta))
  apply integrable_of_measurable_norm_le_const _ hm (2 * Bcap)
  intro z
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by nlinarith [(hbound z).2.1, hBcap], (hbound z).2.2⟩

end Bandits.Support.ReferenceFirstCollectionRenewalFutureQueueReadout

end
