/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalFutureRecordingLaw
public import Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic

/-!
# Retained raw moments on the future first-replacement slice

The scalar below is the accepted raw arrival of the existing stopped run on
the original optional whole prefix, followed by the actual masked physical
cell on the first-replacement slice. Missing prefixes and missing cells remain
missing in the readouts and contribute zero only to this scalar projection.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open scoped Classical MeasureTheory

namespace Bandits.Support.ReferenceFirstCollectionRenewalFutureRetainedMoments

open ReferenceFirstCollectionRenewalFutureRecordingLaw
open ReferenceFirstCollectionRenewalFutureNumericalPrefix
open ReferenceFirstCollectionRenewalFutureFirstReplacementView
open ReferenceFirstCollectionRenewalFutureControlLaw
open ReferenceFirstCollectionRenewalNextRecordingLaw
open ReferenceFirstCollectionRenewalAuxiliaryLaw
open ReferenceSourcePrefixHistoryFiltration

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Z" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.Source
  rate rewards C_star C_h u t
local notation "ν" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
  rate rewards C_star C_h u t
local notation "Q" => _root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "Fq" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
  rate rewards C_star C_h u t control0

/-- The present optional round inputs in the complete inherited prefix. -/
def prefixInputs (q : Fin p.T) (z : Z) :
    Option (List (RecordedQueueRun.RoundInput p.K)) :=
  (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
    rate rewards C_star C_h u t q.val z).mapM id

/-- The existing optional stopped-run readout immediately before date `q`. -/
def priorReadout (q : Fin p.T) (z : Z) :=
  ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
    rate rewards C_star C_h u t q.val z

/-- True exactly when the actual prior optional readout is present and has not
overflowed. -/
def priorClear (q : Fin p.T) (z : Z) : Bool :=
  match priorReadout rate rewards C_star C_h u t q z with
  | some (_, (false, _)) => true
  | _ => false

/-- Actual accepted raw arrival on the same whole inherited prefix and the
actual first-replacement physical cell. Either absent option contributes zero. -/
def futureScalar (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) (z : Z) : ℝ :=
  match prefixInputs rate rewards C_star C_h u t q z,
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
        rate rewards C_star C_h u t z q hfuture with
  | some inputs, some c =>
      RecordedRoundMoments.rawEstimate Q (RecordedQueueRun.run Q inputs) c a
  | _, _ => 0

/-- Prior-measurable floor amplitude for the actual future marker, including
the enabled and prior-overflow cases. -/
def futureAmplitude (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) (z : Z) : ℝ :=
  match ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture with
  | some (true, xi) =>
      if priorClear rate rewards C_star C_h u t q z then
        QuantizedRecordingMoments.quantizedValue
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta (xi a)
          (((rewards q a).val : ℝ) / (D p : ℝ))
      else 0
  | _ => 0

/-- The retained first raw moment, using the same future marker coefficient. -/
def futureMomentOne (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) (z : Z) : ℝ :=
  futureAmplitude rate rewards C_star C_h u t q hfuture a z *
    ReferenceFirstCollectionRenewalFutureRecordingLaw.futureCoefficient
      rate rewards C_star C_h u t (some (some a)) z q hfuture

/-- The retained second raw moment, using the same coefficient rather than its
square. -/
def futureMomentTwo (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) (z : Z) : ℝ :=
  (futureAmplitude rate rewards C_star C_h u t q hfuture a z) ^ 2 *
    ReferenceFirstCollectionRenewalFutureRecordingLaw.futureCoefficient
      rate rewards C_star C_h u t (some (some a)) z q hfuture

/-- The arm fiber of the actual future physical marker. -/
def futureArmTest (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) (z : Z) : ℝ :=
  ReferenceFirstCollectionRenewalFutureRecordingLaw.futureTest
    rate rewards C_star C_h u t (some (some a)) z q hfuture

private theorem measurable_option_elim {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (f : α → β) (hf : Measurable f) (b : β) :
    Measurable (fun o : Option α => o.elim b f) := by
  have hsum : Measurable (fun o : Option α => Equiv.optionEquivSumPUnit α o) :=
    comap_measurable _
  convert (hf.sumElim measurable_const).comp hsum using 1
  funext o
  cases o <;> rfl

private theorem integrable_of_measurable_norm_le_const {X : Type*}
    [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (c : ℝ)
    (hb : ∀ x, ‖f x‖ ≤ c) : Integrable f μ :=
  (integrable_const c).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)

private theorem measurable_quantizedReward (q : Fin p.T) (a : Fin p.K) :
    Measurable (fun xi : Fin p.K → ℝ =>
      QuantizedRecordingMoments.quantizedValue
        (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
        (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta (xi a)
        (((rewards q a).val : ℝ) / (D p : ℝ))) := by
  change Measurable (fun xi : Fin p.K → ℝ =>
    (Nat.floor (((D p : ℝ) * rate.eta.val *
      (((rewards q a).val : ℝ) / (D p : ℝ))) / xi a) : ℝ) /
      (rate.eta.val * (D p : ℝ)))
  have hxi : Measurable (fun xi : Fin p.K → ℝ => xi a) := measurable_pi_apply a
  have harg : Measurable (fun xi : Fin p.K → ℝ =>
      ((D p : ℝ) * rate.eta.val *
        (((rewards q a).val : ℝ) / (D p : ℝ))) / xi a) :=
    (measurable_const : Measurable (fun _ : Fin p.K → ℝ =>
      (D p : ℝ) * rate.eta.val *
        (((rewards q a).val : ℝ) / (D p : ℝ)))).div hxi
  have hfloor : Measurable (fun xi : Fin p.K → ℝ =>
      Nat.floor (((D p : ℝ) * rate.eta.val *
        (((rewards q a).val : ℝ) / (D p : ℝ))) / xi a)) :=
    Nat.measurable_floor.comp harg
  have hcast : Measurable (fun xi : Fin p.K → ℝ =>
      (Nat.floor (((D p : ℝ) * rate.eta.val *
        (((rewards q a).val : ℝ) / (D p : ℝ))) / xi a) : ℝ)) :=
    (measurable_of_countable _).comp hfloor
  exact hcast.div_const _

private theorem rewardAt_bounds (q : Fin p.T) (a : Fin p.K) :
    (((rewards q a).val : ℝ) / (D p : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
  have hD : 0 < (D p : ℝ) := by exact_mod_cast (D_pos p)
  have hv0 : (0 : ℝ) ≤ (rewards q a).val := Nat.cast_nonneg _
  have hvD : ((rewards q a).val : ℝ) ≤ (D p : ℝ) := by
    have hn : (rewards q a).val ≤ D p := Nat.le_of_lt_succ (rewards q a).isLt
    exact_mod_cast hn
  constructor
  · exact div_nonneg hv0 hD.le
  · exact (div_le_iff₀ hD).2 (by simpa using hvD)

/-- The optional prior readout is exactly the existing run state whenever its
whole calendar prefix is present. -/
theorem priorReadout_eq_of_inputs (q : Fin p.T) (z : Z)
    (inputs : List (RecordedQueueRun.RoundInput p.K))
    (hinputs : prefixInputs rate rewards C_star C_h u t q z = some inputs) :
    priorReadout rate rewards C_star C_h u t q z =
      some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.run Q inputs)) := by
  unfold prefixInputs at hinputs
  change ((ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
      rate rewards C_star C_h u t q.val z).mapM id).map
        (fun xs => ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run Q xs)) = _
  rw [hinputs]
  rfl

private theorem priorReadout_none_of_inputs_none (q : Fin p.T) (z : Z)
    (hnone : prefixInputs rate rewards C_star C_h u t q z = none) :
    priorReadout rate rewards C_star C_h u t q z = none := by
  unfold prefixInputs at hnone
  change ((ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
      rate rewards C_star C_h u t q.val z).mapM id).map
        (fun xs => ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run Q xs)) = none
  rw [hnone]
  rfl

private theorem priorClear_false_of_inputs_none (q : Fin p.T) (z : Z)
    (hnone : prefixInputs rate rewards C_star C_h u t q z = none) :
    priorClear rate rewards C_star C_h u t q z = false := by
  unfold priorClear
  rw [priorReadout_none_of_inputs_none rate rewards C_star C_h u t q z hnone]

private theorem priorClear_eq_of_inputs (q : Fin p.T) (z : Z)
    (inputs : List (RecordedQueueRun.RoundInput p.K))
    (hinputs : prefixInputs rate rewards C_star C_h u t q z = some inputs) :
    priorClear rate rewards C_star C_h u t q z =
      !((RecordedQueueRun.run Q inputs).overflow) := by
  unfold priorClear
  rw [priorReadout_eq_of_inputs rate rewards C_star C_h u t q z inputs hinputs]
  cases hflag : (RecordedQueueRun.run Q inputs).overflow <;>
    simp [ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout, hflag]

private theorem futureParameters_present
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) (z : Z)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = some c) :
    ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture = some (c.enabled, c.rate) := by
  have hr := ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_readout
    rate rewards C_star C_h u t z q hfuture
  cases hv : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture with
  | none =>
      rw [hv] at hr
      simp only at hr
      have hbad : (some c : Option (RecordedQueueRun.RoundInput p.K)) = none :=
        hc.symm.trans hr.2
      cases hbad
  | some data =>
      rcases data with ⟨parameters, view, code⟩
      rw [hv] at hr
      obtain ⟨cell, snapshot, valid, hcell, hparameters, hrate, _, _, _⟩ := hr
      have hcell_eq : cell = c := Option.some.inj (hcell.symm.trans hc)
      have hparameters' : parameters = some (c.enabled, c.rate) := by
        rw [← hcell_eq]
        exact hparameters
      simp [ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters, hv,
        hparameters']

/-- A present actual slice cell agrees with the unmasked current physical
calendar readout, by lookup in the same original suffix. -/
theorem futureSliceCell_eq_unmasked (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (z : Z) (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = some c) :
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureCell
      rate rewards C_star C_h u t q z = some c := by
  have hstart : ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
      rate rewards C_star C_h u t z =
      ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z := by
    change ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h =
      ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z
    rw [ReferenceFirstCollectionRenewalIncomingQueuePrefix.start_eq_physicalStart]
  have hlookupV := ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord_lookup
    rate rewards C_star C_h u t z q hfuture
  have hlookupN := ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureRecord_lookup_fields
    rate rewards C_star C_h u t q z hfuture
  have hrecord :
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
        rate rewards C_star C_h u t z q hfuture =
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureRecord
        rate rewards C_star C_h u t q z := by
    have hidx : q.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z =
        q.val - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
          rate rewards C_star C_h u t z := by rw [← hstart]
    change (ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords
        rate rewards C_star C_h u t z)[
      q.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z]? = _ at hlookupV
    have hlookupN' := hlookupN.1
    change (ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
        rate rewards C_star C_h u t z)[
      q.val - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
        rate rewards C_star C_h u t z]? =
          some (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureRecord
            rate rewards C_star C_h u t q z) at hlookupN'
    have hrecords : ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords
        rate rewards C_star C_h u t z =
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
          rate rewards C_star C_h u t z := rfl
    rw [hrecords, hidx] at hlookupV
    exact Option.some.inj (hlookupV.symm.trans hlookupN')
  cases hb : ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch
      rate rewards C_star C_h u t z q hfuture with
  | none =>
      simp [ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell, hb] at hc
  | some branch =>
      have hc' : (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
          (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
            rate rewards C_star C_h u t z q hfuture)).or
          (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
          (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
            rate rewards C_star C_h u t z q hfuture)) = some c := by
        simpa [ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell, hb] using hc
      rw [ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureCell,
        ← hrecord]
      change (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
          (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
            rate rewards C_star C_h u t z q hfuture)).or
          (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
          (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
            rate rewards C_star C_h u t z q hfuture)) = some c
      exact hc'

/-- On a present whole prefix and physical slice cell, the scalar is exactly
the existing run's accepted raw estimate. -/
theorem futureScalar_present_run (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) (z : Z) (inputs : List (RecordedQueueRun.RoundInput p.K))
    (c : RecordedQueueRun.RoundInput p.K)
    (hinputs : prefixInputs rate rewards C_star C_h u t q z = some inputs)
    (hc : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = some c) :
    futureScalar rate rewards C_star C_h u t q hfuture a z =
      RecordedRoundMoments.rawEstimate Q (RecordedQueueRun.run Q inputs) c a := by
  simp [futureScalar, hinputs, hc]

/-- On this same present branch, the successor readout appends the actual
accepted record to the inherited history and retains the first overflow update. -/
theorem futureScalar_present_acceptance (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) (z : Z) (inputs : List (RecordedQueueRun.RoundInput p.K))
    (c : RecordedQueueRun.RoundInput p.K)
    (hinputs : prefixInputs rate rewards C_star C_h u t q z = some inputs)
    (hc : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = some c) :
    futureScalar rate rewards C_star C_h u t q hfuture a z =
        ((RecordedQueueRun.acceptedArrival
          (RecordedQueueRun.acceptedRecord Q (RecordedQueueRun.run Q inputs) c a) : ℝ) /
          ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) ∧
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
        rate rewards C_star C_h u t (q.val + 1) z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c)) ∧
      (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c).records a =
        (RecordedQueueRun.run Q inputs).records a ++
          [RecordedQueueRun.acceptedRecord Q (RecordedQueueRun.run Q inputs) c a] := by
  have hcell := futureSliceCell_eq_unmasked rate rewards C_star C_h u t q hfuture z c hc
  have hread := ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout_succ
    rate rewards C_star C_h u t q z hfuture
  have hprefix : ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
        rate rewards C_star C_h u t q.val z) = some inputs := by
    change (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
      rate rewards C_star C_h u t q.val z).mapM id = some inputs at hinputs
    simpa [ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells] using hinputs
  rw [hprefix, hcell] at hread
  refine ⟨?_, hread, ?_⟩
  · rw [futureScalar_present_run rate rewards C_star C_h u t q hfuture a z inputs c hinputs hc]
    rfl
  · exact ReferenceFirstCollectionRenewalFutureNumericalPrefix.step_records
      rate (RecordedQueueRun.run Q inputs) c a

private theorem futureRate_beta_le (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (control0 : ContinuousLearningRows.TimeControl p) (z : Z) (xi : Fin p.K → ℝ)
    (hp : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture = some (true, xi))
    (a : Fin p.K) : CanonicalRecordingRates.beta p rate.eta.val ≤ xi a := by
  have hsection := ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_marker_section
    rate rewards C_star C_h u t control0 z q hfuture
  cases hv : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture with
  | none =>
      simp [ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters, hv] at hp
  | some data =>
      rcases data with ⟨parameters, view, code⟩
      rw [hv] at hsection
      obtain ⟨enabled, snapshot, valid, hparameters, hcode, hmarker⟩ := hsection
      have hparams : parameters = some (true, xi) := by
        simpa [ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters, hv] using hp
      have henabled : enabled = true := by
        have hpair := Option.some.inj (hparameters.symm.trans hparams)
        exact congrArg Prod.fst hpair
      have hxi : view.payload.rate = xi := by
        have hpair := Option.some.inj (hparameters.symm.trans hparams)
        exact congrArg Prod.snd hpair
      have hcanonical : view.payload.rate =
          CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor := by
        funext b
        exact view.payload.rate_eq_canonical b
      calc
        CanonicalRecordingRates.beta p rate.eta.val ≤
            CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor a :=
          CanonicalRecordingRates.beta_le_xi p rate.eta.property view.payload.anchor a
        _ = view.payload.rate a := (congrFun hcanonical a).symm
        _ = xi a := congrFun hxi a

private theorem futureCell_reward (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (z : Z) (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = some c) :
    c.reward = fun b => ((rewards q b).val : ℝ) / (D p : ℝ) := by
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
      obtain ⟨cell, _, _, hcell, _, _, hreward, _, _⟩ := hread
      have hcell_eq : cell = c := Option.some.inj (hcell.symm.trans hc)
      rw [← hcell_eq]
      exact hreward

private theorem futureArmTest_values (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) (z : Z) :
    futureArmTest rate rewards C_star C_h u t q hfuture a z = 0 ∨
      futureArmTest rate rewards C_star C_h u t q hfuture a z = 1 := by
  unfold futureArmTest ReferenceFirstCollectionRenewalFutureRecordingLaw.futureTest
  split <;> simp_all

private theorem futureAmplitude_eq_of_enabled (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z)
    (xi : Fin p.K → ℝ)
    (hp : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture = some (true, xi))
    (hclear : priorClear rate rewards C_star C_h u t q z = true) :
    futureAmplitude rate rewards C_star C_h u t q hfuture a z =
      QuantizedRecordingMoments.quantizedValue
        (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
        (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta (xi a)
        (((rewards q a).val : ℝ) / (D p : ℝ)) := by
  simp [futureAmplitude, hp, hclear]

private theorem futureAmplitude_zero_of_prior_not_clear (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z)
    (hclear : priorClear rate rewards C_star C_h u t q z = false) :
    futureAmplitude rate rewards C_star C_h u t q hfuture a z = 0 := by
  cases hp : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture with
  | none => simp [futureAmplitude, hp]
  | some parameters =>
      rcases parameters with ⟨enabled, xi⟩
      cases enabled <;> simp [futureAmplitude, hp, hclear]

theorem measurable_futureAmplitude (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) : Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q] (futureAmplitude rate rewards C_star C_h u t
      q hfuture a) := by
  have hparams := ReferenceFirstCollectionRenewalFutureRecordingLaw.measurable_futureParameters
    rate rewards C_star C_h u t control0 q hfuture
  have hread := ReferenceFirstCollectionRenewalFutureNumericalPrefix.measurable_futurePrefixReadout
    rate rewards C_star C_h u t control0 q.val (by omega)
  have hclear : Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q]
      (priorClear rate rewards C_star C_h u t q) := by
    change Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q]
      (fun z : Z => priorClear rate rewards C_star C_h u t q z)
    exact (measurable_of_countable (fun x : Option _ =>
      match x with
      | some (_, (false, _)) => true
      | _ => false)).comp hread
  have hbranch (b : Bool) : Measurable
      (fun v : Bool × (Fin p.K → ℝ) =>
        if v.1 then if b then
          QuantizedRecordingMoments.quantizedValue
            (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
            (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta (v.2 a)
            (((rewards q a).val : ℝ) / (D p : ℝ)) else 0 else 0) := by
    have hbase : Measurable (fun xi : Fin p.K → ℝ =>
        if b then QuantizedRecordingMoments.quantizedValue
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
          (xi a) (((rewards q a).val : ℝ) / (D p : ℝ)) else 0) := by
      cases b with
      | false => simp
      | true => simpa using measurable_quantizedReward rate rewards q a
    exact Measurable.ite (measurable_fst (measurableSet_singleton true))
      (hbase.comp measurable_snd) measurable_const
  have hoption (b : Bool) : Measurable
      (fun o : Option (Bool × (Fin p.K → ℝ)) =>
        o.elim 0 (fun v => if v.1 then if b then
          QuantizedRecordingMoments.quantizedValue
            (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
            (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta (v.2 a)
            (((rewards q a).val : ℝ) / (D p : ℝ)) else 0 else 0)) :=
    measurable_option_elim _ (hbranch b) 0
  have hpair : Measurable (fun v : Option (Bool × (Fin p.K → ℝ)) × Bool =>
      v.1.elim 0 (fun x => if x.1 then if v.2 then
        QuantizedRecordingMoments.quantizedValue
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta (x.2 a)
          (((rewards q a).val : ℝ) / (D p : ℝ)) else 0 else 0)) := by
    refine measurable_from_prod_countable_left ?_
    intro b
    exact hoption b
  have hfun := hpair.comp (hparams.prodMk hclear)
  have heq : futureAmplitude rate rewards C_star C_h u t q hfuture a = fun z =>
      ((ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
        rate rewards C_star C_h u t z q hfuture).elim 0 (fun x =>
          if x.1 then if priorClear rate rewards C_star C_h u t q z then
            QuantizedRecordingMoments.quantizedValue
              (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
              (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta (x.2 a)
              (((rewards q a).val : ℝ) / (D p : ℝ)) else 0 else 0)) := by
    funext z
    cases hp : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
        rate rewards C_star C_h u t z q hfuture with
    | none => simp [futureAmplitude, hp]
    | some pair =>
        rcases pair with ⟨enabled, xi⟩
        cases enabled <;> simp [futureAmplitude, hp]
  rw [heq]
  exact hfun

theorem futureAmplitude_nonneg (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) (z : Z) :
    0 ≤ futureAmplitude rate rewards C_star C_h u t q hfuture a z := by
  cases hp : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture with
  | none => simp [futureAmplitude, hp]
  | some pair =>
      rcases pair with ⟨enabled, xi⟩
      cases enabled with
      | false => simp [futureAmplitude, hp]
      | true =>
          cases hc : priorClear rate rewards C_star C_h u t q z with
          | false => simp [futureAmplitude, hp, hc]
          | true =>
              simp only [futureAmplitude, hp, hc, ite_true]
              exact QuantizedRecordingMoments.quantizedValue_nonneg
                (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
                (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
                (xi a) (((rewards q a).val : ℝ) / (D p : ℝ)) rate.eta.property

private theorem futureAmplitude_le_inv_beta_of_enabled (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) (z : Z) (xi : Fin p.K → ℝ)
    (hp : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture = some (true, xi))
    (hclear : priorClear rate rewards C_star C_h u t q z = true) :
    futureAmplitude rate rewards C_star C_h u t q hfuture a z ≤
      1 / CanonicalRecordingRates.beta p rate.eta.val := by
  have hbeta := futureRate_beta_le rate rewards C_star C_h u t q hfuture control0 z xi hp a
  have hbetapos := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hxi : 0 < xi a := lt_of_lt_of_le hbetapos hbeta
  have hquant := QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta (xi a)
    (((rewards q a).val : ℝ) / (D p : ℝ))
    (CanonicalRecordingRates.beta p rate.eta.val)
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).D_pos
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta_pos hxi
    (rewardAt_bounds (rewards := rewards) (q := q) (a := a)) hbetapos hbeta
  have hQD : (ReferenceFirstLaunchNumericalCell.queueParameters rate).D = D p := rfl
  have hQeta : (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta = rate.eta.val := rfl
  simpa [futureAmplitude, hp, hclear, hQD, hQeta] using hquant

theorem futureAmplitude_le_inv_beta (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) (z : Z) :
    futureAmplitude rate rewards C_star C_h u t q hfuture a z ≤
      1 / CanonicalRecordingRates.beta p rate.eta.val := by
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  cases hp : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture with
  | none => simp [futureAmplitude, hp]; positivity
  | some pair =>
      rcases pair with ⟨enabled, xi⟩
      cases enabled with
      | false => simp [futureAmplitude, hp]; positivity
      | true =>
          cases hc : priorClear rate rewards C_star C_h u t q z with
          | false => simp [futureAmplitude, hp, hc]; positivity
          | true =>
            exact futureAmplitude_le_inv_beta_of_enabled rate rewards C_star C_h u t
              q hfuture control0 a z xi hp hc

theorem futureAmplitude_bounds (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (control0 : ContinuousLearningRows.TimeControl p) (a : Fin p.K) (z : Z) :
    0 ≤ futureAmplitude rate rewards C_star C_h u t q hfuture a z ∧
      futureAmplitude rate rewards C_star C_h u t q hfuture a z ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val :=
  ⟨futureAmplitude_nonneg rate rewards C_star C_h u t q hfuture a z,
    futureAmplitude_le_inv_beta rate rewards C_star C_h u t q hfuture control0 a z⟩

theorem measurable_futureMomentOne (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) : Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q] (futureMomentOne rate rewards C_star C_h u t
      q hfuture a) :=
  (measurable_futureAmplitude rate rewards C_star C_h u t q hfuture control0 a).mul
    (ReferenceFirstCollectionRenewalFutureRecordingLaw.measurable_futureCoefficient
      rate rewards C_star C_h u t control0 q hfuture (some (some a)))

theorem measurable_futureMomentTwo (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) : Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q] (futureMomentTwo rate rewards C_star C_h u t
      q hfuture a) := by
  exact ((measurable_futureAmplitude rate rewards C_star C_h u t q hfuture control0 a).pow_const 2).mul
    (ReferenceFirstCollectionRenewalFutureRecordingLaw.measurable_futureCoefficient
      rate rewards C_star C_h u t control0 q hfuture (some (some a)))

theorem futureMoments_retained_formula (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z)
    (xi : Fin p.K → ℝ)
    (hp : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture = some (true, xi))
    (hclear : priorClear rate rewards C_star C_h u t q z = true) :
    futureMomentOne rate rewards C_star C_h u t q hfuture a z =
        xi a * QuantizedRecordingMoments.quantizedValue
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta (xi a)
          (((rewards q a).val : ℝ) / (D p : ℝ)) ∧
      futureMomentTwo rate rewards C_star C_h u t q hfuture a z =
        xi a * (QuantizedRecordingMoments.quantizedValue
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta (xi a)
          (((rewards q a).val : ℝ) / (D p : ℝ))) ^ 2 := by
  have hamp := futureAmplitude_eq_of_enabled rate rewards C_star C_h u t q hfuture a z xi hp hclear
  have hcoef : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureCoefficient
      rate rewards C_star C_h u t (some (some a)) z q hfuture = xi a := by
    change ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters
      (some (some a))
      (ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
        rate rewards C_star C_h u t z q hfuture) = xi a
    rw [hp]
    rfl
  constructor
  · change futureAmplitude rate rewards C_star C_h u t q hfuture a z *
      ReferenceFirstCollectionRenewalFutureRecordingLaw.futureCoefficient
        rate rewards C_star C_h u t (some (some a)) z q hfuture = _
    rw [hamp, hcoef]
    ring
  · change (futureAmplitude rate rewards C_star C_h u t q hfuture a z) ^ 2 *
      ReferenceFirstCollectionRenewalFutureRecordingLaw.futureCoefficient
        rate rewards C_star C_h u t (some (some a)) z q hfuture = _
    rw [hamp, hcoef]
    ring

theorem futureMoments_retained_bounds (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) (z : Z)
    (xi : Fin p.K → ℝ)
    (hp : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture = some (true, xi))
    (hclear : priorClear rate rewards C_star C_h u t q z = true) :
    (((rewards q a).val : ℝ) / (D p : ℝ)) -
        xi a / ((ReferenceFirstLaunchNumericalCell.queueParameters rate).eta *
          ((ReferenceFirstLaunchNumericalCell.queueParameters rate).D : ℝ)) ≤
        futureMomentOne rate rewards C_star C_h u t q hfuture a z ∧
      futureMomentOne rate rewards C_star C_h u t q hfuture a z ≤
        (((rewards q a).val : ℝ) / (D p : ℝ)) ∧
      0 ≤ futureMomentTwo rate rewards C_star C_h u t q hfuture a z ∧
      futureMomentTwo rate rewards C_star C_h u t q hfuture a z ≤
        (((rewards q a).val : ℝ) / (D p : ℝ)) ^ 2 / xi a := by
  have hbeta := futureRate_beta_le rate rewards C_star C_h u t q hfuture control0 z xi hp a
  have hbetapos := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hxi : 0 < xi a := lt_of_lt_of_le hbetapos hbeta
  have hr : (((rewards q a).val : ℝ) / (D p : ℝ)) ∈ Set.Icc (0 : ℝ) 1 :=
    rewardAt_bounds (rewards := rewards) (q := q) (a := a)
  have hround := QuantizedRecordingMoments.quantizedValue_roundingError
    (D p) rate.eta.val (xi a) (((rewards q a).val : ℝ) / (D p : ℝ))
    (D_pos p) rate.eta.property hxi hr
  have hfirst := QuantizedRecordingMoments.quantizedValue_firstMoment_le
    (D p) rate.eta.val (xi a) (((rewards q a).val : ℝ) / (D p : ℝ))
    (D_pos p) rate.eta.property hxi hr
  have hsecond := QuantizedRecordingMoments.quantizedValue_secondMoment_le
    (D p) rate.eta.val (xi a) (((rewards q a).val : ℝ) / (D p : ℝ))
    (D_pos p) rate.eta.property hxi hr
  have hformula := futureMoments_retained_formula rate rewards C_star C_h u t q hfuture a z xi hp hclear
  have hQD : (ReferenceFirstLaunchNumericalCell.queueParameters rate).D = D p := rfl
  have hQeta : (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta = rate.eta.val := rfl
  constructor
  · rw [hformula.1]
    simpa [hQD, hQeta] using hround
  constructor
  · rw [hformula.1]
    simpa [hQD, hQeta] using hfirst
  constructor
  · rw [hformula.2]
    positivity
  · rw [hformula.2]
    simpa [hQD, hQeta] using hsecond

/-- The retained rounding bounds apply on the actual present enabled cell and
the actual present nonoverflowing whole-prefix run. -/
theorem futureMoments_present_enabled_bounds (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) (z : Z) (inputs : List (RecordedQueueRun.RoundInput p.K))
    (c : RecordedQueueRun.RoundInput p.K)
    (hinputs : prefixInputs rate rewards C_star C_h u t q z = some inputs)
    (hcell : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = some c)
    (henabled : c.enabled = true)
    (hoverflow : (RecordedQueueRun.run Q inputs).overflow = false) :
    (((rewards q a).val : ℝ) / (D p : ℝ)) - c.rate a /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).eta *
          ((ReferenceFirstLaunchNumericalCell.queueParameters rate).D : ℝ)) ≤
        futureMomentOne rate rewards C_star C_h u t q hfuture a z ∧
      futureMomentOne rate rewards C_star C_h u t q hfuture a z ≤
        (((rewards q a).val : ℝ) / (D p : ℝ)) ∧
      0 ≤ futureMomentTwo rate rewards C_star C_h u t q hfuture a z ∧
      futureMomentTwo rate rewards C_star C_h u t q hfuture a z ≤
        (((rewards q a).val : ℝ) / (D p : ℝ)) ^ 2 / c.rate a := by
  have hp := futureParameters_present rate rewards C_star C_h u t q hfuture z c hcell
  have hp' : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture = some (true, c.rate) := by
    simpa [henabled] using hp
  have hclear : priorClear rate rewards C_star C_h u t q z = true := by
    rw [priorClear_eq_of_inputs rate rewards C_star C_h u t q z inputs hinputs,
      hoverflow]
    rfl
  simpa using futureMoments_retained_bounds rate rewards C_star C_h u t q hfuture
    control0 a z c.rate hp' hclear

theorem futureMoments_present_enabled_formula (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z)
    (inputs : List (RecordedQueueRun.RoundInput p.K))
    (c : RecordedQueueRun.RoundInput p.K)
    (hinputs : prefixInputs rate rewards C_star C_h u t q z = some inputs)
    (hcell : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = some c)
    (henabled : c.enabled = true)
    (hoverflow : (RecordedQueueRun.run Q inputs).overflow = false) :
    futureMomentOne rate rewards C_star C_h u t q hfuture a z =
        c.rate a * QuantizedRecordingMoments.quantizedValue
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta (c.rate a)
          (((rewards q a).val : ℝ) / (D p : ℝ)) ∧
      futureMomentTwo rate rewards C_star C_h u t q hfuture a z =
        c.rate a * (QuantizedRecordingMoments.quantizedValue
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta (c.rate a)
          (((rewards q a).val : ℝ) / (D p : ℝ))) ^ 2 := by
  have hp := futureParameters_present rate rewards C_star C_h u t q hfuture z c hcell
  have hp' : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture = some (true, c.rate) := by
    simpa [henabled] using hp
  have hclear : priorClear rate rewards C_star C_h u t q z = true := by
    rw [priorClear_eq_of_inputs rate rewards C_star C_h u t q z inputs hinputs,
      hoverflow]
    rfl
  exact futureMoments_retained_formula rate rewards C_star C_h u t q hfuture a z
    c.rate hp' hclear

theorem futureMomentOne_nonneg (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) (z : Z) :
    0 ≤ futureMomentOne rate rewards C_star C_h u t q hfuture a z := by
  exact mul_nonneg (futureAmplitude_nonneg rate rewards C_star C_h u t q hfuture a z)
    (ReferenceFirstCollectionRenewalFutureRecordingLaw.futureCoefficient_bounds
      rate rewards C_star C_h u t (some (some a)) z q hfuture).1

theorem futureMomentOne_le_one (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) (z : Z) :
    futureMomentOne rate rewards C_star C_h u t q hfuture a z ≤ 1 := by
  cases hp : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture with
  | none => simp [futureMomentOne, futureAmplitude, hp,
      ReferenceFirstCollectionRenewalFutureRecordingLaw.futureCoefficient,
      ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
  | some pair =>
      rcases pair with ⟨enabled, xi⟩
      cases enabled with
      | false => simp [futureMomentOne, futureAmplitude, hp,
          ReferenceFirstCollectionRenewalFutureRecordingLaw.futureCoefficient,
          ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
      | true =>
          cases hc : priorClear rate rewards C_star C_h u t q z with
          | false => simp [futureMomentOne, futureAmplitude, hp, hc,
              ReferenceFirstCollectionRenewalFutureRecordingLaw.futureCoefficient,
              ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
          | true =>
              have hbound := futureMoments_retained_bounds rate rewards C_star C_h u t
                q hfuture control0 a z xi hp hc
              exact hbound.2.1.trans
                (rewardAt_bounds (rewards := rewards) (q := q) (a := a)).2

theorem futureMomentTwo_nonneg (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) (z : Z) :
    0 ≤ futureMomentTwo rate rewards C_star C_h u t q hfuture a z := by
  exact mul_nonneg (sq_nonneg _)
    (ReferenceFirstCollectionRenewalFutureRecordingLaw.futureCoefficient_bounds
      rate rewards C_star C_h u t (some (some a)) z q hfuture).1

theorem futureMomentTwo_le_inv_beta (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (control0 : ContinuousLearningRows.TimeControl p) (a : Fin p.K) (z : Z) :
    futureMomentTwo rate rewards C_star C_h u t q hfuture a z ≤
      1 / CanonicalRecordingRates.beta p rate.eta.val := by
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  cases hp : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture with
  | none =>
      simp [futureMomentTwo, futureAmplitude, hp,
        ReferenceFirstCollectionRenewalFutureRecordingLaw.futureCoefficient,
        ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
      positivity
  | some pair =>
      rcases pair with ⟨enabled, xi⟩
      cases enabled with
      | false =>
          simp [futureMomentTwo, futureAmplitude, hp,
            ReferenceFirstCollectionRenewalFutureRecordingLaw.futureCoefficient,
            ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
          exact hbeta.le
      | true =>
          cases hc : priorClear rate rewards C_star C_h u t q z with
          | false =>
              simp [futureMomentTwo, futureAmplitude, hp, hc,
                ReferenceFirstCollectionRenewalFutureRecordingLaw.futureCoefficient,
                ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
              exact hbeta.le
          | true =>
              have hrate := futureRate_beta_le rate rewards C_star C_h u t q hfuture
                control0 z xi hp a
              have hbound := futureMoments_retained_bounds rate rewards C_star C_h u t
                q hfuture control0 a z xi hp hc
              calc
                futureMomentTwo rate rewards C_star C_h u t q hfuture a z ≤
                    (((rewards q a).val : ℝ) / (D p : ℝ)) ^ 2 / xi a := hbound.2.2.2
                _ ≤ 1 / xi a := by
                  apply div_le_div_of_nonneg_right _ (le_of_lt (lt_of_lt_of_le hbeta hrate))
                  nlinarith [(rewardAt_bounds (rewards := rewards) (q := q) (a := a)).2,
                    (rewardAt_bounds (rewards := rewards) (q := q) (a := a)).1]
                _ ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val :=
                  one_div_le_one_div_of_le hbeta hrate

theorem futureMomentOne_bounds (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) (z : Z) :
    0 ≤ futureMomentOne rate rewards C_star C_h u t q hfuture a z ∧
      futureMomentOne rate rewards C_star C_h u t q hfuture a z ≤ 1 :=
  ⟨futureMomentOne_nonneg rate rewards C_star C_h u t q hfuture a z,
    futureMomentOne_le_one rate rewards C_star C_h u t q hfuture control0 a z⟩

theorem futureMomentTwo_bounds (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) (z : Z) :
    0 ≤ futureMomentTwo rate rewards C_star C_h u t q hfuture a z ∧
      futureMomentTwo rate rewards C_star C_h u t q hfuture a z ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val :=
  ⟨futureMomentTwo_nonneg rate rewards C_star C_h u t q hfuture a z,
    futureMomentTwo_le_inv_beta rate rewards C_star C_h u t q hfuture control0 a z⟩

/-- The actual run arrival is the actual marker fiber times its prior
floor-quantized amplitude, with every option and overflow case retained. -/
theorem futureScalar_eq_test_mul_amplitude (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z) :
    futureScalar rate rewards C_star C_h u t q hfuture a z =
      futureArmTest rate rewards C_star C_h u t q hfuture a z *
        futureAmplitude rate rewards C_star C_h u t q hfuture a z := by
  cases hi : prefixInputs rate rewards C_star C_h u t q z with
  | none =>
      have hclear := priorClear_false_of_inputs_none rate rewards C_star C_h u t q z hi
      have hamp := futureAmplitude_zero_of_prior_not_clear rate rewards C_star C_h u t
        q hfuture a z hclear
      rw [futureScalar, hi, hamp]
      simp
  | some inputs =>
      cases hc : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
          rate rewards C_star C_h u t z q hfuture with
      | none =>
          have htest : futureArmTest rate rewards C_star C_h u t q hfuture a z = 0 := by
            simp [futureArmTest, ReferenceFirstCollectionRenewalFutureRecordingLaw.futureTest,
              ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker, hc]
          simp [futureScalar, hi, hc, htest]
      | some c =>
          have hp := futureParameters_present rate rewards C_star C_h u t q hfuture z c hc
          have hreward := futureCell_reward rate rewards C_star C_h u t q hfuture z c hc
          have hclear := priorClear_eq_of_inputs rate rewards C_star C_h u t q z inputs hi
          cases hoverflow : (RecordedQueueRun.run Q inputs).overflow with
          | true =>
              have hclear' : priorClear rate rewards C_star C_h u t q z = false := by
                rw [hclear, hoverflow]
                rfl
              have hzero := RecordedRoundMoments.rawEstimate_eq_zero_after_overflow
                Q (RecordedQueueRun.run Q inputs) c a hoverflow
              have hamp := futureAmplitude_zero_of_prior_not_clear rate rewards C_star C_h u t
                q hfuture a z hclear'
              simp [futureScalar, hi, hc, hzero, hamp]
          | false =>
              cases henabled : c.enabled with
              | false =>
                  have hzero := RecordedRoundMoments.rawEstimate_eq_zero_of_disabled
                    Q (RecordedQueueRun.run Q inputs) c a henabled
                  simp [futureScalar, hi, hc, futureAmplitude, hp, hzero,
                    henabled]
              | true =>
                  have hclear' : priorClear rate rewards C_star C_h u t q z = true := by
                    rw [hclear, hoverflow]
                    rfl
                  have hnorm := RecordedRoundMoments.rawEstimate_eq_normalizedQuantizedArrival_of_enabled
                    Q (RecordedQueueRun.run Q inputs) c a henabled hoverflow
                  have hp' : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
                      rate rewards C_star C_h u t z q hfuture = some (true, c.rate) := by
                    simpa [henabled] using hp
                  by_cases hrecorded : c.recordedArm = some a
                  · have hquant := RecordedRoundMoments.normalizedQuantizedArrival_eq_quantizedValue_of_recorded
                      Q c a hrecorded
                    have hamp := futureAmplitude_eq_of_enabled rate rewards C_star C_h u t
                      q hfuture a z c.rate hp' hclear'
                    have htest : futureArmTest rate rewards C_star C_h u t q hfuture a z = 1 := by
                      simp [futureArmTest, ReferenceFirstCollectionRenewalFutureRecordingLaw.futureTest,
                        ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker,
                        hc, hrecorded]
                    simp only [futureScalar, hi, hc]
                    rw [hnorm, hquant, hreward, hamp, htest]
                    simp
                  · have hzero : RecordedQueueRun.quantizedArrival Q c a = 0 :=
                      RecordedQueueRun.quantizedArrival_eq_zero Q c a hrecorded
                    have htest : futureArmTest rate rewards C_star C_h u t q hfuture a z = 0 := by
                      simp [futureArmTest, ReferenceFirstCollectionRenewalFutureRecordingLaw.futureTest,
                        ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker,
                        hc, hrecorded]
                    simp only [futureScalar, hi, hc]
                    rw [hnorm]
                    simp [RecordedRoundMoments.normalizedQuantizedArrival, hzero, htest]

/-- Squaring the accepted raw value keeps the same Bernoulli marker and
squares only its prior-measurable amplitude. -/
theorem futureScalar_sq_eq_amplitude_sq_mul_test (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z) :
    (futureScalar rate rewards C_star C_h u t q hfuture a z) ^ 2 =
      (futureAmplitude rate rewards C_star C_h u t q hfuture a z) ^ 2 *
        futureArmTest rate rewards C_star C_h u t q hfuture a z := by
  rw [futureScalar_eq_test_mul_amplitude rate rewards C_star C_h u t q hfuture a z]
  rcases futureArmTest_values rate rewards C_star C_h u t q hfuture a z with h | h
  · simp [h]
  · rw [h]
    ring

theorem measurable_futureArmTest (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) : Measurable (futureArmTest rate rewards C_star C_h u t
      q hfuture a) := by
  have hm := ReferenceFirstCollectionRenewalFutureRecordingLaw.measurable_futureMarker
    rate rewards C_star C_h u t control0 q hfuture
  change Measurable (fun z : Z => if
    ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureMarker
      rate rewards C_star C_h u t z q hfuture = some (some a) then (1 : ℝ) else 0)
  exact (measurable_of_countable (fun m : Option (Option (Fin p.K)) =>
    if m = some (some a) then (1 : ℝ) else 0)).comp hm

theorem measurable_futureScalar (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) : Measurable (futureScalar rate rewards C_star C_h u t
      q hfuture a) := by
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hamp := (measurable_futureAmplitude rate rewards C_star C_h u t
    q hfuture control0 a).mono hfield le_rfl
  have htest := measurable_futureArmTest rate rewards C_star C_h u t q hfuture control0 a
  have heq : futureScalar rate rewards C_star C_h u t q hfuture a = fun z =>
      futureArmTest rate rewards C_star C_h u t q hfuture a z *
        futureAmplitude rate rewards C_star C_h u t q hfuture a z := by
    funext z
    exact futureScalar_eq_test_mul_amplitude rate rewards C_star C_h u t q hfuture a z
  rw [heq]
  exact htest.mul hamp

theorem measurable_futureScalar_sq (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) : Measurable (fun z =>
      (futureScalar rate rewards C_star C_h u t q hfuture a z) ^ 2) :=
  (measurable_futureScalar rate rewards C_star C_h u t q hfuture control0 a).pow_const 2

theorem futureArmTest_bounds (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) (z : Z) :
    0 ≤ futureArmTest rate rewards C_star C_h u t q hfuture a z ∧
      futureArmTest rate rewards C_star C_h u t q hfuture a z ≤ 1 := by
  rcases futureArmTest_values rate rewards C_star C_h u t q hfuture a z with h | h
  · simp [h]
  · simp [h]

theorem futureScalar_bounds (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (control0 : ContinuousLearningRows.TimeControl p) (a : Fin p.K) (z : Z) :
    0 ≤ futureScalar rate rewards C_star C_h u t q hfuture a z ∧
      futureScalar rate rewards C_star C_h u t q hfuture a z ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  rw [futureScalar_eq_test_mul_amplitude rate rewards C_star C_h u t q hfuture a z]
  rcases futureArmTest_values rate rewards C_star C_h u t q hfuture a z with htest | htest
  · constructor
    · simp [htest]
    · simpa [htest] using (one_div_nonneg.mpr hbeta.le)
  · rw [htest]
    simpa using futureAmplitude_bounds rate rewards C_star C_h u t q hfuture control0 a z

theorem futureAmplitude_integrable (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) : Integrable (futureAmplitude rate rewards C_star C_h u t
      q hfuture a) ν := by
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hmeas := (measurable_futureAmplitude rate rewards C_star C_h u t
    q hfuture control0 a).mono hfield le_rfl
  exact integrable_of_measurable_norm_le_const _ hmeas
    (1 / CanonicalRecordingRates.beta p rate.eta.val) (by
      intro z
      rw [Real.norm_eq_abs, abs_of_nonneg
        (futureAmplitude_bounds rate rewards C_star C_h u t q hfuture control0 a z).1]
      exact (futureAmplitude_bounds rate rewards C_star C_h u t q hfuture control0 a z).2)

theorem futureScalar_integrable (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) : Integrable (futureScalar rate rewards C_star C_h u t
      q hfuture a) ν := by
  exact integrable_of_measurable_norm_le_const _
    (measurable_futureScalar rate rewards C_star C_h u t q hfuture control0 a)
    (1 / CanonicalRecordingRates.beta p rate.eta.val) (by
      intro z
      rw [Real.norm_eq_abs, abs_of_nonneg
        (futureScalar_bounds rate rewards C_star C_h u t q hfuture control0 a z).1]
      exact (futureScalar_bounds rate rewards C_star C_h u t q hfuture control0 a z).2)

theorem futureScalar_sq_integrable (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) : Integrable (fun z =>
      (futureScalar rate rewards C_star C_h u t q hfuture a z) ^ 2) ν := by
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hbound (z : Z) :
      ‖(futureScalar rate rewards C_star C_h u t q hfuture a z) ^ 2‖ ≤
        (1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hs := futureScalar_bounds rate rewards C_star C_h u t q hfuture control0 a z
    nlinarith
  exact integrable_of_measurable_norm_le_const _
    (measurable_futureScalar_sq rate rewards C_star C_h u t q hfuture control0 a)
    ((1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2) hbound

theorem futureMomentOne_integrable (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) : Integrable (futureMomentOne rate rewards C_star C_h u t
      q hfuture a) ν := by
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hmeas := (measurable_futureMomentOne rate rewards C_star C_h u t
    q hfuture control0 a).mono hfield le_rfl
  exact integrable_of_measurable_norm_le_const _ hmeas 1 (by
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg
      (futureMomentOne_bounds rate rewards C_star C_h u t q hfuture control0 a z).1]
    exact (futureMomentOne_bounds rate rewards C_star C_h u t q hfuture control0 a z).2)

theorem futureMomentTwo_integrable (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) : Integrable (futureMomentTwo rate rewards C_star C_h u t
      q hfuture a) ν := by
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hmeas := (measurable_futureMomentTwo rate rewards C_star C_h u t
    q hfuture control0 a).mono hfield le_rfl
  exact integrable_of_measurable_norm_le_const _ hmeas
    (1 / CanonicalRecordingRates.beta p rate.eta.val) (by
      intro z
      rw [Real.norm_eq_abs, abs_of_nonneg
        (futureMomentTwo_bounds rate rewards C_star C_h u t q hfuture control0 a z).1]
      exact (futureMomentTwo_bounds rate rewards C_star C_h u t q hfuture control0 a z).2)

theorem futureScalar_condExp (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) :
    ν[(fun z => futureScalar rate rewards C_star C_h u t q hfuture a z) |
      ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q] =ᵐ[ν]
      fun z => futureMomentOne rate rewards C_star C_h u t q hfuture a z := by
  let amp := futureAmplitude rate rewards C_star C_h u t q hfuture a
  let test := futureArmTest rate rewards C_star C_h u t q hfuture a
  have heq : (fun z => futureScalar rate rewards C_star C_h u t q hfuture a z) =
      fun z => amp z * test z := by
    funext z
    exact (futureScalar_eq_test_mul_amplitude rate rewards C_star C_h u t
      q hfuture a z).trans (by ring)
  have hamp : Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q] amp :=
    measurable_futureAmplitude rate rewards C_star C_h u t q hfuture control0 a
  have hprod : Integrable (fun z => amp z * test z) ν :=
    (futureScalar_integrable rate rewards C_star C_h u t q hfuture control0 a).congr
      (Filter.Eventually.of_forall fun z => congrFun heq z)
  have htest := ReferenceFirstCollectionRenewalFutureRecordingLaw.integrable_futureTest
    rate rewards C_star C_h u t control0 q hfuture (some (some a))
  have hpull := condExp_mul_of_stronglyMeasurable_left
    hamp.stronglyMeasurable hprod htest
  have hmarker := ReferenceFirstCollectionRenewalFutureRecordingLaw.futureMarker_condExp
    rate rewards C_star C_h u t control0 q hfuture (some (some a))
  calc
    _ =ᵐ[ν] ν[(fun z => amp z * test z) |
      ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q] :=
      condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun heq z)
    _ =ᵐ[ν] (fun z => amp z * ν[test |
      ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q] z) := hpull
    _ =ᵐ[ν] fun z => futureMomentOne rate rewards C_star C_h u t q hfuture a z := by
      filter_upwards [hmarker] with z hz
      change amp z * ν[(fun w => ReferenceFirstCollectionRenewalFutureRecordingLaw.futureTest
        rate rewards C_star C_h u t (some (some a)) w q hfuture) |
        ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
          rate rewards C_star C_h u t control0 q] z =
        futureMomentOne rate rewards C_star C_h u t q hfuture a z
      rw [hz]
      rfl

theorem futureScalar_sq_condExp (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) :
    ν[(fun z => (futureScalar rate rewards C_star C_h u t q hfuture a z) ^ 2) |
      ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q] =ᵐ[ν]
      fun z => futureMomentTwo rate rewards C_star C_h u t q hfuture a z := by
  let amp := futureAmplitude rate rewards C_star C_h u t q hfuture a
  let test := futureArmTest rate rewards C_star C_h u t q hfuture a
  have heq : (fun z => (futureScalar rate rewards C_star C_h u t q hfuture a z) ^ 2) =
      fun z => (amp z) ^ 2 * test z := by
    funext z
    exact futureScalar_sq_eq_amplitude_sq_mul_test rate rewards C_star C_h u t
      q hfuture a z
  have hamp : Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q] amp :=
    measurable_futureAmplitude rate rewards C_star C_h u t q hfuture control0 a
  have hprod : Integrable (fun z => (amp z) ^ 2 * test z) ν :=
    (futureScalar_sq_integrable rate rewards C_star C_h u t q hfuture control0 a).congr
      (Filter.Eventually.of_forall fun z => congrFun heq z)
  have htest := ReferenceFirstCollectionRenewalFutureRecordingLaw.integrable_futureTest
    rate rewards C_star C_h u t control0 q hfuture (some (some a))
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (hamp.pow_const 2).stronglyMeasurable hprod htest
  have hmarker := ReferenceFirstCollectionRenewalFutureRecordingLaw.futureMarker_condExp
    rate rewards C_star C_h u t control0 q hfuture (some (some a))
  calc
    _ =ᵐ[ν] ν[(fun z => (amp z) ^ 2 * test z) |
      ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q] :=
      condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun heq z)
    _ =ᵐ[ν] (fun z => (amp z) ^ 2 * ν[test |
      ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q] z) := hpull
    _ =ᵐ[ν] fun z => futureMomentTwo rate rewards C_star C_h u t q hfuture a z := by
      filter_upwards [hmarker] with z hz
      change (amp z) ^ 2 * ν[(fun w => ReferenceFirstCollectionRenewalFutureRecordingLaw.futureTest
        rate rewards C_star C_h u t (some (some a)) w q hfuture) |
        ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
          rate rewards C_star C_h u t control0 q] z =
        futureMomentTwo rate rewards C_star C_h u t q hfuture a z
      rw [hz]
      rfl

theorem futureScalar_setIntegral (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) (G : Set Z)
    (hG : MeasurableSet[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q] G) :
    (∫ z in G, futureScalar rate rewards C_star C_h u t q hfuture a z ∂ν) =
      ∫ z in G, futureMomentOne rate rewards C_star C_h u t q hfuture a z ∂ν := by
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hce := futureScalar_condExp rate rewards C_star C_h u t q hfuture control0 a
  have hceG : ∀ᵐ z ∂ν, z ∈ G →
      ν[(fun z => futureScalar rate rewards C_star C_h u t q hfuture a z) |
        ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
          rate rewards C_star C_h u t control0 q] z =
        futureMomentOne rate rewards C_star C_h u t q hfuture a z :=
    hce.mono fun z hz _ => hz
  calc
    _ = ∫ z in G, ν[(fun z => futureScalar rate rewards C_star C_h u t q hfuture a z) |
      ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q] z ∂ν :=
      (setIntegral_condExp hfield
        (futureScalar_integrable rate rewards C_star C_h u t q hfuture control0 a) hG).symm
    _ = _ := setIntegral_congr_ae (hfield _ hG) hceG

theorem futureScalar_sq_setIntegral (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.K) (G : Set Z)
    (hG : MeasurableSet[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q] G) :
    (∫ z in G, (futureScalar rate rewards C_star C_h u t q hfuture a z) ^ 2 ∂ν) =
      ∫ z in G, futureMomentTwo rate rewards C_star C_h u t q hfuture a z ∂ν := by
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hce := futureScalar_sq_condExp rate rewards C_star C_h u t q hfuture control0 a
  have hceG : ∀ᵐ z ∂ν, z ∈ G →
      ν[(fun z => (futureScalar rate rewards C_star C_h u t q hfuture a z) ^ 2) |
        ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
          rate rewards C_star C_h u t control0 q] z =
        futureMomentTwo rate rewards C_star C_h u t q hfuture a z :=
    hce.mono fun z hz _ => hz
  calc
    _ = ∫ z in G, ν[(fun z => (futureScalar rate rewards C_star C_h u t q hfuture a z) ^ 2) |
      ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q] z ∂ν :=
      (setIntegral_condExp hfield
        (futureScalar_sq_integrable rate rewards C_star C_h u t q hfuture control0 a) hG).symm
    _ = _ := setIntegral_congr_ae (hfield _ hG) hceG

theorem futureScalar_zero_of_prefix_absent (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z)
    (hnone : prefixInputs rate rewards C_star C_h u t q z = none) :
    futureScalar rate rewards C_star C_h u t q hfuture a z = 0 ∧
      futureAmplitude rate rewards C_star C_h u t q hfuture a z = 0 ∧
      futureMomentOne rate rewards C_star C_h u t q hfuture a z = 0 ∧
      futureMomentTwo rate rewards C_star C_h u t q hfuture a z = 0 := by
  have hclear := priorClear_false_of_inputs_none rate rewards C_star C_h u t q z hnone
  have hamp := futureAmplitude_zero_of_prior_not_clear rate rewards C_star C_h u t
    q hfuture a z hclear
  refine ⟨?_, hamp, ?_, ?_⟩
  · simp [futureScalar, hnone]
  · simp [futureMomentOne, hamp]
  · simp [futureMomentTwo, hamp]

theorem futureScalar_zero_of_prior_overflow (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z)
    (inputs : List (RecordedQueueRun.RoundInput p.K))
    (hinputs : prefixInputs rate rewards C_star C_h u t q z = some inputs)
    (hoverflow : (RecordedQueueRun.run Q inputs).overflow = true) :
    futureScalar rate rewards C_star C_h u t q hfuture a z = 0 ∧
      futureAmplitude rate rewards C_star C_h u t q hfuture a z = 0 ∧
      futureMomentOne rate rewards C_star C_h u t q hfuture a z = 0 ∧
      futureMomentTwo rate rewards C_star C_h u t q hfuture a z = 0 := by
  have hclear : priorClear rate rewards C_star C_h u t q z = false := by
    rw [priorClear_eq_of_inputs rate rewards C_star C_h u t q z inputs hinputs,
      hoverflow]
    rfl
  have hamp := futureAmplitude_zero_of_prior_not_clear rate rewards C_star C_h u t
    q hfuture a z hclear
  refine ⟨?_, hamp, ?_, ?_⟩
  · rw [futureScalar_eq_test_mul_amplitude rate rewards C_star C_h u t q hfuture a z]
    simp [hamp]
  · simp [futureMomentOne, hamp]
  · simp [futureMomentTwo, hamp]

private theorem futureParameters_none_of_cell_absent (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (z : Z)
    (hcell : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = none) :
    ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture = none := by
  cases hv : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture with
  | none => simp [ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters, hv]
  | some data =>
      rcases data with ⟨parameters, view, code⟩
      have hread := ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_readout
        rate rewards C_star C_h u t z q hfuture
      rw [hv] at hread
      obtain ⟨c, snapshot, valid, hreadCell, _, _, _, _, _⟩ := hread
      have hbad : (some c : Option (RecordedQueueRun.RoundInput p.K)) = none :=
        hreadCell.symm.trans hcell
      cases hbad

theorem futureScalar_zero_of_slice_absent (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z)
    (hcell : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = none) :
    futureScalar rate rewards C_star C_h u t q hfuture a z = 0 ∧
      futureAmplitude rate rewards C_star C_h u t q hfuture a z = 0 ∧
      futureMomentOne rate rewards C_star C_h u t q hfuture a z = 0 ∧
      futureMomentTwo rate rewards C_star C_h u t q hfuture a z = 0 := by
  have hp := futureParameters_none_of_cell_absent rate rewards C_star C_h u t q hfuture z hcell
  have hcoef : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureCoefficient
      rate rewards C_star C_h u t (some (some a)) z q hfuture = 0 := by
    change ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters
      (some (some a))
      (ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
        rate rewards C_star C_h u t z q hfuture) = 0
    rw [hp]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [futureScalar, hcell]
  · simp [futureAmplitude, hp]
  · simp [futureMomentOne, hcoef, futureAmplitude, hp]
  · simp [futureMomentTwo, hcoef, futureAmplitude, hp]

theorem futureScalar_zero_of_disabled_cell (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (z : Z)
    (inputs : List (RecordedQueueRun.RoundInput p.K))
    (c : RecordedQueueRun.RoundInput p.K)
    (hinputs : prefixInputs rate rewards C_star C_h u t q z = some inputs)
    (hcell : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = some c)
    (hdisabled : c.enabled = false) :
    futureScalar rate rewards C_star C_h u t q hfuture a z = 0 ∧
      futureAmplitude rate rewards C_star C_h u t q hfuture a z = 0 ∧
      futureMomentOne rate rewards C_star C_h u t q hfuture a z = 0 ∧
      futureMomentTwo rate rewards C_star C_h u t q hfuture a z = 0 := by
  have hp := futureParameters_present rate rewards C_star C_h u t q hfuture z c hcell
  have hp' : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture = some (false, c.rate) := by
    simpa [hdisabled] using hp
  have hzero := RecordedRoundMoments.rawEstimate_eq_zero_of_disabled Q
    (RecordedQueueRun.run Q inputs) c a hdisabled
  have hcoef : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureCoefficient
      rate rewards C_star C_h u t (some (some a)) z q hfuture = 0 := by
    change ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters
      (some (some a))
      (ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
        rate rewards C_star C_h u t z q hfuture) = 0
    rw [hp']
    simp [ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [futureScalar_present_run rate rewards C_star C_h u t q hfuture a z inputs c hinputs hcell]
    exact hzero
  · simp [futureAmplitude, hp']
  · simp [futureMomentOne, hcoef, futureAmplitude, hp']
  · simp [futureMomentTwo, hcoef, futureAmplitude, hp']
