/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalFutureRetainedMoments

import Mathlib.Tactic

/-!
# Future support and adjacent queue-readout carry

The literal optional calendar remains nested on the same original source.
On consecutive dates, the actual first-replacement support can only shrink;
the resulting exponential carry retains the full optional successor readout.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-290`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`, and
`sources/zip4/manuscript/06_interruptions.tex:391-426`.
-/

@[expose] public section
noncomputable section

open Bandits.Support ConstructorDimensions
open ReferenceFirstCollectionRenewalFutureControlLaw
open ReferenceFirstCollectionRenewalFutureNumericalPrefix
open ReferenceFirstCollectionRenewalFutureFirstReplacementView
open ReferenceFirstCollectionRenewalFutureRecordingLaw
open ReferenceFirstCollectionRenewalFutureRetainedMoments
open ReferenceFirstCollectionRenewalIncomingQueueMeasurability
open ReferenceFirstReplacementLiveFollowerPrefix
open ReferenceFirstCollectionRenewalNextRecordingPriorView
open ReferenceLiveDispatchOutputMeasurability
open ReferenceActivePhysicalStep
open scoped MeasureTheory

namespace Bandits.Support.ReferenceFirstCollectionRenewalFutureSupportChain

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

local notation "Z" => ReferenceFirstCollectionRenewalFutureControlLaw.Source
  rate rewards C_star C_h u t
private theorem mapM_id_prefix_of_prefix {α : Type*}
    {xs ys : List (Option α)} {out : List α}
    (hxy : xs <+: ys) (hout : ys.mapM id = some out) :
    ∃ inputsEarly, xs.mapM id = some inputsEarly ∧ inputsEarly <+: out := by
  rcases hxy with ⟨tail, htail⟩
  subst ys
  rw [List.mapM_append] at hout
  cases hxs : xs.mapM id with
  | none => simp [hxs] at hout
  | some inputsEarly =>
    cases htail' : tail.mapM id with
    | none => simp [hxs, htail'] at hout
    | some suffix =>
      simp [hxs, htail'] at hout
      subst out
      exact ⟨inputsEarly, rfl, ⟨suffix, rfl⟩⟩

/-- The literal original calendar at an earlier natural date is an actual
list prefix of the calendar at every later natural date. -/
theorem calendarCells_prefix (n m : ℕ) (hnm : n ≤ m) (z : Z) :
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
      rate rewards C_star C_h u t n z <+:
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
      rate rewards C_star C_h u t m z := by
  let records := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
    rate rewards C_star C_h u t z
  let start := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
    rate rewards C_star C_h u t z
  have htake : records.take (n - start) <+: records.take (m - start) := by
    apply (List.take_isPrefix_take).2
    exact Or.inl (Nat.sub_le_sub_right hnm start)
  unfold ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
  exact htake.map (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate)

/-- If every cell through `m` is present, the exact same `mapM id` traversal
produces a present input list at `n`, and that list is a prefix of the one
run from the original zero state through `m`. -/
theorem futurePrefixReadout_present_input_prefix (n m : ℕ)
    (hnm : n ≤ m) (z : Z)
    (hm : (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
      rate rewards C_star C_h u t m z).isSome = true) :
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
      rate rewards C_star C_h u t n z).isSome = true ∧
    ∃ inputsN inputsM,
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
        (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
          rate rewards C_star C_h u t n z) = some inputsN ∧
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
        (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
          rate rewards C_star C_h u t m z) = some inputsM ∧
      inputsN <+: inputsM ∧
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
        rate rewards C_star C_h u t n z = some
          (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) inputsN)) ∧
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
        rate rewards C_star C_h u t m z = some
          (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) inputsM)) := by
  have hinputsM :
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
        (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
          rate rewards C_star C_h u t m z) ≠ none := by
    cases hinputs : ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
        (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
          rate rewards C_star C_h u t m z) with
    | none =>
        simp [ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout,
          ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout,
          hinputs] at hm
    | some inputs => exact Option.some_ne_none _
  cases hinputsM' : ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
        rate rewards C_star C_h u t m z) with
  | none => exact (hinputsM hinputsM').elim
  | some inputsM =>
    have hmapM :
        (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
          rate rewards C_star C_h u t m z).mapM id = some inputsM := by
      simpa [ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells]
        using hinputsM'
    obtain ⟨inputsN, hinputsN, hprefix⟩ :=
      mapM_id_prefix_of_prefix
        (calendarCells_prefix rate rewards C_star C_h u t n m hnm z) hmapM
    have hreadM :
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
          rate rewards C_star C_h u t m z = some
            (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
              (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) inputsM)) := by
      simp [ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout,
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout,
        hinputsM']
    have hreadN :
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
          rate rewards C_star C_h u t n z = some
            (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
              (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) inputsN)) := by
      simp [ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout,
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout,
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells,
        hinputsN]
    have hsomeN :
        (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
          rate rewards C_star C_h u t n z).isSome = true := by
      rw [hreadN]
      rfl
    have hinputsN' :
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
          (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
            rate rewards C_star C_h u t n z) = some inputsN := by
      simpa [ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells]
        using hinputsN
    exact ⟨hsomeN, inputsN, inputsM, hinputsN', rfl, hprefix, hreadN, hreadM⟩

private theorem measurable_option_isSome {X α : Type*}
    (μ : MeasurableSpace X) [MeasurableSpace α]
    (f : X → Option α)
    (hf : @Measurable X (Option α) μ inferInstance f) :
    @Measurable X Bool μ inferInstance (fun x => (f x).isSome) := by
  let code := Equiv.optionEquivSumPUnit α
  have hcode : @Measurable X (Sum α PUnit) μ inferInstance
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

/-- Both factors of the literal support test are measurable in the exact
future prior field inherited from the original renewal source. -/
theorem measurableSet_futureSupport
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    @MeasurableSet Z
      (ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q)
      {z : Z |
        (ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
          rate rewards C_star C_h u t z q hfuture).isSome = true ∧
        (ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
          rate rewards C_star C_h u t q z).isSome = true} := by
  let field := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
    rate rewards C_star C_h u t control0 q
  have hparameters :=
    ReferenceFirstCollectionRenewalFutureRecordingLaw.measurable_futureParameters
      rate rewards C_star C_h u t control0 q hfuture
  have hreadout : Measurable[field]
      (fun z : Z => ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
        rate rewards C_star C_h u t q z) := by
    change Measurable[MeasurableSpace.comap Subtype.val
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1))]
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
        rate rewards C_star C_h u t q.val)
    exact ReferenceFirstCollectionRenewalFutureNumericalPrefix.measurable_futurePrefixReadout
      rate rewards C_star C_h u t control0 q.val (by omega)
  have hp := measurable_option_isSome field
    (fun z : Z => ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture) hparameters
  have hr : Measurable[field]
      (fun z : Z => (ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
        rate rewards C_star C_h u t q z).isSome) := by
    have hoption : Measurable (Option.isSome :
        Option ((Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ)))) → Bool) :=
      measurable_of_countable _
    exact hoption.comp hreadout
  have hparamSet : @MeasurableSet Z field
      {z : Z | (ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
        rate rewards C_star C_h u t z q hfuture).isSome = true} := by
    exact (measurableSet_singleton true).preimage hp
  have hreadSet : @MeasurableSet Z field
      {z : Z | (ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
        rate rewards C_star C_h u t q z).isSome = true} := by
    exact (measurableSet_singleton true).preimage hr
  exact hparamSet.inter hreadSet

/-- A present later optional run readout gives an actually present earlier
input prefix, both executed from `RecordedQueueRun.run`'s same original
initial state. -/
theorem priorReadout_present_input_prefix (q q' : Fin p.T)
    (hqle : q.val ≤ q'.val) (z : Z)
    (hlater : (ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
      rate rewards C_star C_h u t q' z).isSome = true) :
    (ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
      rate rewards C_star C_h u t q z).isSome = true ∧
    ∃ inputsQ inputsQ',
      ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
        rate rewards C_star C_h u t q z = some inputsQ ∧
      ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
        rate rewards C_star C_h u t q' z = some inputsQ' ∧
      inputsQ <+: inputsQ' ∧
      ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
        rate rewards C_star C_h u t q z = some
          (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) inputsQ)) ∧
      ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
        rate rewards C_star C_h u t q' z = some
          (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) inputsQ')) := by
  have hnatural := futurePrefixReadout_present_input_prefix rate rewards C_star C_h u t
    q.val q'.val hqle z (by
      simpa [ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout] using hlater)
  obtain ⟨hbefore, inputsQ, inputsQ', hinputsQ, hinputsQ', hprefix, hreadQ, hreadQ'⟩ :=
    hnatural
  have hinputsQFin :
      ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
        rate rewards C_star C_h u t q z = some inputsQ := by
    simpa [ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs,
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells] using hinputsQ
  have hinputsQ'Fin :
      ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
        rate rewards C_star C_h u t q' z = some inputsQ' := by
    simpa [ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs,
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells] using hinputsQ'
  have hreadQFin :=
    ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout_eq_of_inputs
      rate rewards C_star C_h u t q z inputsQ hinputsQFin
  have hreadQ'Fin :=
    ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout_eq_of_inputs
      rate rewards C_star C_h u t q' z inputsQ' hinputsQ'Fin
  have hbeforeFin :
      (ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
        rate rewards C_star C_h u t q z).isSome = true := by
    simpa [ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout] using hbefore
  have hreadQ' :
      ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
        rate rewards C_star C_h u t q' z = some
          (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) inputsQ')) := hreadQ'Fin
  exact ⟨hbeforeFin, inputsQ, inputsQ', hinputsQFin, hinputsQ'Fin, hprefix,
    hreadQFin, hreadQ'⟩

/-- On adjacent genuine future dates, the literal recording-parameter and
whole-prior-readout support at the later date is contained in its predecessor.
The physical tag and first-replacement slice test are discharged from the
actual continuing record. -/
theorem futureSupport_antitone (q q' : Fin p.T)
    (hfuture : t.val + 1 < q.val) (hnext : q'.val = q.val + 1) (z : Z) :
    ((ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
        rate rewards C_star C_h u t z q' (by omega)).isSome = true ∧
      (ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
        rate rewards C_star C_h u t q' z).isSome = true) →
    ((ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
        rate rewards C_star C_h u t z q hfuture).isSome = true ∧
      (ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
        rate rewards C_star C_h u t q z).isSome = true) := by
  intro hsupport
  have hfuture' : t.val + 1 < q'.val := by omega
  have hview' :
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
        rate rewards C_star C_h u t z q' hfuture' ≠ none := by
    cases hv : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
        rate rewards C_star C_h u t z q' hfuture' with
    | none =>
        simp [ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters, hv]
          at hsupport
    | some data => exact Option.some_ne_none _
  have hbranch' : ∃ b,
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch
        rate rewards C_star C_h u t z q' hfuture' = some b := by
    cases hb : ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch
        rate rewards C_star C_h u t z q' hfuture' with
    | none =>
        simp [ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView,
          hb] at hview'
    | some b => exact ⟨b, rfl⟩
  obtain ⟨branch', hbranch'⟩ := hbranch'
  have hgeometry' :=
    ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch_geometry
      rate rewards C_star C_h u t z q' hfuture' branch' hbranch'
  have hq'le : q'.val - (t.val + 1) ≤
      (ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingRecords
        rate rewards C_star C_h u t z).length := by
    cases branch' with
    | false => exact Nat.le_of_lt (hgeometry'.1 rfl)
    | true => exact le_of_eq (hgeometry'.2 rfl)
  have hqbefore : q.val - (t.val + 1) <
      (ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingRecords
        rate rewards C_star C_h u t z).length := by
    omega
  have hrecord :=
    ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord_eq_continuing
      rate rewards C_star C_h u t z q hfuture hqbefore
  have hcontinuing :
      ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
        (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
          rate rewards C_star C_h u t z q hfuture) = true := by
    rw [hrecord]
    exact ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_mem _ _ _
      (List.get_mem _ _)
  have hqle : q.val - (t.val + 1) ≤
      (ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingRecords
        rate rewards C_star C_h u t z).length := Nat.le_of_lt hqbefore
  have hbranch :
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch
        rate rewards C_star C_h u t z q hfuture = some false := by
    unfold ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch
    rw [ite_eq_left hqle,
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureTag_eq]
    cases hcoord : (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
        rate rewards C_star C_h u t z q hfuture).output.preparation.coordinator with
    | live registers owned base outcome =>
      cases outcome <;>
        simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen,
          hcoord, ReferenceLiveDispatchOutputMeasurability.outcomeData,
          ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm] at hcontinuing ⊢
    | dagger => simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen,
        hcoord] at hcontinuing
    | first => simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen,
        hcoord] at hcontinuing
    | collection payload ledger saved =>
        simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen,
          hcoord] at hcontinuing
    | invalidCollectionCutoff =>
        simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen,
          hcoord] at hcontinuing
  obtain ⟨cell, hread, hread0, henabled, hsigma, hrate, hreward, hordinary,
    hmarker, hdown⟩ :=
    ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_live_readout
      rate rewards C_star C_h u t z q hfuture hqbefore
  have hdownView :
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureDownView
        rate rewards C_star C_h u t z q hfuture = some cell.selected.view := by
    simp only [ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureDownView,
      DispatchCut.downView, cell.selection_actual, Option.map_some]
  cases hv : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture with
  | none =>
      have : False := by
        simp [ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView,
          hbranch, ReferenceFirstCollectionRenewalFutureFirstReplacementView.viewOnBranch,
          hdownView] at hv
      exact this.elim
  | some data =>
    rcases data with ⟨parameters, view, code⟩
    have hreadout :=
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_readout
        rate rewards C_star C_h u t z q hfuture
    rw [hv] at hreadout
    rcases hreadout with ⟨cell', snapshot, valid, hcell', hparameters, hrate', hreward',
      hcode, hrecording⟩
    have hparameters' :
        ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
          rate rewards C_star C_h u t z q hfuture = some (cell'.enabled, cell'.rate) := by
      simp [ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters, hv,
        hparameters]
    have hprior :=
      priorReadout_present_input_prefix rate rewards C_star C_h u t q q' (by omega) z
        hsupport.2
    exact ⟨by rw [hparameters']; rfl,
      (by simpa [ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout] using
        hprior.1)⟩

/-- The full optional readout at `q'` is definitionally the numerical-prefix
readout at natural successor `q.val + 1`; absence and overflow remain intact. -/
theorem priorReadout_eq_successor (q q' : Fin p.T) (z : Z)
    (hnext : q'.val = q.val + 1) :
    ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
      rate rewards C_star C_h u t q' z =
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
      rate rewards C_star C_h u t (q.val + 1) z := by
  change ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
    rate rewards C_star C_h u t q'.val z = _
  rw [hnext]

/-- Honest adjacent exponential carry on the exact literal support. The left
readout uses the integer backlog in its present Option value; its localized
zero branch only represents absence. Mass exiting the support is discarded. -/
theorem masked_exponential_carry (q q' : Fin p.T)
    (hfuture : t.val + 1 < q.val) (hnext : q'.val = q.val + 1)
    (a : Fin p.K) (z : Z) :
    (if
      (ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
        rate rewards C_star C_h u t z q' (by omega)).isSome = true ∧
      (ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
        rate rewards C_star C_h u t q' z).isSome = true
      then (1 : ℝ) else 0) * Real.exp
        (CanonicalRecordingRates.beta p rate.eta.val *
          (ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
            rate rewards C_star C_h u t q' z).elim 0
            (fun readout => ((readout.1 a).2 : ℝ) / ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ))) ≤
    (if
      (ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
        rate rewards C_star C_h u t z q hfuture).isSome = true ∧
      (ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
        rate rewards C_star C_h u t q z).isSome = true
      then (1 : ℝ) else 0) * Real.exp
        (CanonicalRecordingRates.beta p rate.eta.val *
          (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
            rate rewards C_star C_h u t (q.val + 1) z).elim 0
            (fun readout => ((readout.1 a).2 : ℝ) / ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ))) := by
  by_cases hsupport :
      (ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
        rate rewards C_star C_h u t z q' (by omega)).isSome = true ∧
      (ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
        rate rewards C_star C_h u t q' z).isSome = true
  · have hbefore := futureSupport_antitone rate rewards C_star C_h u t q q'
      hfuture hnext z hsupport
    rw [ite_eq_left hsupport, ite_eq_left hbefore,
      priorReadout_eq_successor rate rewards C_star C_h u t q q' z hnext]
  · have hright : 0 ≤
        (if
          (ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
            rate rewards C_star C_h u t z q hfuture).isSome = true ∧
          (ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
            rate rewards C_star C_h u t q z).isSome = true
          then (1 : ℝ) else 0) * Real.exp
          (CanonicalRecordingRates.beta p rate.eta.val *
            (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
              rate rewards C_star C_h u t (q.val + 1) z).elim 0
              (fun readout => ((readout.1 a).2 : ℝ) / ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ))) := by
      apply mul_nonneg
      · split_ifs <;> norm_num
      · exact Real.exp_nonneg _
    simpa [ite_eq_right hsupport] using hright

end Bandits.Support.ReferenceFirstCollectionRenewalFutureSupportChain

end
