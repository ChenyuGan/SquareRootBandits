/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveDownCompletionReadout
public import Bandits.Support.ReferenceInspectedPastRoundObservations

/-!
# Strict-past retained decoder flag measurability

Sources: `sources/zip4/manuscript/05_binary_transport.tex:7-55,74-124,293-308`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64,141-157`.

This module defines the literal strict-past retained decoder flag and proves
its adaptation to the existing inspected-history field. Ambiguity is factored
through the actual incoming state, selected row, strict selected-control
prefix, whole private coordinates, and retained whole-round diagnostics. The
private measurable completion is only a proof factor; temporal-read
congruences identify every read used by the retained completion with the
original record. No chronology, source-event equality, or stopping-time claim
is made. The named downstream consumer is
`ReferenceFirstLiveSourceStoppedReleaseEndpoint`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveDecoderPastMeasurability

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The literal retained-record decoder readout, with the fixed postlaunch
stamp cut used by the analytical test. -/
def retainedDecoderRecordFlag (s : ℕ) (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) : Bool :=
  ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag r ||
    decide (∃ i : Fin (p.m - 1),
      ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s r i)

/-- The literal strict-past decoder readout on the unchanged whole source.
Every witness is an actual optional record at its original calendar offset. -/
def strictPastDecoderFlag (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s n : ℕ) (hn : n ≤ p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Bool :=
  decide (∃ j : Fin n, ∃ r,
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      (Fin.castLE hn j) z = some r ∧ retainedDecoderRecordFlag s r = true)

/-- The record readout is exactly the disjunction of the saved wrong flag and
an actual completed all-stamps-after-start ambiguous DOWN batch. -/
theorem retainedDecoderRecordFlag_eq_true_iff (s : ℕ) (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    retainedDecoderRecordFlag s r = true ↔
      ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag r = true ∨
        ∃ i : Fin (p.m - 1),
          ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s r i := by
  simp only [retainedDecoderRecordFlag, Bool.or_eq_true, decide_eq_true_eq]

/-- Exact strict-past some equation, preserving every original record lookup. -/
theorem strictPastDecoderFlag_eq_true_iff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s n : ℕ) (hn : n ≤ p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    strictPastDecoderFlag rate rewards C_star C_h s n hn z = true ↔
      ∃ j : Fin n, ∃ r,
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
          (Fin.castLE hn j) z = some r ∧ retainedDecoderRecordFlag s r = true := by
  simp only [strictPastDecoderFlag, decide_eq_true_eq]

/-- Exact strict-past none equation: absence or a false retained record at
every strict-past lookup is the Boolean complement of the displayed test. -/
theorem strictPastDecoderFlag_eq_false_iff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s n : ℕ) (hn : n ≤ p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    strictPastDecoderFlag rate rewards C_star C_h s n hn z = false ↔
      ∀ j : Fin n, ∀ r,
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
          (Fin.castLE hn j) z = some r → retainedDecoderRecordFlag s r = false := by
  constructor
  · intro h j r hr
    cases hf : retainedDecoderRecordFlag s r with
    | false => rfl
    | true =>
        have htrue : strictPastDecoderFlag rate rewards C_star C_h s n hn z = true :=
          (strictPastDecoderFlag_eq_true_iff rate rewards C_star C_h s n hn z).2
            ⟨j, r, hr, hf⟩
        rw [h] at htrue
        cases htrue
  · intro h
    cases hflag : strictPastDecoderFlag rate rewards C_star C_h s n hn z with
    | false => rfl
    | true =>
        obtain ⟨j, r, hr, hf⟩ :=
          (strictPastDecoderFlag_eq_true_iff rate rewards C_star C_h s n hn z).1 hflag
        rw [h j r hr] at hf
        cases hf

/-- The strict-past detector has no entries at the empty history. -/
theorem strictPastDecoderFlag_zero
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hn : 0 ≤ p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    strictPastDecoderFlag rate rewards C_star C_h s 0 hn z = false := by
  simp [strictPastDecoderFlag]

/-- An absent actual lookup contributes no strict-past decoder entry. -/
theorem retainedDecoderRecordFlag_at_none
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s n : ℕ) (hn : n ≤ p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (j : Fin n)
    (hnone : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      (Fin.castLE hn j) z = none) :
    ¬ ∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      (Fin.castLE hn j) z = some r ∧ retainedDecoderRecordFlag s r = true := by
  rintro ⟨r, hr, _⟩
  rw [hnone] at hr
  cases hr

/-- A present actual lookup contributes exactly its retained-record flag. -/
theorem retainedDecoderRecordFlag_at_some
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s n : ℕ) (hn : n ≤ p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (j : Fin n)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hsome : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      (Fin.castLE hn j) z = some r) :
    (∃ r', ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      (Fin.castLE hn j) z = some r' ∧ retainedDecoderRecordFlag s r' = true) ↔
      retainedDecoderRecordFlag s r = true := by
  constructor
  · rintro ⟨r', hr', hflag⟩
    have hrr : r' = r := Option.some.inj (hr'.symm.trans hsome)
    simpa only [hrr] using hflag
  · intro hflag
    exact ⟨r, hsome, hflag⟩

private def detectorFixedControl (p : ConstructorDimensions.Parameters) :
    ContinuousLearningRows.TimeControl p :=
  (fun _ => ⟨0, le_rfl, zero_lt_one⟩, fun _ => (fun _ => 0, 0))

/-- A fixed-countable-code extension of the original rows using precisely the
selected forward row and the strict selected-control prefix. Controls after
the queried strict-past offset are not read by the corresponding round. -/
private def detectorFactorRows (n : ℕ) (hn : n ≤ p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    CompletePublicTable.CompleteRows p :=
  fun _ => (ReferenceSourceOwnHistoryContainment.selectedForwardRow z,
    fun v : Fin p.T => if hv : v.val < n then
      ReferenceSourceOwnHistoryContainment.selectedControlPrefix n hn z ⟨v.val, hv⟩
    else (fun _ => ⟨0, le_rfl, zero_lt_one⟩,
      fun _ => (fun _ => 0, 0)))

private theorem detectorFactorRows_control (n : ℕ) (hn : n ≤ p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (v : Fin p.T) (hv : v.val < n) (q : Fin (M p)) :
    (detectorFactorRows n hn z q).2 v =
      (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v := by
  simp only [detectorFactorRows, dite_eq_left hv,
    ReferenceSourceOwnHistoryContainment.selectedControlPrefix]
  rfl

private theorem measurable_detectorFactorRows
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn] (detectorFactorRows n hn) := by
  let : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
    ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn
  apply measurable_pi_iff.mpr
  intro q
  apply (ReferenceInspectedPastRoundObservations.selectedForwardRow_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h n hn).prodMk
  apply measurable_pi_iff.mpr
  intro v
  by_cases hv : v.val < n
  · have h := (measurable_pi_apply (⟨v.val, hv⟩ : Fin n)).comp
      (ReferenceInspectedPastRoundObservations.selectedControlPrefix_measurable_in_inspectedHistorySpace
        rate rewards C_star C_h n hn)
    simpa only [detectorFactorRows, dite_eq_left hv, Function.comp_def] using h
  · simp only [dite_eq_right hv]
    exact measurable_const

private abbrev DetectorPresent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :=
  {z : BootstrapPrivateRoundStreams.SourceInput p //
    (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).isSome = true}

private def detectorPresentRecord
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (x : DetectorPresent rate rewards C_star C_h t) : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
  (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t x.val).get x.property

private theorem detectorPresentRecord_lookup
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (x : DetectorPresent rate rewards C_star C_h t) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t x.val =
      some (detectorPresentRecord rate rewards C_star C_h t x) :=
  (Option.some_get x.property).symm

private theorem detectorActualRecord_input_fields
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r) :
    r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.time = t ∧ r.input.rewards = rewards := by
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h t.val z
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hz.1
    have hrec := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h t z _ hl hz.2
    have heq := Option.some.inj (hr.symm.trans hrec)
    have hstart_le : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val := hz.2
    subst r
    refine ⟨rfl, rfl, ?_, rfl⟩
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    omega
  · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hz] at hr
    cases hr

private def detectorFactorInput
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T) (t : Fin p.T)
    (x : DetectorPresent rate rewards C_star C_h t) :
    ReferenceActivePhysicalStep.RoundInput p rate := {
  state := (detectorPresentRecord rate rewards C_star C_h t x).input.state
  rows := detectorFactorRows n hn x.val
  selected := ActualInitializationPhysicalStep.selectedRowIndex p x.val
  time := t
  active := by
    have htime := (detectorActualRecord_input_fields rate rewards C_star C_h t x.val
      (detectorPresentRecord rate rewards C_star C_h t x)
      (detectorPresentRecord_lookup rate rewards C_star C_h t x)).2.2.1
    simpa only [htime] using
      (detectorPresentRecord rate rewards C_star C_h t x).input.active
  rewards := rewards
  }

private theorem measurable_option_get_of_present
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Option Y) (hf : Measurable f)
    (h : ∀ x, (f x).isSome = true) :
    Measurable (fun x => (f x).get (h x)) := by
  intro s hs
  have hm := (hs.inl_image (β := PUnit)).preimage (measurable_comap_iff.mp hf)
  convert hm using 1
  ext x
  cases hx : f x with
  | none => have hh := h x; simp only [hx, Option.isSome_none, Bool.false_eq_true] at hh
  | some y => simp [hx, Equiv.optionEquivSumPUnit]

private theorem measurable_option_isSome_detector {Y : Type*} [MeasurableSpace Y] :
    Measurable (Option.isSome : Option Y → Bool) := by
  have h : Measurable (Sum.elim (fun _ : Y => true) (fun _ : PUnit => false)) :=
    measurable_const.sumElim measurable_const
  convert h.comp (comap_measurable (Equiv.optionEquivSumPUnit Y)) using 1
  funext x
  cases x <;> rfl

private theorem measurable_detectorPresent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T) (t : Fin p.T) (ht : t.val < n) :
    MeasurableSet[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn]
      {z : BootstrapPrivateRoundStreams.SourceInput p | (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).isSome = true} := by
  let : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
    ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn
  have hobs := ReferenceInspectedPastRoundObservations.pastRoundObservations_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h n hn
  have hpresent : (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).isSome) =
    fun z => (ReferenceInspectedPastRoundObservations.pastRoundObservations
      rate rewards C_star C_h n hn z ⟨t.val, ht⟩).isSome := by
    funext z
    cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
    | none =>
        have hnone := ReferenceInspectedPastRoundObservations.pastRoundObservations_none_iff
          rate rewards C_star C_h n hn z ⟨t.val, ht⟩
        simp only [hnone.mpr hr, Option.isSome_none]
    | some r =>
        have hsome := ReferenceInspectedPastRoundObservations.pastRoundObservations_some
          rate rewards C_star C_h n hn z ⟨t.val, ht⟩ r hr
        simp only [hsome, Option.isSome_some]
  convert measurableSet_singleton true |>.preimage
    ((measurable_option_isSome_detector.comp
      ((measurable_pi_apply (⟨t.val, ht⟩ : Fin n)).comp hobs))) using 1
  ext z
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact Iff.of_eq (congrArg (fun b : Bool => b = true) (congrFun hpresent z))

private theorem measurable_detectorFactorInput
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T) (t : Fin p.T) (ht : t.val < n) :
    let : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
      ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
        rate rewards C_star C_h n hn
    Measurable (detectorFactorInput rate rewards C_star C_h n hn t) := by
  let : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
    ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn
  have hincoming := ReferenceSourceOwnHistoryContainment.incoming_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h n hn t (Nat.le_of_lt ht)
  have hpresent (x : DetectorPresent rate rewards C_star C_h t) :
      (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t x.val).isSome = true := by
    simp only [ReferenceSourcePrefixHistoryFiltration.incoming,
      detectorPresentRecord_lookup, Option.map_some, Option.isSome_some]
  have hget := measurable_option_get_of_present _
    (hincoming.comp (measurable_subtype_coe :
      Measurable (Subtype.val : DetectorPresent rate rewards C_star C_h t → BootstrapPrivateRoundStreams.SourceInput p))) hpresent
  have hdecoded (x : DetectorPresent rate rewards C_star C_h t) :
      ReferenceActivePhysicalStepMeasurability.decodeState
        ((ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t x.val).get
          (hpresent x)) = (detectorPresentRecord rate rewards C_star C_h t x).input.state := by
    simp only [ReferenceSourcePrefixHistoryFiltration.incoming,
      detectorPresentRecord_lookup, Option.map_some, Option.get_some,
      ReferenceActivePhysicalStepMeasurability.decodeState_encodeState]
  have hstateCode : Measurable (fun x : DetectorPresent rate rewards C_star C_h t =>
      ReferenceActivePhysicalStepMeasurability.encodeState
        (detectorPresentRecord rate rewards C_star C_h t x).input.state) := by
    convert hget using 1
    funext x
    have hencode := congrArg ReferenceActivePhysicalStepMeasurability.encodeState (hdecoded x).symm
    rw [hencode]
    simp only [Function.comp_apply, ReferenceSourcePrefixHistoryFiltration.incoming,
      detectorPresentRecord_lookup, Option.map_some, Option.get_some,
      ReferenceActivePhysicalStepMeasurability.decodeState_encodeState]
  have hstate : Measurable (fun x : DetectorPresent rate rewards C_star C_h t =>
      (detectorPresentRecord rate rewards C_star C_h t x).input.state) := by
    apply measurable_comap_iff.mpr
    change Measurable (fun x => ReferenceActivePhysicalStepMeasurability.encodeState
      (detectorPresentRecord rate rewards C_star C_h t x).input.state)
    exact hstateCode
  have hrows := (measurable_detectorFactorRows rate rewards C_star C_h n hn).comp
    (measurable_subtype_coe : Measurable (Subtype.val : DetectorPresent rate rewards C_star C_h t → BootstrapPrivateRoundStreams.SourceInput p))
  have hprivate := (ReferenceInspectedPastRoundObservations.privateCoordinates_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h n hn).comp
      (measurable_subtype_coe : Measurable (Subtype.val : DetectorPresent rate rewards C_star C_h t → BootstrapPrivateRoundStreams.SourceInput p))
  have hselected : Measurable (fun x : DetectorPresent rate rewards C_star C_h t =>
      ActualInitializationPhysicalStep.selectedRowIndex p x.val) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp hprivate))
  apply measurable_comap_iff.mpr
  apply Measurable.subtype_mk
  exact hstate.prodMk (hrows.prodMk (hselected.prodMk
    (measurable_const.prodMk measurable_const)))

private theorem detectorFactorInput_code_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T) (t : Fin p.T) (ht : t.val < n)
    (x : DetectorPresent rate rewards C_star C_h t) :
    ReferenceActiveHorizonMeasurability.roundRecordCode
      (detectorPresentRecord rate rewards C_star C_h t x) =
    ReferenceActiveHorizonMeasurability.roundRecordCode
      ⟨detectorFactorInput rate rewards C_star C_h n hn t x,
        ReferenceActivePhysicalStep.step (detectorFactorInput rate rewards C_star C_h n hn t x), rfl⟩ := by
  let r := detectorPresentRecord rate rewards C_star C_h t x
  have hfields := detectorActualRecord_input_fields rate rewards C_star C_h t x.val r
    (detectorPresentRecord_lookup rate rewards C_star C_h t x)
  have hstate : (detectorFactorInput rate rewards C_star C_h n hn t x).state = r.input.state := rfl
  have hcanonical : ReferenceActiveHorizonMeasurability.roundRecordCode r =
      ReferenceActiveHorizonMeasurability.roundRecordCode
        ⟨r.input, ReferenceActivePhysicalStep.step r.input, rfl⟩ := rfl
  rw [hcanonical]
  apply ReferenceInspectedPastRoundObservations.roundRecordCode_eq_of_temporal_reads
    r.input (detectorFactorInput rate rewards C_star C_h n hn t x)
  · exact hstate.symm
  · simpa only [detectorFactorInput] using hfields.2.1
  · simpa only [detectorFactorInput] using hfields.2.2.1
  · simpa only [detectorFactorInput] using hfields.2.2.2
  · change (r.input.rows r.input.selected).2 r.input.time =
      (detectorFactorRows n hn x.val (ActualInitializationPhysicalStep.selectedRowIndex p x.val)).2 t
    rw [hfields.1, hfields.2.1, hfields.2.2.1]
    exact (detectorFactorRows_control n hn x.val t ht
      (ActualInitializationPhysicalStep.selectedRowIndex p x.val)).symm
  · intro v hv
    have hvn : v.val < n := by
      rw [hfields.2.2.1] at hv
      omega
    change (((r.input.rows r.input.selected).2 v).1 ContinuousControlSlice.Label.prop) =
      (((detectorFactorRows n hn x.val (ActualInitializationPhysicalStep.selectedRowIndex p x.val)).2 v).1
        ContinuousControlSlice.Label.prop)
    rw [hfields.1, hfields.2.1, detectorFactorRows_control n hn x.val v hvn]

private theorem detectorPreparedOutput_tail_eq_of_current
    (i : Fin (p.m - 1)) (activation : ReferencePrelaunchFollower.Activation p)
    (incoming : FollowerPrepareJointMeasurability.IncomingConfiguration p rate)
    (row row' : CompletePublicTable.CompleteRow p)
    (time : FollowerPrepareJointMeasurability.ActiveCalendarTime p activation)
    (hc : row.2 time.val = row'.2 time.val) :
    (FollowerPrepareJointMeasurability.prepareOutputOnInput rate i activation
      (FollowerPrepareJointMeasurability.assemblePrepareInput incoming row time)).2 =
    (FollowerPrepareJointMeasurability.prepareOutputOnInput rate i activation
      (FollowerPrepareJointMeasurability.assemblePrepareInput incoming row' time)).2 := by
  cases incoming with
  | none => rfl
  | some data =>
    rcases data with ⟨⟨index, values⟩, memory⟩
    have hp := ReferenceActiveTemporalCausality.prepare_projections_eq_of_current
      i activation time.property
      (FollowerLifecycleMeasurability.localConfigurationOfCode rate
        (some (index.1, memory))
        (FollowerDownJointMeasurability.bufferFromSkeletonAndScalars index.2.2 values)) hc
    have hcode := congrArg (fun pair =>
      FollowerLifecycleMeasurability.PreparedRoundCode.mk pair.1
        (FollowerLifecycleMeasurability.localConfigurationCode pair.2)) hp
    change FollowerLifecycleMeasurability.prepareRoundCodeAt rate i activation
        (some (index.1, memory)) index.2.2 row time values =
      FollowerLifecycleMeasurability.prepareRoundCodeAt rate i activation
        (some (index.1, memory)) index.2.2 row' time values at hcode
    simp only [FollowerPrepareJointMeasurability.prepareOutputOnInput,
      FollowerPrepareJointMeasurability.assemblePrepareInput,
      FollowerPrepareJointMeasurability.prepareRoundCodeOnInput,
      FollowerPrepareJointMeasurability.prepareOutputConfiguration, hcode]

private theorem detector_prepareRegisters_activation_eq
    (i : Fin (p.m - 1)) (a b : ReferencePrelaunchFollower.Activation p)
    (hvalue : a.val = b.val)
    (incoming : FollowerPrepareJointMeasurability.IncomingConfiguration p rate)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (ha : a.val ≤ time.val + 1) (hb : b.val ≤ time.val + 1) :
    ReferenceDownCompletedAmbiguityMeasurability.incomingRegisters
        (FollowerPrepareJointMeasurability.prepareOutputOnInput rate i a
          (FollowerPrepareJointMeasurability.assemblePrepareInput incoming row ⟨time, ha⟩)).2.2 =
      ReferenceDownCompletedAmbiguityMeasurability.incomingRegisters
        (FollowerPrepareJointMeasurability.prepareOutputOnInput rate i b
          (FollowerPrepareJointMeasurability.assemblePrepareInput incoming row ⟨time, hb⟩)).2.2 := by
  have hab : a = b := Subtype.ext hvalue
  subst b
  have htime : (⟨time, ha⟩ : FollowerPrepareJointMeasurability.ActiveCalendarTime p a) =
      ⟨time, hb⟩ := by
    apply Subtype.ext
    rfl
  have hinput := congrArg (FollowerPrepareJointMeasurability.assemblePrepareInput incoming row) htime
  rw [hinput]

private theorem detectorPreparedRegisters_eq_of_current
    (x y : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1))
    (hstate : x.state = y.state) (htime : x.time = y.time)
    (hcurrent : x.row.2 x.time = y.row.2 y.time) :
    ReferenceDownCompletedAmbiguityMeasurability.preparedRegisters x i =
      ReferenceDownCompletedAmbiguityMeasurability.preparedRegisters y i := by
  let ax := x.state.activations i
  let ay := y.state.activations i
  have hactivation : ax = ay := by
    dsimp only [ax, ay]
    exact congrArg (fun state : ReferenceActivePhysicalStep.State p rate => state.activations i) hstate
  have hfollowers : x.state.followers i = y.state.followers i :=
    congrArg (fun state : ReferenceActivePhysicalStep.State p rate => state.followers i) hstate
  have hactivationValue : ax.val = ay.val := congrArg Subtype.val hactivation
  have hvalidAtY : ax.val ≤ y.time.val + 1 := by
    rw [hactivation]
    exact y.active i
  have hcurrentAtY : x.row.2 y.time = y.row.2 y.time := by
    calc
      x.row.2 y.time = x.row.2 x.time := congrArg (fun time => x.row.2 time) htime.symm
      _ = y.row.2 y.time := hcurrent
  have htail := detectorPreparedOutput_tail_eq_of_current (p := p) (rate := rate) i
    ay
    (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
      (y.state.followers i))
    x.row y.row ⟨y.time, y.active i⟩ hcurrentAtY
  change ReferenceDownCompletedAmbiguityMeasurability.incomingRegisters
      (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode x i).2.2.2 =
    ReferenceDownCompletedAmbiguityMeasurability.incomingRegisters
      (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode y i).2.2.2
  change ReferenceDownCompletedAmbiguityMeasurability.incomingRegisters
      (FollowerPrepareJointMeasurability.prepareOutputOnInput rate i
        (x.state.activations i)
        (FollowerPrepareJointMeasurability.assemblePrepareInput
          (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
            (x.state.followers i)) x.row ⟨x.time, x.active i⟩)).2.2 =
    ReferenceDownCompletedAmbiguityMeasurability.incomingRegisters
      (FollowerPrepareJointMeasurability.prepareOutputOnInput rate i
        (y.state.activations i)
        (FollowerPrepareJointMeasurability.assemblePrepareInput
          (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
            (y.state.followers i)) y.row ⟨y.time, y.active i⟩)).2.2
  have htailRegisters := congrArg
    (fun output => ReferenceDownCompletedAmbiguityMeasurability.incomingRegisters output.2) htail
  have htimeInput : (⟨x.time, x.active i⟩ :
      FollowerPrepareJointMeasurability.ActiveCalendarTime p ax) = ⟨y.time, hvalidAtY⟩ := by
    apply Subtype.ext
    exact htime
  have hinputTime := congrArg
    (FollowerPrepareJointMeasurability.assemblePrepareInput
      (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate (y.state.followers i))
      x.row) htimeInput
  calc
    ReferenceDownCompletedAmbiguityMeasurability.incomingRegisters
        (FollowerPrepareJointMeasurability.prepareOutputOnInput rate i ax
          (FollowerPrepareJointMeasurability.assemblePrepareInput
            (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate (x.state.followers i))
            x.row ⟨x.time, x.active i⟩)).2.2 =
      ReferenceDownCompletedAmbiguityMeasurability.incomingRegisters
        (FollowerPrepareJointMeasurability.prepareOutputOnInput rate i ax
          (FollowerPrepareJointMeasurability.assemblePrepareInput
            (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate (y.state.followers i))
            x.row ⟨y.time, hvalidAtY⟩)).2.2 := by
            rw [hfollowers, hinputTime]
    _ = ReferenceDownCompletedAmbiguityMeasurability.incomingRegisters
        (FollowerPrepareJointMeasurability.prepareOutputOnInput rate i ay
          (FollowerPrepareJointMeasurability.assemblePrepareInput
            (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate (y.state.followers i))
            x.row ⟨y.time, y.active i⟩)).2.2 :=
          detector_prepareRegisters_activation_eq i ax ay hactivationValue
            (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
              (y.state.followers i)) x.row y.time hvalidAtY (y.active i)
    _ = ReferenceDownCompletedAmbiguityMeasurability.incomingRegisters
        (FollowerPrepareJointMeasurability.prepareOutputOnInput rate i ay
          (FollowerPrepareJointMeasurability.assemblePrepareInput
            (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate (y.state.followers i))
            y.row ⟨y.time, y.active i⟩)).2.2 := htailRegisters

private theorem detectorRoundDownObservation_eq_of_temporal_reads
    (x y : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1))
    (hstate : x.state = y.state) (htime : x.time = y.time)
    (hcurrent : x.row.2 x.time = y.row.2 y.time)
    (hwhole : ReferenceActiveStepCompositionMeasurability.wholeStepCode x =
      ReferenceActiveStepCompositionMeasurability.wholeStepCode y) :
    ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation x i =
      ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation y i := by
  have hprepared := detectorPreparedRegisters_eq_of_current x y i hstate htime hcurrent
  have hown : ReferenceDownCompletedAmbiguityMeasurability.ownGrid x i =
      ReferenceDownCompletedAmbiguityMeasurability.ownGrid y i := by
    unfold ReferenceDownCompletedAmbiguityMeasurability.ownGrid
    rw [hwhole]
  have hcurrent' : x.row.2 y.time = y.row.2 y.time := by
    calc
      x.row.2 y.time = x.row.2 x.time := congrArg (fun time => x.row.2 time) htime.symm
      _ = y.row.2 y.time := hcurrent
  have hdownSelected' : ActiveFollowerDownAcceptance.downSelected p i x.row y.time =
      ActiveFollowerDownAcceptance.downSelected p i y.row y.time := by
    unfold ActiveFollowerDownAcceptance.downSelected
    rw [hcurrent']
  have hcall : ReferenceDownCompletedAmbiguityMeasurability.roundCallObservation x i =
      ReferenceDownCompletedAmbiguityMeasurability.roundCallObservation y i := by
    unfold ReferenceDownCompletedAmbiguityMeasurability.roundCallObservation
    rw [htime, hprepared, hdownSelected', hcurrent', hown]
  have hdiagnostic : ReferenceDownCompletedAmbiguityMeasurability.diagnosticProjection
      ((ReferenceActiveStepCompositionMeasurability.wholeStepCode x).2.1 i) =
      ReferenceDownCompletedAmbiguityMeasurability.diagnosticProjection
        ((ReferenceActiveStepCompositionMeasurability.wholeStepCode y).2.1 i) := by
    rw [hwhole]
  unfold ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
  rw [htime, hown, hcall, hdiagnostic]

private theorem detectorCompletedReadout_eq_of_temporal_reads
    (left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (hstate : left.input.state = right.input.state)
    (htime : left.input.time = right.input.time)
    (hcurrent : left.input.row.2 left.input.time = right.input.row.2 right.input.time)
    (hcode : ReferenceActiveHorizonMeasurability.roundRecordCode left =
      ReferenceActiveHorizonMeasurability.roundRecordCode right) :
    ReferenceFirstLiveDownCompletionReadout.completedDownBatch left i =
        ReferenceFirstLiveDownCompletionReadout.completedDownBatch right i ∧
      ReferenceFirstLiveDownCompletionReadout.downReadout left i =
        ReferenceFirstLiveDownCompletionReadout.downReadout right i := by
  have hwhole : ReferenceActiveStepCompositionMeasurability.wholeStepCode left.input =
      ReferenceActiveStepCompositionMeasurability.wholeStepCode right.input := by
    exact congrArg (fun code => code.2.2) hcode
  have hobs := detectorRoundDownObservation_eq_of_temporal_reads left.input right.input i
    hstate htime hcurrent hwhole
  have hbatchLeft := ReferenceFirstLiveDownCompletionReadout.completedBatchCode_actual left i
  have hbatchRight := ReferenceFirstLiveDownCompletionReadout.completedBatchCode_actual right i
  have hreadLeft := ReferenceFirstLiveDownCompletionReadout.observationReadout_actual left i
  have hreadRight := ReferenceFirstLiveDownCompletionReadout.observationReadout_actual right i
  constructor
  · calc
      ReferenceFirstLiveDownCompletionReadout.completedDownBatch left i =
          ReferenceFirstLiveDownCompletionReadout.completedBatchCode
            (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation left.input i) := hbatchLeft.symm
      _ = ReferenceFirstLiveDownCompletionReadout.completedBatchCode
          (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation right.input i) :=
            congrArg ReferenceFirstLiveDownCompletionReadout.completedBatchCode hobs
      _ = ReferenceFirstLiveDownCompletionReadout.completedDownBatch right i := hbatchRight
  · calc
      ReferenceFirstLiveDownCompletionReadout.downReadout left i =
          ReferenceFirstLiveDownCompletionReadout.observationReadout
            (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation left.input i) := hreadLeft.symm
      _ = ReferenceFirstLiveDownCompletionReadout.observationReadout
          (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation right.input i) :=
            congrArg ReferenceFirstLiveDownCompletionReadout.observationReadout hobs
      _ = ReferenceFirstLiveDownCompletionReadout.downReadout right i := hreadRight

private theorem detectorAmbiguity_eq_of_temporal_reads
    (s : ℕ) (left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (hstate : left.input.state = right.input.state)
    (htime : left.input.time = right.input.time)
    (hcurrent : left.input.row.2 left.input.time = right.input.row.2 right.input.time)
    (hcode : ReferenceActiveHorizonMeasurability.roundRecordCode left =
      ReferenceActiveHorizonMeasurability.roundRecordCode right) :
    ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s left i ↔
      ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s right i := by
  have hbatch := (detectorCompletedReadout_eq_of_temporal_reads left right i
    hstate htime hcurrent hcode).1
  simp only [ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart]
  rw [hbatch]

private def strictPastAmbiguousFlag
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s n : ℕ) (hn : n ≤ p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) : Bool :=
  decide (∃ j : Fin n, ∃ r,
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      (Fin.castLE hn j) z = some r ∧
    ∃ i : Fin (p.m - 1),
      ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s r i)

private theorem measurable_ambiguousAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s n : ℕ) (hn : n ≤ p.T) (j : Fin n) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn]
      (fun z : BootstrapPrivateRoundStreams.SourceInput p => decide (∃ r,
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
          (Fin.castLE hn j) z = some r ∧
        ∃ i : Fin (p.m - 1),
          ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s r i)) := by
  let : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
    ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn
  let t : Fin p.T := Fin.castLE hn j
  have ht : t.val < n := by simp [t]
  let presentSet : Set (BootstrapPrivateRoundStreams.SourceInput p) := {z |
    (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).isSome = true}
  have hpresentSet : MeasurableSet presentSet := by
    simpa only [presentSet, t] using
      measurable_detectorPresent rate rewards C_star C_h n hn t ht
  have hfactor := measurable_detectorFactorInput rate rewards C_star C_h n hn t ht
  let ambiguousInput (x : ReferenceActivePhysicalStep.RoundInput p rate) : Bool :=
    decide (∃ i : Fin (p.m - 1),
      ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s
        ⟨x, ReferenceActivePhysicalStep.step x, rfl⟩ i)
  have htest : Measurable ambiguousInput := by
    apply measurable_to_bool
    have hset : MeasurableSet (⋃ i : Fin (p.m - 1),
        {x : ReferenceActivePhysicalStep.RoundInput p rate |
          ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s
            ⟨x, ReferenceActivePhysicalStep.step x, rfl⟩ i}) :=
      MeasurableSet.iUnion fun i =>
        ReferenceFirstLiveDownCompletionReadout.measurableSet_completedAmbiguousAfterStart
          (p := p) (rate := rate) s i
    convert hset using 1
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_iUnion, Set.mem_ofPred_eq]
    simp only [ambiguousInput, decide_eq_true_eq]
  let onPresent (x : DetectorPresent rate rewards C_star C_h t) :=
    ambiguousInput (detectorFactorInput rate rewards C_star C_h n hn t x)
  have honPresent : Measurable onPresent := htest.comp hfactor
  have hwhole : Measurable (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      if hz : (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).isSome = true
      then onPresent ⟨z, hz⟩ else false) := by
    apply measurable_of_restrict_of_restrict_compl hpresentSet
    · have hrestrict : presentSet.domRestrict (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
          if hz : (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).isSome = true
          then onPresent ⟨z, hz⟩ else false) = onPresent := by
        funext x
        simp only [Set.domRestrict]
        have hpresent :
            (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t x.val).isSome = true := by
          simpa only [presentSet, Set.mem_ofPred_eq] using x.property
        rw [dite_eq_left hpresent]
        have hsub : (⟨x.val, hpresent⟩ : DetectorPresent rate rewards C_star C_h t) = x :=
          Subtype.ext rfl
        rw [hsub]
      rw [hrestrict]
      exact honPresent
    · have hrestrict : presentSetᶜ.domRestrict (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
          if hz : (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).isSome = true
          then onPresent ⟨z, hz⟩ else false) = fun _ => false := by
        funext x
        simp only [Set.domRestrict]
        have hnone : (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t x.val).isSome ≠ true := by
          simpa only [presentSet, Set.mem_compl_iff, Set.mem_ofPred_eq] using x.property
        simp only [dite_eq_right hnone]
      rw [hrestrict]
      exact measurable_const
  have heq : (fun z : BootstrapPrivateRoundStreams.SourceInput p => decide (∃ r,
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      ∃ i : Fin (p.m - 1),
        ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s r i)) =
    fun z => if hz : (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).isSome = true
      then onPresent ⟨z, hz⟩ else false := by
    funext z
    by_cases hp : (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).isSome = true
    · have hsome : ∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r := by
        cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
        | none => simp [hr] at hp
        | some r => exact ⟨r, rfl⟩
      obtain ⟨r, hr⟩ := hsome
      let hx : DetectorPresent rate rewards C_star C_h t := ⟨z, hp⟩
      rw [dite_eq_left hp]
      change decide (∃ r', ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r' ∧
        ∃ i : Fin (p.m - 1),
          ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s r' i) =
          onPresent ⟨z, hp⟩
      have hfactorEq := detectorFactorInput_code_eq rate rewards C_star C_h n hn t ht hx
      have hcurrent : r.input.row.2 r.input.time =
          (detectorFactorInput rate rewards C_star C_h n hn t hx).row.2
            (detectorFactorInput rate rewards C_star C_h n hn t hx).time := by
        obtain ⟨hrows, hselected, htime, _⟩ :=
          detectorActualRecord_input_fields rate rewards C_star C_h t z r hr
        simp only [ReferenceActivePhysicalStep.RoundInput.row, detectorFactorInput]
        rw [show hx.val = z by rfl]
        rw [hrows, hselected, htime]
        exact (detectorFactorRows_control n hn z t ht
          (ActualInitializationPhysicalStep.selectedRowIndex p z)).symm
      have hrecordEq : detectorPresentRecord rate rewards C_star C_h t hx = r :=
        Option.some.inj ((detectorPresentRecord_lookup rate rewards C_star C_h t hx).symm.trans hr)
      have hfactorEq' : ReferenceActiveHorizonMeasurability.roundRecordCode r =
          ReferenceActiveHorizonMeasurability.roundRecordCode
            ⟨detectorFactorInput rate rewards C_star C_h n hn t hx,
              ReferenceActivePhysicalStep.step (detectorFactorInput rate rewards C_star C_h n hn t hx), rfl⟩ := by
        rw [← hrecordEq]
        exact hfactorEq
      have hamb (i : Fin (p.m - 1)) := detectorAmbiguity_eq_of_temporal_reads s r
        ⟨detectorFactorInput rate rewards C_star C_h n hn t hx,
          ReferenceActivePhysicalStep.step (detectorFactorInput rate rewards C_star C_h n hn t hx), rfl⟩
        i (by simp only [detectorFactorInput, hrecordEq])
        (by
          obtain ⟨_, _, ht', _⟩ :=
            detectorActualRecord_input_fields rate rewards C_star C_h t z r hr
          exact ht') hcurrent hfactorEq'
      have hflag : (onPresent hx = true) ↔
          ∃ i : Fin (p.m - 1),
            ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s r i := by
        simp only [onPresent, ambiguousInput, decide_eq_true_eq]
        exact exists_congr fun i => (hamb i).symm
      have hsingle :
          (∃ r', ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
            some r' ∧ ∃ i : Fin (p.m - 1),
              ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s r' i) ↔
            ∃ i : Fin (p.m - 1),
              ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s r i := by
        constructor
        · rintro ⟨r', hr', i, hi⟩
          have hrr : r' = r := Option.some.inj (hr'.symm.trans hr)
          subst r'
          exact ⟨i, hi⟩
        · rintro ⟨i, hi⟩
          exact ⟨r, hr, i, hi⟩
      have hbool :
          decide (∃ r', ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
            some r' ∧ ∃ i : Fin (p.m - 1),
              ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s r' i) =
            onPresent hx := by
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        exact hsingle.trans hflag.symm
      have hsub : hx = (⟨z, hp⟩ : DetectorPresent rate rewards C_star C_h t) := by
        apply Subtype.ext
        rfl
      rw [← hsub]
      exact hbool
    · have hnone : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = none := by
        cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
        | none => rfl
        | some r => simp [hr] at hp
      rw [dite_eq_right hp]
      simp [hnone]
  change Measurable (fun z : BootstrapPrivateRoundStreams.SourceInput p => decide (∃ r,
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
    ∃ i : Fin (p.m - 1),
      ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s r i))
  simpa only [heq] using hwhole

/-- The literal ambiguity component of the strict-past test is measurable in
the exact existing inspected-history field. -/
private theorem strictPastAmbiguousFlag_measurable_in_inspectedHistorySpace
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s n : ℕ) (hn : n ≤ p.T) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn]
      (strictPastAmbiguousFlag rate rewards C_star C_h s n hn) := by
  let : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
    ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn
  let atSet (j : Fin n) : Set (BootstrapPrivateRoundStreams.SourceInput p) := {z |
    (fun z => decide (∃ r,
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        (Fin.castLE hn j) z = some r ∧
      ∃ i : Fin (p.m - 1),
        ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s r i)) z = true}
  have hset : MeasurableSet (⋃ j : Fin n, atSet j) :=
    MeasurableSet.iUnion fun j =>
      (measurable_ambiguousAt rate rewards C_star C_h s n hn j)
        (measurableSet_singleton true)
  apply measurable_to_bool
  change MeasurableSet {z : BootstrapPrivateRoundStreams.SourceInput p | strictPastAmbiguousFlag rate rewards C_star C_h s n hn z = true}
  have heq : {z : BootstrapPrivateRoundStreams.SourceInput p | strictPastAmbiguousFlag rate rewards C_star C_h s n hn z = true} =
      ⋃ j : Fin n, atSet j := by
    ext z
    simp only [strictPastAmbiguousFlag, atSet, decide_eq_true_eq, Set.mem_ofPred_eq,
      Set.mem_iUnion]
  exact heq ▸ hset

private theorem strictPastDecoderFlag_eq_savedWrong_or_ambiguous
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s n : ℕ) (hn : n ≤ p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    strictPastDecoderFlag rate rewards C_star C_h s n hn z =
      (ReferenceInspectedPastRoundObservations.pastSavedWrongFlag
        rate rewards C_star C_h n hn z ||
        strictPastAmbiguousFlag rate rewards C_star C_h s n hn z) := by
  apply Bool.eq_iff_iff.mpr
  have hiff : strictPastDecoderFlag rate rewards C_star C_h s n hn z = true ↔
      ReferenceInspectedPastRoundObservations.pastSavedWrongFlag
        rate rewards C_star C_h n hn z = true ∨
      strictPastAmbiguousFlag rate rewards C_star C_h s n hn z = true := by
    constructor
    · intro h
      obtain ⟨j, r, hr, hflag⟩ :=
        (strictPastDecoderFlag_eq_true_iff rate rewards C_star C_h s n hn z).1 h
      rcases (retainedDecoderRecordFlag_eq_true_iff s r).1 hflag with hsaved | hamb
      · left
        apply (ReferenceInspectedPastRoundObservations.pastSavedWrongFlag_eq_true_iff
          rate rewards C_star C_h n hn z).2
        exact ⟨j, r, hr, by
          simpa only [ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag,
            decide_eq_true_eq] using hsaved⟩
      · right
        change decide (∃ j : Fin n, ∃ r,
          ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
            (Fin.castLE hn j) z = some r ∧
          ∃ i : Fin (p.m - 1),
            ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s r i) = true
        simp only [decide_eq_true_eq]
        exact ⟨j, r, hr, hamb⟩
    · intro h
      rcases h with hsaved | hamb
      · obtain ⟨j, r, hr, hwrong⟩ :=
          (ReferenceInspectedPastRoundObservations.pastSavedWrongFlag_eq_true_iff
            rate rewards C_star C_h n hn z).1 hsaved
        apply (strictPastDecoderFlag_eq_true_iff rate rewards C_star C_h s n hn z).2
        refine ⟨j, r, hr, ?_⟩
        apply (retainedDecoderRecordFlag_eq_true_iff s r).2
        left
        simpa only [ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag,
          decide_eq_true_eq] using hwrong
      · change decide (∃ j : Fin n, ∃ r,
          ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
            (Fin.castLE hn j) z = some r ∧
          ∃ i : Fin (p.m - 1),
            ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s r i) = true at hamb
        simp only [decide_eq_true_eq] at hamb
        apply (strictPastDecoderFlag_eq_true_iff rate rewards C_star C_h s n hn z).2
        rcases hamb with ⟨j, r, hr, hamb⟩
        exact ⟨j, r, hr, (retainedDecoderRecordFlag_eq_true_iff s r).2 (Or.inr hamb)⟩
  change (strictPastDecoderFlag rate rewards C_star C_h s n hn z = true) ↔
    ((ReferenceInspectedPastRoundObservations.pastSavedWrongFlag
      rate rewards C_star C_h n hn z ||
      strictPastAmbiguousFlag rate rewards C_star C_h s n hn z) = true)
  rw [Bool.or_eq_true]
  exact hiff

/-- The literal strict-past detector is measurable in the exact existing
inspected-history field, using O's saved-wrong field and the retained
completion factor above. -/
theorem strictPastDecoderFlag_measurable_in_inspectedHistorySpace
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s n : ℕ) (hn : n ≤ p.T) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn]
      (strictPastDecoderFlag rate rewards C_star C_h s n hn) := by
  let : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
    ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn
  have hsaved := ReferenceInspectedPastRoundObservations.pastSavedWrongFlag_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h n hn
  have hamb := strictPastAmbiguousFlag_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h s n hn
  have hpair : Measurable (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      (ReferenceInspectedPastRoundObservations.pastSavedWrongFlag
        rate rewards C_star C_h n hn z,
       strictPastAmbiguousFlag rate rewards C_star C_h s n hn z)) :=
    hsaved.prodMk hamb
  have hor : Measurable (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      ReferenceInspectedPastRoundObservations.pastSavedWrongFlag
        rate rewards C_star C_h n hn z ||
        strictPastAmbiguousFlag rate rewards C_star C_h s n hn z) :=
    (measurable_of_countable (fun bits : Bool × Bool => bits.1 || bits.2)).comp hpair
  have heq : (fun z : BootstrapPrivateRoundStreams.SourceInput p => strictPastDecoderFlag rate rewards C_star C_h s n hn z) =
      fun z => ReferenceInspectedPastRoundObservations.pastSavedWrongFlag
        rate rewards C_star C_h n hn z || strictPastAmbiguousFlag rate rewards C_star C_h s n hn z := by
    funext z
    exact strictPastDecoderFlag_eq_savedWrong_or_ambiguous rate rewards C_star C_h s n hn z
  change Measurable (fun z : BootstrapPrivateRoundStreams.SourceInput p => strictPastDecoderFlag rate rewards C_star C_h s n hn z)
  exact heq ▸ hor

/-- The Boolean complement is measurable in the same exact inspected field. -/
theorem strictPastDecoderFlag_compl_measurable_in_inspectedHistorySpace
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s n : ℕ) (hn : n ≤ p.T) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn]
      (fun z => !(strictPastDecoderFlag rate rewards C_star C_h s n hn z)) := by
  let : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
    ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn
  exact (measurable_of_countable (fun b : Bool => !b)).comp
    (strictPastDecoderFlag_measurable_in_inspectedHistorySpace
      rate rewards C_star C_h s n hn)

/-- The detector is Borel on the unchanged original source space. -/
theorem measurable_strictPastDecoderFlag
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s n : ℕ) (hn : n ≤ p.T) :
    Measurable (strictPastDecoderFlag rate rewards C_star C_h s n hn) :=
  (strictPastDecoderFlag_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h s n hn).mono
      (ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_original
        rate rewards C_star C_h (detectorFixedControl p) n hn) le_rfl

/-- The Boolean complement is Borel on the unchanged original source space. -/
theorem measurable_strictPastDecoderFlag_compl
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s n : ℕ) (hn : n ≤ p.T) :
    Measurable (fun z => !(strictPastDecoderFlag rate rewards C_star C_h s n hn z)) :=
  (strictPastDecoderFlag_compl_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h s n hn).mono
      (ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_original
        rate rewards C_star C_h (detectorFixedControl p) n hn) le_rfl
