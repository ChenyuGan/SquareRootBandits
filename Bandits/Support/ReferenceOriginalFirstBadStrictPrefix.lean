/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteSignedFirstBadCalendar
public import Bandits.Support.ReferenceOriginalCalendarContinuingLiveRecorderLaw

import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Strict source prefixes for the original inclusive first-bad scan

The stop test is the strict-past restriction of the accepted source's dated
detector. Its numerical branch keeps the optional pre-boundary readout and the
first detecting update. The physical source remains defined and continues
after an analytic stop. No stopping-time or history premise is added.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput)
open ContinuousLearningRows (TimeControl)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix sourcePrefixFiltration)
open ReferenceFixedTimeSourceControlCoupling (replaceSourceControl)
open ReferenceCompleteInclusivePhysicalDecoderErrors (numericalOverflowBy
  actualInclusivePhysicalScanGate actualInclusivePhysicalScanGate_iff_noNumericalOverflowThrough
  noNumericalOverflowThrough_iff_not_numericalOverflowBy)
open ReferenceOriginalNumericalFirstOverflowLocator (firstOverflowUpdateAt
  observedNumericalOverflowEvent observedNumericalOverflowEvent_eq_firstOverflowUpdateUnion)
open ReferenceCompleteSignedFirstBadCalendar (firstBadDate sourceBadAt
  sourceBadAt_false_before_firstBadDate firstBadDate_firstBadCalendar)
open scoped Classical

namespace Bandits.Support.ReferenceOriginalFirstBadStrictPrefix

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev GridRewardTable (p : Parameters) := ActualInitializationPhysicalStep.GridRewardTable p

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (z : SourceInput p)

local notation "badAt" => sourceBadAt rate rewards C_star C_h z
local notation "numericalReadout" =>
  ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout rate rewards C_star C_h

/-! This is exactly the canonical dated detector restricted to dates before
`q`; the one-based date of a detected bad event is therefore not discarded. -/
public def noBadEventStrictlyBefore (q : Fin p.T) : Prop :=
  ∀ s : Fin p.T, s.val < q.val → ¬ badAt s

public theorem firstBadDate_prefix_iff (q : Fin p.T) :
    q.val + 1 ≤ firstBadDate rate rewards C_star C_h z ↔
      noBadEventStrictlyBefore rate rewards C_star C_h z q := by
  constructor
  · intro hstop s hs hbad
    have hbefore : s.val + 1 < firstBadDate rate rewards C_star C_h z := by omega
    exact sourceBadAt_false_before_firstBadDate rate rewards C_star C_h z s hbefore hbad
  · intro hnone
    by_contra hnot
    have hb : firstBadDate rate rewards C_star C_h z ≤ q.val := by omega
    have hbT : firstBadDate rate rewards C_star C_h z ≤ p.T := by omega
    obtain ⟨s, hdate, hbad⟩ :=
      (firstBadDate_firstBadCalendar rate rewards C_star C_h z).2 hbT
    have hround : s.val + 1 = firstBadDate rate rewards C_star C_h z := by
      change SignedStoppedRegretAccounting.calendarRound s = _ at hdate
      exact hdate
    have hs : s.val < q.val := by omega
    exact hnone s hs (Finset.mem_filter.mp hbad).2

/-! A boundary crossing is witnessed only by a present optional numerical
readout. Thus missing launch/readout branches remain absent. -/
public def numericalBoundaryCrossing (n : ℕ) (z : SourceInput p) : Prop :=
  ∃ o : ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K,
    numericalReadout n z = some o ∧
    ∃ a : Fin p.K, ((o.1 a).2 : ℝ) /
      ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
        1 / (32 * rate.eta.val)

/-! The locator's least-update witness makes the current boundary exactly the
first crossing update, while every earlier observed crossing is excluded. -/
public theorem firstOverflowUpdateAt_iff_boundary (q : Fin p.T) (z : SourceInput p) :
    z ∈ firstOverflowUpdateAt rate rewards C_star C_h q ↔
      numericalBoundaryCrossing rate rewards C_star C_h (q.val + 1) z ∧
        ¬ numericalOverflowBy rate rewards C_star C_h q z := by
  constructor
  · intro hfirst
    rcases hfirst with ⟨L, r, c, a, _hinputs, _hs, _hslt, _hlen, _hnext, _hlookup,
      _htime, _hrecord, _hcell, _hphase, _hread, hpost, _hbefore, _henabled,
      _hflag, hthreshold, _hprior, _hpresent, hleast, _htransition⟩
    refine ⟨⟨_, hpost, a, hthreshold⟩, ?_⟩
    rintro ⟨n, hn, o, ho, arm, ha⟩
    exact hleast n (by omega) ⟨o, ho, arm, ha⟩
  · rintro ⟨hcross, hno⟩
    have hObserved : z ∈ observedNumericalOverflowEvent rate rewards C_star C_h := by
      obtain ⟨o, ho, a, ha⟩ := hcross
      exact ⟨q.val + 1, Nat.succ_le_of_lt q.isLt, o, ho, a, ha⟩
    rw [observedNumericalOverflowEvent_eq_firstOverflowUpdateUnion
      rate rewards C_star C_h] at hObserved
    obtain ⟨q', hfirst⟩ := Set.mem_iUnion.mp hObserved
    have hsave := hfirst
    rcases hfirst with ⟨L, r, c, a, _hinputs, _hs, _hslt, _hlen, _hnext, _hlookup,
      _htime, _hrecord, _hcell, _hphase, _hread, hpost, _hbefore, _henabled,
      _hflag, hthreshold, _hprior, _hpresent, hleast, _htransition⟩
    have hle : q'.val ≤ q.val := by
      by_contra hnot
      obtain ⟨o, ho, arm, ha⟩ := hcross
      exact hleast (q.val + 1) (by omega) ⟨o, ho, arm, ha⟩
    have hge : q.val ≤ q'.val := by
      by_contra hnot
      exact hno ⟨q'.val + 1, by omega, _, hpost, a, hthreshold⟩
    have heq : q' = q := Fin.ext (Nat.le_antisymm hle hge)
    exact heq ▸ hsave

private theorem take_map_optional_lookup {A B : Type*} (f : A → Option B)
    (R : List A) (n : ℕ) (hn : n ≤ R.length) :
    (R.take n).map f = (List.range n).map (fun i => (R[i]?).bind f) := by
  induction n generalizing R with
  | zero => simp only [List.take_zero, List.map_nil, List.range_zero]
  | succ n ih =>
      cases R with
      | nil => simp only [List.length_nil, nonpos_iff_eq_zero, Nat.add_eq_zero_iff,
          Nat.one_ne_zero, and_false] at hn
      | cons a R =>
          have hn' : n ≤ R.length := by
            simpa only [List.length_cons, Nat.succ_le_succ_iff] using hn
          simp [List.range_succ_eq_map, ih R hn']

private theorem numericalReadout_eq_retained (t : Fin p.T) (z : SourceInput p) :
    numericalReadout t.val z =
      ReferenceFirstCollectionCurrentRetainedGate.prefixReadout? rate rewards C_star C_h t z := by
  have hslots :
      (((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).take
        (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)) =
        ReferenceFirstCollectionCurrentRetainedGate.pastSlots rate rewards C_star C_h t z := by
    apply take_map_optional_lookup
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    exact Nat.sub_le_sub_right (Nat.le_of_lt t.isLt) _
  simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart,
    ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?,
    ReferenceFirstCollectionCurrentRetainedGate.pastCells?, hslots]

private theorem numericalBoundaryCrossing_strictPrefix_measurable
    (control0 : TimeControl p) (q : Fin p.T) (n : ℕ) (hnq : n ≤ q.val) :
    MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)]
      {z : SourceInput p | numericalBoundaryCrossing rate rewards C_star C_h n z} := by
  let : MeasurableSpace (SourceInput p) := sourcePrefixFiltration control0 (q.val + 1)
  let t : Fin p.T := ⟨n, lt_of_le_of_lt hnq q.isLt⟩
  let Readout := ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K
  let : MeasurableSpace (Option Readout) := LaterAssignmentStartMeasurability.optionMeasurableSpace
  let test : Option Readout → Bool := fun o =>
    decide (∃ v, o = some v ∧ ∃ a : Fin p.K,
      ((v.1 a).2 : ℝ) / ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
        1 / (32 * rate.eta.val))
  have htest : Measurable test := by
    have hsome : Measurable (fun v : Readout => test (some v)) := by
      have hqueue : Measurable (fun v : Readout => decide (∃ a : Fin p.K,
          ((v.1 a).2 : ℝ) / ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
            1 / (32 * rate.eta.val))) :=
        (measurable_of_countable (fun queues : Fin p.K → ℕ × ℕ => decide (∃ a,
          ((queues a).2 : ℝ) / ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
            1 / (32 * rate.eta.val)))).comp measurable_fst
      simpa only [test, Option.some.injEq, exists_eq_left'] using hqueue
    have hsum : Measurable (fun o : Readout ⊕ PUnit => test
        ((Equiv.optionEquivSumPUnit Readout).symm o)) := hsome.sumElim measurable_const
    convert hsum.comp (comap_measurable (Equiv.optionEquivSumPUnit Readout)) using 1
    funext o
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  have hm := ReferenceFirstCollectionCurrentRetainedGate.prefixReadout_measurable
    rate rewards C_star C_h control0 t
  have hm' := htest.comp (hm.mono
    ((sourcePrefixFiltration control0).mono (Nat.add_le_add_right hnq 1)) le_rfl)
  convert hm' (measurableSet_singleton true) using 1
  ext z
  simp only [Function.comp_apply, test, Set.mem_preimage, Set.mem_singleton_iff,
    decide_eq_true_eq]
  rw [← numericalReadout_eq_retained rate rewards C_star C_h t z]
  rfl

private theorem numericalOverflowBy_strictPrefix_measurable
    (control0 : TimeControl p) (q : Fin p.T) :
    MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)]
      {z : SourceInput p | numericalOverflowBy rate rewards C_star C_h q z} := by
  let : MeasurableSpace (SourceInput p) := sourcePrefixFiltration control0 (q.val + 1)
  have heq : {z : SourceInput p | numericalOverflowBy rate rewards C_star C_h q z} =
      ⋃ n : ℕ, {z | n ≤ q.val ∧ numericalBoundaryCrossing rate rewards C_star C_h n z} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, numericalOverflowBy,
      numericalBoundaryCrossing]
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  by_cases hn : n ≤ q.val
  · simpa only [hn, true_and] using
      numericalBoundaryCrossing_strictPrefix_measurable rate rewards C_star C_h control0 q n hn
  · simp only [hn, false_and, Set.ofPred_false]
    exact MeasurableSet.empty

private theorem prelaunchDownFailure_strictPrefix_measurable
    (control0 : TimeControl p) (q t : Fin p.T) (htq : t.val < q.val)
    (i : Fin (p.m - 1)) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)]
      (fun z : SourceInput p =>
        ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
          rate rewards C_star C_h z i t) :=
  (ReferencePrelaunchInspectedDecoderPast.prelaunchDownFailureAt_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h q.val (Nat.le_of_lt q.isLt) t htq i).mono
      (ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_sourcePrefixFiltration
        rate rewards C_star C_h control0 q.val (Nat.le_of_lt q.isLt)) le_rfl

private theorem decoderFailureAt_iff (t : Fin p.T) (z : SourceInput p) :
    (ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt
        rate rewards C_star C_h t z ∨
      ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt
        rate rewards C_star C_h z t) ↔
      (∃ i, ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
        rate rewards C_star C_h z i t = true) ∨
      ReferenceFirstCollectionAwaitedDownFailureReadout.failureAt
        rate rewards C_star C_h z t := by
  rw [ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt_iff,
    ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt_iff_literal]
  simp only [ReferenceLiteralAwaitedAmbiguityRowObservation.literalDownAmbiguityAt_iff_fixedAwaitedDownFailureAt,
    ReferenceLiteralAwaitedAmbiguityRowObservation.literalUpAmbiguityAt_iff_fixedAwaitedUpFailureAt,
    ReferenceFirstCollectionAwaitedDownFailureReadout.failureAt,
    ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag, decide_eq_true_eq]
  exact or_assoc

private theorem numericalOverflowBy_iff_earlier_firstUpdate (q : Fin p.T) (z : SourceInput p) :
    numericalOverflowBy rate rewards C_star C_h q z ↔
      ∃ t : Fin p.T, t.val < q.val ∧ z ∈ firstOverflowUpdateAt rate rewards C_star C_h t := by
  constructor
  · rintro ⟨n, hn, o, ho, a, ha⟩
    have hevent : z ∈ observedNumericalOverflowEvent rate rewards C_star C_h :=
      ⟨n, hn.trans (Nat.le_of_lt q.isLt), o, ho, a, ha⟩
    rw [observedNumericalOverflowEvent_eq_firstOverflowUpdateUnion rate rewards C_star C_h]
      at hevent
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hevent
    have hsave := ht
    rcases ht with ⟨L, r, c, arm, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hleast, _⟩
    refine ⟨t, ?_, hsave⟩
    by_contra hnot
    exact hleast n (by omega) ⟨o, ho, a, ha⟩
  · rintro ⟨t, ht, hfirst⟩
    obtain ⟨⟨o, ho, a, ha⟩, _⟩ :=
      (firstOverflowUpdateAt_iff_boundary rate rewards C_star C_h t z).mp hfirst
    exact ⟨t.val + 1, by omega, o, ho, a, ha⟩

/-! This observer identity preserves the source's separate prelaunch DOWN
bits and saved/awaited failure flag. The inclusive physical gate is recovered
from absence of every earlier first overflow update. -/
public theorem noBadEventStrictlyBefore_iff_observers (q : Fin p.T) (z : SourceInput p) :
    noBadEventStrictlyBefore rate rewards C_star C_h z q ↔
      ¬ numericalOverflowBy rate rewards C_star C_h q z ∧
      (∀ t : Fin p.T, t.val < q.val → ∀ i : Fin (p.m - 1),
        ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
          rate rewards C_star C_h z i t = false) ∧
      ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
        rate rewards C_star C_h q.val z = false := by
  have hgate (hno : ¬ numericalOverflowBy rate rewards C_star C_h q z)
      (t : Fin p.T) (ht : t.val < q.val) :
      actualInclusivePhysicalScanGate rate rewards C_star C_h z t := by
    rw [actualInclusivePhysicalScanGate_iff_noNumericalOverflowThrough,
      noNumericalOverflowThrough_iff_not_numericalOverflowBy]
    rintro ⟨n, hn, o, ho, a, ha⟩
    exact hno ⟨n, by omega, o, ho, a, ha⟩
  constructor
  · intro hnone
    have hno : ¬ numericalOverflowBy rate rewards C_star C_h q z := by
      rw [numericalOverflowBy_iff_earlier_firstUpdate]
      rintro ⟨t, ht, hfirst⟩
      exact hnone t ht (Or.inr hfirst)
    have hdec (t : Fin p.T) (ht : t.val < q.val) :
        ¬ ((∃ i, ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
          rate rewards C_star C_h z i t = true) ∨
          ReferenceFirstCollectionAwaitedDownFailureReadout.failureAt
            rate rewards C_star C_h z t) := by
      intro h
      exact hnone t ht (Or.inl ⟨hgate hno t ht,
        (decoderFailureAt_iff rate rewards C_star C_h t z).mpr h⟩)
    refine ⟨hno, ?_, ?_⟩
    · intro t ht i
      exact Bool.eq_false_of_not_eq_true (fun hi => hdec t ht (Or.inl ⟨i, hi⟩))
    · rw [ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag_false_iff_no_earlier_failure]
      exact fun t ht hf => hdec t ht (Or.inr hf)
  · rintro ⟨hno, hpre, hflag⟩ t ht (hdecoder | hfirst)
    · have hdec := (decoderFailureAt_iff rate rewards C_star C_h t z).mp hdecoder.2
      rcases hdec with ⟨i, hi⟩ | hf
      · rw [hpre t ht i] at hi
        cases hi
      · exact (ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag_false_iff_no_earlier_failure
          rate rewards C_star C_h z q.val).mp hflag t ht hf
    · exact hno ((numericalOverflowBy_iff_earlier_firstUpdate rate rewards C_star C_h q z).mpr
        ⟨t, ht, hfirst⟩)

/-! The optional numerical boundary scan, original DOWN bits and saved/awaited
failure flag are all Borel on the exact strict source prefix. -/
public theorem noBadEventStrictlyBefore_strictPrefix_measurable
    (control0 : TimeControl p) (q : Fin p.T) :
    MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)]
      {z : SourceInput p | noBadEventStrictlyBefore rate rewards C_star C_h z q} := by
  let : MeasurableSpace (SourceInput p) := sourcePrefixFiltration control0 (q.val + 1)
  have hpre : MeasurableSet {z : SourceInput p | ∀ t : Fin p.T, t.val < q.val →
      ∀ i : Fin (p.m - 1), ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
        rate rewards C_star C_h z i t = false} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun ht =>
      MeasurableSet.iInter fun i =>
        (prelaunchDownFailure_strictPrefix_measurable rate rewards C_star C_h control0 q t ht i)
          (measurableSet_singleton false)
  have hflag := ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag_adapted
    rate rewards C_star C_h control0 q.val
  convert (numericalOverflowBy_strictPrefix_measurable rate rewards C_star C_h control0 q).compl.inter
    (hpre.inter (hflag (measurableSet_singleton false))) using 1
  ext z
  exact noBadEventStrictlyBefore_iff_observers rate rewards C_star C_h q z

/-! The stopping test is determined exactly by the original strict prefix; no
stopping-time assumption is used. -/
public theorem noBadEventStrictlyBefore_strictPrefix_factor (control0 : TimeControl p)
    (q : Fin p.T) (z : SourceInput p) :
    noBadEventStrictlyBefore rate rewards C_star C_h z q ↔
      noBadEventStrictlyBefore rate rewards C_star C_h
        (sourcePrefix control0 q.val z) q := by
  have hm : Measurable[sourcePrefixFiltration control0 (q.val + 1)]
      (fun z : SourceInput p => decide (noBadEventStrictlyBefore rate rewards C_star C_h z q)) := by
    apply measurable_to_bool
    convert noBadEventStrictlyBefore_strictPrefix_measurable
      rate rewards C_star C_h control0 q using 1
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq,
      Set.mem_ofPred_eq]
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ] at hm
  have heq := hm.factorsThrough
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
      control0 q.val q.val le_rfl z).symm
  exact decide_eq_decide.mp heq

public theorem firstBadDate_inclusive_prefix_factor (control0 : TimeControl p) (q : Fin p.T)
    (z : SourceInput p) :
    q.val + 1 ≤ firstBadDate rate rewards C_star C_h z ↔
      q.val + 1 ≤ firstBadDate rate rewards C_star C_h
        (sourcePrefix control0 q.val z) := by
  rw [firstBadDate_prefix_iff, firstBadDate_prefix_iff,
    noBadEventStrictlyBefore_strictPrefix_factor rate rewards C_star C_h control0 q z]

/-! Replacing the whole current physical control leaves the exact stop test
unchanged because `replaceSourceControl` preserves all offsets below `q`. -/
public theorem firstBadDate_inclusive_replaceSourceControl (control0 : TimeControl p)
    (q : Fin p.T) (z : SourceInput p) (control : TimeControl p) :
    q.val + 1 ≤ firstBadDate rate rewards C_star C_h z ↔
      q.val + 1 ≤ firstBadDate rate rewards C_star C_h
        (replaceSourceControl p q z control) := by
  rw [firstBadDate_inclusive_prefix_factor rate rewards C_star C_h control0 q z,
    firstBadDate_inclusive_prefix_factor rate rewards C_star C_h control0 q
      (replaceSourceControl p q z control)]
  rw [ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current control0 q z control]

end Bandits.Support.ReferenceOriginalFirstBadStrictPrefix

end
