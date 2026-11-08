/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteInclusivePhysicalDecoderErrors
public import Bandits.Support.ReferenceActualLiveEmptySignedRewardCalendar

/-!
# Literal first-bad calendar for signed stopped accounting

This module scans the original complete source at every physical date. Its
finite minimum retains the first literal decoder branch or overflow update,
with `T + 1` as the no-tested-event sentinel. It does not stop the physical
run or identify a logical stopping time.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceCompleteSignedFirstBadCalendar

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev GridRewardTable (p : Parameters) :=
  ActualInitializationPhysicalStep.GridRewardTable p

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (z : SourceInput p)

/-- The exact source detector at calendar date `t`. The decoder branches are
tested only when the inclusive physical scan gate passes; the physical
overflow detector remains a separate branch. -/
public def sourceBadAt (t : Fin p.T) : Prop :=
  (ReferenceCompleteInclusivePhysicalDecoderErrors.actualInclusivePhysicalScanGate
      rate rewards C_star C_h z t ∧
    (ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt
        rate rewards C_star C_h t z ∨
      ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt
        rate rewards C_star C_h z t)) ∨
    z ∈ ReferenceOriginalNumericalFirstOverflowLocator.firstOverflowUpdateAt
      rate rewards C_star C_h t

/-- The finite calendar scan of the literal source detector. -/
public def badRounds : Finset (Fin p.T) :=
  Finset.univ.filter fun t => sourceBadAt rate rewards C_star C_h z t

/-- One-based detector dates together with the literal exhaustion sentinel. -/
public def badDateSet : Finset ℕ :=
  (badRounds rate rewards C_star C_h z).image (fun t => t.val + 1) ∪
    {p.T + 1}

/-- The source's literal finite minimum of tested one-based bad dates and
`T + 1`. -/
public def firstBadDate : ℕ :=
  (badDateSet rate rewards C_star C_h z).min'
    (by simp [badDateSet])

/-- The actual launch date of the unchanged generated initialization input. -/
public def actualLaunchRound : ℕ :=
  ReferenceInitializationRun.launchRound
    (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h)

theorem badDateSet_nonempty : (badDateSet rate rewards C_star C_h z).Nonempty := by
  simp [badDateSet]

theorem firstBadDate_mem :
    firstBadDate rate rewards C_star C_h z ∈ badDateSet rate rewards C_star C_h z :=
  Finset.min'_mem _ (badDateSet_nonempty rate rewards C_star C_h z)

theorem firstBadDate_lower_bound :
    1 ≤ firstBadDate rate rewards C_star C_h z := by
  have hmem := firstBadDate_mem rate rewards C_star C_h z
  simp only [badDateSet, Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with himage | hsentinel
  · rcases Finset.mem_image.mp himage with ⟨t, _ht, hdate⟩
    omega
  · omega

theorem firstBadDate_upper_bound :
    firstBadDate rate rewards C_star C_h z ≤ p.T + 1 := by
  apply Finset.min'_le
  simp [badDateSet]

theorem firstBadDate_le_T_iff_exists_bad_date :
    firstBadDate rate rewards C_star C_h z ≤ p.T ↔
      ∃ t : Fin p.T, sourceBadAt rate rewards C_star C_h z t := by
  constructor
  · intro hb
    have hmem := firstBadDate_mem rate rewards C_star C_h z
    change firstBadDate rate rewards C_star C_h z ∈
      ((badRounds rate rewards C_star C_h z).image (fun t => t.val + 1) ∪
        {p.T + 1}) at hmem
    rcases Finset.mem_union.mp hmem with himage | hsentinel
    · rcases Finset.mem_image.mp himage with ⟨t, ht, hdate⟩
      exact ⟨t, (Finset.mem_filter.mp ht).2⟩
    · have hsentinel' : firstBadDate rate rewards C_star C_h z = p.T + 1 :=
        Finset.mem_singleton.mp hsentinel
      omega
  · rintro ⟨t, hbad⟩
    have htmem : t ∈ badRounds rate rewards C_star C_h z :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩
    have hdate : t.val + 1 ∈ badDateSet rate rewards C_star C_h z := by
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_image.mpr ⟨t, htmem, rfl⟩
    have hmin : firstBadDate rate rewards C_star C_h z ≤ t.val + 1 :=
      Finset.min'_le (badDateSet rate rewards C_star C_h z) (t.val + 1) hdate
    omega

theorem firstBadDate_eq_sentinel_iff_no_tested_bad_date :
    firstBadDate rate rewards C_star C_h z = p.T + 1 ↔
      ∀ t : Fin p.T, ¬ sourceBadAt rate rewards C_star C_h z t := by
  constructor
  · intro hb t hbad
    have hle := (firstBadDate_le_T_iff_exists_bad_date rate rewards C_star C_h z).2
      ⟨t, hbad⟩
    rw [hb] at hle
    omega
  · intro hnone
    apply Nat.le_antisymm
    · exact firstBadDate_upper_bound rate rewards C_star C_h z
    · by_contra hnot
      have hwithin : firstBadDate rate rewards C_star C_h z ≤ p.T := by omega
      obtain ⟨t, ht⟩ :=
        (firstBadDate_le_T_iff_exists_bad_date rate rewards C_star C_h z).1 hwithin
      exact hnone t ht

theorem firstBadDate_firstBadCalendar :
    SignedStoppedRegretAccounting.firstBadCalendar
      (badRounds rate rewards C_star C_h z)
      (firstBadDate rate rewards C_star C_h z) := by
  constructor
  · intro t ht
    have hdate : t.val + 1 ∈ badDateSet rate rewards C_star C_h z := by
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
    have hmin : firstBadDate rate rewards C_star C_h z ≤ t.val + 1 :=
      Finset.min'_le (badDateSet rate rewards C_star C_h z) (t.val + 1) hdate
    simpa [SignedStoppedRegretAccounting.calendarRound] using hmin
  · intro hb
    have hmem := firstBadDate_mem rate rewards C_star C_h z
    change firstBadDate rate rewards C_star C_h z ∈
      ((badRounds rate rewards C_star C_h z).image (fun t => t.val + 1) ∪
        {p.T + 1}) at hmem
    rcases Finset.mem_union.mp hmem with himage | hsentinel
    · rcases Finset.mem_image.mp himage with ⟨u, hu, hdate⟩
      refine ⟨u, ?_, ?_⟩
      · simpa [SignedStoppedRegretAccounting.calendarRound] using hdate
      · exact hu
    · have hsentinel' : firstBadDate rate rewards C_star C_h z = p.T + 1 :=
        Finset.mem_singleton.mp hsentinel
      omega

theorem firstBadDate_unique_characterization (candidate : ℕ)
    (_hlo : 1 ≤ candidate) (hhi : candidate ≤ p.T + 1)
    (hfirst : SignedStoppedRegretAccounting.firstBadCalendar
      (badRounds rate rewards C_star C_h z) candidate) :
    candidate = firstBadDate rate rewards C_star C_h z := by
  by_cases hexists : ∃ t : Fin p.T, t ∈ badRounds rate rewards C_star C_h z
  · obtain ⟨t₀, ht₀⟩ := hexists
    have hcandidate_le_T : candidate ≤ p.T := by
      have hle := hfirst.1 t₀ ht₀
      have ht0le : SignedStoppedRegretAccounting.calendarRound t₀ ≤ p.T := by
        simp [SignedStoppedRegretAccounting.calendarRound]
      exact hle.trans ht0le
    obtain ⟨t, htdate, htmem⟩ := hfirst.2 hcandidate_le_T
    have hcandidate_mem : candidate ∈ badDateSet rate rewards C_star C_h z := by
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_image.mpr
      refine ⟨t, htmem, ?_⟩
      simpa [SignedStoppedRegretAccounting.calendarRound] using htdate
    have hmin_le : firstBadDate rate rewards C_star C_h z ≤ candidate :=
      Finset.min'_le (badDateSet rate rewards C_star C_h z) candidate hcandidate_mem
    have hfirstmem := firstBadDate_mem rate rewards C_star C_h z
    change firstBadDate rate rewards C_star C_h z ∈
      ((badRounds rate rewards C_star C_h z).image (fun u => u.val + 1) ∪
        {p.T + 1}) at hfirstmem
    rcases Finset.mem_union.mp hfirstmem with himage | hsentinel
    · rcases Finset.mem_image.mp himage with ⟨u, hu, hdate⟩
      have hle := hfirst.1 u hu
      have hdate' : SignedStoppedRegretAccounting.calendarRound u =
          firstBadDate rate rewards C_star C_h z := by
        simpa [SignedStoppedRegretAccounting.calendarRound] using hdate
      rw [hdate'] at hle
      exact Nat.le_antisymm hle hmin_le
    · have hsentinel' : firstBadDate rate rewards C_star C_h z = p.T + 1 :=
        Finset.mem_singleton.mp hsentinel
      have hle := hfirst.1 t₀ ht₀
      have hdate : SignedStoppedRegretAccounting.calendarRound t₀ ≤ p.T := by
        simp [SignedStoppedRegretAccounting.calendarRound]
      omega
  · have hnoTested : ∀ t : Fin p.T, ¬ sourceBadAt rate rewards C_star C_h z t := by
      intro t hbad
      exact hexists ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩⟩
    have hsentinel :=
      (firstBadDate_eq_sentinel_iff_no_tested_bad_date rate rewards C_star C_h z).2
        hnoTested
    have hcandidate_gt_T : p.T < candidate := by
      by_contra hnot
      have hle : candidate ≤ p.T := Nat.le_of_not_gt hnot
      obtain ⟨t, _htdate, htmem⟩ := hfirst.2 hle
      exact hexists ⟨t, htmem⟩
    omega

private theorem ordinaryWrongCompletionPrefix_false_of_safe_source_prefix
    (n : ℕ) :
    n ≤ p.T →
    (∀ t : Fin p.T, t.val < n →
      ReferenceCompleteInclusivePhysicalDecoderErrors.actualInclusivePhysicalScanGate
        rate rewards C_star C_h z t) →
    (∀ t : Fin p.T, t.val < n → ¬ sourceBadAt rate rewards C_star C_h z t) →
    ¬ ReferenceCompleteOrdinaryFalseEventObservableLocality.ordinaryWrongCompletionPrefix
      rate rewards C_star C_h n z := by
  induction n with
  | zero =>
      intro _ _ _ hprefix
      rw [ReferenceCompleteOrdinaryFalseEventObservableLocality.ordinaryWrongCompletionPrefix_zero
        rate rewards C_star C_h z] at hprefix
      exact hprefix
  | succ n ih =>
      intro hn hgate hclean hprefix
      have hnlt : n < p.T := by omega
      rw [ReferenceCompleteOrdinaryFalseEventObservableLocality.ordinaryWrongCompletionPrefix_succ_iff
        rate rewards C_star C_h n hnlt z] at hprefix
      rcases hprefix with hbefore | hcurrent
      · apply ih (by omega)
          (fun t ht => hgate t (by omega))
          (fun t ht => hclean t (by omega))
        exact hbefore
      · have hnVal : (⟨n, hnlt⟩ : Fin p.T).val < n + 1 := by simp
        apply hclean ⟨n, hnlt⟩ hnVal
        exact Or.inl ⟨hgate ⟨n, hnlt⟩ hnVal, Or.inl hcurrent⟩

theorem firstBadDate_detecting_branch (hb : firstBadDate rate rewards C_star C_h z ≤ p.T) :
    ∃ t : Fin p.T,
      SignedStoppedRegretAccounting.calendarRound t =
        firstBadDate rate rewards C_star C_h z ∧
      ((ReferenceCompleteInclusivePhysicalDecoderErrors.actualInclusivePhysicalScanGate
          rate rewards C_star C_h z t ∧
        (ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt
            rate rewards C_star C_h t z ∨
          ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt
            rate rewards C_star C_h z t)) ∨
        z ∈ ReferenceOriginalNumericalFirstOverflowLocator.firstOverflowUpdateAt
          rate rewards C_star C_h t) := by
  have hfirst := (firstBadDate_firstBadCalendar rate rewards C_star C_h z).2 hb
  rcases hfirst with ⟨t, ht, hmem⟩
  refine ⟨t, ht, ?_⟩
  exact (Finset.mem_filter.mp hmem).2

theorem sourceBadAt_false_before_firstBadDate (t : Fin p.T)
    (ht : t.val + 1 < firstBadDate rate rewards C_star C_h z) :
    ¬ sourceBadAt rate rewards C_star C_h z t := by
  intro hbad
  have htmem : t ∈ badRounds rate rewards C_star C_h z :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩
  have hdate : t.val + 1 ∈ badDateSet rate rewards C_star C_h z := by
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_image.mpr ⟨t, htmem, rfl⟩
  have hmin : firstBadDate rate rewards C_star C_h z ≤ t.val + 1 :=
    Finset.min'_le (badDateSet rate rewards C_star C_h z) (t.val + 1) hdate
  omega

theorem strict_prefix_branch_absence :
    ∀ t : Fin p.T, t.val + 1 < firstBadDate rate rewards C_star C_h z →
      (¬ (ReferenceCompleteInclusivePhysicalDecoderErrors.actualInclusivePhysicalScanGate
          rate rewards C_star C_h z t ∧
        (ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt
            rate rewards C_star C_h t z ∨
          ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt
            rate rewards C_star C_h z t)) ∧
       z ∉ ReferenceOriginalNumericalFirstOverflowLocator.firstOverflowUpdateAt
          rate rewards C_star C_h t) := by
  intro t ht
  have hnone := sourceBadAt_false_before_firstBadDate
    rate rewards C_star C_h z t ht
  simpa only [sourceBadAt, not_or] using hnone

theorem sourceBadAt_exists_iff_event_union :
    (∃ t : Fin p.T, sourceBadAt rate rewards C_star C_h z t) ↔
      z ∈ ReferenceCompleteInclusivePhysicalDecoderErrors.completeInclusiveDecoderFailureEvent
          rate rewards C_star C_h ∪
        ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
          rate rewards C_star C_h := by
  constructor
  · rintro ⟨t, hbad⟩
    rcases hbad with ⟨hgate, hbranches⟩ | hoverflow
    · rcases hbranches with hordinary | hawaited
      · left
        change z ∈
          ReferenceCompleteInclusivePhysicalDecoderErrors.stoppedOrdinaryWrongCompletionEvent
              rate rewards C_star C_h ∨
            z ∈ ReferenceCompleteInclusivePhysicalDecoderErrors.stoppedFixedAwaitedAmbiguityEvent
              rate rewards C_star C_h
        left
        exact ⟨t, hgate, hordinary⟩
      · left
        change z ∈
          ReferenceCompleteInclusivePhysicalDecoderErrors.stoppedOrdinaryWrongCompletionEvent
              rate rewards C_star C_h ∨
            z ∈ ReferenceCompleteInclusivePhysicalDecoderErrors.stoppedFixedAwaitedAmbiguityEvent
              rate rewards C_star C_h
        right
        exact ⟨t, hgate, hawaited⟩
    · right
      have hObserved : z ∈
          ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent
            rate rewards C_star C_h := by
        rw [ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent_eq_firstOverflowUpdateUnion
          rate rewards C_star C_h]
        exact Set.mem_iUnion.mpr ⟨t, hoverflow⟩
      rw [ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent_eq_observedNumericalOverflowEvent
        rate rewards C_star C_h]
      exact hObserved
  · intro hevent
    rcases hevent with hdecoder | hphysical
    · change z ∈
        ReferenceCompleteInclusivePhysicalDecoderErrors.stoppedOrdinaryWrongCompletionEvent
            rate rewards C_star C_h ∨
          z ∈ ReferenceCompleteInclusivePhysicalDecoderErrors.stoppedFixedAwaitedAmbiguityEvent
            rate rewards C_star C_h at hdecoder
      rcases hdecoder with hordinary | hawaited
      · rcases hordinary with ⟨t, hgate, hwrong⟩
        exact ⟨t, Or.inl ⟨hgate, Or.inl hwrong⟩⟩
      · rcases hawaited with ⟨t, hgate, hamb⟩
        exact ⟨t, Or.inl ⟨hgate, Or.inr hamb⟩⟩
    · have hObserved : z ∈
        ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent
          rate rewards C_star C_h := by
        rw [← ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent_eq_observedNumericalOverflowEvent
          rate rewards C_star C_h]
        exact hphysical
      have hUnion :=
        (ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent_eq_firstOverflowUpdateUnion
          rate rewards C_star C_h).symm ▸ hObserved
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hUnion
      exact ⟨t, Or.inr ht⟩

theorem firstBadDate_le_T_iff_event_union :
    firstBadDate rate rewards C_star C_h z ≤ p.T ↔
      z ∈ ReferenceCompleteInclusivePhysicalDecoderErrors.completeInclusiveDecoderFailureEvent
          rate rewards C_star C_h ∪
        ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
          rate rewards C_star C_h := by
  rw [firstBadDate_le_T_iff_exists_bad_date]
  exact sourceBadAt_exists_iff_event_union rate rewards C_star C_h z

/-- A failure of the inclusive scan gate has already passed the actual first
overflow update. The detector remains on the same original zero-origin word. -/
private theorem overflow_update_before_failed_gate (t : Fin p.T)
    (hgate : ¬ ReferenceCompleteInclusivePhysicalDecoderErrors.actualInclusivePhysicalScanGate
      rate rewards C_star C_h z t) :
    ∃ q : Fin p.T,
      q.val + 1 ≤ t.val ∧
      z ∈ ReferenceOriginalNumericalFirstOverflowLocator.firstOverflowUpdateAt
        rate rewards C_star C_h q := by
  have hgateiff :=
    ReferenceCompleteInclusivePhysicalDecoderErrors.actualInclusivePhysicalScanGate_iff_noNumericalOverflowThrough
      rate rewards C_star C_h z t
  have hnotThrough : ¬
      ReferenceCompleteInclusivePhysicalDecoderErrors.noNumericalOverflowThrough
        rate rewards C_star C_h t z := by
    intro hthrough
    exact hgate (hgateiff.mpr hthrough)
  have hnotBy :=
    ReferenceCompleteInclusivePhysicalDecoderErrors.noNumericalOverflowThrough_iff_not_numericalOverflowBy
      rate rewards C_star C_h t z
  have hby :
      ReferenceCompleteInclusivePhysicalDecoderErrors.numericalOverflowBy
        rate rewards C_star C_h t z := by
    by_contra hnone
    exact hnotThrough (hnotBy.mpr hnone)
  rcases hby with ⟨n, hnt, o, ho, a, ha⟩
  have hObserved : z ∈
      ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent
        rate rewards C_star C_h := ⟨n, by omega, o, ho, a, ha⟩
  rw [ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent_eq_firstOverflowUpdateUnion
    rate rewards C_star C_h] at hObserved
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hObserved
  have hqEvent := hq
  simp only [ReferenceOriginalNumericalFirstOverflowLocator.firstOverflowUpdateAt,
    Set.mem_ofPred_eq] at hq
  rcases hq with ⟨L, r, c, arm, _hinputs, _hstart, _hstartlt, _hlen,
    _hnext, _hlookup, _htime, _hrecord, _hcell, _hphase, _hread, _hreadNext,
    _hbeforeOverflow, _henabled, _hoverflow, _hthreshold, _hprior, _hpresent,
    hnoEarlier, _htransition⟩
  have hpost_le : q.val + 1 ≤ n := by
    by_contra hnot
    have hnlt : n < q.val + 1 := by omega
    exact hnoEarlier n hnlt ⟨o, ho, a, ha⟩
  exact ⟨q, by omega, hqEvent⟩

theorem inclusive_gate_through_first_bad_date (t : Fin p.T)
    (ht : t.val + 1 ≤ firstBadDate rate rewards C_star C_h z) :
    ReferenceCompleteInclusivePhysicalDecoderErrors.actualInclusivePhysicalScanGate
      rate rewards C_star C_h z t := by
  by_contra hgate
  obtain ⟨q, hqle, hq⟩ := overflow_update_before_failed_gate
    rate rewards C_star C_h z t hgate
  have hqbad : sourceBadAt rate rewards C_star C_h z q := Or.inr hq
  have hqmem : q ∈ badRounds rate rewards C_star C_h z :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqbad⟩
  have hqdate : q.val + 1 ∈ badDateSet rate rewards C_star C_h z := by
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_image.mpr ⟨q, hqmem, rfl⟩
  have hmin := Finset.min'_le (badDateSet rate rewards C_star C_h z)
    (q.val + 1) hqdate
  change firstBadDate rate rewards C_star C_h z ≤ q.val + 1 at hmin
  omega

theorem ordinaryWrongCompletionPrefix_absent_before_firstBadDate :
    ¬ ReferenceCompleteOrdinaryFalseEventObservableLocality.ordinaryWrongCompletionPrefix
      rate rewards C_star C_h
      (min (firstBadDate rate rewards C_star C_h z - 1) p.T) z := by
  apply ordinaryWrongCompletionPrefix_false_of_safe_source_prefix
    rate rewards C_star C_h z
  · exact Nat.min_le_right _ _
  · intro t ht
    apply inclusive_gate_through_first_bad_date rate rewards C_star C_h z t
    have hbpos := firstBadDate_lower_bound rate rewards C_star C_h z
    omega
  · intro t ht
    apply sourceBadAt_false_before_firstBadDate rate rewards C_star C_h z t
    have hbpos := firstBadDate_lower_bound rate rewards C_star C_h z
    omega

theorem firstBadDate_before_or_after_actual_launch :
    firstBadDate rate rewards C_star C_h z <
        actualLaunchRound rate rewards C_star C_h z ∨
      actualLaunchRound rate rewards C_star C_h z ≤
        firstBadDate rate rewards C_star C_h z :=
  Nat.lt_or_ge _ _

theorem no_launch_has_no_overflow_update
    (hno : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = none) (t : Fin p.T) :
    z ∉ ReferenceOriginalNumericalFirstOverflowLocator.firstOverflowUpdateAt
      rate rewards C_star C_h t := by
  intro hoverflow
  rcases hoverflow with ⟨_L, _r, _c, _a, _hinputs, hstart, _hslt,
    _hlen, _hnext, _hlookup, _htime, _hrecord, _hcell, _hphase, _hread,
    _hreadNext, _hbefore, _henabled, _hoverflow, _hthreshold, _hprior,
    _hpresent, _htransition⟩
  have hstart' :
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val := by
    simpa [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] using hstart
  have hT := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
    rate z rewards C_star C_h hno
  omega

theorem no_launch_has_no_awaited_completion
    (hno : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = none) (t : Fin p.T) :
    ¬ ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt
      rate rewards C_star C_h z t :=
  ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt_false_of_no_launch
    rate rewards C_star C_h z t hno

private theorem physical_overflow_event_false_of_no_overflow_update
    (hno : ∀ t : Fin p.T,
      z ∉ ReferenceOriginalNumericalFirstOverflowLocator.firstOverflowUpdateAt
        rate rewards C_star C_h t) :
    z ∉ ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
      rate rewards C_star C_h := by
  intro hphysical
  have hObserved : z ∈
      ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent
        rate rewards C_star C_h := by
    rw [← ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent_eq_observedNumericalOverflowEvent
      rate rewards C_star C_h]
    exact hphysical
  rw [ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent_eq_firstOverflowUpdateUnion
    rate rewards C_star C_h] at hObserved
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hObserved
  exact hno t ht

theorem no_launch_sentinel_and_absence
    (hno : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = none) :
    actualLaunchRound rate rewards C_star C_h z = p.T + 1 ∧
      z ∉ ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
        rate rewards C_star C_h ∧
      (∀ t, z ∉ ReferenceOriginalNumericalFirstOverflowLocator.firstOverflowUpdateAt
        rate rewards C_star C_h t) ∧
      (∀ t, ¬ ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt
        rate rewards C_star C_h z t) := by
  have hnoUpdate : ∀ t : Fin p.T,
      z ∉ ReferenceOriginalNumericalFirstOverflowLocator.firstOverflowUpdateAt
        rate rewards C_star C_h t := by
    intro t
    exact no_launch_has_no_overflow_update rate rewards C_star C_h z hno t
  refine ⟨?_, physical_overflow_event_false_of_no_overflow_update
    rate rewards C_star C_h z hnoUpdate, hnoUpdate, ?_⟩
  · exact ReferenceCompletePhysicalHistory.no_launch_sentinel_round
      rate z rewards C_star C_h hno
  · intro t
    exact no_launch_has_no_awaited_completion rate rewards C_star C_h z hno t

theorem terminal_crossing_sentinel_and_absence (active : ReferenceActivePhysicalStep.State p rate)
    (hlaunched : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active)
    (hterminal : ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h = p.T) :
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h ≠ none ∧
      actualLaunchRound rate rewards C_star C_h z = p.T + 1 ∧
      z ∉ ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
        rate rewards C_star C_h ∧
      (∀ t, z ∉ ReferenceOriginalNumericalFirstOverflowLocator.firstOverflowUpdateAt
        rate rewards C_star C_h t) ∧
      (∀ t, ¬ ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt
        rate rewards C_star C_h z t) := by
  rcases ReferenceCompletePhysicalHistory.terminal_crossing_sentinel_round
      rate z rewards C_star C_h active hlaunched hterminal with ⟨hne, hL⟩
  have hnoUpdate : ∀ t : Fin p.T,
      z ∉ ReferenceOriginalNumericalFirstOverflowLocator.firstOverflowUpdateAt
        rate rewards C_star C_h t := by
    intro t hoverflow
    rcases hoverflow with ⟨_L, _r, _c, _a, _hinputs, hstart, _hslt,
      _hlen, _hnext, _hlookup, _htime, _hrecord, _hcell, _hphase, _hread,
      _hreadNext, _hbefore, _henabled, _hoverflow, _hthreshold, _hprior,
      _hpresent, _htransition⟩
    have hstart' :
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val := by
      simpa [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] using hstart
    omega
  refine ⟨hne, hL,
    physical_overflow_event_false_of_no_overflow_update
      rate rewards C_star C_h z hnoUpdate, hnoUpdate, ?_⟩
  · intro t
    exact ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt_false_of_terminal_start
      rate rewards C_star C_h z t hterminal

theorem complete_signed_first_bad_calendar :
    1 ≤ firstBadDate rate rewards C_star C_h z ∧
    firstBadDate rate rewards C_star C_h z ≤ p.T + 1 ∧
    SignedStoppedRegretAccounting.firstBadCalendar
      (badRounds rate rewards C_star C_h z)
      (firstBadDate rate rewards C_star C_h z) ∧
    (firstBadDate rate rewards C_star C_h z ≤ p.T ↔
      z ∈ ReferenceCompleteInclusivePhysicalDecoderErrors.completeInclusiveDecoderFailureEvent
          rate rewards C_star C_h ∪
        ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
          rate rewards C_star C_h) ∧
    (∀ t : Fin p.T, t.val + 1 ≤ firstBadDate rate rewards C_star C_h z →
      ReferenceCompleteInclusivePhysicalDecoderErrors.actualInclusivePhysicalScanGate
        rate rewards C_star C_h z t) ∧
    (firstBadDate rate rewards C_star C_h z = p.T + 1 ↔
      ∀ t : Fin p.T, ¬ sourceBadAt rate rewards C_star C_h z t) ∧
    (firstBadDate rate rewards C_star C_h z < actualLaunchRound rate rewards C_star C_h z ∨
      actualLaunchRound rate rewards C_star C_h z ≤ firstBadDate rate rewards C_star C_h z) := by
  exact ⟨firstBadDate_lower_bound rate rewards C_star C_h z,
    firstBadDate_upper_bound rate rewards C_star C_h z,
    firstBadDate_firstBadCalendar rate rewards C_star C_h z,
    firstBadDate_le_T_iff_event_union rate rewards C_star C_h z,
    fun t ht => inclusive_gate_through_first_bad_date rate rewards C_star C_h z t ht,
    firstBadDate_eq_sentinel_iff_no_tested_bad_date rate rewards C_star C_h z,
    firstBadDate_before_or_after_actual_launch rate rewards C_star C_h z⟩

end Bandits.Support.ReferenceCompleteSignedFirstBadCalendar

end
