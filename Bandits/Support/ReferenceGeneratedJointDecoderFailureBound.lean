/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedAllWrongDownEvent
public import Bandits.Support.ReferenceStrictPastFailureCalendarAlignment
public import Bandits.Support.ReferenceAwaitedUpDecoderErrorProbability

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.FieldSimp

/-!
# Joint original-source budget for literal decoder failures

The saved-wrong diagnostic is split into its retained UP and DOWN meanings
inside one fixed complete-suffix prefix. The same fixed-horizon event then
covers the strict-past calendar readouts, without conditioning on launch fibres
or summing over phases, dates, or identifiers.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Bandits.Support.ReferenceGeneratedJointDecoderFailureBound

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)

abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput p
abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

/-- The saved-wrong diagnostic on a fixed physical complete-suffix prefix is
covered by the existing actual all-wrong-DOWN event and the literal generated
wrong-UP event on that same prefix. -/
theorem savedWrongSuffixPrefixEvent_subset_jointDecoderEvents
    (prefixCount : ℕ) :
    ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
        (r := rate) rewards C_star C_h prefixCount ⊆
      ReferenceGeneratedAllWrongDownEvent.generatedAllWrongDownSourceEvent
          rate rewards C_star C_h ∪
        ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent
          (r := rate) rewards C_star C_h prefixCount := by
  intro source hsource
  rcases (ReferenceStrictPastFailureCalendarAlignment.savedWrongSuffixPrefixEvent_expanded
      rate rewards C_star C_h source prefixCount).mp hsource with hup | hdown
  · rcases hup with ⟨record, hrecord, diagnostic, hdiag, hwrong⟩
    exact Or.inr ((ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent_true_iff
      (rate := rate) rewards C_star C_h prefixCount source).2
        ⟨record, hrecord, diagnostic, hdiag, hwrong⟩)
  · rcases hdown with ⟨record, hrecord, i, cut, hcut, hwrong⟩
    rw [ReferenceGeneratedAllWrongDownEvent.generatedAllWrongDownSourceEvent_eq_completeSuffixEvent
      rate rewards C_star C_h]
    exact Or.inl ⟨record, List.mem_of_mem_take hrecord, i, cut, hcut, hwrong⟩

/-- The literal saved-wrong suffix-prefix event is Borel on the complete
original source input, retaining the public output and every private array. -/
theorem measurableSet_savedWrongSuffixPrefixEvent
    (prefixCount : ℕ) :
    MeasurableSet (ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
      (r := rate) rewards C_star C_h prefixCount) :=
  ReferenceGeneratedSavedWrongEvent.measurableSet_savedWrongSuffixPrefixEvent
    (rate := rate) rewards C_star C_h prefixCount

/-- The source-law ENNReal budget for the saved-wrong prefix is at most twice
the existing one-direction finite-factor decoder envelope. -/
theorem savedWrongSuffixPrefixEvent_measure_le
    (control0 : ContinuousLearningRows.TimeControl p) (prefixCount : ℕ) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
          (r := rate) rewards C_star C_h prefixCount) ≤
      (2 : ENNReal) *
        (((p.m - 1 : ℕ) : ENNReal) * (p.T : ENNReal) *
          (2 : ENNReal) ^ AffineBatchDecoder.width p *
          ((1 : ENNReal) / 2) ^ AffineBatchDecoder.quota p) := by
  let single : ENNReal :=
    (((p.m - 1 : ℕ) : ENNReal) * (p.T : ENNReal) *
      (2 : ENNReal) ^ AffineBatchDecoder.width p) *
      ((1 : ENNReal) / 2) ^ AffineBatchDecoder.quota p
  have hdown :=
    ReferenceGeneratedAllWrongDownEvent.generatedAllWrongDownSourceEvent_measure_le_geometric
      rate rewards C_star C_h control0
  have hup := ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent_measure_le
    (rate := rate) rewards C_star C_h control0 prefixCount
  change BootstrapPrivateRoundStreams.sourceInputLaw p
      (ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
        (r := rate) rewards C_star C_h prefixCount) ≤ 2 * single
  calc
    _ ≤ BootstrapPrivateRoundStreams.sourceInputLaw p
        (ReferenceGeneratedAllWrongDownEvent.generatedAllWrongDownSourceEvent
            rate rewards C_star C_h ∪
          ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent
            (r := rate) rewards C_star C_h prefixCount) :=
      measure_mono (savedWrongSuffixPrefixEvent_subset_jointDecoderEvents
        rate rewards C_star C_h prefixCount)
    _ ≤ BootstrapPrivateRoundStreams.sourceInputLaw p
          (ReferenceGeneratedAllWrongDownEvent.generatedAllWrongDownSourceEvent
            rate rewards C_star C_h) +
        BootstrapPrivateRoundStreams.sourceInputLaw p
          (ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent
            (r := rate) rewards C_star C_h prefixCount) := measure_union_le _ _
    _ ≤ single + single := add_le_add (by simpa only [single] using hdown)
      (by simpa only [single] using hup)
    _ = 2 * single := by rw [← two_mul]

/-- The original-source real probability of any saved-wrong suffix prefix is
at most the sum of the two accepted one-quarter budgets. -/
theorem savedWrongSuffixPrefixEvent_measureReal_bound
    (control0 : ContinuousLearningRows.TimeControl p) (prefixCount : ℕ) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
          (r := rate) rewards C_star C_h prefixCount) ≤
      1 / (2 * (ConstructorDimensions.N p : ℝ) ^ 2) := by
  have hdown :=
    ReferenceGeneratedAllWrongDownEvent.generatedAllWrongDownSourceEvent_measureReal_quota_bound
      rate rewards C_star C_h control0
  have hup := ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent_measureReal_le
    (rate := rate) rewards C_star C_h control0 prefixCount
  have hNpos : 0 < (ConstructorDimensions.N p : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
  have hsum :
      1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) +
        1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) =
      1 / (2 * (ConstructorDimensions.N p : ℝ) ^ 2) := by
    have hNne : (ConstructorDimensions.N p : ℝ) ≠ 0 := ne_of_gt hNpos
    field_simp [hNne]
    ring
  calc
    _ ≤ (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (ReferenceGeneratedAllWrongDownEvent.generatedAllWrongDownSourceEvent
            rate rewards C_star C_h ∪
          ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent
            (r := rate) rewards C_star C_h prefixCount) :=
      measureReal_mono (savedWrongSuffixPrefixEvent_subset_jointDecoderEvents
        rate rewards C_star C_h prefixCount) (by finiteness)
    _ ≤ (BootstrapPrivateRoundStreams.sourceInputLaw p).real
          (ReferenceGeneratedAllWrongDownEvent.generatedAllWrongDownSourceEvent
            rate rewards C_star C_h) +
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real
          (ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent
            (r := rate) rewards C_star C_h prefixCount) := measureReal_union_le _ _
    _ ≤ 1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) +
        1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) := add_le_add hdown hup
    _ = 1 / (2 * (ConstructorDimensions.N p : ℝ) ^ 2) := hsum

/-- For every calendar index, the pointwise actual-record diagnostic is
contained in one fixed whole-horizon saved-wrong suffix event. The strict-past
lookup lemma handles the natural subtraction, empty prelaunch prefix, absent
launch, terminal crossing, and saturation at or beyond the horizon. -/
theorem savedWrongActualCalendarEvent_subset_horizon (n : ℕ) :
    {source : SourceInput (p := p) |
      ∃ t : Fin p.T, ∃ record : Record (rate := rate),
        t.val < n ∧
          ReferenceFirstCollectionAwaitedDownFailureReadout.actualRecord
              rate rewards C_star C_h t source = some record ∧
            ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record} ⊆
      ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
        (r := rate) rewards C_star C_h p.T := by
  intro source hsource
  obtain ⟨record, hrecord, hwrong⟩ :=
    (ReferenceStrictPastFailureCalendarAlignment.actualRecord_calendarPrefix_exists_iff
      rate rewards C_star C_h source n
      (fun record =>
        ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record)).mp hsource
  have hrecordSuffix : record ∈
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h :=
    List.mem_of_mem_take hrecord
  have hlength := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate source rewards C_star C_h
  have htake :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).take
        p.T =
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h := by
    apply (List.take_eq_self_iff _).2
    rw [hlength]
    exact Nat.sub_le _ _
  have hrecordHorizon : record ∈
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).take
        p.T := by
    rw [htake]
    exact hrecordSuffix
  change ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record at hwrong
  change (∃ diagnostic,
      record.output.coordinator.up = some diagnostic ∧
        diagnostic.wrongUniqueAccepted = true) ∨
    (∃ i cut, (record.output.followers i).down = some cut ∧
      ReferenceDownReception.wrongUniqueAccepted cut) at hwrong
  rcases hwrong with hup | hdown
  · exact (ReferenceStrictPastFailureCalendarAlignment.savedWrongSuffixPrefixEvent_expanded
      rate rewards C_star C_h source p.T).2
        (Or.inl ⟨record, hrecordHorizon, hup⟩)
  · exact (ReferenceStrictPastFailureCalendarAlignment.savedWrongSuffixPrefixEvent_expanded
      rate rewards C_star C_h source p.T).2
        (Or.inr ⟨record, hrecordHorizon, hdown⟩)

private abbrev RoundCode :=
  ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)

private theorem measurableSet_savedWrongActualRecordEvent (t : Fin p.T) :
    MeasurableSet {source : SourceInput (p := p) |
      ∃ record : Record (rate := rate),
        ReferenceFirstCollectionAwaitedDownFailureReadout.actualRecord
            rate rewards C_star C_h t source = some record ∧
          ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record} := by
  let observation := ReferenceInspectedPastRoundObservations.pastRoundObservations
    rate rewards C_star C_h p.T (Nat.le_refl p.T)
  let decode : Option (RoundCode (p := p) (rate := rate)) → Bool :=
    fun code => code.elim false ReferenceSavedWrongUniqueMeasurability.savedWrongCode
  have hdecode : Measurable decode := by
    have hsum := (ReferenceSavedWrongUniqueMeasurability.measurable_savedWrongCode
      (p := p) (rate := rate)).sumElim
        (measurable_const : Measurable (fun _ : PUnit => false))
    convert hsum.comp (comap_measurable (Equiv.optionEquivSumPUnit
      (RoundCode (p := p) (rate := rate)))) using 1
    funext code
    cases code <;> rfl
  have hobs : Measurable observation :=
    ReferenceInspectedPastRoundObservations.measurable_pastRoundObservations
      rate rewards C_star C_h p.T (Nat.le_refl p.T)
  have hflag : Measurable (fun source : SourceInput (p := p) => decode (observation source t)) :=
    hdecode.comp ((measurable_pi_iff.mp hobs) t)
  have heq :
      {source : SourceInput (p := p) |
        ∃ record : Record (rate := rate),
          ReferenceFirstCollectionAwaitedDownFailureReadout.actualRecord
              rate rewards C_star C_h t source = some record ∧
            ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record} =
      {source | decode (observation source t) = true} := by
    ext source
    change (∃ record : Record (rate := rate),
        ReferenceFirstCollectionAwaitedDownFailureReadout.actualRecord
            rate rewards C_star C_h t source = some record ∧
          ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record) ↔
      ((ReferenceFirstCollectionAwaitedDownFailureReadout.actualRecord
          rate rewards C_star C_h t source).map
          ReferenceActiveHorizonMeasurability.roundRecordCode).elim false
        ReferenceSavedWrongUniqueMeasurability.savedWrongCode = true
    cases hrecord : ReferenceFirstCollectionAwaitedDownFailureReadout.actualRecord
        rate rewards C_star C_h t source with
    | none => simp
    | some record =>
        simp only [Option.map_some, Option.elim_some,
          ReferenceSavedWrongUniqueMeasurability.savedWrongCode_roundRecord_iff,
          Option.some.injEq]
        exact ⟨fun ⟨_, h, hw⟩ => h.symm ▸ hw,
          fun hw => ⟨record, rfl, hw⟩⟩
  rw [heq]
  exact hflag (measurableSet_singleton true)

/-- The actual strict-past saved-wrong calendar event is Borel by a finite
union of the accepted retained-record diagnostics. -/
theorem measurableSet_savedWrongActualCalendarEvent (n : ℕ) :
    MeasurableSet {source : SourceInput (p := p) |
      ∃ t : Fin p.T, ∃ record : Record (rate := rate),
        t.val < n ∧
          ReferenceFirstCollectionAwaitedDownFailureReadout.actualRecord
              rate rewards C_star C_h t source = some record ∧
            ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record} := by
  rw [show
    {source : SourceInput (p := p) |
      ∃ t : Fin p.T, ∃ record : Record (rate := rate),
        t.val < n ∧
          ReferenceFirstCollectionAwaitedDownFailureReadout.actualRecord
              rate rewards C_star C_h t source = some record ∧
            ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record} =
      ⋃ t : {t : Fin p.T // t.val < n},
        {source : SourceInput (p := p) |
          ∃ record : Record (rate := rate),
            ReferenceFirstCollectionAwaitedDownFailureReadout.actualRecord
                rate rewards C_star C_h t.val source = some record ∧
              ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record} by
      ext source
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨t, record, htn, hactual, hwrong⟩
        exact ⟨⟨t, htn⟩, record, hactual, hwrong⟩
      · rintro ⟨⟨t, htn⟩, hflag⟩
        obtain ⟨record, hactual, hwrong⟩ := hflag
        exact ⟨t, record, htn, hactual, hwrong⟩]
  exact MeasurableSet.iUnion fun t =>
    measurableSet_savedWrongActualRecordEvent rate rewards C_star C_h t.val

/-- The original-source real probability of the actual strict-past saved-wrong
calendar event is bounded through the same fixed full-horizon event. -/
theorem savedWrongActualCalendarEvent_measureReal_bound
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        {source : SourceInput (p := p) |
          ∃ t : Fin p.T, ∃ record : Record (rate := rate),
            t.val < n ∧
              ReferenceFirstCollectionAwaitedDownFailureReadout.actualRecord
                  rate rewards C_star C_h t source = some record ∧
                ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record} ≤
      1 / (2 * (ConstructorDimensions.N p : ℝ) ^ 2) := by
  apply le_trans (measureReal_mono
    (savedWrongActualCalendarEvent_subset_horizon rate rewards C_star C_h n) (by finiteness))
  exact savedWrongSuffixPrefixEvent_measureReal_bound
    rate rewards C_star C_h control0 p.T

private theorem savedWrongSuffixPrefixEvent_subset_horizon (prefixCount : ℕ) :
    ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
        (r := rate) rewards C_star C_h prefixCount ⊆
      ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
        (r := rate) rewards C_star C_h p.T := by
  intro source hsource
  rcases (ReferenceStrictPastFailureCalendarAlignment.savedWrongSuffixPrefixEvent_expanded
      rate rewards C_star C_h source prefixCount).mp hsource with hup | hdown
  · rcases hup with ⟨record, hrecord, diagnostic, hdiag, hwrong⟩
    have hrecordSuffix := List.mem_of_mem_take hrecord
    have hlength := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate source rewards C_star C_h
    have htake :
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).take
          p.T =
        ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h := by
      apply (List.take_eq_self_iff _).2
      rw [hlength]
      exact Nat.sub_le _ _
    have hrecordHorizon : record ∈
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).take
          p.T := by
      rw [htake]
      exact hrecordSuffix
    exact (ReferenceStrictPastFailureCalendarAlignment.savedWrongSuffixPrefixEvent_expanded
      rate rewards C_star C_h source p.T).2
        (Or.inl ⟨record, hrecordHorizon, diagnostic, hdiag, hwrong⟩)
  · rcases hdown with ⟨record, hrecord, i, cut, hcut, hwrong⟩
    have hrecordSuffix := List.mem_of_mem_take hrecord
    have hlength := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate source rewards C_star C_h
    have htake :
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).take
          p.T =
        ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h := by
      apply (List.take_eq_self_iff _).2
      rw [hlength]
      exact Nat.sub_le _ _
    have hrecordHorizon : record ∈
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).take
          p.T := by
      rw [htake]
      exact hrecordSuffix
    exact (ReferenceStrictPastFailureCalendarAlignment.savedWrongSuffixPrefixEvent_expanded
      rate rewards C_star C_h source p.T).2
        (Or.inr ⟨record, hrecordHorizon, i, cut, hcut, hwrong⟩)

/-- The set read by the existing literal strict-past Boolean failure flag is
Borel as a finite calendar union of its actual per-round diagnostics. -/
theorem measurableSet_pastFailureFlag_true_event (n : ℕ) :
    MeasurableSet {source : SourceInput (p := p) |
      ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
        rate rewards C_star C_h n source = true} := by
  rw [show
    {source : SourceInput (p := p) |
      ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
        rate rewards C_star C_h n source = true} =
      ⋃ t : {t : Fin p.T // t.val < n},
        {source : SourceInput (p := p) |
          ReferenceFirstCollectionAwaitedDownFailureReadout.failureAt
            rate rewards C_star C_h source t.val} by
      ext source
      simp [ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag]]
  exact MeasurableSet.iUnion fun t =>
    ReferenceFirstCollectionAwaitedDownFailureReadout.failureAt_borel
      rate rewards C_star C_h t.val

private theorem pastFailureFlag_true_event_subset_budgetEvents (n : ℕ) :
    {source : SourceInput (p := p) |
      ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
        rate rewards C_star C_h n source = true} ⊆
      ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
          (r := rate) rewards C_star C_h p.T ∪
        (ReferenceAwaitedDownDecoderErrorProbability.fixedAwaitedDownFailureEvent
            rate rewards C_star C_h ∪
          ReferenceAwaitedUpDecoderErrorProbability.fixedAwaitedUpFailureEvent
            rate rewards C_star C_h) := by
  intro source hsource
  rcases (ReferenceStrictPastFailureCalendarAlignment.pastFailureFlag_true_iff
      rate rewards C_star C_h source n).mp hsource with hsaved | hdown | hup
  · exact Or.inl (savedWrongSuffixPrefixEvent_subset_horizon
      rate rewards C_star C_h (n - ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h) hsaved)
  · rcases hdown with ⟨t, ht, hfail⟩
    exact Or.inr (Or.inl ⟨t, hfail⟩)
  · rcases hup with ⟨t, ht, hfail⟩
    exact Or.inr (Or.inr ⟨t, hfail⟩)

/-- The existing literal strict-past failure readout has one source-law real
budget of `N⁻²`: saved-wrong contributes at most one half, and each fixed-
awaited direction contributes at most one quarter of `N⁻²`. -/
theorem pastFailureFlag_true_event_measureReal_bound
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        {source : SourceInput (p := p) |
          ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
            rate rewards C_star C_h n source = true} ≤
      1 / (ConstructorDimensions.N p : ℝ) ^ 2 := by
  have hsaved := savedWrongSuffixPrefixEvent_measureReal_bound
    rate rewards C_star C_h control0 p.T
  have hdown := ReferenceAwaitedDownDecoderErrorProbability.fixedAwaitedDownFailureEvent_measureReal_bound
    rate rewards C_star C_h control0
  have hup := ReferenceAwaitedUpDecoderErrorProbability.fixedAwaitedUpFailureEvent_measureReal_bound
    rate rewards C_star C_h control0
  have hNpos : 0 < (ConstructorDimensions.N p : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
  have hsum :
      1 / (2 * (ConstructorDimensions.N p : ℝ) ^ 2) +
        (1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) +
          1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2)) =
      1 / (ConstructorDimensions.N p : ℝ) ^ 2 := by
    have hNne : (ConstructorDimensions.N p : ℝ) ≠ 0 := ne_of_gt hNpos
    field_simp [hNne]
    ring
  calc
    _ ≤ (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
            (r := rate) rewards C_star C_h p.T ∪
          (ReferenceAwaitedDownDecoderErrorProbability.fixedAwaitedDownFailureEvent
              rate rewards C_star C_h ∪
            ReferenceAwaitedUpDecoderErrorProbability.fixedAwaitedUpFailureEvent
              rate rewards C_star C_h)) :=
      measureReal_mono
        (pastFailureFlag_true_event_subset_budgetEvents rate rewards C_star C_h n)
        (by finiteness)
    _ ≤ (BootstrapPrivateRoundStreams.sourceInputLaw p).real
          (ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
            (r := rate) rewards C_star C_h p.T) +
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real
          (ReferenceAwaitedDownDecoderErrorProbability.fixedAwaitedDownFailureEvent
              rate rewards C_star C_h ∪
            ReferenceAwaitedUpDecoderErrorProbability.fixedAwaitedUpFailureEvent
              rate rewards C_star C_h) := measureReal_union_le _ _
    _ ≤ 1 / (2 * (ConstructorDimensions.N p : ℝ) ^ 2) +
        (1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) +
          1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2)) := by
      apply add_le_add hsaved
      exact (measureReal_union_le _ _).trans (add_le_add hdown hup)
    _ = 1 / (ConstructorDimensions.N p : ℝ) ^ 2 := hsum

end Bandits.Support.ReferenceGeneratedJointDecoderFailureBound

end
