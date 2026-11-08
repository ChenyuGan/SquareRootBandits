/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceSavedWrongUniqueMeasurability
public import Bandits.Support.ReferenceGeneratedDownAmbiguityMeasurability

/-!
# Generated saved-wrong acceptance on the actual physical suffix

Sources: `sources/zip4/manuscript/08_main_theorem.tex:26-42,67-75`,
`sources/zip4/manuscript/07_public_setup.tex:123-164`,
`sources/zip4/manuscript/06_interruptions.tex:355-362`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-153`.

This internal observable reads the literal saved-wrong-unique-acceptance
diagnostic on the actual complete postlaunch suffix. Its prefixes and first
physical occurrence are Borel on the original source input. It is not the
manuscript event stopped at the first queue-overflow update and proves no
probability bound or regret conclusion.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActiveHorizonMeasurability
open Bandits.Support.ReferenceActiveStoppedPrefixCoupling
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.ReferenceGeneratedDownAmbiguityMeasurability
open Bandits.Support.ReferenceSavedWrongUniqueMeasurability

namespace Bandits.Support.ReferenceGeneratedSavedWrongEvent

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p

variable {p : Parameters} {rate : RateInput p}

/-- The literal saved-wrong-unique predicate on one actual suffix record. -/
def savedWrongRecordFlag
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) : Bool :=
  by
    classical
    exact decide (ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record)

/-- The Boolean diagnostic that a saved wrong unique acceptance occurs in
the first `prefixCount` records of the actual complete postlaunch suffix. -/
def savedWrongSuffixPrefixCode
    (r : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (prefixCount : ℕ) (source : SourceInput p) : Bool :=
  ((ReferenceCompletePhysicalHistory.completeSuffixRecords r source rewards C_star C_h).take prefixCount).any
    (savedWrongRecordFlag (rate := r))

/-- The literal chronological saved-wrong prefix event on the original source
carrier. No diagnostic is appended before the actual corrected launch. -/
def savedWrongSuffixPrefixEvent
    (r : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (prefixCount : ℕ) : Set (SourceInput p) :=
  {source | savedWrongSuffixPrefixCode r rewards C_star C_h
      prefixCount source = true}

/-- The zero-based offset of the first saved-wrong record in the same actual
chronological suffix list. -/
def savedWrongSuffixFirstOffset
    (r : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) : Option ℕ :=
  (ReferenceCompletePhysicalHistory.completeSuffixRecords r source rewards C_star C_h)
    |>.findIdx? (savedWrongRecordFlag (rate := r))

/-- The absolute zero-based physical time of the first saved-wrong record.
The launch-relative offset remains available separately as
`savedWrongSuffixFirstOffset`. -/
def savedWrongSuffixFirstPhysicalTime
    (r : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) : Option ℕ :=
  (savedWrongSuffixFirstOffset r rewards C_star C_h source).map
    (fun offset => ReferenceCompletePhysicalHistory.physicalStart r source rewards C_star C_h + offset)

/-- Prefix existence is exactly existence of an actual saved-wrong record in
that prefix of `completeSuffixRecords`. -/
theorem savedWrongSuffixPrefixEvent_true_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (prefixCount : ℕ) (source : SourceInput p) :
    source ∈ savedWrongSuffixPrefixEvent (r := rate) rewards C_star C_h prefixCount ↔
      ∃ record ∈
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).take prefixCount,
        ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record := by
  change savedWrongSuffixPrefixCode (r := rate) rewards C_star C_h prefixCount source = true ↔ _
  unfold savedWrongSuffixPrefixCode
  rw [List.any_eq_true]
  simp only [savedWrongRecordFlag, decide_eq_true_eq]

/-- The exact complement of a prefix event is safety of every actual record
in that same `take prefixCount` list. -/
theorem savedWrongSuffixPrefixEvent_false_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (prefixCount : ℕ) (source : SourceInput p) :
  source ∉ savedWrongSuffixPrefixEvent (r := rate) rewards C_star C_h prefixCount ↔
      ∀ record ∈
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).take prefixCount,
        ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted record := by
  rw [savedWrongSuffixPrefixEvent_true_iff]
  constructor
  · intro hsafe record hmem
    apply (ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted_iff record).2
    intro hbad
    exact hsafe ⟨record, hmem, hbad⟩
  · intro hsafe ⟨record, hmem, hbad⟩
    exact (ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted_iff record).1
      (hsafe record hmem) hbad

/-- The actual generated launch payload and its full remaining physical
calendar, on one genuine launch-start fibre. -/
def launchCalendarRunInput
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (start : Fin (p.T + 1))
    (source : GeneratedLaunchFiber (rate := rate) rewards C_star C_h start.val) :
    ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate) := by
  let active := generatedActiveRunInput (rate := rate) rewards C_star C_h start.val source
  refine ⟨(start.val, (p.T - start.val, active.val)), ?_⟩
  constructor
  · have hstart : start.val ≤ p.T := Nat.le_of_lt_succ start.isLt
    calc
      start.val + (p.T - start.val) = p.T := Nat.add_sub_of_le hstart
      _ ≤ p.T := le_rfl
  · exact active.property

private theorem measurable_launchCalendarRunInput
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (start : Fin (p.T + 1)) :
    Measurable (launchCalendarRunInput (rate := rate) rewards C_star C_h start) := by
  have hactive := measurable_generatedActiveRunInput
    (rate := rate) rewards C_star C_h start.val
  have hdata : Measurable (fun source : GeneratedLaunchFiber
      (rate := rate) rewards C_star C_h start.val =>
      (start.val, (p.T - start.val,
        (generatedActiveRunInput (rate := rate) rewards C_star C_h start.val source).val))) := by
    exact measurable_const.prodMk
      (measurable_const.prodMk (measurable_subtype_coe.comp hactive))
  exact hdata.subtype_mk

/-- On each genuine launch-start fibre, the actual calendar run records are
the whole actual `completeSuffixRecords` list. The `T` crossing remains a
present zero-length run. -/
private theorem launchCalendarRun_records_eq_completeSuffixRecords
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (start : Fin (p.T + 1))
    (source : GeneratedLaunchFiber (rate := rate) rewards C_star C_h start.val) :
    (calendarReferenceRun (launchCalendarRunInput
      (rate := rate) rewards C_star C_h start source)).records =
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source.1 rewards C_star C_h := by
  have hprefix := generatedRun_records_eq_completeSuffixRecords_take
    (rate := rate) rewards C_star C_h start.val (p.T - start.val) (by omega) source
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate source.1 rewards C_star C_h
  rw [source.2.2] at hlen
  have htake :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source.1 rewards C_star C_h).take
        (p.T - start.val) =
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source.1 rewards C_star C_h :=
    List.take_of_length_le (Nat.le_of_eq hlen)
  change (ReferenceActiveHorizonMeasurability.runOfInput start.val (p.T - start.val)
      (by omega) (generatedActiveRunInput (rate := rate) rewards C_star C_h start.val source)).records = _
  rw [hprefix, htake]

private def savedWrongPrefixOnLaunchFiber
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (start : Fin (p.T + 1)) (prefixCount : ℕ) :
    Set (GeneratedLaunchFiber (rate := rate) rewards C_star C_h start.val) :=
  {source | calendarSavedWrongPrefixCode
      (launchCalendarRunInput (rate := rate) rewards C_star C_h start source) prefixCount = true}

private theorem savedWrongPrefixOnLaunchFiber_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (start : Fin (p.T + 1)) (prefixCount : ℕ)
    (source : GeneratedLaunchFiber (rate := rate) rewards C_star C_h start.val) :
    source ∈ savedWrongPrefixOnLaunchFiber
        (rate := rate) rewards C_star C_h start prefixCount ↔
      source.1 ∈ savedWrongSuffixPrefixEvent (r := rate) rewards C_star C_h prefixCount := by
  rw [savedWrongPrefixOnLaunchFiber, Set.mem_setOf_eq,
    calendarSavedWrongPrefixCode_true_iff]
  rw [launchCalendarRun_records_eq_completeSuffixRecords
    (rate := rate) rewards C_star C_h start source]
  exact (savedWrongSuffixPrefixEvent_true_iff
    (rate := rate) rewards C_star C_h prefixCount source.1).symm

private theorem measurableSet_savedWrongPrefixOnLaunchFiber
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (start : Fin (p.T + 1)) (prefixCount : ℕ) :
    MeasurableSet (savedWrongPrefixOnLaunchFiber
      (rate := rate) rewards C_star C_h start prefixCount) := by
  have hcode : Measurable (fun source : GeneratedLaunchFiber
      (rate := rate) rewards C_star C_h start.val =>
      calendarSavedWrongPrefixCode
        (launchCalendarRunInput (rate := rate) rewards C_star C_h start source) prefixCount) :=
    (measurable_calendarSavedWrongPrefixCode
      (p := p) (rate := rate) prefixCount).comp
      (measurable_launchCalendarRunInput
        (rate := rate) rewards C_star C_h start)
  exact hcode (measurableSet_singleton true)

private theorem savedWrongSuffixPrefixEvent_eq_launchFiber_union
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (prefixCount : ℕ) :
    savedWrongSuffixPrefixEvent (r := rate) rewards C_star C_h prefixCount =
      ⋃ start : Fin (p.T + 1),
        Subtype.val '' savedWrongPrefixOnLaunchFiber
          (rate := rate) rewards C_star C_h start prefixCount := by
  ext source
  constructor
  · intro hevent
    by_cases hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h = none
    · have hrecords :
          ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h = [] := by
        simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hnone]
      have : source ∉ savedWrongSuffixPrefixEvent (r := rate) rewards C_star C_h prefixCount := by
        rw [savedWrongSuffixPrefixEvent_true_iff]
        rw [hrecords]
        simp
      exact (this hevent).elim
    · have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
          rate source rewards C_star C_h).isSome = true :=
        Option.ne_none_iff_isSome.mp hnone
      have hcrossing :
          (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h).crossing.isSome = true := by
        have h := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate source rewards C_star C_h).1 hsome
        simpa [ReferenceCompletePhysicalHistory.generatedBoundary,
          ReferenceCompletePhysicalHistory.generatedInput] using h
      have hstart := ReferenceCompletePhysicalHistory.physicalStart_le_T
        rate source rewards C_star C_h
      let start : Fin (p.T + 1) := ⟨
        ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h, by omega⟩
      have hfiber : source ∈ generatedLaunchFiberSet
          (rate := rate) rewards C_star C_h start.val := by
        exact ⟨hcrossing, rfl⟩
      let fiber : GeneratedLaunchFiber (rate := rate) rewards C_star C_h start.val :=
        ⟨source, hfiber⟩
      have hbranch : fiber ∈ savedWrongPrefixOnLaunchFiber
          (rate := rate) rewards C_star C_h start prefixCount :=
        (savedWrongPrefixOnLaunchFiber_iff
          (rate := rate) rewards C_star C_h start prefixCount fiber).2 hevent
      apply Set.mem_iUnion.mpr
      refine ⟨start, ?_⟩
      exact ⟨fiber, hbranch, rfl⟩
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨start, hmem⟩
    rcases hmem with ⟨fiber, hbranch, hsource⟩
    subst source
    exact (savedWrongPrefixOnLaunchFiber_iff
      (rate := rate) rewards C_star C_h start prefixCount fiber).1 hbranch

/-- The prefix event is Borel on the complete original source input, with the
full published output and every private coordinate retained. -/
theorem measurableSet_savedWrongSuffixPrefixEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (prefixCount : ℕ) :
    MeasurableSet (savedWrongSuffixPrefixEvent (r := rate) rewards C_star C_h prefixCount) := by
  rw [savedWrongSuffixPrefixEvent_eq_launchFiber_union
    (rate := rate) rewards C_star C_h prefixCount]
  apply MeasurableSet.iUnion
  intro start
  exact MeasurableSet.subtype_image
    (measurableSet_generatedLaunchFiberSet
      (rate := rate) rewards C_star C_h start.val)
    (measurableSet_savedWrongPrefixOnLaunchFiber
      (rate := rate) rewards C_star C_h start prefixCount)

/-- Fixing a public output gives a Borel section on the complete original
extended-private-coordinate carrier. -/
theorem measurableSet_savedWrongSuffixPrefixEvent_fixedPublic
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (prefixCount : ℕ)
    (published : CompletePublicTable.PublishedOutput p) :
    MeasurableSet {privateCoordinates : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p |
      (published, privateCoordinates) ∈ savedWrongSuffixPrefixEvent (r := rate) rewards C_star C_h prefixCount} := by
  have hsection : Measurable (fun privateCoordinates :
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p => (published, privateCoordinates)) :=
    measurable_const.prodMk measurable_id
  exact (measurableSet_savedWrongSuffixPrefixEvent (rate := rate) rewards C_star C_h prefixCount).preimage hsection

/-- The first position is in a prefix exactly when the prefix through that
position detects a bad record and the strict predecessor prefix is safe. -/
private theorem savedWrongSuffixFirstOffset_some_iff_prefix
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (index : ℕ) :
    savedWrongSuffixFirstOffset (r := rate) rewards C_star C_h source = some index ↔
      source ∈ savedWrongSuffixPrefixEvent (r := rate) rewards C_star C_h (index + 1) ∧
        source ∉ savedWrongSuffixPrefixEvent (r := rate) rewards C_star C_h index := by
  let records := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  have hpositions :
      savedWrongSuffixFirstOffset (r := rate) rewards C_star C_h source = some index ↔
        ∃ hindex : index < records.length,
          savedWrongRecordFlag records[index] = true ∧
          ∀ earlier (hearlier : earlier < index),
            savedWrongRecordFlag records[earlier] = false := by
    unfold savedWrongSuffixFirstOffset
    dsimp [records]
    rw [List.findIdx?_eq_some_iff_getElem]
    simp only [Bool.not_eq_true]
  rw [hpositions]
  constructor
  · rintro ⟨hindex, hbad, hsafe⟩
    constructor
    · apply (savedWrongSuffixPrefixEvent_true_iff
        (rate := rate) rewards C_star C_h (index + 1) source).2
      refine ⟨records[index], ?_, ?_⟩
      · exact List.mem_take_iff_getElem.mpr ⟨index,
          (Nat.lt_min).2 ⟨by omega, hindex⟩, rfl⟩
      · simpa [savedWrongRecordFlag] using hbad
    · intro hprefix
      rcases (savedWrongSuffixPrefixEvent_true_iff
        (rate := rate) rewards C_star C_h index source).1 hprefix with
        ⟨record, hmem, hwrong⟩
      rcases List.mem_take_iff_getElem.mp hmem with ⟨earlier, hearlier, hrecord⟩
      have hsafeEarlier := hsafe earlier (by omega)
      rw [hrecord] at hsafeEarlier
      have : savedWrongRecordFlag record = true := by simpa [savedWrongRecordFlag] using hwrong
      rw [this] at hsafeEarlier
      contradiction
  · rintro ⟨hthrough, hbefore⟩
    rcases (savedWrongSuffixPrefixEvent_true_iff
      (rate := rate) rewards C_star C_h (index + 1) source).1 hthrough with
      ⟨record, hmem, hwrong⟩
    rcases List.mem_take_iff_getElem.mp hmem with ⟨position, hposition, hrecord⟩
    have hpositionLen : position < records.length :=
      lt_of_lt_of_le hposition (Nat.min_le_right _ _)
    have hposLe : position ≤ index := by omega
    have hpositionEq : position = index := by
      by_contra hne
      have hlt : position < index := by omega
      have hmemBefore : record ∈ records.take index :=
        List.mem_take_iff_getElem.mpr ⟨position,
          (Nat.lt_min).2 ⟨hlt, hpositionLen⟩, hrecord⟩
      exact hbefore ((savedWrongSuffixPrefixEvent_true_iff
        (rate := rate) rewards C_star C_h index source).2
          ⟨record, hmemBefore, hwrong⟩)
    subst position
    have hindex : index < records.length := hpositionLen
    have hbad : savedWrongRecordFlag records[index] = true := by
      have hflagRecord : savedWrongRecordFlag record = true := by
        simpa [savedWrongRecordFlag] using hwrong
      rw [← hrecord] at hflagRecord
      exact hflagRecord
    have hsafe : ∀ earlier (hearlier : earlier < index),
        savedWrongRecordFlag records[earlier] = false := by
      intro earlier hearlier
      by_contra hnot
      have hbadEarlier : savedWrongRecordFlag records[earlier] = true := by
        cases hflag : savedWrongRecordFlag records[earlier] <;> simp_all
      have hmemBefore : records[earlier] ∈ records.take index :=
        List.mem_take_iff_getElem.mpr ⟨earlier,
          (Nat.lt_min).2 ⟨hearlier, Nat.lt_trans hearlier hindex⟩, rfl⟩
      have hprefix := (savedWrongSuffixPrefixEvent_true_iff
        (rate := rate) rewards C_star C_h index source).2
          ⟨records[earlier], hmemBefore, by
            simpa [savedWrongRecordFlag] using hbadEarlier⟩
      exact hbefore hprefix
    exact ⟨hindex, hbad, hsafe⟩

/-- Every `some k` offset fibre is Borel, using the already proved prefix
events on the original source space. -/
private theorem measurableSet_savedWrongSuffixFirstOffset_some
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (index : ℕ) :
    MeasurableSet {source : SourceInput p |
      savedWrongSuffixFirstOffset (r := rate) rewards C_star C_h source = some index} := by
  have hset : {source : SourceInput p |
      savedWrongSuffixFirstOffset (r := rate) rewards C_star C_h source = some index} =
      {source | source ∈ savedWrongSuffixPrefixEvent (r := rate) rewards C_star C_h (index + 1)} ∩
      {source | source ∉ savedWrongSuffixPrefixEvent (r := rate) rewards C_star C_h index} := by
    ext source
    exact savedWrongSuffixFirstOffset_some_iff_prefix
      (rate := rate) rewards C_star C_h source index
  rw [hset]
  exact (measurableSet_savedWrongSuffixPrefixEvent (rate := rate) rewards C_star C_h (index + 1)).inter
      (measurableSet_savedWrongSuffixPrefixEvent (rate := rate) rewards C_star C_h index).compl

/-- The first offset, including its genuine absent value, is Borel on the
original source input. -/
theorem measurable_savedWrongSuffixFirstOffset
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    Measurable (savedWrongSuffixFirstOffset (r := rate) rewards C_star C_h) := by
  apply FollowerDownMeasurability.measurable_of_countable_fibers
  intro value
  cases value with
  | some index =>
      exact measurableSet_savedWrongSuffixFirstOffset_some
        rate rewards C_star C_h index
  | none =>
      have hset : {source : SourceInput p |
          savedWrongSuffixFirstOffset (r := rate) rewards C_star C_h source = none} =
          ⋂ index : ℕ, {source | savedWrongSuffixFirstOffset (r := rate) rewards C_star C_h source ≠ some index} := by
        ext source
        cases h : savedWrongSuffixFirstOffset (r := rate) rewards C_star C_h source <;>
          simp [h]
      rw [hset]
      apply MeasurableSet.iInter
      intro index
      exact (measurableSet_savedWrongSuffixFirstOffset_some
        rate rewards C_star C_h index).compl

/-- An absolute-time fibre is the finite union of a genuine launch fibre and
the corresponding measurable launch-relative first-offset fibre. -/
private theorem savedWrongSuffixFirstPhysicalTime_some_iff_launch_fiber
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (time : ℕ) :
    savedWrongSuffixFirstPhysicalTime (r := rate) rewards C_star C_h source = some time ↔
      ∃ start : Fin (p.T + 1), ∃ offset : ℕ,
        start.val + offset = time ∧
        source ∈ generatedLaunchFiberSet (rate := rate) rewards C_star C_h start.val ∧
        savedWrongSuffixFirstOffset (r := rate) rewards C_star C_h source = some offset := by
  constructor
  · intro htime
    unfold savedWrongSuffixFirstPhysicalTime at htime
    cases hoffset : savedWrongSuffixFirstOffset (r := rate) rewards C_star C_h source with
    | none => simp [hoffset] at htime
    | some offset =>
        simp [hoffset] at htime
        refine ⟨⟨ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h,
          by have hle := ReferenceCompletePhysicalHistory.physicalStart_le_T rate source rewards C_star C_h; omega⟩,
          offset, ?_⟩
        constructor
        · simpa using htime
        constructor
        · by_contra hnotfiber
          cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
              rate source rewards C_star C_h with
          | none =>
              simp [savedWrongSuffixFirstOffset,
                ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch] at hoffset
          | some active =>
              have hcrossing := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
                rate source rewards C_star C_h).1 (by simp [hlaunch])
              have hfiber : source ∈ generatedLaunchFiberSet
                  (rate := rate) rewards C_star C_h
                    (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) := by
                refine ⟨?_, rfl⟩
                simpa [ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet,
                  ReferenceCompletePhysicalHistory.generatedBoundary,
                  ReferenceCompletePhysicalHistory.generatedInput] using hcrossing
              exact hnotfiber hfiber
        · rfl
  · rintro ⟨start, offset, htime, hfiber, hoffset⟩
    unfold savedWrongSuffixFirstPhysicalTime
    have hstart : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h =
        start.val := hfiber.2
    simp [hoffset, hstart, htime]

private theorem measurableSet_savedWrongSuffixFirstPhysicalTime_some_fiber
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (time : ℕ) :
    MeasurableSet {source : SourceInput p |
      savedWrongSuffixFirstPhysicalTime (r := rate) rewards C_star C_h source = some time} := by
  have hset : {source : SourceInput p |
      savedWrongSuffixFirstPhysicalTime (r := rate) rewards C_star C_h source = some time} =
      ⋃ start : Fin (p.T + 1), ⋃ offset : ℕ,
        {source | start.val + offset = time} ∩
        ({source | source ∈ generatedLaunchFiberSet
          (rate := rate) rewards C_star C_h start.val} ∩
        {source | savedWrongSuffixFirstOffset (r := rate) rewards C_star C_h source = some offset}) := by
    ext source
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    exact savedWrongSuffixFirstPhysicalTime_some_iff_launch_fiber
      (rate := rate) rewards C_star C_h source time
  rw [hset]
  apply MeasurableSet.iUnion
  intro start
  apply MeasurableSet.iUnion
  intro offset
  exact (MeasurableSet.const (start.val + offset = time)).inter
    ((measurableSet_generatedLaunchFiberSet
      (rate := rate) rewards C_star C_h start.val).inter
      (measurableSet_savedWrongSuffixFirstOffset_some
        (rate := rate) rewards C_star C_h offset))

/-- The first absolute physical-time map is Borel. Each present-value fibre
uses the genuine finite launch-start partition; the absent fibre is its
countable complement. -/
theorem measurable_savedWrongSuffixFirstPhysicalTime
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    Measurable (savedWrongSuffixFirstPhysicalTime (r := rate) rewards C_star C_h) := by
  apply FollowerDownMeasurability.measurable_of_countable_fibers
  intro value
  cases value with
  | some time =>
      exact measurableSet_savedWrongSuffixFirstPhysicalTime_some_fiber
        (rate := rate) rewards C_star C_h time
  | none =>
      have hset : {source : SourceInput p |
          savedWrongSuffixFirstPhysicalTime (r := rate) rewards C_star C_h source = none} =
          ⋂ time : ℕ, {source | savedWrongSuffixFirstPhysicalTime (r := rate) rewards C_star C_h source ≠ some time} := by
        ext source
        cases h : savedWrongSuffixFirstPhysicalTime (r := rate) rewards C_star C_h source <;>
          simp [h]
      rw [hset]
      apply MeasurableSet.iInter
      intro time
      exact (measurableSet_savedWrongSuffixFirstPhysicalTime_some_fiber
        (rate := rate) rewards C_star C_h time).compl

/-- Every fixed-public section of the first offset map is Borel on the whole
extended private-coordinate carrier. -/
theorem measurable_savedWrongSuffixFirstOffset_fixedPublic
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : CompletePublicTable.PublishedOutput p) :
    Measurable (fun privateCoordinates : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      savedWrongSuffixFirstOffset (r := rate) rewards C_star C_h
        (published, privateCoordinates)) := by
  exact (measurable_savedWrongSuffixFirstOffset (rate := rate) rewards C_star C_h).comp
      (measurable_const.prodMk measurable_id)

/-- Every fixed-public section of the first absolute-time map is Borel on the
whole extended private-coordinate carrier. -/
theorem measurable_savedWrongSuffixFirstPhysicalTime_fixedPublic
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : CompletePublicTable.PublishedOutput p) :
    Measurable (fun privateCoordinates : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      savedWrongSuffixFirstPhysicalTime (r := rate) rewards C_star C_h
        (published, privateCoordinates)) := by
  exact (measurable_savedWrongSuffixFirstPhysicalTime (rate := rate) rewards C_star C_h).comp
      (measurable_const.prodMk measurable_id)

private theorem firstSavedWrongOffset_eq_actualSuffix
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (start : Fin (p.T + 1))
    (source : GeneratedLaunchFiber (rate := rate) rewards C_star C_h start.val) :
    firstSavedWrongOffset (launchCalendarRunInput
      (rate := rate) rewards C_star C_h start source) =
      savedWrongSuffixFirstOffset (r := rate) rewards C_star C_h source.1 := by
  let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source.1 rewards C_star C_h
  have hflag (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
      savedWrongCode (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
        savedWrongRecordFlag record := by
    classical
    by_cases hbad : ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record
    · have hcode := (savedWrongCode_roundRecord_iff record).2 hbad
      rw [hcode]
      simp [savedWrongRecordFlag, hbad]
    · have hfalse : savedWrongCode
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) = false := by
        cases hcode : savedWrongCode
            (ReferenceActiveHorizonMeasurability.roundRecordCode record) with
        | false => rfl
        | true =>
            have hwrong := (savedWrongCode_roundRecord_iff record).1 hcode
            exact (hbad hwrong).elim
      rw [hfalse]
      simp [savedWrongRecordFlag, hbad]
  have hmap (xs : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
      (xs.map ReferenceActiveHorizonMeasurability.roundRecordCode).findIdx? savedWrongCode =
        xs.findIdx? savedWrongRecordFlag := by
    induction xs with
    | nil => rfl
    | cons record rest ih =>
        simp only [List.map_cons, List.findIdx?_cons, hflag record, ih]
  unfold ReferenceSavedWrongUniqueMeasurability.firstSavedWrongOffset
    savedWrongSuffixFirstOffset
  rw [ReferenceActiveHorizonMeasurability.calendarRunObservation_eq_actual]
  have hcalendarRecords := launchCalendarRun_records_eq_completeSuffixRecords
    (rate := rate) rewards C_star C_h start source
  change ((calendarReferenceRun (launchCalendarRunInput
      (rate := rate) rewards C_star C_h start source)).records.map
        ReferenceActiveHorizonMeasurability.roundRecordCode).findIdx? savedWrongCode =
    records.findIdx? savedWrongRecordFlag
  rw [hcalendarRecords]
  exact hmap records

/-- `some t` is an actual saved-wrong suffix record at physical time `t`.
Its inclusive prefix contains that record, and every strict predecessor
record is safe. The returned zero-based offset is separate from `t`. -/
theorem savedWrongSuffixFirstPhysicalTime_some_spec
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) {time : ℕ}
    (hfirst : savedWrongSuffixFirstPhysicalTime
      (r := rate) rewards C_star C_h source = some time) :
    time < p.T ∧
      ∃ offset,
        savedWrongSuffixFirstOffset (r := rate) rewards C_star C_h source = some offset ∧
        ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + offset = time ∧
        ∃ record ∈
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).take
            (offset + 1),
          ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record ∧
          record.input.time.val = time ∧
          ∀ earlier ∈
            (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).take offset,
            ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted earlier := by
  obtain ⟨start, offset, htime, hfiber, hoffset⟩ :=
    (savedWrongSuffixFirstPhysicalTime_some_iff_launch_fiber
      (rate := rate) rewards C_star C_h source time).1 hfirst
  let fiber : GeneratedLaunchFiber (rate := rate) rewards C_star C_h start.val :=
    ⟨source, hfiber⟩
  let calendar := launchCalendarRunInput (rate := rate) rewards C_star C_h start fiber
  have hoffsetCalendar : firstSavedWrongOffset calendar = some offset := by
    exact (firstSavedWrongOffset_eq_actualSuffix
      (rate := rate) rewards C_star C_h start fiber).trans hoffset
  have hspec := firstSavedWrongOffset_some_spec calendar hoffsetCalendar
  have hrecords := launchCalendarRun_records_eq_completeSuffixRecords
    (rate := rate) rewards C_star C_h start fiber
  have hphysicalStart : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h = start.val := hfiber.2
  rcases hspec with ⟨hoffsetLt, hbad, hrecordMem, hrecordTime, hsafe⟩
  have htime' : start.val + offset = time := by
    simpa [hphysicalStart] using htime
  refine ⟨?_, offset, hoffset, ?_, ?_⟩
  · have hoffsetLt' : offset < p.T - start.val := by
      simpa [calendar, launchCalendarRunInput] using hoffsetLt
    have hphysicalTimeLt : start.val + offset < p.T := by omega
    omega
  · simpa [hphysicalStart] using htime
  · let record := calendarReferenceRecordAt calendar offset hoffsetLt
    refine ⟨record, ?_, hbad, ?_, ?_⟩
    · rw [← hrecords]
      exact hrecordMem
    · calc
        record.input.time.val = start.val + offset := hrecordTime
        _ = time := htime'
    · intro earlier hearlier
      have hearlierCalendar : earlier ∈ (calendarReferenceRun calendar).records.take offset := by
        rw [hrecords]
        exact hearlier
      exact hsafe earlier hearlierCalendar

/-- On a first-occurrence launch fibre, apply the accepted stopped-boundary
comparison to the produced earliest-offset facts. The detecting round is
included in its physical prefix; successor-state agreement is only through
the predecessor boundary, exactly as in the admitted API. -/
abbrev FirstSavedWrongBoundaryComparison
    (input : ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate))
    {index : ℕ} (hfirst : firstSavedWrongOffset input = some index) : Prop :=
  (∃ record ∈ (calendarReferenceRun input).records,
      record.input.time.val = input.val.1 + index ∧
        ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record) ∧
    (∀ (k : ℕ) (_hk : k ≤ index),
      (ReferenceActiveStoppedPrefixCoupling.run input.val.2.2.1 input.val.2.2.2.1
        input.val.2.2.2.2.1 input.val.2.2.2.2.2 input.val.1 k (by
          have hindex := (firstSavedWrongOffset_some_iff_indexed input index).mp hfirst |>.1
          omega) input.property.2).finalState =
      (ReferenceActivePhysicalHorizon.run input.val.2.2.1 input.val.2.2.2.1
        input.val.2.2.2.2.1 input.val.2.2.2.2.2 input.val.1 k (by
          have hindex := (firstSavedWrongOffset_some_iff_indexed input index).mp hfirst |>.1
          omega) input.property.2).finalState) ∧
    (∀ k, k ≤ index + 1 →
      (ReferenceActiveStoppedPrefixCoupling.run input.val.2.2.1 input.val.2.2.2.1
        input.val.2.2.2.2.1 input.val.2.2.2.2.2 input.val.1 input.val.2.1
        input.property.1 input.property.2).physicalTrace.take k =
        ((calendarReferenceRun input).records.map
          ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k) ∧
    (ReferenceActiveStoppedPrefixCoupling.run input.val.2.2.1 input.val.2.2.2.1
      input.val.2.2.2.2.1 input.val.2.2.2.2.2 input.val.1 (index + 1) (by
        have hindex := (firstSavedWrongOffset_some_iff_indexed input index).mp hfirst |>.1
        omega)
      input.property.2).totalReward =
      (ReferenceActivePhysicalHorizon.run input.val.2.2.1 input.val.2.2.2.1
        input.val.2.2.2.2.1 input.val.2.2.2.2.2 input.val.1 (index + 1) (by
          have hindex := (firstSavedWrongOffset_some_iff_indexed input index).mp hfirst |>.1
          omega) input.property.2).totalReward

abbrev SavedWrongSafeRunComparison
    (input : ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate)) : Prop :=
  (ReferenceActiveStoppedPrefixCoupling.run input.val.2.2.1 input.val.2.2.2.1
      input.val.2.2.2.2.1 input.val.2.2.2.2.2 input.val.1 input.val.2.1
      input.property.1 input.property.2).finalState = (calendarReferenceRun input).finalState ∧
    (ReferenceActiveStoppedPrefixCoupling.run input.val.2.2.1 input.val.2.2.2.1
      input.val.2.2.2.2.1 input.val.2.2.2.2.2 input.val.1 input.val.2.1
      input.property.1 input.property.2).physicalTrace =
      (calendarReferenceRun input).records.map ReferenceActiveStoppedPrefixCoupling.referencePhysical ∧
    (ReferenceActiveStoppedPrefixCoupling.run input.val.2.2.1 input.val.2.2.2.1
      input.val.2.2.2.2.1 input.val.2.2.2.2.2 input.val.1 input.val.2.1
      input.property.1 input.property.2).totalReward = (calendarReferenceRun input).totalReward

theorem firstSavedWrong_stoppedBoundary_on_launchFiber
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (start : Fin (p.T + 1))
    (source : GeneratedLaunchFiber (rate := rate) rewards C_star C_h start.val)
    {offset : ℕ}
    (hfirst : savedWrongSuffixFirstOffset
      (r := rate) rewards C_star C_h source.1 = some offset) :
    FirstSavedWrongBoundaryComparison
      (launchCalendarRunInput (rate := rate) rewards C_star C_h start source)
      (index := offset)
      (by rw [firstSavedWrongOffset_eq_actualSuffix
        (rate := rate) rewards C_star C_h start source]; exact hfirst) :=
  firstSavedWrong_boundary
    (launchCalendarRunInput (rate := rate) rewards C_star C_h start source)
    (by rw [firstSavedWrongOffset_eq_actualSuffix
      (rate := rate) rewards C_star C_h start source]; exact hfirst)

/-- If the actual suffix has no saved wrong acceptance, apply the accepted
whole-safe-run comparison on the same genuine launch state and full suffix. -/
theorem calendarRun_eq_reference_of_savedWrongSuffixFirstOffset_none
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (start : Fin (p.T + 1))
    (source : GeneratedLaunchFiber (rate := rate) rewards C_star C_h start.val)
    (hnone : savedWrongSuffixFirstOffset
      (r := rate) rewards C_star C_h source.1 = none) :
    SavedWrongSafeRunComparison
      (launchCalendarRunInput (rate := rate) rewards C_star C_h start source) :=
  calendarRun_eq_reference_of_firstSavedWrongOffset_none
    (launchCalendarRunInput (rate := rate) rewards C_star C_h start source)
    (by rw [firstSavedWrongOffset_eq_actualSuffix
      (rate := rate) rewards C_star C_h start source]; exact hnone)

/-- Source exhaustion has no actual postlaunch suffix, so both diagnostics
are genuinely absent. -/
theorem savedWrongSuffixFirst_none_of_no_crossing
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none) :
    savedWrongSuffixFirstOffset (r := rate) rewards C_star C_h source = none ∧
      savedWrongSuffixFirstPhysicalTime (r := rate) rewards C_star C_h source = none ∧
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h = [] := by
  have hrecords := (ReferenceCompletePhysicalHistory.no_launch_complete_history
    rate source rewards C_star C_h hlaunch).2.1
  constructor
  · simp [savedWrongSuffixFirstOffset, hrecords]
  constructor
  · simp [savedWrongSuffixFirstPhysicalTime, savedWrongSuffixFirstOffset, hrecords]
  · exact hrecords

/-- A crossing at `T` is still a present launch with an empty zero-length
suffix. It is kept separate from source exhaustion. -/
theorem savedWrongSuffixFirst_none_of_terminal_crossing
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p)
    (active : ReferenceCompletePhysicalHistory.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active)
    (hterminal : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h = p.T) :
    savedWrongSuffixFirstOffset (r := rate) rewards C_star C_h source = none ∧
      savedWrongSuffixFirstPhysicalTime (r := rate) rewards C_star C_h source = none ∧
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h = [] := by
  have hrecords := (ReferenceCompletePhysicalHistory.terminal_crossing_complete_history
    rate source rewards C_star C_h active hlaunch hterminal).1
  constructor
  · simp [savedWrongSuffixFirstOffset, hrecords]
  constructor
  · simp [savedWrongSuffixFirstPhysicalTime, savedWrongSuffixFirstOffset, hrecords]
  · exact hrecords

end ReferenceGeneratedSavedWrongEvent

end Bandits.Support
